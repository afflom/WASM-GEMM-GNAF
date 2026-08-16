//! SHA-1, implemented over std, for one purpose: recomputing **git blob object
//! ids** from vendored bytes.
//!
//! SPEC section 5 requires offline verification to recompute a pin from CONTENT
//! rather than trust a checksum string. `vendor/wasm-spec/SHA256SUMS` does that
//! for the bytes, but it is a file this repository wrote: it proves the tree has
//! not changed since we wrote it down, not that the tree is the one the pinned
//! commit names.
//!
//! `vendor/wasm-spec/BLOBS` closes that. A git blob id is
//! `sha1("blob " ++ len ++ "\0" ++ content)` -- a function of the bytes alone --
//! and it is exactly the identity the pinned commit's tree lists each file
//! under. Recomputing it here turns "these are the vendored bytes we recorded"
//! into "these are the bytes commit 9d360199... names", with no network and no
//! `git` invocation.
//!
//! SHA-1 is used here as a CONTENT ADDRESS, never as a security primitive: the
//! chain of trust is the pinned commit id, and SPEC section 19 forbids resting
//! any claim on a cryptographic collision assumption. A colliding blob would
//! also have to satisfy `SHA256SUMS`, which this does not replace.

const INIT: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

/// A streaming SHA-1 state. FIPS 180-4, no options.
pub struct Sha1 {
    state: [u32; 5],
    buffer: [u8; 64],
    buffered: usize,
    length: u64,
}

impl Sha1 {
    pub fn new() -> Self {
        Sha1 {
            state: INIT,
            buffer: [0; 64],
            buffered: 0,
            length: 0,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        self.length = self.length.wrapping_add(data.len() as u64);
        if self.buffered > 0 {
            let want = 64 - self.buffered;
            let take = want.min(data.len());
            self.buffer[self.buffered..self.buffered + take].copy_from_slice(&data[..take]);
            self.buffered += take;
            data = &data[take..];
            if self.buffered == 64 {
                let block = self.buffer;
                self.compress(&block);
                self.buffered = 0;
            }
        }
        while data.len() >= 64 {
            let mut block = [0u8; 64];
            block.copy_from_slice(&data[..64]);
            self.compress(&block);
            data = &data[64..];
        }
        if !data.is_empty() {
            self.buffer[..data.len()].copy_from_slice(data);
            self.buffered = data.len();
        }
    }

    pub fn finish(mut self) -> [u8; 20] {
        let bits = self.length.wrapping_mul(8);
        self.update(&[0x80]);
        // `update` counted the padding byte; the length field must not.
        self.length = self.length.wrapping_sub(1);
        while self.buffered != 56 {
            self.update(&[0x00]);
            self.length = self.length.wrapping_sub(1);
        }
        let mut tail = [0u8; 8];
        tail.copy_from_slice(&bits.to_be_bytes());
        self.update(&tail);

        let mut out = [0u8; 20];
        for (i, word) in self.state.iter().enumerate() {
            out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
        }
        out
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 80];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[i * 4],
                block[i * 4 + 1],
                block[i * 4 + 2],
                block[i * 4 + 3],
            ]);
        }
        for i in 16..80 {
            w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
        }

        let [mut a, mut b, mut c, mut d, mut e] = self.state;
        for (i, wi) in w.iter().enumerate() {
            let (f, k) = match i {
                0..=19 => ((b & c) | ((!b) & d), 0x5a827999u32),
                20..=39 => (b ^ c ^ d, 0x6ed9eba1),
                40..=59 => ((b & c) | (b & d) | (c & d), 0x8f1bbcdc),
                _ => (b ^ c ^ d, 0xca62c1d6),
            };
            let temp = a
                .rotate_left(5)
                .wrapping_add(f)
                .wrapping_add(e)
                .wrapping_add(k)
                .wrapping_add(*wi);
            e = d;
            d = c;
            c = b.rotate_left(30);
            b = a;
            a = temp;
        }

        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
    }
}

impl Default for Sha1 {
    fn default() -> Self {
        Self::new()
    }
}

pub fn to_hex(digest: &[u8; 20]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(40);
    for byte in digest {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

/// The git blob object id of `content`: `sha1("blob " ++ len ++ "\0" ++ content)`.
///
/// This is the identity a git tree lists a file under, so it is what ties the
/// vendored bytes to the pinned COMMIT rather than to a digest file we wrote.
pub fn blob_hex(content: &[u8]) -> String {
    let mut hasher = Sha1::new();
    hasher.update(b"blob ");
    hasher.update(content.len().to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(content);
    to_hex(&hasher.finish())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_fips_vectors() {
        let mut h = Sha1::new();
        h.update(b"abc");
        assert_eq!(
            to_hex(&h.finish()),
            "a9993e364706816aba3e25717850c26c9cd0d89d"
        );

        let h = Sha1::new();
        assert_eq!(
            to_hex(&h.finish()),
            "da39a3ee5e6b4b0d3255bfef95601890afd80709"
        );

        let mut h = Sha1::new();
        h.update(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq");
        assert_eq!(
            to_hex(&h.finish()),
            "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
        );
    }

    #[test]
    fn spans_block_boundaries() {
        // 1,000,000 'a' -- the FIPS long message, fed in awkward chunks so the
        // buffering path is exercised rather than the aligned fast path.
        let mut h = Sha1::new();
        let chunk = vec![b'a'; 7];
        for _ in 0..142857 {
            h.update(&chunk);
        }
        h.update(b"a");
        assert_eq!(
            to_hex(&h.finish()),
            "34aa973cd4c4daa4f61eeb2bdbad27316534016f"
        );
    }

    #[test]
    fn computes_git_blob_ids() {
        // `printf '' | git hash-object --stdin`
        assert_eq!(blob_hex(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391");
        // `printf 'hello\n' | git hash-object --stdin`
        assert_eq!(
            blob_hex(b"hello\n"),
            "ce013625030ba8dba906f756967f9e9ca394464a"
        );
    }
}
