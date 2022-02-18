use sha3::{Digest, Sha3_256};

pub trait ProtectedState {
    fn compute_seal_info(&self) -> String;

    fn verify_seal(&self, seal: &str) -> bool {
        verify(self.compute_seal_info(), seal)
    }
}

pub fn seal(s: String) -> String {
    let payload = format!(
        "i understand that modifying this object may lead to incorrect proofs|{}",
        s
    );
    let mut hasher = Sha3_256::new();
    hasher.update(payload);
    let res = hasher.finalize();
    let mut s = String::new();
    for b in res {
        s.push_str(&format!("{:02x}", b));
    }
    s.to_uppercase()
}

pub fn verify(s: String, hash: &str) -> bool {
    seal(s) == hash
}
