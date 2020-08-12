use sha3::{Digest, Sha3_256};

pub trait ProtectedState {
    fn info(&self) -> String;
    fn seal(&self) -> &String;
    fn set_seal(&mut self, seal: String);

    fn compute_seal(&mut self) {
        self.set_seal(seal(self.info()))
    }

    fn verify_seal(&self) -> bool {
        verify(self.info(), self.seal())
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
    s
}

pub fn verify(s: String, hash: &str) -> bool {
    seal(s) == hash
}
