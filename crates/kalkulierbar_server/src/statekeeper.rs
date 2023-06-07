use chrono::Utc;
use core::fmt;
use sha3::{Digest, Sha3_256};
use std::{fs, io::Write, sync::Mutex};

use kalkulierbar::CalculusKind;
use serde::{Deserialize, Serialize};

const PATH: &str = "kbar-state.json";

const EXAMPLE_NAME_SIZE: usize = 140;
const EXAMPLE_DESC_SIZE: usize = 280;
const EXAMPLE_FORMULA_SIZE: usize = 1024;
const EXAMPLE_PARAM_SIZE: usize = 512;
const EXAMPLE_CALC_NAME_SIZE: usize = 64;
const MAX_EXAMPLE_COUNT: usize = 128;

#[derive(Debug, Clone)]
pub enum StateKeeperErr {
    AuthErr,
    StorageErr(&'static str, usize),
    NoSuchExample(usize),
    ExampleLimit,
}

impl fmt::Display for StateKeeperErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StateKeeperErr::AuthErr => write!(f, "Invalid password"),
            StateKeeperErr::StorageErr(field, limit) => {
                write!(f, "Example {field} exceeds size limit of {limit}")
            }
            StateKeeperErr::NoSuchExample(id) => write!(f, "Example with ID {id} does not exist"),
            StateKeeperErr::ExampleLimit => {
                write!(
                    f,
                    "Maximum number of stored examples ({MAX_EXAMPLE_COUNT}) exceeded"
                )
            }
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AppState {
    key: String,
    disabled_calculi: Vec<CalculusKind>,
    examples: Vec<Example>,
}

impl AppState {
    fn new(key: String) -> Self {
        Self {
            key,
            disabled_calculi: vec![],
            examples: vec![],
        }
    }

    pub fn to_config(&self) -> Config {
        Config {
            disabled: self.disabled_calculi.clone(),
            examples: self.examples.clone(),
        }
    }
}

impl Default for AppState {
    fn default() -> Self {
        Self::new("WildFlowers/UncomfortableMoons".to_string())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    disabled: Vec<CalculusKind>,
    examples: Vec<Example>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Example {
    name: String,
    description: String,
    calculus: String,
    formula: String,
    params: String,
}

pub struct StateKeeper {
    pub state: Mutex<AppState>,
}

lazy_static! {
    static ref DATE: String = {
        let utc = Utc::now();
        utc.format("%Y%m&d").to_string()
    };
}

impl StateKeeper {
    pub fn new() -> Self {
        let state: AppState = match fs::read_to_string(PATH) {
            Ok(s) => serde_json::from_str(&s).unwrap(),
            Err(_) => AppState::default(),
        };
        Self {
            state: Mutex::new(state),
        }
    }

    pub fn get_config(&self) -> Config {
        // TODO: Stats.logHit("config")

        self.state.lock().unwrap().to_config()
    }

    pub fn check_credentials(&self, mac: &str) -> Result<bool, StateKeeperErr> {
        let fingerprint = "kbcc";
        if !self.verify_mac(fingerprint, mac) {
            Err(StateKeeperErr::AuthErr)
        } else {
            Ok(true)
        }
    }

    pub fn set_calculus_state(
        &self,
        c: CalculusKind,
        enable: bool,
        mac: &str,
    ) -> Result<bool, StateKeeperErr> {
        let fingerprint = format!("kbsc|{c}|{enable}");
        if !self.verify_mac(&fingerprint, mac) {
            return Err(StateKeeperErr::AuthErr);
        }

        let mut state = self.state.lock().unwrap();
        if enable {
            let index = state.disabled_calculi.iter().position(|x| *x == c);
            if let Some(index) = index {
                state.disabled_calculi.remove(index);
            }
        } else if !state.disabled_calculi.contains(&c) {
            state.disabled_calculi.push(c);
        }

        self.flush();

        Ok(true)
    }

    pub fn add_example(
        &self,
        example: Example,
        ex_json: &str,
        mac: &str,
    ) -> Result<bool, StateKeeperErr> {
        let fp = format!("kbae|{ex_json}");
        if !self.verify_mac(&fp, mac) {
            return Err(StateKeeperErr::AuthErr);
        }

        // Since we will be writing this to disk, let's
        // make sure that the example is somewhat sane
        check_sanity(&example)?;

        let mut state = self.state.lock().unwrap();
        if state.examples.len() >= MAX_EXAMPLE_COUNT {
            return Err(StateKeeperErr::ExampleLimit);
        }
        state.examples.push(example);
        self.flush();

        Ok(true)
    }

    pub fn remove_example(&self, example_id: usize, mac: &str) -> Result<bool, StateKeeperErr> {
        let fp = format!("kbde|{example_id}");
        if !self.verify_mac(&fp, mac) {
            return Err(StateKeeperErr::AuthErr);
        }

        let mut state = self.state.lock().unwrap();
        if example_id >= state.examples.len() {
            return Err(StateKeeperErr::NoSuchExample(example_id));
        }

        state.examples.remove(example_id);
        self.flush();

        Ok(true)
    }

    fn verify_mac(&self, payload: &str, mac: &str) -> bool {
        let state = self.state.lock().unwrap();
        let p_with_key = format!("{payload}|{}|{}", *DATE, state.key);
        let c_mac = {
            let mut hasher = Sha3_256::new();
            hasher.update(p_with_key);
            let res = hasher.finalize();
            let mut s = String::new();
            for b in res {
                s.push_str(&format!("{:02x}", b));
            }
            s.to_uppercase()
        };
        c_mac == mac.to_uppercase()
    }

    fn reset(&self) {
        let mut state = self.state.lock().unwrap();
        state.disabled_calculi.clear();
        state.examples.clear();
    }

    fn flush(&self) {
        let mut file = match fs::File::open(PATH) {
            Ok(f) => f,
            Err(_) => fs::File::create(PATH).unwrap(),
        };
        let s = serde_json::to_string(&self.state).expect("couldn't serialize state");
        file.write_all(s.as_bytes())
            .expect("couldn't write buffer to file");
    }
}
fn check_sanity(e: &Example) -> Result<(), StateKeeperErr> {
    if e.name.len() > EXAMPLE_NAME_SIZE {
        return Err(StateKeeperErr::StorageErr("name", EXAMPLE_NAME_SIZE));
    }
    if e.description.len() > EXAMPLE_DESC_SIZE {
        return Err(StateKeeperErr::StorageErr("description", EXAMPLE_DESC_SIZE));
    }
    if e.formula.len() > EXAMPLE_FORMULA_SIZE {
        return Err(StateKeeperErr::StorageErr("formula", EXAMPLE_FORMULA_SIZE));
    }
    if e.params.len() > EXAMPLE_PARAM_SIZE {
        return Err(StateKeeperErr::StorageErr("parameters", EXAMPLE_PARAM_SIZE));
    }
    if e.calculus.len() > EXAMPLE_CALC_NAME_SIZE {
        return Err(StateKeeperErr::StorageErr(
            "calculus name",
            EXAMPLE_CALC_NAME_SIZE,
        ));
    }
    Ok(())
}
