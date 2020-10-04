use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct CloseMsg {
    pub closed: bool,
    pub msg: String,
}

pub trait Calculus<'f> {
    type Params;
    type State;
    type Move;
    type Error;

    fn parse_formula(
        formula: &'f str,

        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error>;

    fn validate(_state: Self::State) -> bool {
        true
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error>;

    fn check_close(state: Self::State) -> CloseMsg;
}
