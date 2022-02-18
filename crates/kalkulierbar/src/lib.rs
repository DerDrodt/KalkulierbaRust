#![feature(new_uninit, maybe_uninit_slice)]
pub mod calculi;
pub mod calculus;
pub mod clause;
mod consts;
pub mod logic;
#[macro_use]
mod macros;
#[allow(clippy::all)]
mod arena;
pub mod parse;
pub mod symbol;
pub mod tamper_protect;

pub use consts::CNF_BLOWUP_LIMIT;
pub use logic::Lit;
pub use symbol::Symbol;

pub use calculi::tableaux;
pub use calculi::CalculusKind;
pub use calculus::Calculus;

// Per-session global variables: this struct is stored in thread-local storage
// in such a way that it is accessible without any kind of handle to all
// threads within the compilation session, but is not accessible outside the
// session.
pub struct SessionGlobals {
    symbol_interner: symbol::Interner,
}

impl SessionGlobals {
    pub fn new() -> SessionGlobals {
        SessionGlobals {
            symbol_interner: symbol::Interner::fresh(),
        }
    }
}

impl Default for SessionGlobals {
    fn default() -> Self {
        Self::new()
    }
}

scoped_tls::scoped_thread_local!(static SESSION_GLOBALS: SessionGlobals);

#[inline]
pub fn session<R>(f: impl FnOnce() -> R) -> R {
    assert!(
        !SESSION_GLOBALS.is_set(),
        "SESSION_GLOBALS should never be overwritten! \
         Use another thread if you need another SessionGlobals"
    );
    let session_globals = SessionGlobals::new();
    SESSION_GLOBALS.set(&session_globals, f)
}

#[inline]
pub fn with_session_globals<R, F>(f: F) -> R
where
    F: FnOnce(&SessionGlobals) -> R,
{
    SESSION_GLOBALS.with(f)
}
