use std::{collections::HashMap, fmt, hash::Hash, sync::Mutex};

use crate::{arena::DroplessArena, with_session_globals, SynEq};

newtype_index! {
    pub struct SymbolIndex { .. }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(SymbolIndex);

impl Symbol {
    const fn new(n: u32) -> Self {
        Symbol(SymbolIndex::from_u32(n))
    }

    /// Maps a string to its interned representation.
    pub fn intern(string: &str) -> Self {
        with_session_globals(|session_globals| session_globals.symbol_interner.intern(string))
    }

    /// Access the underlying string. This is a slowish operation because it
    /// requires locking the symbol interner.
    ///
    /// Note that the lifetime of the return value is a lie. It's not the same
    /// as `&self`, but actually tied to the lifetime of the underlying
    /// interner. Interners are long-lived, and there are very few of them, and
    /// this function is typically used for short-lived things, so in practice
    /// it works out ok.
    pub fn as_str(&self) -> &str {
        with_session_globals(|session_globals| unsafe {
            std::mem::transmute::<&str, &str>(session_globals.symbol_interner.get(*self))
        })
    }

    pub fn as_u32(self) -> u32 {
        self.0.as_u32()
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl SynEq for Symbol {
    fn syn_eq(&self, o: &Self) -> bool {
        self == o
    }
}

#[derive(Default)]
pub(crate) struct Interner(Mutex<InternerInner>);

#[derive(Default)]
struct InternerInner {
    arena: DroplessArena,
    names: HashMap<&'static str, Symbol>,
    strings: Vec<&'static str>,
}

impl Interner {
    pub fn fresh() -> Self {
        Self {
            ..Default::default()
        }
    }

    #[inline]
    fn intern(&self, string: &str) -> Symbol {
        let mut inner = self.0.lock().unwrap();
        if let Some(&name) = inner.names.get(string) {
            return name;
        }

        let name = Symbol::new(inner.strings.len() as u32);

        // SAFETY: we convert from `&str` to `&[u8]`, clone it into the arena,
        // and immediately convert the clone back to `&[u8], all because there
        // is no `inner.arena.alloc_str()` method. This is clearly safe.
        let string: &str =
            unsafe { std::str::from_utf8_unchecked(inner.arena.alloc_slice(string.as_bytes())) };

        // SAFETY: we can extend the arena allocation to `'static` because we
        // only access these while the arena is still alive.
        let string: &'static str = unsafe { &*(string as *const str) };
        inner.strings.push(string);

        // This second hash table lookup can be avoided by using `RawEntryMut`,
        // but this code path isn't hot enough for it to be worth it. See
        // #91445 for details.
        inner.names.insert(string, name);
        name
    }

    // Get the symbol as a string. `Symbol::as_str()` should be used in
    // preference to this function.
    fn get(&self, symbol: Symbol) -> &str {
        self.0.lock().unwrap().strings[symbol.0.as_usize()]
    }
}

mod serde {
    use super::Symbol;
    use ::serde::de::{Deserializer, Error, Unexpected, Visitor};
    use std::fmt;

    fn symbol<'de: 'a, 'a, D>(deserializer: D) -> Result<Symbol, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct KStrVisitor;

        impl<'a> Visitor<'a> for KStrVisitor {
            type Value = Symbol;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a string")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(Symbol::intern(v))
            }

            fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(Symbol::intern(v))
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(Symbol::intern(&v))
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: Error,
            {
                match std::str::from_utf8(v) {
                    Ok(s) => Ok(Symbol::intern(s)),
                    Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
                }
            }

            fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
            where
                E: Error,
            {
                match std::str::from_utf8(v) {
                    Ok(s) => Ok(Symbol::intern(s)),
                    Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
                }
            }

            fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
            where
                E: Error,
            {
                match String::from_utf8(v) {
                    Ok(s) => Ok(Symbol::intern(&s)),
                    Err(e) => Err(Error::invalid_value(
                        Unexpected::Bytes(&e.into_bytes()),
                        &self,
                    )),
                }
            }
        }

        deserializer.deserialize_str(KStrVisitor)
    }

    impl From<&str> for Symbol {
        fn from(s: &str) -> Self {
            Symbol::intern(s)
        }
    }

    impl serde::Serialize for Symbol {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            self.as_str().serialize(serializer)
        }
    }

    impl<'de> serde::Deserialize<'de> for Symbol {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            symbol(deserializer)
        }
    }
}
