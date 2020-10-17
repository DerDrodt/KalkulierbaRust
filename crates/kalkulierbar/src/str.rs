use std::{borrow::Borrow, cmp::Ordering, fmt, hash, iter, ops::Deref, sync::Arc};

#[derive(Clone)]
pub struct KStr(Repr);

impl KStr {
    pub const fn new_inline(text: &str) -> Self {
        let mut buf = [0; INLINE_CAP];
        let mut i = 0;
        while i < text.len() {
            buf[i] = text.as_bytes()[i];
            i += 1
        }
        KStr(Repr::Inline {
            len: text.len() as u8,
            buf,
        })
    }

    pub fn new<T>(text: T) -> Self
    where
        T: AsRef<str>,
    {
        KStr(Repr::new(text))
    }

    #[inline(always)]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    #[inline(always)]
    pub fn to_string(&self) -> String {
        self.as_str().to_string()
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline(always)]
    pub fn is_heap_allocated(&self) -> bool {
        match self.0 {
            Repr::Heap(..) => true,
            _ => false,
        }
    }

    fn from_char_iter<I: iter::Iterator<Item = char>>(mut iter: I) -> Self {
        let (min_size, _) = iter.size_hint();
        if min_size > INLINE_CAP {
            let heap: String = iter.collect();
            return KStr(Repr::Heap(heap.into_boxed_str().into()));
        }
        let mut len = 0;
        let mut buf = [0u8; INLINE_CAP];
        while let Some(ch) = iter.next() {
            let size = ch.len_utf8();
            if size + len > INLINE_CAP {
                let (min_remaining, _) = iter.size_hint();
                let mut heap = String::with_capacity(size + len + min_remaining);
                heap.push_str(std::str::from_utf8(&buf[..len]).unwrap());
                heap.push(ch);
                heap.extend(iter);
                return KStr(Repr::Heap(heap.into_boxed_str().into()));
            }
            ch.encode_utf8(&mut buf[len..]);
            len += size;
        }
        KStr(Repr::Inline {
            len: len as u8,
            buf,
        })
    }
}

impl Default for KStr {
    fn default() -> Self {
        KStr::new("")
    }
}

impl Deref for KStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl PartialEq<KStr> for KStr {
    fn eq(&self, other: &KStr) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for KStr {}

impl PartialEq<str> for KStr {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<KStr> for str {
    fn eq(&self, other: &KStr) -> bool {
        other == self
    }
}

impl<'a> PartialEq<&'a str> for KStr {
    fn eq(&self, other: &&'a str) -> bool {
        self == *other
    }
}

impl<'a> PartialEq<KStr> for &'a str {
    fn eq(&self, other: &KStr) -> bool {
        *self == other
    }
}

impl PartialEq<String> for KStr {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<KStr> for String {
    fn eq(&self, other: &KStr) -> bool {
        other == self
    }
}

impl<'a> PartialEq<&'a String> for KStr {
    fn eq(&self, other: &&'a String) -> bool {
        self == *other
    }
}

impl<'a> PartialEq<KStr> for &'a String {
    fn eq(&self, other: &KStr) -> bool {
        *self == other
    }
}

impl Ord for KStr {
    fn cmp(&self, other: &KStr) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for KStr {
    fn partial_cmp(&self, other: &KStr) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl hash::Hash for KStr {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl fmt::Debug for KStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for KStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl iter::FromIterator<char> for KStr {
    fn from_iter<I: iter::IntoIterator<Item = char>>(iter: I) -> Self {
        let iter = iter.into_iter();
        Self::from_char_iter(iter)
    }
}

fn build_from_str_iter<T>(mut iter: impl Iterator<Item = T>) -> KStr
where
    T: AsRef<str>,
    String: iter::Extend<T>,
{
    let mut len = 0;
    let mut buf = [0u8; INLINE_CAP];
    while let Some(slice) = iter.next() {
        let slice = slice.as_ref();
        let size = slice.len();
        if size + len > INLINE_CAP {
            let mut heap = String::with_capacity(size + len);
            heap.push_str(std::str::from_utf8(&buf[..len]).unwrap());
            heap.push_str(&slice);
            heap.extend(iter);
            return KStr(Repr::Heap(heap.into_boxed_str().into()));
        }
        (&mut buf[len..][..size]).copy_from_slice(slice.as_bytes());
        len += size;
    }
    KStr(Repr::Inline {
        len: len as u8,
        buf,
    })
}

impl iter::FromIterator<String> for KStr {
    fn from_iter<I: iter::IntoIterator<Item = String>>(iter: I) -> KStr {
        build_from_str_iter(iter.into_iter())
    }
}

impl<'a> iter::FromIterator<&'a String> for KStr {
    fn from_iter<I: iter::IntoIterator<Item = &'a String>>(iter: I) -> KStr {
        KStr::from_iter(iter.into_iter().map(|x| x.as_str()))
    }
}

impl<'a> iter::FromIterator<&'a str> for KStr {
    fn from_iter<I: iter::IntoIterator<Item = &'a str>>(iter: I) -> KStr {
        build_from_str_iter(iter.into_iter())
    }
}

impl<T> From<T> for KStr
where
    T: Into<String> + AsRef<str>,
{
    fn from(text: T) -> Self {
        Self::new(text)
    }
}

impl From<KStr> for String {
    fn from(text: KStr) -> Self {
        text.as_str().into()
    }
}

impl Borrow<str> for KStr {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

const INLINE_CAP: usize = 22;
#[derive(Clone, Debug)]
enum Repr {
    Heap(Arc<str>),
    Inline { len: u8, buf: [u8; INLINE_CAP] },
}

impl Repr {
    fn new<T>(text: T) -> Self
    where
        T: AsRef<str>,
    {
        let text = text.as_ref();
        let len = text.len();

        if len <= INLINE_CAP {
            let mut buf = [0; INLINE_CAP];
            buf[..len].copy_from_slice(text.as_bytes());
            return Repr::Inline {
                len: len as u8,
                buf,
            };
        }

        Repr::Heap(text.into())
    }

    #[inline(always)]
    fn len(&self) -> usize {
        match self {
            Repr::Heap(data) => data.len(),
            Repr::Inline { len, .. } => *len as usize,
        }
    }

    #[inline(always)]
    fn is_empty(&self) -> bool {
        match self {
            Repr::Heap(data) => data.is_empty(),
            Repr::Inline { len, .. } => *len == 0,
        }
    }

    #[inline]
    fn as_str(&self) -> &str {
        match self {
            Repr::Heap(data) => &*data,
            Repr::Inline { len, buf } => {
                let len = *len as usize;
                let buf = &buf[..len];
                unsafe { ::std::str::from_utf8_unchecked(buf) }
            }
        }
    }
}

mod serde {
    use super::KStr;
    use ::serde::de::{Deserializer, Error, Unexpected, Visitor};
    use std::fmt;

    fn k_str<'de: 'a, 'a, D>(deserializer: D) -> Result<KStr, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct KStrVisitor;

        impl<'a> Visitor<'a> for KStrVisitor {
            type Value = KStr;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a string")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(KStr::from(v))
            }

            fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(KStr::from(v))
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(KStr::from(v))
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: Error,
            {
                match std::str::from_utf8(v) {
                    Ok(s) => Ok(KStr::from(s)),
                    Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
                }
            }

            fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
            where
                E: Error,
            {
                match std::str::from_utf8(v) {
                    Ok(s) => Ok(KStr::from(s)),
                    Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
                }
            }

            fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
            where
                E: Error,
            {
                match String::from_utf8(v) {
                    Ok(s) => Ok(KStr::from(s)),
                    Err(e) => Err(Error::invalid_value(
                        Unexpected::Bytes(&e.into_bytes()),
                        &self,
                    )),
                }
            }
        }

        deserializer.deserialize_str(KStrVisitor)
    }

    impl serde::Serialize for KStr {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            self.as_str().serialize(serializer)
        }
    }

    impl<'de> serde::Deserialize<'de> for KStr {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            k_str(deserializer)
        }
    }
}
