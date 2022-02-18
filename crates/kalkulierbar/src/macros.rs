#[macro_export]
macro_rules! newtype_index {
    // ---- public rules ----

    // Use default constants
    ($(#[$attrs:meta])* $v:vis struct $name:ident { .. }) => (
        newtype_index!(
            // Leave out derives marker so we can use its absence to ensure it comes first
            @attrs        [$(#[$attrs])*]
            @type         [$name]
            // shave off 256 indices at the end to allow space for packing these indices into enums
            @max          [0xFFFF_FF00]
            @vis          [$v]
            @debug_format ["{}"]);
    );

    // Define any constants
    ($(#[$attrs:meta])* $v:vis struct $name:ident { $($tokens:tt)+ }) => (
        newtype_index!(
            // Leave out derives marker so we can use its absence to ensure it comes first
            @attrs        [$(#[$attrs])*]
            @type         [$name]
            // shave off 256 indices at the end to allow space for packing these indices into enums
            @max          [0xFFFF_FF00]
            @vis          [$v]
            @debug_format ["{}"]
                          $($tokens)+);
    );

    // ---- private rules ----

    // Base case, user-defined constants (if any) have already been defined
    (@derives      [$($derives:ident,)*]
     @attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]) => (
        $(#[$attrs])*
        #[derive(Copy, PartialEq, Eq, Hash, PartialOrd, Ord, $($derives),*)]
        $v struct $type {
            private: u32
        }

        impl Clone for $type {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl $type {
            $v const MAX_AS_U32: u32 = $max;

            $v const MAX: $type = $type::from_u32_const($max);

            #[inline]
            $v fn from_usize(value: usize) -> Self {
                assert!(value <= ($max as usize));
                $type::from_u32_unchecked(value as u32)
            }

            #[inline]
            $v const fn from_u32(value: u32) -> Self {
                assert!(value <= $max);
                $type::from_u32_unchecked(value)
            }

            /// Hacky variant of `from_u32` for use in constants.
            /// This version checks the "max" constraint by using an
            /// invalid array dereference.
            #[inline]
            $v const fn from_u32_const(value: u32) -> Self {
                // This will fail at const eval time unless `value <=
                // max` is true (in which case we get the index 0).
                // It will also fail at runtime, of course, but in a
                // kind of wacky way.
                let _ = ["out of range value used"][
                    !(value <= $max) as usize
                ];

                //unsafe {
                    $type { private: value }
                //}
            }

            #[inline]
            $v const fn from_u32_unchecked(value: u32) -> Self {
                $type { private: value }
            }

            /// Extracts the value of this index as an integer.
            #[inline]
            $v fn index(self) -> usize {
                self.as_usize()
            }

            /// Extracts the value of this index as a `u32`.
            #[inline]
            $v fn as_u32(self) -> u32 {
                self.private
            }

            /// Extracts the value of this index as a `usize`.
            #[inline]
            $v fn as_usize(self) -> usize {
                self.as_u32() as usize
            }
        }

        impl From<$type> for u32 {
            #[inline]
            fn from(v: $type) -> u32 {
                v.as_u32()
            }
        }

        impl From<$type> for usize {
            #[inline]
            fn from(v: $type) -> usize {
                v.as_usize()
            }
        }

        impl From<usize> for $type {
            #[inline]
            fn from(value: usize) -> Self {
                $type::from_usize(value)
            }
        }

        impl From<u32> for $type {
            #[inline]
            fn from(value: u32) -> Self {
                $type::from_u32(value)
            }
        }

        newtype_index!(
            @handle_debug
            @derives      [$($derives,)*]
            @type         [$type]
            @debug_format [$debug_format]);
    );

    // base case for handle_debug where format is custom. No Debug implementation is emitted.
    (@handle_debug
     @derives      [$($_derives:ident,)*]
     @type         [$type:ident]
     @debug_format [custom]) => ();

    // base case for handle_debug, no debug overrides found, so use default
    (@handle_debug
     @derives      []
     @type         [$type:ident]
     @debug_format [$debug_format:tt]) => (
        impl ::std::fmt::Debug for $type {
            fn fmt(&self, fmt: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                write!(fmt, $debug_format, self.as_u32())
            }
        }
    );

    // Debug is requested for derive, don't generate any Debug implementation.
    (@handle_debug
     @derives      [Debug, $($derives:ident,)*]
     @type         [$type:ident]
     @debug_format [$debug_format:tt]) => ();

    // It's not Debug, so just pop it off the front of the derives stack and check the rest.
    (@handle_debug
     @derives      [$_derive:ident, $($derives:ident,)*]
     @type         [$type:ident]
     @debug_format [$debug_format:tt]) => (
        newtype_index!(
            @handle_debug
            @derives      [$($derives,)*]
            @type         [$type]
            @debug_format [$debug_format]);
    );

    // Append comma to end of derives list if it's missing
    (@attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   derive [$($derives:ident),*]
                   $($tokens:tt)*) => (
        newtype_index!(
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          derive [$($derives,)*]
                          $($tokens)*);
    );

    // By not including the @derives marker in this list nor in the default args, we can force it
    // to come first if it exists. When encodable is custom, just use the derives list as-is.
    (@attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   derive [$($derives:ident,)+]
                   ENCODABLE = custom
                   $($tokens:tt)*) => (
        newtype_index!(
            @attrs        [$(#[$attrs])*]
            @derives      [$($derives,)+]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
    );

    // By not including the @derives marker in this list nor in the default args, we can force it
    // to come first if it exists. When encodable isn't custom, add serialization traits by default.
    (@attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   derive [$($derives:ident,)+]
                   $($tokens:tt)*) => (
        newtype_index!(
            @derives      [$($derives,)+ RustcEncodable,]
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
        newtype_index!(@decodable $type);
    );

    // The case where no derives are added, but encodable is overridden. Don't
    // derive serialization traits
    (@attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   ENCODABLE = custom
                   $($tokens:tt)*) => (
        newtype_index!(
            @derives      []
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
    );

    // The case where no derives are added, add serialization derives by default
    (@attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   $($tokens:tt)*) => (
        newtype_index!(
            @derives      []
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
        //newtype_index!(@decodable $type);
    );

    // Rewrite final without comma to one that includes comma
    (@derives      [$($derives:ident,)*]
     @attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   $name:ident = $constant:expr) => (
        newtype_index!(
            @derives      [$($derives,)*]
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $name = $constant,);
    );

    // Rewrite final const without comma to one that includes comma
    (@derives      [$($derives:ident,)*]
     @attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   $(#[doc = $doc:expr])*
                   const $name:ident = $constant:expr) => (
        newtype_index!(
            @derives      [$($derives,)*]
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $(#[doc = $doc])* const $name = $constant,);
    );

    // Replace existing default for max
    (@derives      [$($derives:ident,)*]
     @attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$_max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   MAX = $max:expr,
                   $($tokens:tt)*) => (
        newtype_index!(
            @derives      [$($derives,)*]
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
    );

    // Replace existing default for debug_format
    (@derives      [$($derives:ident,)*]
     @attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$_debug_format:tt]
                   DEBUG_FORMAT = $debug_format:tt,
                   $($tokens:tt)*) => (
        newtype_index!(
            @derives      [$($derives,)*]
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
    );

    // Assign a user-defined constant
    (@derives      [$($derives:ident,)*]
     @attrs        [$(#[$attrs:meta])*]
     @type         [$type:ident]
     @max          [$max:expr]
     @vis          [$v:vis]
     @debug_format [$debug_format:tt]
                   $(#[doc = $doc:expr])*
                   const $name:ident = $constant:expr,
                   $($tokens:tt)*) => (
        $(#[doc = $doc])*
        pub const $name: $type = $type::from_u32_const($constant);
        newtype_index!(
            @derives      [$($derives,)*]
            @attrs        [$(#[$attrs])*]
            @type         [$type]
            @max          [$max]
            @vis          [$v]
            @debug_format [$debug_format]
                          $($tokens)*);
    );
}
