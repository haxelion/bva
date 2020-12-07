use std::convert::{From, TryFrom};
use std::fmt::{Binary, Display, LowerHex, Octal, UpperHex};
use std::io::{Read, Write};
use std::iter::repeat;
use std::mem::size_of;
use std::num::Wrapping;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, 
    Range, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use crate::{Bit, BitVector, Endianness};

// Beware! Here be hardcore macro magic!

/// Implement the binary operation (`$trait`, `$method`) for `$t` backed by the underlying type `$st`
/// and the rhs `$rhs`.
/// Also implement the various borrowed versions
macro_rules! impl_op { ($t:ident, $st:ty, $rhs:ty, $trait:ident, $method:ident) => {
    impl $trait<$rhs> for $t {
        type Output = $t;
        fn $method(self, rhs: $rhs) -> $t {
            let length = u8::max(self.length, rhs.length);
            $t {
                data: self.data.$method(Wrapping(rhs.data.0 as $st)) & <$t>::mask(length as usize),
                length
            }
        }
    }

    impl $trait<&'_ $rhs> for $t {
        type Output = $t;
        fn $method(self, rhs: &'_ $rhs) -> $t {
            let length = u8::max(self.length, rhs.length);
            $t {
                data: self.data.$method(Wrapping(rhs.data.0 as $st)) & <$t>::mask(length as usize),
                length
            }
        }
    }

    impl $trait<$rhs> for &'_ $t {
        type Output = $t;
        fn $method(self, rhs: $rhs) -> $t {
            let length = u8::max(self.length, rhs.length);
            $t {
                data: self.data.$method(Wrapping(rhs.data.0 as $st)) & <$t>::mask(length as usize),
                length
            }
        }
    }

    impl $trait<&'_ $rhs> for &'_ $t {
        type Output = $t;
        fn $method(self, rhs: &'_ $rhs) -> $t {
            let length = u8::max(self.length, rhs.length);
            $t {
                data: self.data.$method(Wrapping(rhs.data.0 as $st)) & <$t>::mask(length as usize),
                length
            }
        }
    }
}}

/// Implement the assign variant of the binary operation (`$trait`, `$method`) for `$t` 
/// backed by the underlying type `$st` and the rhs `$t2`.
/// Also implement the various borrowed versions.
macro_rules! impl_op_assign { ($t:ident, $st:ty, $rhs:ty, $trait:ident, $method:ident) => {
    impl $trait<$rhs> for $t {
        fn $method(&mut self, rhs: $rhs) {
            self.length = u8::max(self.length, rhs.length);
            self.data.$method(Wrapping(rhs.data.0 as $st));
            self.data &= Self::mask(self.len());
        }
    }

    impl $trait<&'_ $rhs> for $t {
        fn $method(&mut self, rhs: &'_ $rhs) {
            self.length = u8::max(self.length, rhs.length);
            self.data.$method(Wrapping(rhs.data.0 as $st));
            self.data &= Self::mask(self.len());

        }
    }
}}

macro_rules! impl_shl {($t:ident, {$($rhs:ty),+}) => {
    $(
        impl Shl<$rhs> for $t {
            type Output = $t;
            fn shl(self, rhs: $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shl(rhs as u32).unwrap_or(0)) & <$t>::mask(self.len()),
                    length: self.length
                }
            }
        }

        impl Shl<$rhs> for &'_ $t {
            type Output = $t;
            fn shl(self, rhs: $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shl(rhs as u32).unwrap_or(0)) & <$t>::mask(self.len()),
                    length: self.length
                }
            }
        }

        impl Shl<&'_ $rhs> for $t {
            type Output = $t;
            fn shl(self, rhs: &'_ $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shl(*rhs as u32).unwrap_or(0)) & <$t>::mask(self.len()),
                    length: self.length
                }
            }
        }

        impl Shl<&'_ $rhs> for &'_ $t {
            type Output = $t;
            fn shl(self, rhs: &'_ $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shl(*rhs as u32).unwrap_or(0)) & <$t>::mask(self.len()),
                    length: self.length
                }
            }
        }
    )+
}}

macro_rules! impl_shr {($t:ident, {$($rhs:ty),+}) => {
    $(
        impl Shr<$rhs> for $t {
            type Output = $t;
            fn shr(self, rhs: $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shr(rhs as u32).unwrap_or(0)),
                    length: self.length
                }
            }
        }

        impl Shr<$rhs> for &'_ $t {
            type Output = $t;
            fn shr(self, rhs: $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shr(rhs as u32).unwrap_or(0)),
                    length: self.length
                }
            }
        }

        impl Shr<&'_ $rhs> for $t {
            type Output = $t;
            fn shr(self, rhs: &'_ $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shr(*rhs as u32).unwrap_or(0)),
                    length: self.length
                }
            }
        }

        impl Shr<&'_ $rhs> for &'_ $t {
            type Output = $t;
            fn shr(self, rhs: &'_ $rhs) -> $t {
                $t {
                    data: Wrapping(self.data.0.checked_shr(*rhs as u32).unwrap_or(0)),
                    length: self.length
                }
            }
        }
    )+
}}

macro_rules! impl_shl_assign {($t:ident, {$($rhs:ty),+}) => {
    $(
        impl ShlAssign<$rhs> for $t {
            fn shl_assign(&mut self, rhs: $rhs) {
                self.data = Wrapping(self.data.0.checked_shl(rhs as u32).unwrap_or(0)) & Self::mask(self.len());
            }
        }


        impl ShlAssign<&'_ $rhs> for $t {
            fn shl_assign(&mut self, rhs: &'_ $rhs) {
                self.data = Wrapping(self.data.0.checked_shl(*rhs as u32).unwrap_or(0)) & Self::mask(self.len());
            }
        }
    )+
}}

macro_rules! impl_shr_assign {($t:ident, {$($rhs:ty),+}) => {
    $(
        impl ShrAssign<$rhs> for $t {
            fn shr_assign(&mut self, rhs: $rhs) {
                self.data = Wrapping(self.data.0.checked_shr(rhs as u32).unwrap_or(0));
            }
        }

        impl ShrAssign<&'_ $rhs> for $t {
            fn shr_assign(&mut self, rhs: &'_ $rhs) {
                self.data = Wrapping(self.data.0.checked_shr(*rhs as u32).unwrap_or(0));
            }
        }
    )+
}}

/// Declare a new fixed BitVector type named `$name`, backed by the underlying storage type `$st` 
/// and accepting for its operations a list of valid rhs BA types `$rhs`.
/// In addition, a list of sub storage type is also specified.
macro_rules! decl_bv { ($name:ident, $st:ty, {$(($rhs:ident, $sst:ty)),*}) => {
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
    pub struct $name {
        data: Wrapping<$st>,
        length: u8
    }

    /// Fixed capacity bit vector backed by a single unsigned integer.
    /// Operation exceding the underlying capacity will panic.
    impl $name {
        pub const CAPACITY: usize = size_of::<$st>() * 8;

        fn mask(length: usize) -> Wrapping<$st> {
            Wrapping(<$st>::MAX.checked_shr((Self::CAPACITY - length) as u32).unwrap_or(0))
        }
    }

    impl BitVector for $name {
        fn zeros(length: usize) -> Self {
            debug_assert!(length <= Self::CAPACITY);
            Self {
                data: Wrapping(0),
                length: length as u8,
            }
        }

        fn ones(length: usize) -> Self {
            debug_assert!(length <= Self::CAPACITY);
            Self {
                data: Wrapping(<$st>::MAX) & Self::mask(length),
                length: length as u8
            }
        }

        fn from_binary<S: AsRef<str>>(string: S) -> Option<Self> {
            let mut data: Wrapping<$st> = Wrapping(0);
            let mut length = 0;
            for c in string.as_ref().chars() {
                if length as usize >= Self::CAPACITY {
                    return None;
                }
                if c == '0' {
                    data = data << 1;
                    length += 1;
                }
                else if c == '1' {
                    data = (data << 1) | Wrapping(1);
                    length += 1;
                }
                else {
                    return None;
                }
            }
            return Some(Self {
                data,
                length
            })
        }

        fn from_hex<S: AsRef<str>>(string: S) -> Option<Self> {
            let mut data: Wrapping<$st> = Wrapping(0);
            let mut length = 0;
            for c in string.as_ref().chars() {
                if length as usize >= Self::CAPACITY {
                    return None;
                }
                if let Some(n) = c.to_digit(16) {
                    data = (data << 4) | Wrapping(n as $st);
                    length += 4;
                }
                else {
                    return None;
                }
            }
            return Some(Self {
                data,
                length
            })
        }

        #[allow(arithmetic_overflow)]
        fn from_bytes<B: AsRef<[u8]>>(bytes: B, endianness: Endianness) -> Self {
            debug_assert!(bytes.as_ref().len() * 8 <= Self::CAPACITY);
            let mut data: Wrapping<$st> = Wrapping(0);
            let mut length = 0;
            match endianness {
                Endianness::LE => {
                    for &b in bytes.as_ref().iter().rev() {       
                        data = data << 8 | Wrapping(b as $st);
                        length += 8;
                    }
                },
                Endianness::BE => {
                    for &b in bytes.as_ref().iter() {       
                        data = data << 8 | Wrapping(b as $st);
                        length += 8;
                    }
                }
            }
            return Self {
                data,
                length
            }
        }

        fn to_vec(&self, endianness: Endianness) -> Vec<u8> {
            let num_bytes = (self.length as usize + 7) / 8;
            let mut buf: Vec<u8> = repeat(0u8).take(num_bytes).collect();
            match endianness {
                Endianness::LE => {
                    for i in 0..num_bytes {
                        buf[i] = (self.data.0 >> (i * 8) & 0xff) as u8;
                    }
                },
                Endianness::BE => {
                    for i in 0..num_bytes {
                        buf[num_bytes - i - 1] = (self.data.0 >> (i * 8) & 0xff) as u8;
                    }
                }
            }
            return buf;
        }

        fn read<R: Read>(reader: &mut R, length: usize, endianness: Endianness) -> std::io::Result<Self> {
            debug_assert!(length <= Self::CAPACITY);
            let mut buf = [0u8; size_of::<$st>()];
            let num_bytes = (length + 7) / 8;
            reader.read_exact(&mut buf[0..num_bytes])?;
            let mut bv = Self::from_bytes(&buf[0..num_bytes], endianness);
            bv.data &= Self::mask(length);
            bv.length = length as u8;
            return Ok(bv);

        }

        fn write<W: Write>(&self, writer: &mut W, endianness: Endianness) -> std::io::Result<()> {
            let mut buf = [0u8; size_of::<$st>()];
            let num_bytes = (self.length as usize + 7) / 8;
            match endianness {
                Endianness::LE => {
                    for i in 0..num_bytes {
                        buf[i] = (self.data.0 >> (i * 8) & 0xff) as u8;
                    }
                },
                Endianness::BE => {
                    for i in 0..num_bytes {
                        buf[num_bytes - i - 1] = (self.data.0 >> (i * 8) & 0xff) as u8;
                    }
                }
            }
            return writer.write_all(&buf[0..num_bytes]);
        }

        fn get(&self, index: usize) -> Bit {
            debug_assert!(index < self.len());
            (self.data.0 >> index & 1).into()
        }

        fn set(&mut self, index: usize, bit: Bit){
            debug_assert!(index < self.len());
            self.data = (self.data & !(Wrapping(1 as $st) << index)) | (Wrapping(bit as $st) << index);
        }

        fn copy_slice(&self, range: Range<usize>) -> Self {
            debug_assert!(range.start < self.len() && range.end <= self.len());
            let len = range.end - usize::min(range.start, range.end);
            Self {
                data: self.data >> range.start & Self::mask(len),
                length: len as u8
            }
        }

        fn push(&mut self, bit: Bit) {
            debug_assert!(self.len() < Self::CAPACITY);
            self.data |= Wrapping(bit as $st) << self.len();
            self.length += 1;
        }

        fn pop(&mut self) -> Option<Bit> {
            if self.length > 0 {
                self.length -= 1;
                Some((self.data.0 >> self.length & 1).into())
            }
            else {
                None
            }
        }

        fn resize(&mut self, new_length: usize, bit: Bit) {
            debug_assert!(new_length <= Self::CAPACITY);
            let sign_mask = <$st>::MIN.wrapping_sub(<$st>::from(bit))
                            .checked_shr((Self::CAPACITY + self.len() - new_length) as u32)
                            .unwrap_or(0).checked_shl(self.len() as u32).unwrap_or(0);
            self.data = self.data & Self::mask(new_length) | Wrapping(sign_mask);
            self.length = new_length as u8;
        }

        fn shl_in(&mut self, bit: Bit) -> Bit {
            let out = self.data.0 >> (self.length - 1);
            self.data = (self.data << 1 & Self::mask(self.len())) | Wrapping(bit as $st);
            return out.into();
        }

        fn shr_in(&mut self, bit: Bit) -> Bit {
            let out = self.data.0 & 1;
            self.data = (self.data >> 1) | (Wrapping(bit as $st) << (self.len() - 1));
            return out.into();
        }

        fn rotl(&mut self, rot: usize) {
            debug_assert!(rot <= self.len());
            self.data = (self.data << rot & Self::mask(self.len())) | (self.data >> (self.len() - rot));
        }

        fn rotr(&mut self, rot: usize) {
            debug_assert!(rot <= self.len());
            self.data = (self.data >> rot) | (self.data << (self.len() - rot) & Self::mask(self.len()));
        }

        fn len(&self) -> usize {
            self.length as usize
        }
    }

    $(
        impl From<&'_ $rhs> for $name {
            fn from(a: &'_ $rhs) -> $name {
                $name {
                    data: Wrapping(a.data.0 as $st),
                    length: a.length
                }
            }
        }

        impl From<$rhs> for $name {
            fn from(a: $rhs) -> $name {
                $name::from(&a)
            }
        }

        impl TryFrom<&'_ $name> for $rhs {
            type Error = &'static str;
            fn try_from(a: &'_ $name) -> Result<Self, Self::Error> {
                Ok($rhs {
                    data: Wrapping(<$sst>::try_from(a)?),
                    length: a.length
                })
            }
        }
        
        impl TryFrom<$name> for $rhs {
            type Error = &'static str;
            fn try_from(a: $name) -> Result<Self, Self::Error> {
                return Ok(<$rhs>::try_from(&a)?);
            }
        }

        impl From<$sst> for $name {
            fn from(a: $sst) -> $name {
                $name {
                    data: Wrapping(a as $st),
                    length: (std::mem::size_of::<$sst>() * 8) as u8
                }
            }
        }

        impl TryFrom<&'_ $name> for $sst {
            type Error = &'static str;
            fn try_from(a: &'_ $name) -> Result<Self, Self::Error> {
                if a.len() > size_of::<$sst>() * 8 {
                    return Err(concat!(stringify!($name), " is too large to convert into this type"));
                }
                return Ok(a.data.0 as $sst);
            }
        }

        impl TryFrom<$name> for $sst {
            type Error = &'static str;
            fn try_from(a: $name) -> Result<Self, Self::Error> {
                return Ok(<$sst>::try_from(&a)?);
            }
        }
    )*

    impl From<$st> for $name {
        fn from(a: $st) -> $name {
            $name {
                data: Wrapping(a),
                length: (std::mem::size_of::<$st>() * 8) as u8
            }
        }
    }

    impl From<$name> for $st {
        fn from(a: $name) -> $st {
            a.data.0
        }
    }

    impl From<&'_ $name> for $st {
        fn from(a: &'_ $name) -> $st {
            a.data.0
        }
    }

    impl Not for $name {
        type Output = $name;
        fn not(self) -> $name {
            $name {
                data: !self.data & Self::mask(self.length as usize),
                length: self.length
            }
        }
    }

    $(
        impl_op!{$name, $st, $rhs, BitAnd, bitand}
        impl_op!{$name, $st, $rhs, BitOr, bitor}
        impl_op!{$name, $st, $rhs, BitXor, bitxor}
        impl_op!{$name, $st, $rhs, Add, add}
        impl_op!{$name, $st, $rhs, Sub, sub}

        impl_op_assign!{$name, $st, $rhs, BitAndAssign, bitand_assign}
        impl_op_assign!{$name, $st, $rhs, BitOrAssign, bitor_assign}
        impl_op_assign!{$name, $st, $rhs, BitXorAssign, bitxor_assign}
        impl_op_assign!{$name, $st, $rhs, AddAssign, add_assign}
        impl_op_assign!{$name, $st, $rhs, SubAssign, sub_assign}
    )*

    impl_op!{$name, $st, $name, BitAnd, bitand}
    impl_op!{$name, $st, $name, BitOr, bitor}
    impl_op!{$name, $st, $name, BitXor, bitxor}
    impl_op!{$name, $st, $name, Add, add}
    impl_op!{$name, $st, $name, Sub, sub}

    impl_op_assign!{$name, $st, $name, BitAndAssign, bitand_assign}
    impl_op_assign!{$name, $st, $name, BitOrAssign, bitor_assign}
    impl_op_assign!{$name, $st, $name, BitXorAssign, bitxor_assign}
    impl_op_assign!{$name, $st, $name, AddAssign, add_assign}
    impl_op_assign!{$name, $st, $name, SubAssign, sub_assign}

    impl_shl!{$name, {u8, u16, u32, u64, u128, usize}}
    impl_shr!{$name, {u8, u16, u32, u64, u128, usize}}

    impl_shl_assign!{$name, {u8, u16, u32, u64, u128, usize}}
    impl_shr_assign!{$name, {u8, u16, u32, u64, u128, usize}}

    impl Binary for $name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            let length = self.len();
            let mut s = String::with_capacity(length);
            for i in 0..length {
                match self.data.0 >> (length - i - 1) & 1 {
                    0 => s.push('0'),
                    1 => s.push('1'),
                    _ => unreachable!()
                }
            }
            if f.alternate() {
                return write!(f, "0b{}", s.as_str());
            }
            else {
                return write!(f, "{}", s.as_str());
            }
        }
    }

    impl Display for $name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            if f.alternate() {
                // SMT-LIB format
                return write!(f, "(_ bv{} {})", self.data, self.length);
            }
            else {
                return write!(f, "{}", self.data);
            }
        }
    }

    impl LowerHex for $name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            const NIBBLE: [char;16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'];
            let length = (self.len() + 3) / 4;
            let mut s = String::with_capacity(length);
            for i in (0..length).rev() {
                s.push(NIBBLE[(self.data.0 >> (i * 4) & 0xf) as usize])
            }
            if f.alternate() {
                return write!(f, "0x{}", s.as_str());
            }
            else {
                return write!(f, "{}", s.as_str());
            }
        }
    }

    impl UpperHex for $name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            const NIBBLE: [char;16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'];
            let length = (self.len() + 3) / 4;
            let mut s = String::with_capacity(length);
            for i in (0..length).rev() {
                s.push(NIBBLE[(self.data.0 >> (i * 4) & 0xf) as usize])
            }
            if f.alternate() {
                return write!(f, "0x{}", s.as_str());
            }
            else {
                return write!(f, "{}", s.as_str());
            }
        }
    }

    impl Octal for $name {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
            const SEMI_NIBBLE: [char;8] = ['0', '1', '2', '3', '4', '5', '6', '7'];
            let length = (self.len() + 2) / 3;
            let mut s = String::with_capacity(length);
            for i in (0..length).rev() {
                s.push(SEMI_NIBBLE[(self.data.0 >> (i * 3) & 0x7) as usize])
            }
            if f.alternate() {
                return write!(f, "0o{}", s.as_str());
            }
            else {
                return write!(f, "{}", s.as_str());
            }
        }
    }
}}

decl_bv! (BV8, u8, {});
decl_bv! (BV16, u16, {(BV8, u8)});
decl_bv! {BV32, u32, {(BV8, u8), (BV16, u16)}}
decl_bv! {BV64, u64, {(BV8, u8), (BV16, u16), (BV32, u32)}}
decl_bv! {BV128, u128, {(BV8, u8), (BV16, u16), (BV32, u32), (BV64, u64)}}