use super::{Rat};
use rug::{Integer, integer::Order::Lsf, integer::Order::Msf, Assign};
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use crate::str_num;
use std::fmt;
use std::ops::{Rem, Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign, Neg, BitAnd, BitOr};
use std::error::Error;
use crate::box_err:: box_dyn_error;
use std::ops::{Shl, Shr};
use ethereum_types::U256;
use super::RandState;

pub use rug::integer::Order;

#[derive(Hash, Default, Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct Int ( pub Integer );

macro_rules! op_return_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_ for Int 
            where Integer: $trait_<Output = Integer> {
            type Output = Int;
            fn $method(self) -> Int {
                let Int(a) = self;
                Int(a.$method())
            }
        }
    };
}

macro_rules! op_other_return_self {
    ($trait_: ident ($method: ident)) => {
        impl<T> $trait_<T> for Int 
            where Integer: $trait_<T, Output = Integer> {
            type Output = Int;
            fn $method(self, b: T) -> Int {
                let Int(a) = self;
                Int(a.$method(b))
            }
        }
    };
}

macro_rules! op_other_mut_self {
    ($trait_: ident ($method: ident)) => {
        impl<T> $trait_<T> for Int 
            where Integer: $trait_<T> {
            fn $method(&mut self, b: T) {
                self.0.$method(b)
            }
        }
    };
}

macro_rules! op_self_return_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_<Int> for Int 
            where Integer: $trait_<Integer, Output = Integer> {
            type Output = Int;
            fn $method(self, b: Int) -> Int {
                Int(self.0.$method(b.0))

            }
        }
    };
}

macro_rules! op_self_pointer_return_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_<&'_ Int> for Int {
            type Output = Int;
            fn $method(self, b: &Int) -> Int {
                Int(self.0.$method(&b.0))

            }
        }
    };
}

macro_rules! op_self_mut_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_<Int> for Int 
            where Integer: $trait_<Integer> {
            fn $method(&mut self, b: Int) {
                self.0.$method(b.0)
            }
        }
    };
}

macro_rules! op_self_pointer_mut_self {
    ($trait_: ident ($method: ident)) => {
        impl<'a> $trait_<&'a Int> for Int 
            where Integer: $trait_<&'a Integer> {
            fn $method(&mut self, b: &'a Int) {
                self.0.$method(&b.0)
            }
        }
    };
}


op_return_self!(Neg (neg));
op_other_return_self!(Add (add));
op_other_return_self!(Sub (sub));
op_other_return_self!(Mul (mul));
op_other_return_self!(Div (div));
op_other_return_self!(Shr (shr));
op_other_return_self!(Shl (shl));
op_other_return_self!(BitAnd (bitand));
op_other_return_self!(BitOr (bitor));
op_other_return_self!(Rem (rem));
op_other_mut_self!(AddAssign (add_assign));
op_other_mut_self!(SubAssign (sub_assign));
op_other_mut_self!(MulAssign (mul_assign));
op_other_mut_self!(DivAssign (div_assign));
op_self_return_self!(Add (add));
op_self_return_self!(Sub (sub));
op_self_return_self!(Mul (mul));
op_self_return_self!(Div (div));
op_self_return_self!(Rem (rem));
op_self_return_self!(BitOr (bitor));
op_self_pointer_return_self!(Add (add));
op_self_pointer_return_self!(Sub (sub));
op_self_pointer_return_self!(Mul (mul));
op_self_pointer_return_self!(Div (div));
op_self_pointer_return_self!(Rem (rem));
op_self_mut_self!(AddAssign (add_assign));
op_self_mut_self!(SubAssign (sub_assign));
op_self_mut_self!(MulAssign (mul_assign));
op_self_mut_self!(DivAssign (div_assign));
op_self_pointer_mut_self!(AddAssign (add_assign));
op_self_pointer_mut_self!(SubAssign (sub_assign));
op_self_pointer_mut_self!(MulAssign (mul_assign));
op_self_pointer_mut_self!(DivAssign (div_assign));


impl From<&Int> for Int {
    fn from(int: &Int) -> Self {
        Self(Integer::from(&int.0))
    }
}

impl<T> From<T> for Int 
    where Integer: From<T> {
    fn from(source: T) -> Self {
        Int(Integer::from(source))
    }
}

impl From<DisplayVersion> for Int {
    fn from(source: DisplayVersion) -> Self {
        let s = str_num::mdp(&source.display, source.decimals).unwrap();
        Self::from_str_radix(&s, 10).unwrap()
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T> PartialOrd<T> for Int 
    where Integer: PartialOrd<T>, Int: PartialEq<T> {
    fn lt(&self, other: &T) -> bool {
        self.0.lt(other)
    }
    fn le(&self, other: &T) -> bool {
        self.0.le(other)
    }
    fn gt(&self, other: &T) -> bool {
        self.0.gt(other)
    }
    fn ge(&self, other: &T) -> bool {
        self.0.ge(other)
    }
    fn partial_cmp(&self, other: &T) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}

impl<T> PartialEq<T> for Int 
    where Integer: PartialEq<T> {
    fn eq(&self, other: &T) -> bool {
        &self.0 == other
    }
}


impl Serialize for Int {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let hex = self.0.to_string_radix(16);
        serializer.serialize_str(&hex)
    }
}

#[derive(Deserialize)]
struct DisplayVersion {
    display: String,
    decimals: i32,
}


#[derive(Deserialize)]
#[serde(untagged)]
enum SerializedInt {
    Hex(String),
    Display(DisplayVersion),
    U64(u64),
}



impl<'de> Deserialize<'de> for Int {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let serialized_int: SerializedInt = Deserialize::deserialize(deserializer)?;
        let res = match serialized_int {
            SerializedInt::Hex(v) => {
                let rel_str = v.trim_start_matches("0x");
                match Self::from_str_radix(rel_str, 16) {
                    Ok(w) => w,
                    Err(err) => {
                        return Err(serde::de::Error::custom(&err.to_string()))
                    },
                }
            },
            SerializedInt::Display(v) => {
                Self::from(v)
            },
            SerializedInt::U64(v) => {
                Self::from(v)
            }
        };
        Ok( res )
    }
}

pub enum Rounding {
    TowardZero,
    Closest,
    NotAllowed,
}

impl Int {
    pub fn random_in_range (low: &Self, high: &Self, rand_state: &mut RandState) -> Self {
        let mut res = Int::from(high);
        res -= low;
        res.random_below_mut(rand_state);
        res += low;
        res
    }

    // pub fn random_in_range<T> (low: T, high: T, rand_state: &mut RandState) -> Self where Int: From<T> + SubAssign<T> + AddAssign<T> {
    //     let mut res: Int = Int::from(high);
    //     res -= low;
    //     res.random_below_mut(rand_state);
    //     res += low;
    //     res
    // }

    pub fn seed_rand_state(self, rand_state: &mut RandState) {
        rand_state.seed(&self.0);
    }

    pub fn random_below(self, rand_state: &mut RandState) -> Self {
        let inner = self.0.random_below(rand_state);
        Self(inner)
    }

    pub fn random_below_mut(&mut self, rand_state: &mut RandState) {
        self.0.random_below_mut(rand_state)
    }
    
    pub fn to_string_radix(&self, radix: i32) -> String {
        self.0.to_string_radix(radix)
    }

    pub fn from_str_radix(s: &str, radix: i32) -> Result<Self, Box<dyn Error>> {
        Ok( Self ( Integer::from_str_radix(s, radix)? ) )
    }

    pub fn abs(&self) -> Self {
        Self(Integer::from(self.0.abs_ref()))
    }

    pub fn reverse_sign(self) -> Self {
        Self(Integer::from(self.0 * -1))
    }

    pub fn keep_bits(self, n: u32) -> Self {
        self.0.keep_bits(n).into()
    }

    pub fn keep_signed_bits(self, n: u32) -> Self {
        self.0.keep_signed_bits(n).into()
    }

    pub fn abs_mut(&mut self) {
        self.0.abs_mut();
    }

    pub fn from_4_u64s_lsf (digits: &[u64; 4]) -> Self {
        Self(Integer::from_digits(digits, Lsf))
    }

    pub fn from_u256(source: U256) -> Self {
        Self(Integer::from_digits(&source.0, Lsf))
    }

    pub fn from_u256_ref(source: &U256) -> Self {
        Self(Integer::from_digits(&source.0, Lsf))
    }

    pub fn from_32_u8s_msf (digits: &[u8; 32]) -> Self {
        Self(Integer::from_digits(digits, Msf))
    }

    pub fn from_256_bools_lsf (digits: &[bool; 256]) -> Self {
        Self(Integer::from_digits(digits, Lsf))
    }

    pub fn from_bytes_msf (digits: &Vec<u8>) -> Self {
        Self(Integer::from_digits(digits, Msf))
    }

    pub fn from_bytes_msf_slice (digits: &[u8]) -> Self {
        Self(Integer::from_digits(digits, Msf))
    }

    pub fn to_bytes_msf(&self) -> Vec<u8> {
        let digits = self.0.to_digits::<u8>(Order::Msf);
        digits
    }

    pub fn from_f64 (source: f64) -> Option<Self> {
        match Integer::from_f64(source) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    pub fn from_f32 (source: f32) -> Option<Self> {
        match Integer::from_f32(source) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    pub fn from_hex_str(s: &str, with_0x_prefix: bool) -> Result<Self, Box<dyn Error>> {
        let inner = if with_0x_prefix {
            if !s.starts_with("0x") {
                return Err(box_dyn_error("expected 0x-prefixed hex string"));
            }
            Integer::from_str_radix(&s[2..], 16)?
        } else {
            Integer::from_str_radix(s, 16)?
        };
        Ok(Self (inner))
    }


    pub fn from_dec_str(s: &str, with_0x_prefix: bool) -> Result<Self, Box<dyn Error>> {
        let inner = if with_0x_prefix {
            if !s.starts_with("0x") {
                return Err(box_dyn_error("expected 0x-prefixed hex string"));
            }
            Integer::from_str_radix(&s[2..], 10)?
        } else {
            Integer::from_str_radix(s, 10)?
        };
        Ok(Self (inner))
    }

    pub fn div_rnd (self, den: &Self)-> Self {
        let (quo, rem) = self.0.div_rem(Integer::from(&den.0));
        let double_rem = Integer::from(2) * &rem;
        if &double_rem >= &den.0 {
            return Int(quo + 1)
        } else {
            return Int(quo)
        }
    }

    pub fn from_display_str(source: &str, decimals: i32, rounding: Rounding) -> Result<Self, Box<dyn Error>> {

        let shift_string = str_num::mdp(source, decimals)?;
        let inner = match rounding {
            Rounding::TowardZero => {
                let int_string = str_num::truncate(&shift_string, 0)?;
                let int = Integer::from_str_radix(&int_string, 10)?;
                Self::from(int)
            },
            Rounding::Closest => {
                let parts: Vec<&str> = shift_string.split('.').collect();
                let r = if parts.len() == 1 {
                    Integer::from_str_radix(&parts[0], 10)?
                } else if parts.len() == 2 {
                    let floor = Integer::from_str_radix(&parts[0], 10)?;
                    
                    let five_to_nine = "56789".as_bytes(); 
                    let zero_to_four = "01234".as_bytes(); 

                    let sign = parts[0].as_bytes()[0];
                    let tenths = parts[1].as_bytes()[0];

                    if sign == b'-' {
                        
                        if five_to_nine.contains(&tenths) {
                            floor - 1
                        } else if zero_to_four.contains(&tenths) {
                            floor
                        } else {
                            panic!("")
                        }
                        
                    } else {
                        if five_to_nine.contains(&tenths) {
                            floor + 1
                        } else if zero_to_four.contains(&tenths) {
                            floor
                        } else {
                            panic!("")
                        }

                    }

                } else {
                    return Err(box_dyn_error("invalid length"))
                };
                
                Self::from(r)
            },
            Rounding::NotAllowed => {
                let parts: Vec<&str> = shift_string.split('.').collect();
                let r = if parts.len() == 1 {
                    Integer::from_str_radix(&parts[0], 10)?
                } else if parts.len() == 2 {
                    for byte in parts[1].as_bytes() {
                        if byte != &b'0' {
                            return Err(box_dyn_error("string is not an integer"))
                        }
                    }
                    Integer::from_str_radix(&parts[0], 10)?
                } else {
                    return Err(box_dyn_error("invalid length"))
                };
                
                Self::from(r)
            },
        };
        Ok(inner)
    }

    pub fn from_e_notation_display_str(source: &str, decimals: i32, rounding: Rounding) -> Result<Self, Box<dyn Error>> {
        let without_e_notation = str_num::without_e_notation(source)?;
        Self::from_display_str(&without_e_notation, decimals, rounding)
    }

    pub fn to_display_string(&self, decimals: i32) -> String {
        let int_string = self.0.to_string_radix(10);
        let display_string = str_num::mdp(&int_string, -decimals).unwrap();
        display_string
    }

    pub fn to_hex_string(&self, with_0x_prefix: bool) -> String {
        let mut s = String::new();
        if with_0x_prefix {
            s += "0x"
        }
        s += &self.0.to_string_radix(16);
        s
    }

    pub fn mul_rat(&self, rat: &Rat, rounding: Rounding) -> Self {
        match rounding {
            Rounding::Closest => {
                let num = Integer::from(rat.0.numer()) * &self.0;
                let den = Integer::from(rat.0.denom());
                let res: Integer = (num + den/2) / rat.0.denom();
                res.into()
            },
            Rounding::TowardZero => {
                let num = Integer::from(rat.0.numer()) * &self.0;
                let den = Integer::from(rat.0.denom());
                (num / den).into()
            },
            Rounding::NotAllowed => {
                let num = Integer::from(rat.0.numer()) * &self.0;
                let den = Integer::from(rat.0.denom());
                if num.clone() % &den == 0 {
                    (num / den).into()
                } else {
                    panic!("rounding necessary")
                }
                
            }
        }
    }

    pub fn div_rat(&self, rat: &Rat, rounding: Rounding) -> Self {
        match rounding {
            Rounding::Closest => {
                let num = Integer::from(rat.0.denom()) * &self.0;
                let den = Integer::from(rat.0.numer());
                let res: Integer = (num + den/2) / rat.0.numer();
                res.into()
            },
            Rounding::TowardZero => {
                let num = Integer::from(rat.0.denom()) * &self.0;
                let den = Integer::from(rat.0.numer());
                (num / den).into()
            },
            Rounding::NotAllowed => {
                let num = Integer::from(rat.0.denom()) * &self.0;
                let den = Integer::from(rat.0.numer());
                if num.clone() % &den == 0 {
                    (num / den).into()
                } else {
                    panic!("rounding necessary")
                }
                
            }
        }
    }

    pub fn to_f64(&self) -> f64 {
        self.0.to_f64()
    }

    // pub fn to_u256(&self) -> Result<U256, Box<dyn Error>> {
    //     let digits = self.0.to_digits::<u8>(Lsf);
    //     if digits.len() > 32 {
    //         return Err(box_dyn_error("U256 limited to 32 bytes"))
    //     }
    //     let u256 = U256::from_little_endian(&digits);
    //     Ok(u256)
    // }

    pub fn to_four_u64s_lsf(&self) -> Result<[u64; 4], Box<dyn Error>> {
        let digits_vec = self.0.to_digits::<u64>(Lsf);
        if digits_vec.len() > 4 {
            return Err(box_dyn_error("too many digits"));
        }
        let mut quad = [0_u64; 4];
        for ind in 0..digits_vec.len() {
            quad[ind] = digits_vec[ind];
        }
        Ok(quad)
    }

    pub fn to_256_bools_lsf(&self) -> [bool; 256] {

        let bitmap = {
            let mut digits = [false; 256];
            self.0.write_digits(&mut digits, Order::Lsf);
            digits
        };
        bitmap
    }

    pub fn to_u256(&self) -> Result<U256, Box<dyn Error>> {
        assert!(self >= &0);
        let inner = self.to_four_u64s_lsf()?;
        Ok(U256(inner))
    }

    pub fn to_i256(&self) -> Result<U256, Box<dyn Error>> {
        let inner = self.clone().keep_bits(256).to_four_u64s_lsf()?;
        Ok(U256(inner))
    }

    pub fn to_u64(&self) -> Option<u64> {
        self.0.to_u64()
    }

    pub fn to_usize(&self) -> Option<usize> {
        self.0.to_usize()
    }

    pub fn from_u_pow_u(base: u32, power: u32) -> Self {
        let mut inner = Integer::new();
        inner.assign(Integer::u_pow_u(base, power));
        Self(inner)
    }


    pub fn u256_max() -> Self {
        (Self::from(1) << 256) - 1
    }

    pub fn u160_max() -> Self {
        (Self::from(1) << 160) - 1
    }

    pub fn significant_bits(&self) -> u32 {
        self.0.significant_bits()
    }

    pub fn sqrt(self) -> Self {
        Self(self.0.sqrt())
    }

    pub fn mod_u(&self, modulo: u32) -> u32 {
        self.0.mod_u(modulo)
    }

    pub fn abi_encode(&self) -> Vec<u8> {
        let incomplete = self.0.keep_bits_ref(256);
        let sized = Integer::from(incomplete);
        let digits = sized.to_digits::<u8>(Order::Msf);
        let padded = zero_pad_start(digits, 32);
        padded
    }

}


