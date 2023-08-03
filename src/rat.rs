use super::Int;
use rug::{Integer, Rational, ops::Pow};
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use crate::str_num;
use std::error::Error;
use crate::box_err:: box_dyn_error;
use std::fmt;
use std::ops::{Rem, Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign, Neg};



#[derive(Default, Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct Rat ( pub Rational );

macro_rules! op_return_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_ for Rat 
            where Rational: $trait_<Output = Rational> {
            type Output = Rat;
            fn $method(self) -> Rat {
                let Rat(a) = self;
                Rat(a.$method())
            }
        }
    };
}

macro_rules! op_other_return_self {
    ($trait_: ident ($method: ident)) => {
        impl<T> $trait_<T> for Rat 
            where Rational: $trait_<T, Output = Rational> {
            type Output = Rat;
            fn $method(self, b: T) -> Rat {
                let Rat(a) = self;
                Rat(a.$method(b))
            }
        }
    };
}

macro_rules! op_other_mut_self {
    ($trait_: ident ($method: ident)) => {
        impl<T> $trait_<T> for Rat 
            where Rational: $trait_<T> {
            fn $method(&mut self, b: T) {
                self.0.$method(b)
            }
        }
    };
}

macro_rules! op_self_return_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_<Rat> for Rat 
            where Rational: $trait_<Rational, Output = Rational> {
            type Output = Rat;
            fn $method(self, b: Rat) -> Rat {
                Rat(self.0.$method(b.0))

            }
        }
    };
}

macro_rules! op_self_pointer_return_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_<&'_ Rat> for Rat {
            type Output = Rat;
            fn $method(self, b: &Rat) -> Rat {
                Rat(self.0.$method(&b.0))

            }
        }
    };
}

macro_rules! op_self_mut_self {
    ($trait_: ident ($method: ident)) => {
        impl $trait_<Rat> for Rat 
            where Rational: $trait_<Rational> {
            fn $method(&mut self, b: Rat) {
                self.0.$method(b.0)
            }
        }
    };
}

macro_rules! op_self_pointer_mut_self {
    ($trait_: ident ($method: ident)) => {
        impl<'a> $trait_<&'a Rat> for Rat 
            where Rational: $trait_<&'a Rational> {
            fn $method(&mut self, b: &'a Rat) {
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
op_other_return_self!(Rem (rem));
op_other_mut_self!(AddAssign (add_assign));
op_other_mut_self!(SubAssign (sub_assign));
op_other_mut_self!(MulAssign (mul_assign));
op_other_mut_self!(DivAssign (div_assign));
op_self_return_self!(Add (add));
op_self_return_self!(Sub (sub));
op_self_return_self!(Mul (mul));
op_self_return_self!(Div (div));
op_self_pointer_return_self!(Add (add));
op_self_pointer_return_self!(Sub (sub));
op_self_pointer_return_self!(Mul (mul));
op_self_pointer_return_self!(Div (div));
op_self_mut_self!(AddAssign (add_assign));
op_self_mut_self!(SubAssign (sub_assign));
op_self_mut_self!(MulAssign (mul_assign));
op_self_mut_self!(DivAssign (div_assign));
op_self_pointer_mut_self!(AddAssign (add_assign));
op_self_pointer_mut_self!(SubAssign (sub_assign));
op_self_pointer_mut_self!(MulAssign (mul_assign));
op_self_pointer_mut_self!(DivAssign (div_assign));

impl<T> From<T> for Rat 
    where Rational: From<T> {
    fn from(source: T) -> Self {
        Rat(Rational::from(source))
    }
}

impl From<&Rat> for Rat {
    fn from(rat: &Rat) -> Self {
        Self(Rational::from(&rat.0))
    }
}

// impl From<((Int, Int))> for Rat {
//     fn from(u: (Int, Int)) -> Self {
//         Self(Rational::from((u.0.0, u.1.0)))
//     }
// }

impl Serialize for Rat {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let hex = format!("{}/{}", self.0.numer().to_string_radix(16), self.0.denom().to_string_radix(16));
        serializer.serialize_str(&hex)
    }
}


#[derive(Deserialize)]
struct DisplayVersion {
    display: String,
    num_decimals: i32,
    den_decimals: i32,
}


#[derive(Deserialize)]
#[serde(untagged)]
enum SerializedRat {
    Hex(String),
    Float(f64),
    Display(DisplayVersion),
}


impl<'de> Deserialize<'de> for Rat {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let serialized_rat: SerializedRat = Deserialize::deserialize(deserializer)?;
        let res = match serialized_rat {
            SerializedRat::Hex(v) => {
                let num_den: Vec<&str> = v.split("/").collect();
                let num = Int::from_hex_str(num_den[0], false).unwrap();
                let den = Int::from_hex_str(num_den[1], false).unwrap();
                Self::from((num.0, den.0))
            },
            SerializedRat::Float(v) => {
                Self::from_f64(v).unwrap()
            },
            SerializedRat::Display(v) => {
                Self::from_display_str(&v.display, v.num_decimals, v.den_decimals).unwrap()
            },
        };
        Ok( res )
    }
}


impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T> PartialOrd<T> for Rat 
    where Rational: PartialOrd<T>, Rat: PartialEq<T> {
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

impl<T> PartialEq<T> for Rat 
    where Rational: PartialEq<T> {
    fn eq(&self, other: &T) -> bool {
        &self.0 == other
    }
}

impl Rat {

    pub fn to_abs(&self) -> Self {
        Self(Rational::from(self.0.abs_ref()))
    }

    // pub fn abs_ref(&self) -> &Self {
    //     self.0.abs_ref()
    // 
    pub fn mul_int(&self, other: &Int) -> Self {
        Self( self.0.clone() * &other.0 )
    }

    pub fn mul_int_mut(&mut self, other: &Int) {
        self.0 *= &other.0;
    }

    pub fn div_int(&self, other: &Int) -> Self {
        Self( self.0.clone() / &other.0 )
    }

    pub fn div_int_mut(&mut self, other: &Int) {
        self.0 /= &other.0;
    }

    pub fn into_closest_int(self) -> Int {
        let rounded = self.0.round();
        let (num, den) = rounded.into_numer_denom();
        assert!(den == 1);
        Int::from(num)
    }

    pub fn recip_mut(&mut self) {
        self.0.recip_mut()
    }

    pub fn recip(self) -> Self {
        Self(self.0.recip())
    }

    pub fn to_f64(&self) -> f64 {
        self.0.to_f64()
    }

    pub fn from_display_str (source: &str, num_decimals: i32, den_decimals: i32) -> Result<Self, Box<dyn Error>> {
        let conv_string = str_num::mdp(&source, num_decimals - den_decimals)?;
        let fraction_string = str_num::dec_to_rat(&conv_string)?;
        let rat = Rational::from_str_radix(&fraction_string, 10)?;
        let res = Self::from(rat);
        Ok(res)
    }

    pub fn to_decimal_string(&self) -> Result<String, Box<dyn Error>> {

        let (orig_num, orig_den) = Rational::from(&self.0).into_numer_denom();
        let mut mut_den = Integer::from(&orig_den);
        let fives = mut_den.remove_factor_mut(&Integer::from(5));
        let twos = mut_den.remove_factor_mut(&Integer::from(2));
        if mut_den != Integer::from(1) {
            return Err(box_dyn_error("this rational can't be expressed exactly as decimal"))
        }
        let mut multiplier = Integer::from(1);
        if fives > twos {
            let exp = fives - twos;
            multiplier *= Integer::from(2).pow(exp);
        }
        if twos > fives {
            let exp = twos - fives;
            multiplier *= Integer::from(5).pow(exp);
        }
        let scaled_num_string = (orig_num*&multiplier).to_string();
        let scaled_den_string = (orig_den*&multiplier).to_string();

        let decimals = (scaled_den_string.len() -1 ) as i32;
        let dec_str = str_num::mdp(&scaled_num_string, -decimals)?;
        Ok(dec_str)

    }

    pub fn to_display_string(&self, num_decimals: i32, den_decimals: i32) -> Result<String, Box<dyn Error>> {

        let price_string = self.to_decimal_string()?;
        let display_string = str_num::mdp(&price_string, den_decimals - num_decimals)?;
        Ok(display_string)
    }

    pub fn from_f64 (source: f64) -> Option<Self> {
        match Rational::from_f64(source) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    pub fn from_f32 (source: f32) -> Option<Self> {
        match Rational::from_f32(source) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }

    pub fn from_ints(u: (Int, Int)) -> Self {
        Self(Rational::from((u.0.0, u.1.0)))
    }

    pub fn into_numer_denom(self) -> (Int, Int) {
        let (inner_num, inner_den) = self.0.into_numer_denom();
        (Int::from(inner_num), Int::from(inner_den))

    }
}

