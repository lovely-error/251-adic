#![feature(inline_const)]
#![feature(portable_simd)]
use core::{mem::transmute, ops::{Add, BitXor, Mul, Not, Rem, Sub}, simd::{Mask, Simd, SimdFloat, SimdInt, SimdPartialOrd, SimdUint, ToBitMask}};
use std::process::Output;


fn fdiv251_u64(num: u64) -> u64 {

    // https://github.com/lemire/fast_division/blob/main/include/fast_division/fast_division.h

    let (c, log2_divisor) = const {
        let log2_divisor = 63 - 251u64.leading_zeros();
        let m = 1u128 << (64 + log2_divisor);
        let needs_fallback = 251 - (m % 251) >= m / u64::MAX as u128 + 1;
        let c_floor = m / 251;
        let c_ceiling = c_floor + 1;
        let c = if needs_fallback { c_floor } else { c_ceiling } ;
        // let cc = if needs_fallback { c } else { 0 };

        (c, log2_divisor)
    };

    ((c * (num + 1) as u128) >> (64 + log2_divisor)) as u64

    // num / 251
}
fn frem251_u64(num: u64) -> u64 {
    num - (251 * fdiv251_u64(num))
}

fn frem251_250x2(num: u16) -> u16 {
    assert!(num <= 500);
    num - (251 * (num >= 251) as u16)
}


#[derive(Clone, Copy)]
#[repr(transparent)]
struct Zmod251(u64);

impl Zmod251 {
    const MAX: u64 =
        250 +
        250 * 251u64 +
        250 * 251u64.pow(2) +
        250 * 251u64.pow(3) +
        250 * 251u64.pow(4) +
        250 * 251u64.pow(5) +
        250 * 251u64.pow(6) +
        250 * 251u64.pow(7) ;
    fn zero() -> Self {
        Self(unsafe { transmute([0u8;8]) })
    }
    fn from_terms(terms: &[u8]) -> Self {
        assert!(terms.len() <= 8);
        let mut result = [0u8;8];
        for ix in 0 .. 8 {
            result[ix] = terms[ix];
        }
        return Self(unsafe { transmute(result) });
    }
    fn from_signed(num: i64) -> Self {
        let bitnum = num.abs_diff(0);
        if num >= 0 {
            Self::from_two_complement(bitnum)
        } else {
            let num = Self::MAX - bitnum + 1;
            Self::from_two_complement(num)
        }
    }
    fn from_positive(num: u64) -> Self {
        Self::from_two_complement(num)
    }
    fn from_two_complement(num: u64) -> Self {
        assert!(num <= Self::MAX, "Cant fit!");

        let mut terms = [0u8;8];
        let mut n = num;
        for i in 0 .. 8 {
            let d = fdiv251_u64(n);
            let rem = n - d * 251;
            terms[i] = rem as u8;
            n = d;
            if d == 0 { break }
        }

        let val = unsafe { transmute(terms) };
        return Self(val);
    }
    fn as_positive(&self) -> u64 {
        self.as_complement_faster()
    }
    fn as_signed(&self) -> (u64, bool) {
        let val = self.as_complement_faster();
        if val > (Self::MAX / 2) - 1 {
            ((Self::MAX + 1 - val), false)
        } else {
            (val, true)
        }
    }
    fn as_complement_number(&self) -> u64 {
        let terms = self.0;

        let mask = (1 << 8) - 1;
        let k0 = terms & mask ;
        let k1 = (terms >> 8 & mask) * 251u64;
        let k2 = (terms >> 16 & mask) * 251u64.pow(2);
        let k3 = (terms >> 24 & mask) * 251u64.pow(3);
        let k4 = (terms >> 32 & mask) * 251u64.pow(4);
        let k5 = (terms >> 40 & mask) * 251u64.pow(5);
        let k6 = (terms >> 48 & mask) * 251u64.pow(6);
        let k7 = (terms >> 56 & mask) * 251u64.pow(7);

        let k = k0 + k1 + k2 + k3 + k4 + k5 + k6 + k7 ;

        return k;
    }
    fn as_complement_faster(&self) -> u64 {
        let powers = Simd::from_array([
            1,
            251,
            251u64.pow(2),
            251u64.pow(3),
            251u64.pow(4),
            251u64.pow(5),
            251u64.pow(6),
            251u64.pow(7)
        ]);

        let terms = self.as_terms();
        let terms = Simd::from_array(terms).cast::<u64>();
        terms.mul(powers).reduce_sum()
    }
    fn trailing_zeroes(&self) -> u32 {
        self.0.leading_zeros() >> 3
    }
    fn as_terms(&self) -> [u8;8] {
        unsafe { transmute(self.0) }
    }
    fn add(&self, another: Self) -> Self {

        let terms1 = self.0;
        let terms2 = another.0;
        let mask = (1 << 8) - 1;
        let mut res = 0u64;

        fn frem251_250x2(num: u64) -> u64 {
            num - (251 * (num >= 251) as u64)
        }

        let t = (terms1 & mask) + (terms2 & mask) ;
        res |= frem251_250x2(t) ;
        let t = ((terms1 >> 8) & mask) + ((terms2 >> 8) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 8;
        let t = ((terms1 >> 16) & mask) + ((terms2 >> 16) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 16;
        let t = ((terms1 >> 24) & mask) + ((terms2 >> 24) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 24;
        let t = ((terms1 >> 32) & mask) + ((terms2 >> 32) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 32;
        let t = ((terms1 >> 40) & mask) + ((terms2 >> 40) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 40;
        let t = ((terms1 >> 48) & mask) + ((terms2 >> 48) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 48;
        let t = ((terms1 >> 56) & mask) + ((terms2 >> 56) & mask) + ((t >= 251) as u64);
        res |= (frem251_250x2(t) ) << 56;

        // let c = t >> 8;
        // if c != 0 {
        //     // overflowed
        //     println!("Overflowed {}", c)
        // }

        return Self(res);
    }
    fn add_faster(&self, another: Self) -> Self {

        let this = Simd::from_array(self.as_terms()).cast::<u16>();
        let another = Simd::from_array(another.as_terms()).cast::<u16>();
        let mut rot_mask = Mask::splat(true);
        rot_mask.set(7, false);
        let mut stop_mask = Mask::splat(false);
        stop_mask.set(7, true);

        let mut comb = this.add(another);
        let mut o_bits_acc = Mask::splat(false);
        loop {
            let overflow_bits1 = comb.simd_ge(Simd::splat(251));
            let overflow_bits1 = overflow_bits1 ^ o_bits_acc;
            o_bits_acc |= overflow_bits1;
            if !overflow_bits1.any() || overflow_bits1 == stop_mask { break }
            let overflow_bits1 = overflow_bits1
                .not()
                .to_int()
                .add(Simd::splat(1))
                .cast::<u16>();
            let overflow_bits1_shifted = rot_mask
                .select(overflow_bits1, Simd::splat(0))
                .rotate_lanes_right::<1>();
            comb = comb.add(overflow_bits1_shifted);
        }

        let antis = o_bits_acc.select(Simd::splat(251u16), Simd::splat(0));
        let rems = comb.sub(antis).cast::<u8>();

        let val = unsafe { transmute(rems) };
        return Self(val);
    }
    fn __add(&self, another: Self) -> Self { unsafe {
        let terms1: [u8;8] = transmute(self.0);
        let terms2: [u8;8] = transmute(another.0);
        let mut out = [0u8;8];

        let mut carry = 0u16;
        for i in 0 .. 8 {
            let t1 = terms1[i] as u16;
            let t2 = terms2[i] as u16;

            let t3 = t1 + t2 + carry;
            let d = frem251_u64(t3 as _);
            out[i] = d as u8;

            carry = (t3 >= 251) as u16;
        }

        return transmute(out);
    } }
    fn mul(&self, another: Self) -> Self {
        let powers = Simd::from_array([
            1,
            251,
            251u64.pow(2),
            251u64.pow(3),
            251u64.pow(4),
            251u64.pow(5),
            251u64.pow(6),
            251u64.pow(7)
        ]);
        let another_ = another.as_terms();
        let terms1 = Simd::from_array(another_).cast::<u64>();
        let this = self.as_complement_faster();
        let number = Simd::splat(this);
        let muled = terms1.mul(powers).mul(number);
        let muled = muled.to_array();
        let mut lim = 0;
        for ix in 0 .. 8 {
            if terms1[7 - ix] != 0 { break }
            lim = ix
        }
        lim = 7 - lim;

        let mut terms = [0u8;8];
        for ix in 0 .. lim {
            let mut mul = muled[ix];
            let mut ix_ = 0;
            loop {
                if ix_ == 8 || ix_ >= lim && mul == 0 { break }
                let d = fdiv251_u64(mul);
                let rem = mul - 251 * d;
                let n = terms[ix_] as u16;
                let n = n + rem as u16;
                let n_ = n % 251;
                terms[ix_] = n_ as u8;
                mul = d + (n > n_) as u64;
                ix_ += 1;
            }
        }

        let ret = unsafe { transmute(terms) };
        return Self(ret);
    }
    fn abs(&self) -> Self {
        let this = *self;
        if self.0 & ((1 << 8) - 1) << 56 != 0 {
            let a = Zmod251::from_signed(0).sub(this);
            a
        } else {
            this
        }
    }
    fn mul_signed(&self, another: Self) -> Self {
        let mut bc = 0;
        let mut this = *self;
        if self.0 & ((1 << 8) - 1) << 56 != 0 {
            bc += 1;
            this = self.abs();
        };
        let mut another = another;
        if another.0 & ((1 << 8) - 1) << 56 != 0 {
            bc += 1;
            another = another.abs();
        };
        let neg = bc & 1 == 1;
        let powers = Simd::from_array([
            1,
            251,
            251u64.pow(2),
            251u64.pow(3),
            251u64.pow(4),
            251u64.pow(5),
            251u64.pow(6),
            251u64.pow(7)
        ]);
        let another_ = another.as_terms();
        let terms1 = Simd::from_array(another_).cast::<u64>();
        let number = this.as_complement_faster();
        let muled = terms1.mul(powers).mul(Simd::splat(number));
        let muled = muled.to_array();
        let mut lim = 0;
        for ix in 0 .. 8 {
            if terms1[7 - ix] != 0 { break }
            lim = ix
        }
        lim = 7 - lim;

        let mut terms = [0u8;8];
        for ix in 0 .. lim {
            let mut mul = muled[ix];
            let mut ix_ = 0;
            loop {
                if ix_ == 8 || ix_ >= lim && mul == 0 { break }
                let d = fdiv251_u64(mul);
                let rem = mul - 251 * d;
                let n = terms[ix_] as u16;
                let n = n + rem as u16;
                let n_ = n % 251;
                terms[ix_] = n_ as u8;
                mul = d + (n > n_) as u64;
                ix_ += 1;
            }
        }

        let ret = unsafe { transmute(terms) };
        let mut ret = Self(ret);
        if neg {
            ret = Self::zero().sub(ret);
        }

        return ret;
    }
    fn sub(&self, another: Self) -> Self {
        let this = self.as_terms();
        let another = another.as_terms();

        let mut borrow = 0;
        let mut result = [0u8;8];
        for ix in 0 .. 8 {
            let a = this[ix] as i16 - borrow;
            let b = another[ix] as i16;
            let c = a - b;
            let c = if c >= 0 { borrow = 0; c } else { borrow = 1; 251 + c };
            result[ix] = c as u8;
        }

        let result = unsafe { transmute(result) };
        return Self(result);
    }
    fn reciprocal(&self) -> Self {
        todo!()
    }
}

#[test]
fn props_tests() {

    // a + b = 0
    let a = Zmod251::from_signed(-1);
    let b = Zmod251::from_signed(1);
    let c = a.add_faster(b);
    assert!(c.as_signed() == (0, true));

    // a * 2 = 1
    let mut a = Zmod251::from_positive(0);
    a.0 = unsafe {
        transmute([126u8, 125, 125, 125, 125, 125, 125, 125])
    };
    let b = Zmod251::from_positive(2);
    let c = a.mul(b);
    assert!(c.as_positive() == 1);

    // -1 - -1 = 0
    let a = Zmod251::from_signed(-1);
    let b = Zmod251::from_signed(-1);
    let c = a.sub(b);
    assert!(c.as_signed() == (0, true));

    // -1 + -1 = -2
    let a = Zmod251::from_signed(-1);
    let b = Zmod251::from_signed(-1);
    let c = a.add_faster(b);
    assert!(c.as_signed() == (2, false));

}

#[test]
fn t1() {

    let a_ = 1313131313;
    let b_ = a_;
    let a = Zmod251::from_positive(a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = Zmod251::from_positive(b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul(b);
    // println!("{} {:?} mul2", c.as_positive(), c.as_terms());
    // println!("{}", a_ * b_);
    let correct = a_ * b_;
    assert!(c.as_positive() == correct);

    let mut a = Zmod251::from_positive(0);
    a.0 = unsafe {
        transmute([0u8, 0, 250, 250, 0, 0, 0, 0])
    };
    let n = 3969063000u64;
    assert!(n == a.as_positive());
    let m = n*n;
    let b = a.mul(a);
    assert!(b.as_positive() == m);
}
#[test]
fn t2() {

    let a_ = 131313;
    let b_ = 171717;
    let n = (a_ * b_) as u64;
    let a = Zmod251::from_signed(-a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = Zmod251::from_signed(b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul_signed(b);
    assert!(c.as_signed() == (n, false));
    // println!("{:?} {:?} mul", c.as_signed(), c.as_terms());

    let a = Zmod251::from_signed(a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = Zmod251::from_signed(-b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul_signed(b);
    assert!(c.as_signed() == (n, false));

    let a = Zmod251::from_signed(-a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = Zmod251::from_signed(-b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul_signed(b);
    assert!(c.as_signed() == (n, true));
}

fn main() {

}

// let primes = [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251];

// for prime in primes {

//     if ((u64::MAX / prime) * prime) == u64::MAX {
//         println!("{prime} is an exact divisor! Skipping...");
//         continue;
//     }

//     let m = prime - 1;
//     let num =
//         m +
//         m * prime.pow(1) +
//         m * prime.pow(2) +
//         m * prime.pow(3) +
//         m * prime.pow(4) +
//         m * prime.pow(5) +
//         m * prime.pow(6) +
//         m * prime.pow(7) ;

//     let magic = (u64::MAX / prime) + 1;
//     let d = ((magic as u128 * num as u128) >> 64) as u64;

//     let a = d * prime ;

//     if a > num {
//         let b = num - ((num / prime) * prime);
//         println!("{} !!!! {} > {} !!!! {} OFF !!! Correct is {} bellow", prime, a, num, a - num, b);
//     }
// }