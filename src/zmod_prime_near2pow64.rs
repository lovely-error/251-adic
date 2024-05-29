
use core::{mem::transmute, ops::{Add, Mul, Not, Sub}, simd::{prelude::{SimdInt, SimdPartialOrd, SimdUint}, Mask, Simd }};



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
#[allow(dead_code)]
fn frem251_u64(num: u64) -> u64 {
    num - (251 * fdiv251_u64(num))
}
#[allow(dead_code)]
fn frem251_250x2(num: u16) -> u16 {
    assert!(num <= 500);
    num - (251 * (num >= 251) as u16)
}
#[allow(dead_code)]
fn binpow(mut a: u128, mut b: u128, m: u128) -> u128 {
    a %= m;
    let mut res = 1;
    while b > 0 {
        if b & 1 == 1 {
          res = res * a % m;
        }
        a = a * a % m;
        b >>= 1;
    }
    return res;
}

const fn mod_inverse_u16(mut a: i32, mut m: i32) -> i32 {
  let m0 = m;
  let mut y = 0;
  let mut x = 1;

  while a > 1 && m > 0 {
    let q = a / m;
    let mut t = m;
    m = a % m;
    a = t;
    t = y;
    y = x - (q * y);
    x = t;
  }
  if x < 0 {
    x += m0;
  }
  return x;
}
#[allow(dead_code)]
fn mod_inverse_u64(mut a: i128, mut m: i128) -> i128 {
  let m0 = m;
  let mut y = 0;
  let mut x = 1;

  while a > 1 && m > 0 {
    let q = a / m;
    let mut t = m;
    m = a % m;
    a = t;
    t = y;
    y = x - (q * y);
    x = t;
  }
  if x < 0 {
    x += m0;
  }
  return x;
}

// dont use this ever
fn brute_force_mul_inverse(terms:[u8;8]) -> Option<[u8;8]> {
    if terms == [0;8] { return Some([0;8]) }
    if terms[0] == 0 { return None }
    // solve n * i == 1 (mod 251)
    fn solve_eqn_1(n: u16) -> u16 {
        if n == 1 { return 1 }
        for i in (250 / n) .. 251 {
            let c = (i * n) % 251;
            if c == 1 { return i }
        }
        panic!("Failed to solve eqn K * {} mod 251 == 1", n)
    }
    let mut result = [0u8;8];
    result[0] = solve_eqn_1(terms[0] as u16) as u8;
    'ord_trav:for i in 1 .. 8 {
        for k in 1 .. 251 {
            let mut t = result;
            t[i] = k;
            let c = multiply(t, terms);
            if c[i] == 0 {
                result[i] = k;
                continue 'ord_trav;
            }
        }
    }
    return Some(result);
}

const MOD1_TABLE : [u8;251] = {
    let mut t = [0u8;251];
    let mut i = 1;
    loop {
        if i == 251 { break };
        let inv = mod_inverse_u16(i as _, 251) ;
        assert!(inv * (i as i32) % 251 == 1);
        t[i] = inv as _;
        i += 1;
    }
    t
};
fn mult_inverse(terms:[u8;8]) -> Option<[u8;8]> {
    if terms == [0;8] { return Some([0;8]) }
    if terms[0] == 0 { return None }
    let mut result = [0u8;8];
    let zeroth = MOD1_TABLE[terms[0] as usize];
    result[0] = zeroth as u8;
    let mut tmp = compute_row(terms, zeroth as u8);
    for i in 1 .. 8 {
        let c = 251 - tmp[i];
        let inv = ((zeroth as u16 * c as u16) % 251) as u8;
        result[i] = inv;
        let tmp2 = compute_row(terms, inv);
        tmp = merge(i, tmp, tmp2);
    }
    return Some(result)
}

fn compute_row(
    row: [u8;8],
    number: u8
) -> [u8;8] {
    let number = number as u16;
    let mut ords = [0u8;8];
    let mut extent = 0;
    for i in 0 .. 8 {
        let mult = row[i] as u16 * number + extent;
        let rem = mult % 251;
        ords[i] = rem as u8;
        extent = (mult - rem) / 251;
    }
    return ords;
}
fn merge(
    pivot: usize,
    acc: [u8;8],
    row: [u8;8]
) -> [u8;8] {
    let mut acc = acc;
    let mut extent = 0;
    for i in pivot .. 8 {
        let v = acc[i] as u16 + row[i - pivot] as u16 + extent;
        acc[i] = (v % 251) as u8;
        extent = (v >= 251) as _;
    }
    return acc;
}
fn multiply(
    a: [u8; 8],
    b: [u8; 8],
) -> [u8;8] {
    let mut dig_ords = [0u8;8];
    for i in 0 .. 8 {
        let row = compute_row(a, b[i]);
        dig_ords = merge(i, dig_ords, row);
    }
    return dig_ords
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
#[repr(align(8))]
pub struct ZModB64([u8;8]);

impl ZModB64 {
    pub const MAX: u64 =
        250 +
        250 * 251u64 +
        250 * 251u64.pow(2) +
        250 * 251u64.pow(3) +
        250 * 251u64.pow(4) +
        250 * 251u64.pow(5) +
        250 * 251u64.pow(6) +
        250 * 251u64.pow(7) ;


    pub const ZERO: Self = Self([0u8;8]);
    pub const ONE: Self = Self([1,0,0,0,0,0,0,0]);

    pub fn from_terms(terms: &[u8]) -> Self {
        assert!(terms.len() <= 8);
        let mut result = [0u8;8];
        for ix in 0 .. terms.len() {
            result[ix] = terms[ix];
        }
        return Self(result);
    }
    pub fn from_signed(num: i64) -> Self {
        let bitnum = num.abs_diff(0);
        if num >= 0 {
            Self::from_two_complement(bitnum)
        } else {
            let num = Self::MAX - bitnum + 1;
            Self::from_two_complement(num)
        }
    }
    pub fn from_positive(num: u64) -> Self {
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

        return Self(terms);
    }
    pub fn as_positive(&self) -> u64 {
        self.as_complement_faster()
    }
    pub fn as_signed(&self) -> (u64, bool) {
        let val = self.as_complement_faster();
        if val > (Self::MAX / 2) - 1 {
            ((Self::MAX + 1 - val), false)
        } else {
            (val, true)
        }
    }
    fn _as_complement_number(&self) -> u64 {
        let terms: u64 = unsafe { transmute(self.0) };

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
        const POWERS: Simd<u64, 8> = Simd::from_array([
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
        terms.mul(POWERS).reduce_sum()
    }
    pub fn as_terms(&self) -> [u8;8] {
        self.0
    }
    pub fn as_reversed_terms(&self) -> [u8;8] {
        let mut t = self.0;
        t.reverse();
        t
    }
    fn _add(&self, another: Self) -> Self {

        let terms1: u64 = unsafe { transmute(self.0) };
        let terms2: u64 = unsafe { transmute(another.0) };
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

        let v = unsafe { transmute(res) };
        return Self(v);
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
                .rotate_elements_right::<1>();
            comb = comb.add(overflow_bits1_shifted);
        }

        let antis = o_bits_acc.select(Simd::splat(251u16), Simd::splat(0));
        let rems = comb.sub(antis).cast::<u8>();

        let val = unsafe { transmute(rems) };
        return Self(val);
    }
    fn __add(&self, another: Self) -> Self {
        let terms1: [u8;8] = self.as_terms();
        let terms2: [u8;8] = another.as_terms();
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

        return Self(out);
    }
    pub fn absolute_value(&self) -> Self {
        let this = *self;
        if self.0[7] != 0 {
            let a = Self::ZERO.sub(this);
            a
        } else {
            this
        }
    }
    pub fn subtract(&self, another: Self) -> Self {
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
    pub fn additive_inverse(&self) -> Self {
        let mut neg_one = [250u8;8];
        let terms = self.as_terms();
        for i in 0 .. 8 {
            neg_one[i] -= terms[i];
        }
        let n = Self(neg_one);
        n.add_faster(Self::ONE)
    }
    fn _multiplicative_inverse1_euclid(&self) -> Self {
        let m = self.as_complement_faster();
        if m % 251 == 0 {
            panic!("Cannot invert number {} because it doesnt satisfy the equation N % 251 > 0", m)
        }
        let n = mod_inverse_u64(m as _, (Self::MAX + 1) as _);
        Self::from_positive(n as _)
    }
    // has weird quirk
    fn _multiplicative_inverse2_brute(&self) -> Self {
        let inv = brute_force_mul_inverse(self.as_terms()).unwrap_or_else(||{
            panic!("Cannot invert number {} because it doesnt satisfy the equation N % 251 > 0", self.as_complement_faster())
        });
        return Self(inv);
    }
    fn _multiplicative_inverse3_fast(&self) -> Self {
        let inv = mult_inverse(self.as_terms()).unwrap_or_else(||{
            panic!("Cannot invert number {} because it doesnt satisfy the equation N % 251 > 0", self.as_complement_faster())
        });
        return Self(inv);
    }
    pub fn multiplicative_inverse(&self) -> Self {
        self._multiplicative_inverse3_fast()
    }
    pub fn multiply(&self, another: Self) -> Self {
        let a = self.as_terms();
        let b = another.as_terms();
        let c = multiply(a, b);
        return Self(c);
    }
    pub fn shift_right(&self, amount: usize) -> Self {
        let mut result = [0u8;8];
        let terms = self.as_terms();
        for i in amount .. 8 {
            result[i] = terms[i - amount];
        }
        return Self(result);
    }
    pub fn shift_left(&self, amount: usize) -> Self {
        let mut result = [0u8;8];
        let terms = self.as_terms();
        for i in amount .. 8 {
            result[i - amount] = terms[i];
        }
        return Self(result);
    }
}

impl core::ops::Add for ZModB64 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add_faster(rhs)
    }
}
impl core::ops::Mul for ZModB64 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::multiply(&self, rhs)
    }
}
impl core::ops::Sub for ZModB64 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::subtract(&self, rhs)
    }
}
impl core::ops::Neg for ZModB64 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.additive_inverse()
    }
}
impl core::ops::Div for ZModB64 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let recip = rhs._multiplicative_inverse2_brute();
        self * recip
    }
}

macro_rules! zmod_autoimpl_pos {
    ($($conformer:ident),+) => {
        $(
            impl Into<ZModB64> for $conformer {
                fn into(self) -> ZModB64 {
                    ZModB64::from_positive(self as _)
                }
            }
        )+
    };
}
zmod_autoimpl_pos!(u8, u16, u32, u64);
macro_rules! zmod_autoimpl_neg {
    ($($conformer:ident),+) => {
        $(
            impl Into<ZModB64> for $conformer {
                fn into(self) -> ZModB64 {
                    ZModB64::from_signed(self as _)
                }
            }
        )+
    };
}
zmod_autoimpl_neg!(i8, i16, i32, i64);

#[test]
fn props_tests() {

    // a + b = 0
    let a = ZModB64::from_signed(-1);
    let b = ZModB64::from_signed(1);
    let c = a + b;
    assert!(c.as_signed() == (0, true));

    // a * 2 = 1
    let a = ZModB64::from_positive(2);
    let b = a._multiplicative_inverse3_fast();
    let c = a.mul(b);
    assert!(c.as_positive() == 1);

    // -1 - -1 = 0
    let a = ZModB64::from_signed(-1);
    let b = ZModB64::from_signed(-1);
    let c = a.sub(b);
    assert!(c.as_signed() == (0, true));

    // -1 + -1 = -2
    let a = ZModB64::from_signed(-1);
    let b = ZModB64::from_signed(-1);
    let c = a.add_faster(b);
    assert!(c.as_signed() == (2, false));

    // a * a = 2

    // a * a = -1

}

#[test]
fn t1() {

    let a_ = 1313131313;
    let b_ = a_;
    let a = ZModB64::from_positive(a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = ZModB64::from_positive(b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul(b);
    println!("{} {:?} __mul2", c.as_positive(), c.as_terms());

    let correct = a_ * b_;
    println!("{} correct", correct);

    let correct_computed = ZModB64::from_two_complement(correct);
    println!("{} {:?}", correct_computed.as_positive(), correct_computed.as_terms());

    let computed = c.as_complement_faster();
    assert!(computed == correct);


    let mut a = ZModB64::from_positive(0);
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
    let a = ZModB64::from_signed(-a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = ZModB64::from_signed(b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul(b);
    println!("{:?} {:?} mul", c.as_signed(), c.as_terms());
    assert!(c.as_signed() == (n, false));

    let a = ZModB64::from_signed(a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = ZModB64::from_signed(-b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul(b);
    assert!(c.as_signed() == (n, false));

    let a = ZModB64::from_signed(-a_);
    // println!("{:?} {:?}", a.as_signed(), a.as_terms());
    let b = ZModB64::from_signed(-b_);
    // println!("{:?} {:?}", b.as_signed(), b.as_terms());
    let c = a.mul(b);
    assert!(c.as_signed() == (n, true));
}

#[test]
fn t3() {
    // (1/3 + 1/3) * 3 = 2
    let a = ZModB64::from_positive(3);
    let b = a._multiplicative_inverse3_fast();
    // println!("{} {:?}", b.as_positive(), b.as_terms());
    let b = b + b;
    // println!("{} {:?}", b.as_positive(), b.as_terms());
    let c = b * a;

    // println!("{} {:?}", d.as_positive(), d.as_terms());
    assert!(c.as_positive() == 2);
}

#[test]
fn t15() {
    // 1/11 + 10/11 = 1
    let k = ZModB64::from_positive(11);
    let k = k._multiplicative_inverse2_brute();

    let d = k * 10.into();
    let r = k + d;
    // println!("{}", r.as_complement_faster());
    assert!(r.as_complement_faster() == 1);
}

#[test] #[ignore]
fn t5() {
    let mut str = String::new();
    use core::fmt::Write;
    for p in 1 .. 10 {
        let lim = 2u64.pow(p);
        for k in 1 .. lim {
            if k % 251 == 0 { continue }
            let a = ZModB64::from_positive(k);
            let a = a._multiplicative_inverse3_fast();
            // println!("{:?} recip", a.as_terms());
            let b = ZModB64::from_positive(lim*k);
            let c = a.mul(b);
            let n = c.as_signed();
            // println!("{:?} {:?} res", c.as_signed(), c.as_terms());
            let ok = if n.0 == lim { "✔️" } else { "❌" };
            writeln!(&mut str, "({} * {}) * 1/{} = {:?} {}", lim, k, k, n, ok).unwrap();
        }
        writeln!(&mut str, "").unwrap();
    }
    println!("{}", str)
}

#[test]
fn t6() {
    for i in 1 .. u16::MAX {
        let a: ZModB64 = i.into();
        let b: ZModB64 = a.additive_inverse();
        let c = a * b;
        // println!("{:?} {} {:?}", c.as_signed(), c.as_positive(), c.as_terms());
        let i = i as u64;
        assert!(c.as_signed() == (i * i, false));
    }
}

#[test] #[ignore]
fn t7() {
    let mut str = String::new();
    use core::fmt::Write;
    for p in 1 .. 256u64 * 16 {
        if p % 251 == 0 {
            writeln!(&mut str, "skipping {} cus its divisible by 251", p).unwrap();
            continue;
        }
        let a = ZModB64::from_positive(p);
        let b = a._multiplicative_inverse3_fast();
        // println!("{:?} recip", a.as_terms());
        let c = a.mul(b);
        let n = c.as_signed();
        // println!("{:?} {:?} res", c.as_signed(), c.as_terms());
        let ok = if n.0 == 1 { "✔️" } else { "❌" };
        writeln!(&mut str, "{} * 1/{} = {:?} {}", p, p, n, ok).unwrap();
    }
    println!("{}", str)
}

#[test]
fn t8() {
    for i in 1 .. u16::MAX {
        if i % 251 == 0 { continue }
        let a: ZModB64 = i.into();
        let b: ZModB64 = a._multiplicative_inverse3_fast();
        let c = a * b;
        // println!("{:?} {} {:?}", c.as_signed(), c.as_positive(), c.as_terms());
        assert!(c.as_signed() == (1, true));
    }
}

#[test] #[ignore]
fn t9() {
    let m_ = ZModB64::from_positive(999);
    let m = m_.as_terms();
    let k = brute_force_mul_inverse(m).unwrap();
    let c = multiply(m, k);
    println!("{:?} {:?} {:?}", m, k, c);

    let m = m_.as_complement_faster() as u128;
    let k = m_._multiplicative_inverse2_brute().as_complement_faster() as u128;
    let c = (m * k) % (ZModB64::MAX as u128 + 1);
    println!("{}", c);
    assert!(c == 1);


    // let m_ = ZModB64::from_positive(251);
    // let k = m_._multiplicative_inverse1_euclid();
    // let c = m_ * k;
    // println!("{}", c.as_complement_faster());

}

#[test] #[ignore]
fn t13() {
    let primes = [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251];

    for prime in primes {

        if ((u64::MAX / prime) * prime) == u64::MAX {
            println!("{prime} is an exact divisor! Skipping...");
            continue;
        }

        let m = prime - 1;
        let num =
            m +
            m * prime.pow(1) +
            m * prime.pow(2) +
            m * prime.pow(3) +
            m * prime.pow(4) +
            m * prime.pow(5) +
            m * prime.pow(6) +
            m * prime.pow(7) ;

        let magic = (u64::MAX / prime) + 1;
        let d = ((magic as u128 * num as u128) >> 64) as u64;

        let a = d * prime ;

        if a > num {
            let b = num - ((num / prime) * prime);
            println!("{} !!!! {} > {} !!!! {} OFF !!! Correct is {} bellow", prime, a, num, a - num, b);
        }
    }
}

#[allow(dead_code)]
fn mult_mod_inv(n: u64) -> u64 {
    assert!(n & 1 == 1, "Doesnt work for even numbers");
    assert!(n != 0, "Equation 0 mod Y == 1 does not have a solution");
    let mut k = 1u64;
    let mut i = 1u64;
    for _ in 0 .. 64 {
        i <<= 1;
        let c = k.wrapping_mul(n);
        if c & i != 0 { k ^= i }
    }

    return k;
}

#[test]
fn t14() {
    let d = 9;
    let k = mult_mod_inv(d);
    println!("{} {}", k, k.wrapping_mul(d));

    let d = 11;
    let k = mult_mod_inv(d);
    let j = k.wrapping_mul(10);

    let m = k.wrapping_add(j);
    println!("{}", m);
}


