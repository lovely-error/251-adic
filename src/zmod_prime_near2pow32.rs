use core::mem::transmute;
use std::collections::HashMap;


#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy)]

pub struct ZMod_n2p32(u32);

impl ZMod_n2p32 {
  pub const MAX_MUL_INVERSE: u32 = 3_969_125_989;
  pub const MAX_ADDITIVE_INVERSE: u32 =
    250 * 251u32.pow(0) +
    250 * 251u32.pow(1) +
    250 * 251u32.pow(2) +
    250 * 251u32.pow(3) ;

  pub fn from_number(number: u32) -> Self {
    assert!(
      number <= Self::MAX_ADDITIVE_INVERSE &&
      number <= Self::MAX_MUL_INVERSE
    );
    Self(number)
  }
  pub fn as_terms(&self) -> [u8;4] {
    let mut terms = [0u8;4];
    let mut n = self.0;
    for i in 0 .. 4 {
      let d = n / 251;
      let rem = n - d * 251;
      terms[i] = rem as u8;
      n = d;
      if d == 0 { break }
    }
    return unsafe { transmute(terms) }
  }
  pub fn as_two_complement(&self) -> u32 {
    self.0
  }
  pub fn is_positive(&self) -> bool {
    self.as_terms()[3] != 250
  }
  pub fn as_signed(&self) -> (u32, bool) {
    let num = self.as_two_complement();
    let pos = self.is_positive();
    if pos {
      return (num, true);
    } else {
      return (num, false);
    }
  }
  pub fn add(&self, another: Self) -> Self {
    let t1 = self.as_terms();
    let t2 = another.as_terms();
    let v = Self::add_terms(t1, t2);
    Self::from_terms(v)
  }
  fn add_terms(one: [u8;4], another: [u8;4]) -> [u8;4] {
    let terms1:u32 = unsafe { transmute(one) };
    let terms2:u32 = unsafe { transmute(another) };
    let mask = (1 << 8) - 1;
    let mut res = 0u32;

    fn frem251_250x2(num: u32) -> u32 {
        num - (251 * (num >= 251) as u32)
    }

    let t = (terms1 & mask) + (terms2 & mask) ;
    res |= frem251_250x2(t) ;
    let t = ((terms1 >> 8) & mask) + ((terms2 >> 8) & mask) + ((t >= 251) as u32);
    res |= (frem251_250x2(t) ) << 8;
    let t = ((terms1 >> 16) & mask) + ((terms2 >> 16) & mask) + ((t >= 251) as u32);
    res |= (frem251_250x2(t) ) << 16;
    let t = ((terms1 >> 24) & mask) + ((terms2 >> 24) & mask) + ((t >= 251) as u32);
    res |= (frem251_250x2(t) ) << 24;

    return unsafe { transmute(res) };
  }
  pub fn additive_inverse(&self) -> Self {
    let mut neg_one = [250u8,250,250,250];
    let der = self.as_terms();
    for i in 0 .. 4 {
      neg_one[i] -= der[i]
    }
    let terms = unsafe { transmute(neg_one) };
    let res = Self::add_terms(terms, [1,0,0,0]);
    return Self::from_terms(res);
  }
  pub fn from_terms(terms: [u8;4]) -> Self {
    Self(Self::terms_to_num(terms))
  }
  fn terms_to_num(terms: [u8;4]) -> u32 {
    let mut n = 0;
    for i in 0 .. 4 {
      n += terms[i] as u32 * 251u32.pow(i as u32)
    }
    return n;
  }
  pub fn multiplicative_inverse(&self) -> Self {
    let n = self.as_two_complement();
    assert!(
      n < Self::MAX_MUL_INVERSE,
      "Cant form multiplicative inverse because number is too big. Max is {}",
      Self::MAX_MUL_INVERSE
    );
    let n = mod_inverse(n as i64, Self::MAX_MUL_INVERSE as i64);
    Self(n as u32)
  }
  pub fn mul(&self, another: Self) -> Self {
    let a = self.as_two_complement() as u64;
    let b = another.as_two_complement() as u64;
    let c = a * b;
    let r = c % (Self::MAX_MUL_INVERSE as u64);
    return Self::from_number(r as u32);
  }
  pub fn log(&self, base: Self) -> Option<Self> {
    let this = self.as_two_complement();
    let base = base.as_two_complement();
    if let Some(pow) = try_solve_log(base as _, this as _, Self::MAX_MUL_INVERSE as i64) {
      return Some(Self::from_number(pow as _))
    } else {
      return None;
    };
  }
  pub fn pow(&self, number: Self) -> Self {
    let this = self.as_two_complement();
    let number = number.as_two_complement();
    let pow = binpow(this as _, number as _, Self::MAX_ADDITIVE_INVERSE as _);
    return Self::from_number(pow as _);
  }
}

fn try_solve_log(a: i64, b: i64, m: i64) -> Option<i64> {
    let a = a % m;
    let b = b % m;
    let n = (m as f64).sqrt() as i64 + 1;

    let mut an = 1;
    for _ in 0..n {
        an = (an * a) % m;
    }

    let mut vals = HashMap::new();
    let mut cur = b;
    for q in 0..=n {
        vals.insert(cur, q);
        cur = (cur * a) % m;
    }

    let mut cur = 1;
    for p in 1..=n {
        cur = (cur * an) % m;
        if let Some(&q) = vals.get(&cur) {
            let ans = n * p - q;
            return Some(ans);
        }
    }
    return None;
}

// https://cp-algorithms.com/algebra/module-inverse.html
#[allow(dead_code)]
fn mod_inverse(mut a: i64, mut m: i64) -> i64 {
  let m0 = m;
  let mut y = 0;
  let mut x = 1;

  while a > 1 {
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

// https://cp-algorithms.com/algebra/binary-exp.html
#[allow(dead_code)]
fn binpow(mut a: u64, mut b: u64, m: u64) -> u64 {
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

impl PartialEq for ZMod_n2p32 {
  fn eq(&self, other: &Self) -> bool {
      self.0 == other.0
  }
}


#[test]
fn t1 () {
  for n in 1 .. u16::MAX {
    let a = ZMod_n2p32::from_number(n as _);
    let b = a.multiplicative_inverse();
    let c = a.mul(b);
    assert!(c.0 == 1);
  }
}

#[test] #[ignore]
fn t3() {
    let mut str = String::new();
    use core::fmt::Write;
    for p in 1 .. 256u32 {
        let a = ZMod_n2p32::from_number(p);
        let b = a.multiplicative_inverse();
        // println!("{:?} recip", a.as_terms());
        let c = a.mul(b);
        let n = c.0;
        // println!("{:?} {:?} res", c.as_signed(), c.as_terms());
        let ok = if n == 1 { "✔️" } else { "❌" };
        writeln!(&mut str, "{} * 1/{} = {:?} {}", p, p, n, ok).unwrap();
    }
    println!("{}", str)
}

#[test]
fn t4 () {
  for n in 1 .. u16::MAX {
    let a = ZMod_n2p32::from_number(n as _);
    let b = a.additive_inverse();
    let c = a.add(b);
    assert!(c.0 == 0);
  }
}

#[test]
fn t5() {
  for k in 1 .. 8u32 {
    for r in 1 .. 8 {
      let p = k.pow(r);
      println!("{k}^{r} log {k}");
      let n = ZMod_n2p32::from_number(p);
      let m = ZMod_n2p32::from_number(k);
      let p = n.log(m);
      match p {
        Some(num) => {
          let k = m.pow(num);
          assert!(k == n);
        },
        None => {
          panic!("Aint got logs {} log {}", k, r);
        },
      }
    }
  }
}

#[test]
fn t6() {
  let m = ZMod_n2p32::from_number(11);
  let im = m.additive_inverse();
  println!("{:?}", im.as_signed())
}