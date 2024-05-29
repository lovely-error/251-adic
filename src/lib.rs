#![feature(inline_const)]
#![feature(portable_simd)]
#![feature(generic_arg_infer)]

mod zmod_prime_near2pow64;
mod zmod_prime_near2pow32;

pub use zmod_prime_near2pow32::ZMod_n2p32;