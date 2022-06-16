use std::mem;
use std::num;
use core::mem::MaybeUninit;
use gmp_mpfr_sys::gmp;
use byteorder::{BigEndian, WriteBytesExt, ReadBytesExt};

/// chain_order_encode takes a vector representing the
/// order of a number and converts it into a vector of bytes
///
/// Format of the first byte is:
///
/// 1cxxxxxx
///
/// Format of each following byte is:
///
/// cxxxxxxx
///
/// where c is the chain bit. If zero, then
/// we are terminal, otherwise there is another size
/// to come.
///
/// The first bit is a sign bit, we will twos complement the
/// entire result and therby end up with a negative, so it
/// is always 1 here.
///fn chain_order_encode(v : Vec<u8>) -> Vec<u8> {
///}

fn bytes_and_pad(bits : usize) -> (usize,u8) {
    assert!(bits > 0);
    let mut bytes = 0;
    let mut remainder = bits as i64;
    let mut shift = 2;
    while remainder > 0 {
        remainder = remainder - (8 - shift);
        bytes += 1;
        shift = 1;
    }
    (bytes, remainder.abs() as u8)
}

fn make_ones_mask(size : u8) -> u8 {
    2 ^ size - 1
}
const TERMINAL : usize = 0;
const CONTINUATION : usize = 0b10000000usize;
const FIRST_CONTINUATION : usize = 0b01000000usize;
const BASE_MASK : usize = !CONTINUATION;
const FIRST_MASK : usize = !FIRST_CONTINUATION;

fn size_enc(size : usize) -> Vec<u8> {
    let mut remainder = size;
    let mut v = vec![];
    let mut last = true;
    while remainder > 0 {
        println!("remainder: {:}", remainder);
        if remainder >= CONTINUATION {
            println!("big");
            let continued = if last {TERMINAL} else {CONTINUATION};
            println!("continued: {:#b}", continued);
            let byte = ((remainder & BASE_MASK) | continued) as u8;
            println!("byte: {:#b}", byte);
            v.push(byte);
        }else if remainder >= FIRST_CONTINUATION {
            // special case where we fit in 7 bits but not 6
            // and we need a zero padded initial byte.
            println!("medium");
            let continued = if last {0} else {CONTINUATION};
            println!("continued: {:#b}", continued);
            let byte = ((remainder & BASE_MASK) | continued) as u8;
            println!("byte: {:#b}", byte);
            v.push(byte);
            println!("zero pad");
            let byte = FIRST_CONTINUATION as u8;
            println!("byte: {:#b}", byte);
            v.push(byte)
        }else{
            println!("small");
            let continued = if last {0} else {FIRST_CONTINUATION};
            println!("continued: {:#b}", continued);
            let byte = ((remainder & FIRST_MASK) | continued) as u8;
            println!("byte: {:#b}", byte);
            v.push(byte)
        }
        remainder = remainder >> 7;
        last = false;
    }
    v.reverse();
    v
}

fn size_dec(v : &[u8]) -> usize {
    println!("v: {:?}", v);
    let mut size = 0;
    for i in 0..v.len() {
        println!("size: {:}",size);
        let vi = v[i] as usize;
        println!("v[i]: {:#b}", v[i]);
        if i == 0 {
            if vi & FIRST_CONTINUATION == 0 {
                return size & FIRST_MASK
            }else{
                size = size + (vi & FIRST_MASK)
            }
        }else{
            if vi & CONTINUATION == 0 {
                println!("continuation: {:#b}", CONTINUATION);
                return size + (vi & BASE_MASK)
            }else{
                size = size + (vi & BASE_MASK)
            }
        }
        size = size << 7;
    }
    size
}

fn limb_vec(l : gmp_mpfr_sys::gmp::limb_t) -> Vec<u8> {
    let mut wtr = vec![];
    wtr.write_u64::<BigEndian>(l).unwrap();
    wtr
}

// We need to panic if this is wrong
const BYTES_PER_WORD : usize = 8;

fn convert_mpz_lex(z : *mut gmp_mpfr_sys::gmp::mpz_t) -> Vec<u8> {
    // This should not be hard-coded, but arch dependent
    let sign = unsafe{ gmp::mpz_sgn(z) };
    let size = unsafe{ gmp::mpz_size(z) };
    if size == 0 {
        return vec![0]
    }else{
        // we need to get the first limb to get the true size
        // as we need leading zeros to be neglected
        let limb0 = unsafe{ gmp::mpz_getlimbn(z,0) };
        let zeros = limb0.leading_zeros();
        let zero_bytes = zeros as usize / BYTES_PER_WORD;
        println!("size: {:}", size);
        println!("zero_bytes: {:}", zero_bytes);
        let bytes = size * BYTES_PER_WORD - zero_bytes;
        let encoded_size = size_enc(bytes);
        let mut vec = limb_vec(limb0)[zero_bytes..BYTES_PER_WORD].to_vec();
        for i in 1..size {
            let limb_num = unsafe{ gmp::mpz_getlimbn(z,i as i64) };
            let mut limb = limb_vec(limb_num);
            vec.append(&mut limb);
        }
        if sign == -1 {
            negate(&mut vec)
        }
        println!("{:?}", vec);
        return vec
    }
}

fn negate(v : &mut [u8]) -> () {
    for i in 0..v.len() {
        v[i] = !v[i]
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {

    use core::mem::MaybeUninit;
    use gmp_mpfr_sys::gmp;

    #[test]
    fn find_bytes_and_pad() {
        let size = 4095; // [0b00001111u8,0b11111111u8];
        let enc = crate::size_enc(size);
        assert_eq!(enc, vec![0b01011111u8, 0b01111111u8]);

        let size = 72057594037927935;
        let enc = crate::size_enc(size);
        assert_eq!(enc, vec![0b01000000u8, 0b11111111u8, 0b11111111u8,
                             0b11111111u8, 0b11111111u8, 0b11111111u8,
                             0b11111111u8, 0b11111111u8, 0b01111111u8 ])

    }

    #[test]
    fn in_and_out() {
        let size = 4095; // [0b00001111u8,0b11111111u8];
        assert_eq!(size, crate::size_dec(&crate::size_enc(size)));

        // just a random number
        let size = 23423423;
        assert_eq!(size, crate::size_dec(&crate::size_enc(size)));

        // boundary case for overflow spillover
        let size = 72057594037927935;
        assert_eq!(size, crate::size_dec(&crate::size_enc(size)));

    }

    #[test]
    fn mpz_lex_conversions() {
        unsafe {
            let mut z = MaybeUninit::uninit();
            gmp::mpz_init(z.as_mut_ptr());
            let mut z = z.assume_init();
            gmp::mpz_set_ui(&mut z, 15);
        }
    }

    #[test]
    fn encode_gmp() {
        unsafe {
            let mut z = MaybeUninit::uninit();
            gmp::mpz_init(z.as_mut_ptr());
            let mut z = z.assume_init();
            gmp::mpz_set_si(&mut z, 4095);
            let vec = crate::convert_mpz_lex(&mut z);
            assert_eq!(vec, vec![0]);
        }
    }

    #[test]
    fn test_gmp_order() {
        unsafe {
            let mut z = MaybeUninit::uninit();
            gmp::mpz_init(z.as_mut_ptr());
            let mut z = z.assume_init();
            gmp::mpz_set_ui(&mut z, 15);
            let sign = gmp::mpz_sgn(&z);
            assert_eq!(sign, 1);
            let sz = gmp::mpz_sizeinbase(&z,2);
            assert_eq!(sz, 4);
            let u = gmp::mpz_get_ui(&z);
            assert_eq!(u, 15);
            gmp::mpz_clear(&mut z);
        }
    }
}
