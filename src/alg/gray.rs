pub fn gray(i: u64) -> u64 {
    i ^ i >> 1
}

pub fn inv_gray(mut i: u64) -> u64 {
    i ^= i >> 1;
    i ^= i >> 2;
    i ^= i >> 4;
    i ^= i >> 8;
    i ^= i >> 16;
    i ^= i >> 32;
    i
}
