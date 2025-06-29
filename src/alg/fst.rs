use std::ops::{Add, Div, MulAssign, Sub};

/// O(n log n)
pub fn and_transform<const INV: u8, T: Clone + Add<Output = T> + Sub<Output = T>>(a: &mut [T]) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                (a[j], a[j + k]) = if INV == 1 {
                    (a[j].clone() - a[j + k].clone(), a[j + k].clone())
                } else {
                    (a[j].clone() + a[j + k].clone(), a[j + k].clone())
                };
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
pub fn or_transform<const INV: u8, T: Clone + Add<Output = T> + Sub<Output = T>>(a: &mut [T]) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                (a[j], a[j + k]) = if INV == 1 {
                    (a[j].clone(), a[j + k].clone() - a[j].clone())
                } else {
                    (a[j].clone(), a[j].clone() + a[j + k].clone())
                };
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

/// O(n log n)
pub fn xor_transform<
    const INV: u8,
    T: Clone + Add<Output = T> + Sub<Output = T> + Div<Output = T> + From<i32>,
>(
    a: &mut [T],
) {
    let n = a.len();
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in i..i + k {
                (a[j], a[j + k]) = (
                    a[j].clone() + a[j + k].clone(),
                    a[j].clone() - a[j + k].clone(),
                );
            }
            i += k << 1;
        }
        k <<= 1;
    }
    if INV == 1 {
        for x in a {
            *x = (*x).clone() / T::from(n as i32);
        }
    }
}

pub fn and_conv<T: Clone + Add<Output = T> + Sub<Output = T> + MulAssign>(
    a: &mut [T],
    b: &mut [T],
) {
    and_transform::<0, T>(a);
    and_transform::<0, T>(b);
    for i in 0..a.len() {
        a[i] *= b[i].clone();
    }
    and_transform::<1, T>(a);
}

pub fn or_conv<T: Clone + Add<Output = T> + Sub<Output = T> + MulAssign>(a: &mut [T], b: &mut [T]) {
    or_transform::<0, T>(a);
    or_transform::<0, T>(b);
    for i in 0..a.len() {
        a[i] *= b[i].clone();
    }
    or_transform::<1, T>(a);
}

pub fn xor_conv<
    T: Clone + Add<Output = T> + Sub<Output = T> + MulAssign + Div<Output = T> + From<i32>,
>(
    a: &mut [T],
    b: &mut [T],
) {
    xor_transform::<0, T>(a);
    xor_transform::<0, T>(b);
    for i in 0..a.len() {
        a[i] *= b[i].clone();
    }
    xor_transform::<1, T>(a);
}
