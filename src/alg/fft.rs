use num::Complex;
use std::f64::consts::PI;

pub fn fft(a: &mut [Complex<f64>]) {
    let n = a.len();
    let l = n.ilog2();
    let mut rt = vec![Complex::<f64>::ZERO; n];
    rt[0..2].fill(Complex::ONE);
    let mut k = 2;
    while k < n {
        let x = Complex::from_polar(1., -PI / k as f64);
        for i in k..2 * k {
            rt[i] = if i & 1 != 0 {
                rt[i >> 1] * x
            } else {
                rt[i >> 1]
            };
        }
        k <<= 1;
    }
    for i in 0..n {
        let rev_i = i.reverse_bits() >> usize::BITS - l;
        if i < rev_i {
            a.swap(i, rev_i);
        }
    }
    let mut k = 1;
    while k < n {
        let mut i = 0;
        while i < n {
            for j in 0..k {
                let (ij, ijk) = (i + j, i + j + k);
                let z = rt[j + k] * a[ijk];
                a[ijk] = a[ij] - z;
                a[ij] += z;
            }
            i += k << 1;
        }
        k <<= 1;
    }
}

pub fn fft_conv<T: Clone + Into<f64>>(a: &[T], b: &[T]) -> Vec<f64> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let n = (a.len() + b.len() - 1).next_power_of_two();
    let mut res = vec![0_f64; n];
    let (mut inp, mut out) = (vec![Complex::ZERO; n], vec![Complex::ZERO; n]);
    let mut i = 0;
    while i < a.len() || i < b.len() {
        if i < a.len() && i < b.len() {
            inp[i] = Complex::new(a[i].clone().into(), b[i].clone().into());
        } else if i < a.len() {
            inp[i] = Complex::new(a[i].clone().into(), 0.);
        } else {
            inp[i] = Complex::new(0., b[i].clone().into());
        }
        i += 1;
    }
    fft(&mut inp);
    inp.iter_mut().for_each(|v| *v *= *v);
    for i in 0..n {
        out[i] = inp[(n - i) & (n - 1)] - inp[i].conj();
    }
    fft(&mut out);
    for i in 0..res.len() {
        res[i] = out[i].im / (4. * n as f64);
    }

    res
}
