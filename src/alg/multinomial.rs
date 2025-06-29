// TODO: implement computing multinomials
// https://github.com/kth-competitive-programming/kactl/blob/main/content/combinatorial/multinomial.h

pub fn multinomial(v: &[u64]) -> u64 {
    let mut c = 1;
    let mut m = if v.is_empty() { 1 } else { v[0] };
    for i in 1..v.len() {
        for j in 0..v[i] {
            m += 1;
            c = c * m / (j + 1);
        }
    }
    c
}
