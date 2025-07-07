use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Sub, SubAssign,
};

fn div_floor_i32(a: i32, b: i32) -> i32 {
    a / b - if a % b < 0 { 1 } else { 0 }
}

fn div_floor_i64(a: i64, b: i64) -> i64 {
    a / b - if a % b < 0 { 1 } else { 0 }
}

fn div_round_i32(a: i32, b: i32) -> i32 {
    div_floor_i32(2 * a + b, 2 * b)
}

fn div_round_i64(a: i64, b: i64) -> i64 {
    div_floor_i64(2 * a + b, 2 * b)
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Zi<T>(pub T, pub T);

impl<T> Zi<T> {
    pub fn new(x: T, y: T) -> Self {
        Zi(x, y)
    }
}

impl<T> Zi<T>
where
    T: Copy + Add<Output = T> + Mul<Output = T>,
{
    pub fn norm(&self) -> T {
        let Zi(a, b) = *self;
        a * a + b * b
    }
}

impl<T: Neg<Output = T>> Not for Zi<T> {
    type Output = Self;
    fn not(self) -> Self::Output {
        Zi(self.0, -self.1)
    }
}

impl<T: Neg<Output = T>> Neg for Zi<T> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Zi(-self.0, -self.1)
    }
}

impl<T: AddAssign> AddAssign for Zi<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.1 += rhs.1;
    }
}

impl<T: Add<Output = T>> Add for Zi<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Zi(self.0 + rhs.0, self.1 + rhs.1)
    }
}

impl<T: SubAssign> SubAssign for Zi<T> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
        self.1 -= rhs.1;
    }
}

impl<T: Sub<Output = T>> Sub for Zi<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Zi(self.0 - rhs.0, self.1 - rhs.1)
    }
}

impl<T> MulAssign for Zi<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    fn mul_assign(&mut self, rhs: Self) {
        (self.0, self.1) = (
            self.0 * rhs.0 - self.1 * rhs.1,
            self.0 * rhs.1 + self.1 * rhs.0,
        );
    }
}

impl<T> Mul for Zi<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T>,
{
    type Output = Self;
    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl DivAssign for Zi<i32> {
    fn div_assign(&mut self, rhs: Self) {
        *self *= !rhs;
        let d = rhs.norm();
        self.0 = div_round_i32(self.0, d);
        self.1 = div_round_i32(self.1, d);
    }
}

impl Div for Zi<i32> {
    type Output = Self;
    fn div(mut self, rhs: Self) -> Self::Output {
        self /= rhs;
        self
    }
}

impl DivAssign for Zi<i64> {
    fn div_assign(&mut self, rhs: Self) {
        *self *= !rhs;
        let d = rhs.norm();
        self.0 = div_round_i64(self.0, d);
        self.1 = div_round_i64(self.1, d);
    }
}

impl Div for Zi<i64> {
    type Output = Self;
    fn div(mut self, rhs: Self) -> Self::Output {
        self /= rhs;
        self
    }
}

impl RemAssign for Zi<i32> {
    fn rem_assign(&mut self, rhs: Self) {
        *self -= *self / rhs * rhs;
    }
}

impl Rem for Zi<i32> {
    type Output = Self;
    fn rem(mut self, rhs: Self) -> Self::Output {
        self %= rhs;
        self
    }
}

impl RemAssign for Zi<i64> {
    fn rem_assign(&mut self, rhs: Self) {
        *self -= *self / rhs * rhs;
    }
}

impl Rem for Zi<i64> {
    type Output = Self;
    fn rem(mut self, rhs: Self) -> Self::Output {
        self %= rhs;
        self
    }
}

impl<T: Default> Default for Zi<T> {
    fn default() -> Self {
        Zi(T::default(), T::default())
    }
}

impl<T: Copy> Zi<T> {
    pub fn gcd(mut self, mut rhs: Zi<T>) -> Zi<T>
    where
        T: Default + PartialEq + Clone,
        Zi<T>: RemAssign + Clone + Default + PartialEq,
    {
        while rhs != Zi::default() {
            self %= rhs.clone();
            std::mem::swap(&mut self, &mut rhs);
        }
        self
    }

    pub fn ext_gcd(self, rhs: Zi<T>) -> (Zi<T>, Zi<T>, Zi<T>)
    where
        T: Default + PartialEq + Clone,
        i32: Into<T>,
        Zi<T>: Sub<Output = Zi<T>>
            + Mul<Output = Zi<T>>
            + Div<Output = Zi<T>>
            + Clone
            + Default
            + PartialEq,
    {
        if rhs != Zi::default() {
            let q = self / rhs;
            let (g, x, y) = rhs.ext_gcd(self - q * rhs);
            (g, y, x - q * y)
        } else {
            (
                self,
                Zi(1.into(), T::default()),
                Zi(T::default(), T::default()),
            )
        }
    }

    // TODO: sum of two squares
    // https://judge.yosupo.jp/submission/235398
    // https://codeforces.com/blog/entry/116519
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let a = Zi(3, 4);
        let b = Zi(1, 2);
        assert_eq!(a + b, Zi(4, 6));
        assert_eq!(a - b, Zi(2, 2));
        assert_eq!(a * b, Zi(-5, 10));
        assert_eq!(a.norm(), 25);
        assert_eq!((!a), Zi(3, -4));
        assert_eq!((-a), Zi(-3, -4));
    }

    #[test]
    fn test_division() {
        let a = Zi(10, 5);
        let b = Zi(2, 1);
        let result = a / b;
        assert_eq!(result, Zi(5, 0));
    }

    #[test]
    fn test_gcd() {
        let a = Zi(10, 15);
        let b = Zi(6, 9);
        let result = a.gcd(b);
        println!("{:?}", result);
        assert_eq!(a % result, Zi(0, 0));
        assert_eq!(b % result, Zi(0, 0));
    }

    #[test]
    fn test_gcd_with_one() {
        // GCD with 1 should be 1
        let a = Zi(5i32, 3i32);
        let b = Zi(1i32, 0i32);
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        assert_eq!(result, Zi(1, 0));
    }

    #[test]
    fn test_gcd_with_zero() {
        // GCD with 0 should be the other number (up to units)
        let a = Zi(5i32, 3i32);
        let b = Zi(0i32, 0i32);
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        assert_eq!(result, a);
    }

    #[test]
    fn test_gcd_equal_numbers() {
        // GCD of equal numbers should be that number (up to units)
        let a = Zi(3i32, 4i32);
        let b = Zi(3i32, 4i32);
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        assert_eq!(result, a);
    }

    #[test]
    fn test_gcd_coprime() {
        // 3 and 1+i are coprime in ℤ[i] (1+i does _not_ divide 3):
        let a = Zi(3, 0); // 3
        let b = Zi(1, 1); // 1 + i
        let d = a.gcd(b);
        // Only a unit divides both, so norm(d) == 1
        assert_eq!(d.norm(), 1);
    }

    #[test]
    fn test_gcd_gaussian_units() {
        // Test with Gaussian units: 1, -1, i, -i
        let a = Zi(2i32, 2i32); // 2 + 2i = 2(1 + i)
        let b = Zi(2i32, -2i32); // 2 - 2i = 2(1 - i)
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        // Both should be divisible by the result
        assert_eq!(a % result, Zi(0, 0));
        assert_eq!(b % result, Zi(0, 0));
    }

    #[test]
    fn test_gcd_larger_numbers() {
        // Test with larger numbers
        let a = Zi(15i32, 20i32); // 15 + 20i
        let b = Zi(9i32, 12i32); // 9 + 12i
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        // Both should be divisible by the result
        assert_eq!(a % result, Zi(0, 0));
        assert_eq!(b % result, Zi(0, 0));

        // The GCD should have a reasonable norm
        assert!(result.norm() > 0);
    }

    #[test]
    fn test_gcd_negative_components() {
        // Test with negative components
        let a = Zi(-6i32, 8i32); // -6 + 8i
        let b = Zi(10i32, -15i32); // 10 - 15i
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        // Both should be divisible by the result
        assert_eq!(a % result, Zi(0, 0));
        assert_eq!(b % result, Zi(0, 0));
    }

    #[test]
    fn test_gcd_real_numbers() {
        // Test with real Gaussian integers (imaginary part = 0)
        let a = Zi(12i32, 0i32);
        let b = Zi(8i32, 0i32);
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        // For real numbers, this should behave like regular integer GCD
        assert_eq!(a % result, Zi(0, 0));
        assert_eq!(b % result, Zi(0, 0));
    }

    #[test]
    fn test_gcd_purely_imaginary() {
        // Test with purely imaginary numbers
        let a = Zi(0i32, 12i32); // 12i
        let b = Zi(0i32, 8i32); // 8i
        let result = a.gcd(b);

        println!("GCD of {:?} and {:?} is {:?}", a, b, result);
        // Both should be divisible by the result
        assert_eq!(a % result, Zi(0, 0));
        assert_eq!(b % result, Zi(0, 0));
    }

    #[test]
    fn test_extgcd_basic() {
        let a = Zi(4i32, 2i32);
        let b = Zi(2i32, 1i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity: a*x + b*y = g
        assert_eq!(a * x + b * y, g);
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
        println!(
            "Verification: {:?} * {:?} + {:?} * {:?} = {:?}",
            a,
            x,
            b,
            y,
            a * x + b * y
        );
    }

    #[test]
    fn test_extgcd_with_one() {
        let a = Zi(5i32, 3i32);
        let b = Zi(1i32, 0i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        assert_eq!(g, Zi(1, 0)); // GCD with 1 should be 1
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
    }

    #[test]
    fn test_extgcd_with_zero() {
        let a = Zi(5i32, 3i32);
        let b = Zi(0i32, 0i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        assert_eq!(g, a); // GCD with 0 should be a
        assert_eq!(x, Zi(1, 0)); // x should be 1
        assert_eq!(y, Zi(0, 0)); // y should be 0
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
    }

    #[test]
    fn test_extgcd_coprime() {
        let a = Zi(3, 0);
        let b = Zi(1i32, 1i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        // For coprime numbers, GCD should be a unit
        assert_eq!(g.norm(), 1);
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
    }

    #[test]
    fn test_extgcd_larger_numbers() {
        let a = Zi(15i32, 20i32);
        let b = Zi(9i32, 12i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
        println!(
            "Verification: {:?} * {:?} + {:?} * {:?} = {:?}",
            a,
            x,
            b,
            y,
            a * x + b * y
        );
    }

    #[test]
    fn test_extgcd_negative_components() {
        let a = Zi(-6i32, 8i32);
        let b = Zi(10i32, -15i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
    }

    #[test]
    fn test_extgcd_real_numbers() {
        let a = Zi(12i32, 0i32);
        let b = Zi(8i32, 0i32);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        // For real numbers, this should behave like regular extended GCD
        assert_eq!(g, Zi(-4, 0));
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
    }

    #[test]
    fn test_extgcd_i64() {
        let a = Zi(100i64, 200i64);
        let b = Zi(50i64, 75i64);
        let (g, x, y) = a.ext_gcd(b);

        // Verify the Bezout identity
        assert_eq!(a * x + b * y, g);
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g, x, y);
    }

    #[test]
    fn test_extgcd_symmetric() {
        let a = Zi(6i32, 8i32);
        let b = Zi(4i32, 3i32);

        let (g1, x1, y1) = a.ext_gcd(b);
        let (g2, x2, y2) = b.ext_gcd(a);

        // Both should satisfy their respective Bezout identities
        assert_eq!(a * x1 + b * y1, g1);
        assert_eq!(b * x2 + a * y2, g2);

        // The GCDs should be the same (up to units)
        assert_eq!(g1.norm(), g2.norm());

        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", a, b, g1, x1, y1);
        println!("extgcd({:?}, {:?}) = ({:?}, {:?}, {:?})", b, a, g2, x2, y2);
    }
}
