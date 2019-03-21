//!	Exports functions for integer square root calculations.
//! 
//! Perfect squares are guarrenteed to have correct results.  
//! All other numbers are guarrenteed to be off by one.  
//! 
//! # Examples
//! 
//! ```
//! use sqrt::sqrt_u32;
//! 
//! assert_eq!(sqrt_u32(1000), 32);
//! assert_eq!(sqrt_u32(1024), 32);
//! assert_eq!(sqrt_u32(1100), 34);
//! ```
//! 
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2019-03-07

#![deny(missing_docs,)]
#![feature(test,)]

#[cfg(test,)]
extern crate test;

/// Calculates the square root of a 8bit number.
pub fn sqrt_u8(num: u8,) -> u8 {
  if num == 0 { return 0 }
  if num <= 2 { return 1 }

  let num = num as i16;
  let mut sqrt = num >> (15 - num.leading_zeros());
  let mut square = sqrt * sqrt;
  let mut diff = num - square;
  let mut diff_half = diff / 2;

  loop {
    let shift = diff_half / sqrt;

    sqrt += shift;
    square = sqrt * sqrt;

    if shift.abs() == 0 { break }

    diff = num - square;
    diff_half = diff / 2;
  }

  if num == square + (sqrt << 1) + 1 { sqrt as u8 + 1 }
  else if num == square - (sqrt << 1) + 1 { sqrt as u8 - 1 }
  else { sqrt as u8 }
}

/// Calculates the square root of a 16bit number.
pub fn sqrt_u16(num: u16,) -> u16 {
  if num == 0 { return 0 }
  if num <= 2 { return 1 }

  let num = num as i32;
  let mut sqrt = num >> (31 - num.leading_zeros());
  let mut square = sqrt * sqrt;
  let mut diff = num - square;
  let mut diff_half = diff / 2;

  loop {
    let shift = diff_half / sqrt;

    sqrt += shift;
    square = sqrt * sqrt;

    if shift.abs() == 0 { break }

    diff = num - square;
    diff_half = diff / 2;
  }

  if num == square + (sqrt << 1) + 1 { sqrt as u16 + 1 }
  else if num == square - (sqrt << 1) + 1 { sqrt as u16 - 1 }
  else { sqrt as u16 }
}

/// Calculates the square root of a 32bit number.
pub fn sqrt_u32(num: u32,) -> u32 {
  if num == 0 { return 0 }
  if num <= 2 { return 1 }

  let num = num as i64;
  let mut sqrt = num >> (63 - num.leading_zeros());
  let mut square = sqrt * sqrt;
  let mut diff = num - square;
  let mut diff_half = diff / 2;

  loop {
    let shift = diff_half / sqrt;

    sqrt += shift;
    square = sqrt * sqrt;

    if shift.abs() == 0 { break }

    diff = num - square;
    diff_half = diff / 2;
  }

  if num == square + (sqrt << 1) + 1 { sqrt as u32 + 1 }
  else if num == square - (sqrt << 1) + 1 { sqrt as u32 - 1 }
  else { sqrt as u32 }
}

/// Calculates the square root of a 64bit number.
pub fn sqrt_u64(num: u64,) -> u64 {
  if num == 0 { return 0 }
  if num <= 2 { return 1 }

  let num = num as i128;
  let mut sqrt = num >> (127 - num.leading_zeros());
  let mut square = sqrt * sqrt;
  let mut diff = num - square;
  let mut diff_half = diff / 2;

  loop {
    let shift = diff_half / sqrt;

    sqrt += shift;
    square = sqrt * sqrt;

    if shift.abs() == 0 { break }

    diff = num - square;
    diff_half = diff / 2;
  }

  if num == square + (sqrt << 1) + 1 { sqrt as u64 + 1 }
  else if num == square - (sqrt << 1) + 1 { sqrt as u64 - 1 }
  else { sqrt as u64 }
}

#[cfg(test,)]
mod tests {
  use super::*;
  use test::{Bencher, black_box,};

  #[test]
  fn test_sqrt_u8() {
    //Test all numbers.
    for num in 0..std::u8::MAX {
      //Calculate square root.
      let sqrt = sqrt_u8(num,);
      let num = num as u16;
      //Recalculate square.
      let square = sqrt as u16 * sqrt as u16;

      //Confirm that an inacurate answer is off by <1.
      if square < num {
        let sqrt1 = sqrt as u16 + 1;
        let square =  sqrt1 * sqrt1;

        assert!(square > num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      } else if square > num {
        let sqrt1 = sqrt as u16 - 1;
        let square =  sqrt1 * sqrt1;

        assert!(square < num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      }
    }
  }
  #[test]
  fn test_sqrt_u16() {
    //Test all numbers.
    for num in 0..std::u16::MAX {
      //Calculate square root.
      let sqrt = sqrt_u16(num,);
      let num = num as u32;
      //Recalculate square.
      let square = sqrt as u32 * sqrt as u32;

      //Confirm that an inacurate answer is off by <1.
      if square < num {
        let sqrt1 = sqrt as u32 + 1;
        let square =  sqrt1 * sqrt1;

        assert!(square > num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      } else if square > num {
        let sqrt1 = sqrt as u32 - 1;
        let square =  sqrt1 * sqrt1;

        assert!(square < num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      }
    }
  }
  #[test]
  fn test_sqrt_u32() {
    #[cfg(feature = "test-all-nums",)]
    let numbers = 0..;
    #[cfg(not(feature = "test-all-nums",),)] 
    let numbers = (0..1000000)
      .chain(std::iter::successors(
        Some(1000000u32),
        |&num,| num.checked_add(num / 100,),),
      );

    //Test all numbers.
    for num in numbers {
      //Calculate square root.
      let sqrt = sqrt_u32(num,);
      //Recalculate square.
      let square = sqrt * sqrt;

      //Confirm that an inacurate answer is off by <1.
      if square < num {
        let sqrt1 = sqrt + 1;
        let square =  sqrt1 * sqrt1;

        assert!(square > num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      } else if square > num {
        let sqrt1 = sqrt - 1;
        let square =  sqrt1 * sqrt1;

        assert!(square < num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      }
    }
  }
  #[test]
  fn test_sqrt_u64() {
    #[cfg(feature = "test-all-nums",)]
    let numbers = 0..;
    #[cfg(not(feature = "test-all-nums",),)]
    let numbers = (0..100000)
      .chain(std::iter::successors(
        Some(100000u64),
        |&num,| num.checked_add(num / 100,),),
      );

    //Test all numbers.
    for num in numbers {
      let sqrt = sqrt_u64(num,);
      //Recalculate square.
      let square = sqrt * sqrt;

      //Confirm that an inacurate answer is off by <1.
      if square < num {
        let sqrt1 = sqrt + 1;
        let square =  sqrt1 * sqrt1;

        assert!(square > num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      } else if square > num {
        let sqrt1 = sqrt - 1;
        let square =  sqrt1 * sqrt1;

        assert!(square < num,
          "sqrt failed on {} for {} with {}", num, sqrt1, sqrt,
        );
      }
    }
  }
  
  #[bench]
  fn bench_sqrt_u8(bencher: &mut Bencher,) {
    let numbers = (0..std::u8::MAX).step_by((std::u8::MAX / 100) as usize,);

    bencher.iter(move || for num in numbers.clone() {
      black_box(sqrt_u8(num,),);
    },);
  }
  #[bench]
  fn bench_sqrt_u16(bencher: &mut Bencher,) {
    let numbers = (0..std::u16::MAX).step_by((std::u16::MAX / 100) as usize,);

    bencher.iter(move || for num in numbers.clone() {
      black_box(sqrt_u16(num,),);
    },);
  }
  #[bench]
  fn bench_sqrt_u32(bencher: &mut Bencher,) {
    let numbers = (0..=std::u32::MAX).step_by((std::u32::MAX / 100) as usize,);

    bencher.iter(move || for num in numbers.clone() {
      black_box(sqrt_u32(num,),);
    },);
  }
  #[bench]
  fn bench_sqrt_u64(bencher: &mut Bencher,) {
    let numbers = (0..=std::u64::MAX).step_by((std::u64::MAX / 100) as usize,);

    bencher.iter(move || for num in numbers.clone() {
      black_box(sqrt_u64(num,),); 
    },);
  }
  #[bench]
  fn bench_sqrt_f32(bencher: &mut Bencher,) {
    let numbers = (0..=std::u32::MAX).step_by((std::u32::MAX / 100) as usize,);

    bencher.iter(move || for num in numbers.clone() {
      black_box((num as f32).sqrt(),);
    },);
  }
  #[bench]
  fn bench_sqrt_f64(bencher: &mut Bencher,) {
    let numbers = (0..=std::u64::MAX).step_by((std::u64::MAX / 100) as usize,);

    bencher.iter(move || for num in numbers.clone() {
      black_box((num as f64).sqrt(),); 
    },);
  }
}
