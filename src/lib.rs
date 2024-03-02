//! `finitelib` contains algorithms to work with finite fields.

#![feature(test)]
#![feature(bigint_helper_methods)]

extern crate test;

pub mod utils;
pub mod group;
pub mod field;
pub mod ring;
pub mod bigi;
pub mod polynomial;
pub mod common;
pub mod gf;
