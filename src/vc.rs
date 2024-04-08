use std::ops::Mul;

use ark_bls12_381::{Fr as Field, G1Projective as G1, G2Projective as G2};
use ark_ec::Group;
use ark_ff::{FftField, One, Zero};
use ark_poly::{DenseUVPolynomial, Polynomial, polynomial::univariate::DensePolynomial};
use ark_poly::univariate::DenseOrSparsePolynomial;
use ark_std::UniformRand;

pub fn generate_tau() -> Field {
    let mut rng = rand::thread_rng();
    Field::rand(&mut rng)
}

pub fn calculate_roots_of_unity(m: u64) -> Vec<Field> {
    let omega = Field::get_root_of_unity(m).unwrap();
    let mut roots_of_unity: Vec<Field> = Vec::with_capacity(m as usize);
    let mut previous = Field::one();
    for _ in 0..m {
        previous *= omega;
        roots_of_unity.push(previous);
    }
    assert_eq!(previous, Field::one());
    roots_of_unity
}

pub fn calculate_g1_tau_powers(tau: Field, m: u64) -> Vec<G1> {
    let mut tau_powers: Vec<G1> = Vec::with_capacity(m as usize);
    let mut previous = G1::generator();
    for _ in 0..m {
        tau_powers.push(previous);
        previous *= tau;
    }
    tau_powers
}

pub fn calculate_g2_tau_powers(tau: Field, m: u64) -> Vec<G2> {
    let mut tau_powers: Vec<G2> = Vec::with_capacity(m as usize);
    let mut previous = G2::generator();
    for _ in 0..m {
        tau_powers.push(previous);
        previous *= tau;
    }
    tau_powers
}

pub fn calculate_lagrange_polynomials(m: u64, roots_of_unity: &Vec<Field>) -> Vec<DensePolynomial<Field>> {
    assert_eq!(roots_of_unity.len(), m as usize);
    let mut polynomials: Vec<DensePolynomial<Field>> = Vec::with_capacity(m as usize);
    for j in 0..m as usize {
        let mut p = DensePolynomial::from_coefficients_vec(vec![Field::one()]);
        for i in 0..m as usize {
            if i != j {
                let denominator = roots_of_unity[j] - roots_of_unity[i];
                assert_ne!(denominator, Field::zero());
                let q = DensePolynomial::from_coefficients_vec(vec![-roots_of_unity[i]/denominator, Field::one()/denominator]);
                p = multiply_polynomials(&p, &q);
            }
        }
        polynomials.push(p);
    }
    polynomials
}

pub fn calculate_g1_lambdas(lagrange_polynomials: &Vec<DensePolynomial<Field>>, tau: Field) -> Vec<G1> {
    let mut lambdas: Vec<G1> = Vec::with_capacity(lagrange_polynomials.len());
    for lagrange_polynomial in lagrange_polynomials {
        let lambda = lagrange_polynomial.evaluate(&tau);
        lambdas.push(G1::generator() * lambda);
    }
    lambdas
}

pub fn calculate_g2_lambdas(lagrange_polynomials: &Vec<DensePolynomial<Field>>, tau: Field) -> Vec<G2> {
    let mut lambdas: Vec<G2> = Vec::with_capacity(lagrange_polynomials.len());
    for lagrange_polynomial in lagrange_polynomials {
        let lambda = lagrange_polynomial.evaluate(&tau);
        lambdas.push(G2::generator() * lambda);
    }
    lambdas
}

pub fn inner_product_with_polynomial(a: &Vec<Field>, polynomials: &Vec<DensePolynomial<Field>>) -> DensePolynomial<Field> {
    assert_eq!(a.len(), polynomials.len());
    let mut q = DensePolynomial::zero();
    for i in 0..a.len() {
        q = q + polynomials[i].mul(a[i]);
    }
    q
}

pub fn inner_product(a: &Vec<Field>, b: &Vec<Field>) -> Field {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b.iter()).map(|(x, y)| x * y).sum()
}

pub fn calculate_vanishing_polynomial(roots_of_unity: &Vec<Field>) -> DensePolynomial<Field> {
    let mut p = DensePolynomial::from_coefficients_vec(vec![Field::one()]);
    for i in 0..roots_of_unity.len() {
        p = multiply_polynomials(&p, &DensePolynomial::from_coefficients_vec(vec![-roots_of_unity[i], Field::one()]));
    }
    p
}

pub fn multiply_polynomials(p: &DensePolynomial<Field>, q: &DensePolynomial<Field>) -> DensePolynomial<Field> {
    let mut coeffs: Vec<Field> = vec![Field::zero(); p.coeffs.len() + q.coeffs.len() - 1];
    for i in 0..p.coeffs.len() {
        for j in 0..q.coeffs.len() {
            coeffs[i+j] += p.coeffs[i] * q.coeffs[j];
        }
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

pub fn calculate_h_and_r(a: &Vec<Field>, b: &Vec<Field>, lagrange_polynomials: &Vec<DensePolynomial<Field>>, y: Field,
                         vanishing_polynomial: &DensePolynomial<Field>) -> (DensePolynomial<Field>, DensePolynomial<Field>) {
    assert_eq!(y, inner_product(&a, &b));
    let a_poly = inner_product_with_polynomial(&a, &lagrange_polynomials);
    let b_poly = inner_product_with_polynomial(&b, &lagrange_polynomials);
    let p = multiply_polynomials(&a_poly, &b_poly);
    let p_into: DenseOrSparsePolynomial<Field> = p.clone().into();
    let (h, r) = p_into.divide_with_q_and_r(&vanishing_polynomial.clone().into()).unwrap();
    assert_eq!(r.coeffs[0], y / Field::from(b.len() as u64));

    let r_shifted = DensePolynomial::from_coefficients_slice(&r.coeffs[1..]);
    assert!(r_shifted.degree() < b.len() - 1);

    return (h, r_shifted);
}

pub fn multiply_by_x_power(p: &DensePolynomial<Field>, power: usize) -> DensePolynomial<Field> {
    let mut coeffs = vec![Field::zero(); power];
    coeffs.append(&mut p.coeffs.clone());
    DensePolynomial::from_coefficients_vec(coeffs)
}