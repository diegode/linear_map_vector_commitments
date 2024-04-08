#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
use ark_bls12_381::{Fr as ScalarField, G1Projective as G1, G2Projective as G2};
use ark_ec::Group;
use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Field, One, Zero};
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_poly::polynomial::univariate::DensePolynomial;

use crate::vc::*;

pub struct PublicParameters {
    pub g1_tau_powers: Vec<G1>,
    pub g2_tau_powers: Vec<G2>,
    pub g1_lambdas: Vec<G1>,
    pub g2_lambdas: Vec<G2>,
}

pub struct Commitment {
    pub c: G1,
    pub v: Vec<ScalarField>,
}

pub struct Function {
    pub f: Vec<ScalarField>,
    pub kappa: u32,
    pub nu: u32,
    pub s: usize, // chunk index
}

pub struct Proof {
    pub h: G1,
    pub h_b: G1,
    pub h_b_prefixes: Vec<G1>,
    pub r: G1,
    pub r_hat: G1,
    pub c_b: G1,
    pub c_hat_b: G1,
}

pub struct UnvariateVectorTreeCommitment {
    m: u64,
    tau: ScalarField, // left for debugging purposes
    vanishing_polynomial: DensePolynomial<ScalarField>,
    lagrange_polynomials: Vec<DensePolynomial<ScalarField>>,
    public_parameters: PublicParameters,
}

impl UnvariateVectorTreeCommitment {

    pub fn new(m: u64) -> Self {
        assert_eq!(m & (m - 1), 0, "m has to be a power of 2");
        let roots_of_unity = calculate_roots_of_unity(m);
        let tau = generate_tau();

        let lagrange_polynomials = calculate_lagrange_polynomials(m, &roots_of_unity);
        let g1_lambdas = calculate_g1_lambdas(&lagrange_polynomials, tau);
        let g2_lambdas = calculate_g2_lambdas(&lagrange_polynomials, tau);
        Self {
            m,
            tau,
            vanishing_polynomial: calculate_vanishing_polynomial(&roots_of_unity),
            lagrange_polynomials,
            public_parameters: PublicParameters {
                g1_tau_powers: calculate_g1_tau_powers(tau, 2*m),
                g2_tau_powers: calculate_g2_tau_powers(tau, 2*m),
                g1_lambdas,
                g2_lambdas
            }
        }
    }

    pub fn commit(&self, v: Vec<ScalarField>) -> Commitment {
        assert_eq!(v.len(), self.m as usize);
        let c = self.commit_in_g1(&v);
        Commitment {
            c,
            v,
        }
    }

    pub fn open(&self, c: &Commitment, f: Function, y: ScalarField) -> Proof {
        assert_eq!(self.m, 2u64.pow(f.kappa + f.nu + 1));
        assert_eq!(f.f.len(), 2usize.pow(f.kappa));
        assert!(f.s < 2usize.pow(f.nu));

        let v_b = c.v.iter().cloned()
            .skip(f.s * 2usize.pow(f.kappa))
            .take(2usize.pow(f.kappa))
            .collect();

        //let mut c_b_prefixes: Vec<DensePolynomial<ScalarField>> = vec![DensePolynomial::zero(); (f.nu + 1) as usize];
        let roots_of_unity = self.calculate_roots_of_unity(f.s, f.nu);
        let lagrange_polynomials = calculate_lagrange_polynomials(2u64.pow(f.nu), &roots_of_unity);
        let vanishing_polynomial = calculate_vanishing_polynomial(&roots_of_unity);

        let (h_b, r) = calculate_h_and_r(&v_b, &f.f, &lagrange_polynomials, y, &vanishing_polynomial);
        let h_b_at_tau = self.evaluate_at_g1_tau(&h_b);
        let r_at_tau = self.evaluate_at_g1_tau(&r);
        let r_hat = multiply_by_x_power(&r, (self.m + 2 - 2u64.pow(f.kappa)) as usize);
        let r_hat_at_tau = self.evaluate_at_g1_tau(&r_hat);

        Proof {
            h_b: h_b_at_tau,
            r: r_at_tau,
            r_hat: r_hat_at_tau,
            h: G1::zero(),
            h_b_prefixes: vec![G1::zero(); 2],
            c_b: G1::zero(),
            c_hat_b: G1::zero(),
        }
    }

    pub fn verify_opening(&self, c: &Commitment, b: Vec<ScalarField>, y: ScalarField, pi: Proof) -> bool {
        unimplemented!()
    }

    fn calculate_roots_of_unity(&self, s: usize, j: u32) -> Vec<ScalarField> {
        let r = self.m / 2u64.pow(j + 1);
        let omega = ScalarField::get_root_of_unity(r).unwrap();
        let mut roots_of_unity: Vec<ScalarField> = Vec::with_capacity(r as usize);
        let mut previous = omega.pow([s as u64]);
        for _ in 0..r {
            previous *= omega;
            roots_of_unity.push(previous);
        }
        assert_eq!(previous, ScalarField::one());
        roots_of_unity
    }

    fn commit_in_g1(&self, a: &Vec<ScalarField>) -> G1 {
        let mut c = G1::zero();
        for i in 0..a.len() {
            c += self.public_parameters.g1_lambdas[i] * a[i];
        }
        assert_eq!(c, G1::generator() * inner_product_with_polynomial(&a, &self.lagrange_polynomials).evaluate(&self.tau));
        c
    }

    fn commit_in_g2(&self, a: &Vec<ScalarField>) -> G2 {
        let mut c = G2::zero();
        for i in 0..a.len() {
            c += self.public_parameters.g2_lambdas[i] * a[i];
        }
        assert_eq!(c, G2::generator() * inner_product_with_polynomial(&a, &self.lagrange_polynomials).evaluate(&self.tau));
        c
    }

    fn evaluate_at_g1_tau(&self, p: &DensePolynomial<ScalarField>) -> G1 {
        assert!(p.coeffs.len() <= self.public_parameters.g1_tau_powers.len());
        let mut result = G1::zero();
        for i in 0..p.coeffs.len() {
            result += self.public_parameters.g1_tau_powers[i] * p.coeffs[i];
        }
        assert_eq!(result, G1::generator() * p.evaluate(&self.tau));
        result
    }

    fn evaluate_at_g2_tau(&self, p: &DensePolynomial<ScalarField>) -> G2 {
        assert!(p.coeffs.len() <= self.public_parameters.g2_tau_powers.len());
        let mut result = G2::zero();
        for i in 0..p.coeffs.len() {
            result += self.public_parameters.g2_tau_powers[i] * p.coeffs[i];
        }
        assert_eq!(result, G2::generator() * p.evaluate(&self.tau));
        result
    }
}
