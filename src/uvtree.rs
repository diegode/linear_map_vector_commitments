#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]
use ark_bls12_381::{Fr as Field, G1Projective as G1, G2Projective as G2};
use ark_ec::Group;
use ark_ec::pairing::Pairing;
use ark_ff::Zero;
use ark_poly::Polynomial;
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
    pub a: Vec<Field>,
}

pub struct Proof {
    pub r: G1,
    pub h: G1,
    pub r_hat: G1,
}

pub struct UnvariateVectorTreeCommitment {
    m: u64,
    tau: Field, // left for debugging purposes
    vanishing_polynomial: DensePolynomial<Field>,
    lagrange_polynomials: Vec<DensePolynomial<Field>>,
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

    pub fn commit(&self, a: Vec<Field>) -> Commitment {
        assert_eq!(a.len(), self.m as usize);
        let c = self.commit_in_g1(&a);
        Commitment {
            c,
            a,
        }
    }

    pub fn open(&self, c: &Commitment, b: Vec<Field>, y: Field) -> Proof {
        unimplemented!()
    }

    pub fn verify_opening(&self, c: &Commitment, b: Vec<Field>, y: Field, pi: Proof) -> bool {
        unimplemented!()
    }


    fn commit_in_g1(&self, a: &Vec<Field>) -> G1 {
        let mut c = G1::zero();
        for i in 0..a.len() {
            c += self.public_parameters.g1_lambdas[i] * a[i];
        }
        assert_eq!(c, G1::generator() * inner_product(&a, &self.lagrange_polynomials).evaluate(&self.tau));
        c
    }

    fn commit_in_g2(&self, a: &Vec<Field>) -> G2 {
        let mut c = G2::zero();
        for i in 0..a.len() {
            c += self.public_parameters.g2_lambdas[i] * a[i];
        }
        assert_eq!(c, G2::generator() * inner_product(&a, &self.lagrange_polynomials).evaluate(&self.tau));
        c
    }

    fn evaluate_at_g1_tau(&self, p: &DensePolynomial<Field>) -> G1 {
        assert!(p.coeffs.len() <= self.public_parameters.g1_tau_powers.len());
        let mut result = G1::zero();
        for i in 0..p.coeffs.len() {
            result += self.public_parameters.g1_tau_powers[i] * p.coeffs[i];
        }
        assert_eq!(result, G1::generator() * p.evaluate(&self.tau));
        result
    }

    fn evaluate_at_g2_tau(&self, p: &DensePolynomial<Field>) -> G2 {
        assert!(p.coeffs.len() <= self.public_parameters.g2_tau_powers.len());
        let mut result = G2::zero();
        for i in 0..p.coeffs.len() {
            result += self.public_parameters.g2_tau_powers[i] * p.coeffs[i];
        }
        assert_eq!(result, G2::generator() * p.evaluate(&self.tau));
        result
    }
}
