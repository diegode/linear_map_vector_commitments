use ark_bls12_381::{Bls12_381, Fr as Field, G1Projective as G1, G2Projective as G2};
use ark_ec::{Group, pairing::Pairing};
use ark_ff::Zero;
use ark_poly::{DenseUVPolynomial, Polynomial, polynomial::univariate::DensePolynomial, univariate::DenseOrSparsePolynomial};

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

pub struct LinearMapVectorCommitment {
    m: u64,
    tau: Field, // left for debugging purposes
    vanishing_polynomial: DensePolynomial<Field>,
    lagrange_polynomials: Vec<DensePolynomial<Field>>,
    public_parameters: PublicParameters,
}

impl LinearMapVectorCommitment {

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
        assert_eq!(b.len(), self.m as usize);
        let a_poly = inner_product(&c.a, &self.lagrange_polynomials);
        let b_poly = inner_product(&b, &self.lagrange_polynomials);
        let p = multiply_polynomials(&a_poly, &b_poly);
        let p_into: DenseOrSparsePolynomial<Field> = p.clone().into();
        let (h, r) = p_into.divide_with_q_and_r(&self.vanishing_polynomial.clone().into()).unwrap();
        assert_eq!(r.coeffs[0], y / Field::from(self.m));

        let h_at_tau = self.evaluate_at_g1_tau(&h);

        let r_shifted = DensePolynomial::from_coefficients_slice(&r.coeffs[1..]);
        assert!(r_shifted.degree() < (self.m - 1) as usize);
        let r_shifted_at_tau = self.evaluate_at_g1_tau(&r_shifted);

        let mut r_hat_coeffs = vec![Field::zero(), Field::zero()];
        r_hat_coeffs.append(&mut r_shifted.coeffs.clone());
        let r_hat = DensePolynomial::from_coefficients_vec(r_hat_coeffs);
        let r_hat_at_tau = self.evaluate_at_g1_tau(&r_hat);

        Proof {
            r: r_shifted_at_tau,
            h: h_at_tau,
            r_hat: r_hat_at_tau,
        }
    }

    pub fn verify_opening(&self, c: &Commitment, b: Vec<Field>, y: Field, pi: Proof) -> bool {
        assert_eq!(b.len(), self.m as usize);
        let g2_c = self.commit_in_g2(&b);

        let vanishing_at_tau = self.evaluate_at_g2_tau(&self.vanishing_polynomial);

        let cond1 = Bls12_381::pairing(c.c, g2_c) - Bls12_381::pairing(G1::generator() * (y / Field::from(self.m)), G2::generator())
            == Bls12_381::pairing(pi.r, self.public_parameters.g2_tau_powers[1]) + Bls12_381::pairing(pi.h, vanishing_at_tau);
        let cond2 = Bls12_381::pairing(pi.r, self.public_parameters.g2_tau_powers[2]) == Bls12_381::pairing(pi.r_hat, G2::generator());
        return cond1 && cond2;
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
