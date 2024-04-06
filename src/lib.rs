use std::ops::Mul;
use ark_bls12_381::{Bls12_381, Fr as Field, G1Projective as G1, G2Projective as G2};
use ark_ec::{pairing::Pairing, Group};
use ark_ff::{Zero, One, UniformRand, FftField};
use ark_std::rand;
use ark_poly::{polynomial::univariate::DensePolynomial, DenseUVPolynomial, Polynomial, univariate::DenseOrSparsePolynomial};

struct PublicParameters {
    pub g1_tau_powers: Vec<G1>,
    pub g2_tau_powers: Vec<G2>,
    pub g1_lambdas: Vec<G1>,
    pub g2_lambdas: Vec<G2>,
}

struct Commitment {
    pub c: G1,
    pub a: Vec<Field>,
}

struct Proof {
    pub r: G1,
    pub h: G1,
    pub r_hat: G1,
}

struct LinearMapVectorCommitment {
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
        let mut rng = rand::thread_rng();
        let tau = Field::rand(&mut rng);

        let lagrange_polynomials = calculate_lagrange_polynomials(m, &roots_of_unity);
        let mut g1_lambdas: Vec<G1> = Vec::with_capacity(m as usize);
        let mut g2_lambdas: Vec<G2> = Vec::with_capacity(m as usize);
        for i in 0..m as usize {
            let lambda = lagrange_polynomials[i].evaluate(&tau);
            g1_lambdas.push(G1::generator() * lambda);
            g2_lambdas.push(G2::generator() * lambda);
        }
        Self {
            m,
            tau,
            vanishing_polynomial: calculate_vanishing_polynomial(&roots_of_unity),
            lagrange_polynomials,
            public_parameters: PublicParameters {
                g1_tau_powers: calculate_g1_tau_powers(tau, 2*m),
                g2_tau_powers: calculate_g2_tau_powers(tau, 2*m),
                g1_lambdas,
                g2_lambdas,
            }
        }
    }

    pub fn commit(&self, a: Vec<Field>) -> Commitment {
        assert_eq!(a.len(), self.m as usize);
        let c = commit_in_g1(&a, &self.public_parameters.g1_lambdas);
        assert_eq!(c, G1::generator() * inner_product(&a, &self.lagrange_polynomials).evaluate(&self.tau));
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

        let h_at_tau = evaluate_at_g1_tau(&h, &self.public_parameters.g1_tau_powers);
        assert_eq!(h_at_tau, G1::generator() * h.evaluate(&self.tau));

        let r_shifted = DensePolynomial::from_coefficients_slice(&r.coeffs[1..]);
        assert!(r_shifted.degree() < (self.m - 1) as usize);
        let r_shifted_at_tau = evaluate_at_g1_tau(&r_shifted, &self.public_parameters.g1_tau_powers);
        assert_eq!(r_shifted_at_tau, G1::generator() * r_shifted.evaluate(&self.tau));

        let mut r_hat_coeffs = vec![Field::zero(), Field::zero()];
        r_hat_coeffs.append(&mut r_shifted.coeffs.clone());
        let r_hat = DensePolynomial::from_coefficients_vec(r_hat_coeffs);
        let r_hat_at_tau = evaluate_at_g1_tau(&r_hat, &self.public_parameters.g1_tau_powers);
        assert_eq!(r_hat_at_tau, G1::generator() * r_hat.evaluate(&self.tau));

        Proof {
            r: r_shifted_at_tau,
            h: h_at_tau,
            r_hat: r_hat_at_tau,
        }
    }

    pub fn verify_opening(&self, c: &Commitment, b: Vec<Field>, y: Field, pi: Proof) -> bool {
        assert_eq!(b.len(), self.m as usize);
        let g2_c = commit_in_g2(&b, &self.public_parameters.g2_lambdas);
        assert_eq!(g2_c, G2::generator() * inner_product(&b, &self.lagrange_polynomials).evaluate(&self.tau));

        let vanishing_at_tau = evaluate_at_g2_tau(&self.vanishing_polynomial, &self.public_parameters.g2_tau_powers);
        assert_eq!(vanishing_at_tau, G2::generator() * self.vanishing_polynomial.evaluate(&self.tau));

        let cond2 = Bls12_381::pairing(pi.r, self.public_parameters.g2_tau_powers[2]) == Bls12_381::pairing(pi.r_hat, G2::generator());
        assert!(cond2);

        let cond1 = Bls12_381::pairing(c.c, g2_c) - Bls12_381::pairing(G1::generator() * (y / Field::from(self.m)), G2::generator())
            == Bls12_381::pairing(pi.r, self.public_parameters.g2_tau_powers[1]) + Bls12_381::pairing(pi.h, vanishing_at_tau);
        assert!(cond1);

        return cond1 && cond2;
    }
}

fn calculate_roots_of_unity(m: u64) -> Vec<Field> {
    let omega = Field::get_root_of_unity(m).unwrap();
    let mut roots_of_unity: Vec<Field> = Vec::with_capacity(m as usize);
    let mut previous = Field::one();
    for _ in 0..m {
        previous *= omega;
        roots_of_unity.push(previous);
    }
    roots_of_unity
}

fn calculate_g1_tau_powers(tau: Field, m: u64) -> Vec<G1> {
    let mut tau_powers: Vec<G1> = Vec::with_capacity(m as usize);
    let mut previous = G1::generator();
    for _ in 0..m {
        tau_powers.push(previous);
        previous *= tau;
    }
    tau_powers
}

fn calculate_g2_tau_powers(tau: Field, m: u64) -> Vec<G2> {
    let mut tau_powers: Vec<G2> = Vec::with_capacity(m as usize);
    let mut previous = G2::generator();
    for _ in 0..m {
        tau_powers.push(previous);
        previous *= tau;
    }
    tau_powers
}

fn commit_in_g1(a: &Vec<Field>, g1_lambdas: &Vec<G1>) -> G1 {
    let mut c = G1::zero();
    for i in 0..a.len() {
        c += g1_lambdas[i] * a[i];
    }
    c
}

fn commit_in_g2(a: &Vec<Field>, g2_lambdas: &Vec<G2>) -> G2 {
    let mut c = G2::zero();
    for i in 0..a.len() {
        c += g2_lambdas[i] * a[i];
    }
    c
}

fn calculate_lagrange_polynomials(m: u64, roots_of_unity: &Vec<Field>) -> Vec<DensePolynomial<Field>> {
    let mut polynomials: Vec<DensePolynomial<Field>> = Vec::with_capacity(m as usize);
    for j in 0..m as usize {
        let mut p = DensePolynomial::from_coefficients_vec(vec![Field::one()]);
        for i in 0..m as usize {
            if i != j {
                let denominator = roots_of_unity[j] - roots_of_unity[i];
                let q = DensePolynomial::from_coefficients_vec(vec![-roots_of_unity[i]/denominator, Field::one()/denominator]);
                p = multiply_polynomials(&p, &q);
            }
        }
        polynomials.push(p);
    }
    polynomials
}

fn inner_product(a: &Vec<Field>, polynomials: &Vec<DensePolynomial<Field>>) -> DensePolynomial<Field> {
    assert_eq!(a.len(), polynomials.len());
    let mut q = DensePolynomial::zero();
    for i in 0..a.len() {
        q = q + polynomials[i].mul(a[i]);
    }
    q
}

fn calculate_vanishing_polynomial(roots_of_unity: &Vec<Field>) -> DensePolynomial<Field> {
    let mut p = DensePolynomial::from_coefficients_vec(vec![Field::one()]);
    for i in 0..roots_of_unity.len() {
        p = multiply_polynomials(&p, &DensePolynomial::from_coefficients_vec(vec![-roots_of_unity[i], Field::one()]));
    }
    p
}

fn multiply_polynomials(p: &DensePolynomial<Field>, q: &DensePolynomial<Field>) -> DensePolynomial<Field> {
    let mut coeffs: Vec<Field> = vec![Field::zero(); p.coeffs.len() + q.coeffs.len() - 1];
    for i in 0..p.coeffs.len() {
        for j in 0..q.coeffs.len() {
            coeffs[i+j] += p.coeffs[i] * q.coeffs[j];
        }
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

fn evaluate_at_g1_tau(p: &DensePolynomial<Field>, g1_tau_powers: &Vec<G1>) -> G1 {
    assert!(p.coeffs.len() <= g1_tau_powers.len());
    let mut result = G1::zero();
    for i in 0..p.coeffs.len() {
        result += g1_tau_powers[i] * p.coeffs[i];
    }
    result
}

fn evaluate_at_g2_tau(p: &DensePolynomial<Field>, g2_tau_powers: &Vec<G2>) -> G2 {
    assert!(p.coeffs.len() <= g2_tau_powers.len());
    let mut result = G2::zero();
    for i in 0..p.coeffs.len() {
        result += g2_tau_powers[i] * p.coeffs[i];
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example1() {
        let lvc = LinearMapVectorCommitment::new(8);
        let c = lvc.commit(vec![
            Field::from(1), Field::from(2), Field::from(3), Field::from(4),
            Field::from(5), Field::from(6), Field::from(7), Field::from(8)]);
        let pi = lvc.open(&c, vec![Field::one(); 8], Field::from(36));
        assert!(lvc.verify_opening(&c, vec![Field::one(); 8], Field::from(36), pi));
    }
}