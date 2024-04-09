#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

use std::collections::HashMap;
use ark_bls12_381::{Bls12_381, Fr as ScalarField, G1Projective as G1, G2Projective as G2};
use ark_ec::Group;
use ark_ec::pairing::{Pairing, PairingOutput};
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

pub struct TreeNode {
    vector: Vec<ScalarField>,
    roots_of_unity: Vec<ScalarField>,
}

pub struct Commitment {
    pub c: G1,
    pub v: Vec<ScalarField>,
    pub tree: HashMap<Vec<bool>, TreeNode>
}

pub struct Function {
    pub f: Vec<ScalarField>,
    pub kappa: u32,
    pub nu: u32,
    pub s: usize, // chunk index
}

pub struct Proof {
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
    roots_of_unity: Vec<ScalarField>,
    vanishing_polynomial: DensePolynomial<ScalarField>,
    lagrange_polynomials: Vec<DensePolynomial<ScalarField>>,
    public_parameters: PublicParameters,
}

impl UnvariateVectorTreeCommitment {

    pub fn new(m: u64) -> Self {
        assert_eq!(m & (m - 1), 0, "m has to be a power of 2");
        let roots_of_unity = calculate_roots_of_unity(m);
        let tau = generate_tau();

        let lagrange_polynomials = calculate_lagrange_polynomials(&roots_of_unity);
        let vanishing_polynomial = calculate_vanishing_polynomial(&roots_of_unity);
        let g1_lambdas = calculate_g1_lambdas(&lagrange_polynomials, tau);
        let g2_lambdas = calculate_g2_lambdas(&lagrange_polynomials, tau);
        Self {
            m,
            tau,
            roots_of_unity,
            vanishing_polynomial,
            lagrange_polynomials,
            public_parameters: PublicParameters {
                g1_tau_powers: calculate_g1_tau_powers(tau, 2*m),
                g2_tau_powers: calculate_g2_tau_powers(tau, 2*m),
                g1_lambdas,
                g2_lambdas
            }
        }
    }

    pub fn commit(&self, v: Vec<ScalarField>, kappa: u32, nu: u32) -> Commitment {
        assert_eq!(v.len(), self.m as usize);
        assert_eq!(self.m, 2u64.pow(kappa + nu + 1));
        let c = self.commit_in_g1(&v);
        let tree = self.build_vector_tree(&v, kappa, nu);
        Commitment {
            c,
            v,
            tree,
        }
    }

    pub fn open(&self, c: &Commitment, f: &Function, y: ScalarField) -> Proof {
        assert_eq!(self.m, 2u64.pow(f.kappa + f.nu + 1));
        assert_eq!(f.f.len(), 2usize.pow(f.kappa));
        assert!(f.s < 2usize.pow(f.nu));

        let mut h_b_prefixes: Vec<G1> = Vec::with_capacity((f.nu + 1) as usize);
        for j in 0..=f.nu {
            let b_j = number_to_bin_vector(f.s, j);
            let left_child = c.tree.get(&[b_j.clone(), vec![false]].concat()).unwrap();
            let right_child = c.tree.get(&[b_j.clone(), vec![true]].concat()).unwrap();
            let vanishing_polynomial = calculate_vanishing_polynomial(&c.tree.get(&b_j).unwrap().roots_of_unity);
            let omega_sr = -vanishing_polynomial.coeffs[0];
            if j == 0 {
                assert_eq!(omega_sr, ScalarField::one());
            }
            let k_bj = ScalarField::one() / (omega_sr * ScalarField::from(2));
            let h_bj = (self.calculate_g1_commitment(&left_child) - self.calculate_g1_commitment(&right_child)) * k_bj;
            h_b_prefixes.push(h_bj);
        }

        let b = number_to_bin_vector(f.s, f.nu + 1);
        let tree_node = &c.tree.get(&b).unwrap();
        let lagrange_polynomials = calculate_lagrange_polynomials(&tree_node.roots_of_unity);
        let vanishing_polynomial = calculate_vanishing_polynomial(&tree_node.roots_of_unity);

        let (h_b, r) = calculate_h_and_r(&tree_node.vector, &f.f, &lagrange_polynomials, y, &vanishing_polynomial);
        let r_hat = multiply_by_x_power(&r, (self.m + 2 - 2u64.pow(f.kappa)) as usize);
        let c_b = inner_product_with_polynomial(&tree_node.vector, &lagrange_polynomials);
        let c_hat_b = multiply_by_x_power(&c_b, (self.m - 2u64.pow(f.kappa)) as usize);
        Proof {
            h_b: self.evaluate_at_g1_tau(&h_b),
            r: self.evaluate_at_g1_tau(&r),
            r_hat: self.evaluate_at_g1_tau(&r_hat),
            c_b: self.evaluate_at_g1_tau(&c_b),
            c_hat_b: self.evaluate_at_g1_tau(&c_hat_b),
            h_b_prefixes,
        }
    }

    pub fn verify_opening(&self, c: &Commitment, f: &Function, y: ScalarField, pi: Proof) -> bool {
        let cond3_lhs = Bls12_381::pairing(pi.r, self.public_parameters.g2_tau_powers[(self.m + 2 - 2u64.pow(f.kappa)) as usize]);
        let cond3_rhs = Bls12_381::pairing(pi.r_hat, G2::generator());
        assert_eq!(cond3_lhs, cond3_rhs);

        let cond4_lhs = Bls12_381::pairing(pi.c_b, self.public_parameters.g2_tau_powers[(self.m - 2u64.pow(f.kappa)) as usize]);
        let cond4_rhs = Bls12_381::pairing(pi.c_hat_b, G2::generator());
        assert_eq!(cond4_lhs, cond4_rhs);

        let b = number_to_bin_vector(f.s, f.nu + 1);
        let tree_node = &c.tree.get(&b).unwrap();
        let lagrange_polynomials = calculate_lagrange_polynomials(&tree_node.roots_of_unity);
        let c_f = self.evaluate_at_g2_tau(&inner_product_with_polynomial(&f.f, &lagrange_polynomials));

        let vanishing_polynomial = calculate_vanishing_polynomial(&tree_node.roots_of_unity);
        let vanishing_at_tau = self.evaluate_at_g2_tau(&vanishing_polynomial);

        let cond2_lhs = Bls12_381::pairing(pi.c_b, c_f)
            - Bls12_381::pairing(G1::generator() * (y / ScalarField::from(2u128.pow(f.kappa))), G2::generator());
        let cond2_rhs = Bls12_381::pairing(pi.r, self.public_parameters.g2_tau_powers[1]) + Bls12_381::pairing(pi.h_b, vanishing_at_tau);
        assert_eq!(cond2_lhs, cond2_rhs);

        let cond1_lhs = Bls12_381::pairing(c.c - pi.c_b, G2::generator());
        let mut cond1_rhs = PairingOutput::zero();
        for j in 0..=f.nu {
            let b_j = number_to_bin_vector(f.s, j + 1);
            let roots_of_unity = &c.tree.get(&b_j).unwrap().roots_of_unity;
            let vanishing_bj_at_tau: G2 = self.evaluate_at_g2_tau(&calculate_vanishing_polynomial(&roots_of_unity));
            cond1_rhs += Bls12_381::pairing(pi.h_b_prefixes[j as usize], vanishing_bj_at_tau);
        }
        assert_eq!(cond1_lhs, cond1_rhs);

        return true;
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

    fn build_vector_tree(&self, v: &Vec<ScalarField>, kappa: u32, nu: u32) -> HashMap<Vec<bool>, TreeNode> {
        let mut tree: HashMap<Vec<bool>, TreeNode> = HashMap::new();
        tree.insert(vec![], TreeNode {
            vector: v.clone(),
            roots_of_unity: self.roots_of_unity.clone()
        });
        for level in 1..=(nu + 1) {
            for i in 0..2usize.pow(level) {
                let mut b = Vec::with_capacity(level as usize);
                for j in 0..level {
                    b.push(i & (1 << j) != 0);
                }
                let parent_node = tree.get(&b[..(level - 1) as usize]).unwrap();
                let child_vector: Vec<ScalarField> = parent_node.vector.iter().cloned()
                    .skip(if b[0] { 1 } else { 0 })
                    .step_by(2)
                    .collect();
                let child_roots_of_unity: Vec<ScalarField> = parent_node.roots_of_unity.iter().cloned()
                    .skip(if b[0] { 1 } else { 0 })
                    .step_by(2)
                    .collect();
                tree.insert(b, TreeNode { vector: child_vector, roots_of_unity: child_roots_of_unity });
            }
        }
        tree
    }

    fn calculate_g1_commitment(&self, tree_node: &TreeNode) -> G1 {
        let lagrange_polynomials = calculate_lagrange_polynomials(&tree_node.roots_of_unity);
        self.evaluate_at_g1_tau(&inner_product_with_polynomial(&tree_node.vector, &lagrange_polynomials))
    }
}
