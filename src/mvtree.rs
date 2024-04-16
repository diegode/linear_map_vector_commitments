use std::collections::HashMap;

use ark_bls12_381::{Bls12_381, Fr as Field, G1Projective as G1, G2Projective as G2};
use ark_ec::{Group, pairing::Pairing};
use ark_ec::pairing::PairingOutput;
use ark_ff::{Field as OtherField, One, Zero};
use ark_poly::DenseMVPolynomial;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm, Term};
use ark_poly::univariate::DensePolynomial;

use crate::lvc;
use crate::lvc::LinearMapVectorCommitment;
use crate::vc::*;

type Polynomial = SparsePolynomial<Field, SparseTerm>;

pub struct PublicParameters {
    tensored_tau_r: Vec<G1>,
    tau_product_power: Field,
    tensored_lambda_r: Vec<G1>,
    tau_g2: Vec<G2>,
}

pub struct Commitment {
    pub c: G1,
    pub v: Vec<Field>,
    tree: HashMap<Vec<u32>, TreeNode>,
}

pub struct Function {
    pub f: Vec<Field>,
    pub i: u32,
}

pub struct Proof {
    pub internal_proof: lvc::Proof,
    pub c_hat: G1,
    pub h: Vec<G1>,
}

pub struct TreeNode {
    c: G1,
    internal_leaf_commitment: Option<lvc::Commitment>,
}

pub struct MultivariateVectorTreeCommitment {
    k: u32,
    alphabet_size: u32,
    nu: u32,
    internal_lvc: LinearMapVectorCommitment,
    public_parameters: PublicParameters,
    tau: Vec<Field>, // left for debugging purposes
    lambdas: Vec<Vec<Field>>, // g1_lambdas[i] is the vector of alphabet_size, with the evaluation of the lagrange polynomials at tau_i.
    lagrange_polynomials: Vec<DensePolynomial<Field>>,
}

impl MultivariateVectorTreeCommitment {
    pub fn new(k: u32, alphabet_size: u32, nu: u32) -> Self {
        let internal_lvc = LinearMapVectorCommitment::new(k);
        let r = &internal_lvc.public_parameters.g1_lambdas;
        let tau : Vec<Field> = (0..nu).map(|_| generate_tau()).collect();
        let tensored_tau_r = Self::tensor_product_g1(&r, &tau);
        let mut tau_product_power = Field::one();
        for j in 0..nu as usize {
            tau_product_power *= tau[j].pow([(alphabet_size - 1) as u64])
        }
        let alphabet = (0..alphabet_size).map(|a| Field::from(a)).collect();
        let lagrange_polynomials = calculate_lagrange_polynomials(&alphabet);
        let mut lambdas = Vec::with_capacity(nu as usize);
        for j in 0..nu as usize {
            lambdas.push(calculate_lambdas(&lagrange_polynomials, tau[j]));
        }
        let mut tensored_lambda = vec![Field::one()];
        for j in 0..nu as usize {
            tensored_lambda = Self::tensor_product(&tensored_lambda, &lambdas[j]);
        }
        let tensored_lambda_r = Self::tensor_product_g1(&r, &tensored_lambda);
        let tau_g2 = tau.iter().map(|t| G2::generator() * t).collect();
        let public_parameters = PublicParameters {
            tensored_tau_r,
            tau_product_power,
            tensored_lambda_r,
            tau_g2,
        };
        Self {
            k,
            alphabet_size,
            nu,
            internal_lvc,
            public_parameters,
            tau,
            lambdas,
            lagrange_polynomials,
        }
    }

    pub fn commit(&self, v: &Vec<Field>) -> Commitment {
        assert_eq!(v.len(), (self.k * self.alphabet_size.pow(self.nu)) as usize);
        let tree = self.build_vector_tree(v);
        let c = tree.get(&vec![]).unwrap().c;
        Commitment {
            c,
            v: v.clone(),
            tree,
        }
    }

    pub fn open(&self, c: &Commitment, f: &Function, y: Field) -> Proof {
        assert_eq!(f.f.len(), self.k as usize);
        assert!(f.i < self.alphabet_size.pow(self.nu));
        let i_digits = number_to_digits_vector(f.i, self.nu, self.alphabet_size);
        let tree_node = c.tree.get(&i_digits).unwrap();
        let leaf_commitment = tree_node.internal_leaf_commitment.as_ref().unwrap();

        let tau_product_power_times_r = self.internal_lvc.public_parameters.g1_lambdas.clone()
            .iter().map(|l| *l * self.public_parameters.tau_product_power).collect();
        let c_hat = inner_product_g1(&tau_product_power_times_r, &leaf_commitment.a);

        // TODO this is work in progress
        // let mut polynomial = Polynomial::from_coefficients_slice(
        //     (self.nu + self.k) as usize, &vec![(Field::one(), SparseTerm::new(vec![]))]);
        // for i in 0..self.lagrange_polynomials.len() {
        //     let l = &self.lagrange_polynomials[i];
        //     for j in 0..l.coeffs.len() {
        //         let term = SparseTerm::new(vec![(i, j)]);
        //         let term_coeff = l.coeffs[j];
        //         polynomial = Self::multiply_polynomials(&polynomial,
        //                                                 &Polynomial::from_coefficients_slice(1, &vec![(term_coeff, term)]));
        //     }
        // }

        Proof {
            internal_proof: self.internal_lvc.open(leaf_commitment, &f.f, y),
            c_hat,
            h: vec![G1::generator(); self.nu as usize], // TODO change this
        }
    }

    pub fn verify_opening(&self, c: &Commitment, f: &Function, y: Field, pi: &Proof) -> bool {
        assert_eq!(f.f.len(), self.k as usize);
        assert!(f.i < self.alphabet_size.pow(self.nu));
        let i_digits = number_to_digits_vector(f.i, self.nu, self.alphabet_size);
        let tree_node = c.tree.get(&i_digits).unwrap();
        let leaf_commitment = tree_node.internal_leaf_commitment.as_ref().unwrap();

        let cond_leaf = self.internal_lvc.verify_opening(leaf_commitment, &f.f, y, &pi.internal_proof);
        assert!(cond_leaf);

        let cond_low_degree = Bls12_381::pairing(leaf_commitment.c, G2::generator() * self.public_parameters.tau_product_power)
            == Bls12_381::pairing(pi.c_hat, G2::generator());
        assert!(cond_low_degree);

        let root_node = c.tree.get(&vec![]).unwrap();
        let mut cond_path_rhs = PairingOutput::zero();
        for j in 0..self.nu as usize {
            cond_path_rhs += Bls12_381::pairing(pi.h[j], self.public_parameters.tau_g2[j] - (G2::generator() * Field::from(i_digits[j])));
        }
        let cond_path_lhs = Bls12_381::pairing(root_node.c - leaf_commitment.c, G2::generator());
        assert_eq!(cond_path_lhs, cond_path_rhs);

        true
    }

    fn multiply_polynomials(cur: &Polynomial, other: &Polynomial) -> Polynomial {
        if cur.is_zero() || other.is_zero() {
            Polynomial::zero()
        } else {
            let mut result_terms = Vec::new();
            for (cur_coeff, cur_term) in cur.terms.iter() {
                for (other_coeff, other_term) in other.terms.iter() {
                    let mut term: Vec<(usize, usize)> = cur_term.iter().cloned().collect();
                    let other: Vec<(usize, usize)> = other_term.iter().cloned().collect();
                    term.extend(other);
                    result_terms.push((*cur_coeff * *other_coeff, SparseTerm::new(term)));
                }
            }
            Polynomial::from_coefficients_slice(cur.num_vars, result_terms.as_slice())
        }
    }

    fn build_vector_tree(&self, v: &Vec<Field>) -> HashMap<Vec<u32>, TreeNode> {
        let mut tree: HashMap<Vec<u32>, TreeNode> = HashMap::new();
        for j in (0..=self.nu).rev() {
            for s in 0..self.alphabet_size.pow(j) {
                let s_digits = number_to_digits_vector(s, j, self.alphabet_size);
                if j == self.nu {
                    let a = v.iter().cloned()
                        .skip((self.k * s) as usize)
                        .take(self.k as usize)
                        .collect();
                    let c = self.internal_lvc.commit(&a);
                    tree.insert(s_digits, TreeNode {
                        c: c.c,
                        internal_leaf_commitment: Option::from(c),
                    });
                } else {
                    let mut child_commitments: Vec<G1> = Vec::with_capacity(self.alphabet_size as usize);
                    for digit in 0..self.alphabet_size {
                        let child_node = tree.get(&[s_digits.clone(), vec![digit]].concat()).unwrap();
                        child_commitments.push(child_node.c);
                    }
                    let lambda = &self.lambdas[(self.nu - j - 1) as usize];
                    let c = inner_product_g1(&child_commitments, lambda);
                    tree.insert(s_digits, TreeNode {
                        c,
                        internal_leaf_commitment: None,
                    });
                }
            }
        }
        tree
    }

    fn tensor_product(a: &Vec<Field>, b: &Vec<Field>) -> Vec<Field> {
        let mut result = Vec::with_capacity(a.len() * b.len());
        for ai in a {
            for bi in b {
                result.push(ai * bi);
            }
        }
        result
    }

    fn tensor_product_g1(a: &Vec<G1>, b: &Vec<Field>) -> Vec<G1> {
        let mut result = Vec::with_capacity(a.len() * b.len());
        for ai in a {
            for bi in b {
                result.push(*ai * bi);
            }
        }
        result
    }
}