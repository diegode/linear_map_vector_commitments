
mod lvc;
mod uvtree;
mod vc;
mod mvtree;

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fr as Field;
    use ark_ff::One;
    use ark_poly::Polynomial;
    use crate::lvc::LinearMapVectorCommitment;
    use crate::{mvtree, uvtree};
    use crate::mvtree::MultivariateVectorTreeCommitment;
    use crate::uvtree::UnvariateVectorTreeCommitment;
    use crate::vc::{calculate_interpolation_polynomial, calculate_lagrange_polynomials, number_to_bin_vector};

    #[test]
    fn test_lvc() {
        let lvc = LinearMapVectorCommitment::new(8);
        let c = lvc.commit(&vec![
            Field::from(1), Field::from(2), Field::from(3), Field::from(4),
            Field::from(5), Field::from(6), Field::from(7), Field::from(8)]);
        let pi = lvc.open(&c, &vec![Field::one(); 8], Field::from(36));
        assert!(lvc.verify_opening(&c, &vec![Field::one(); 8], Field::from(36), &pi));
    }

    #[test]
    fn test_mvtree() {
        let mvtree = MultivariateVectorTreeCommitment::new(2, 2, 2);
        let c = mvtree.commit(&vec![
            Field::from(1), Field::from(2), Field::from(3), Field::from(4),
            Field::from(5), Field::from(6), Field::from(7), Field::from(8)]);
        let f = mvtree::Function {
            f: vec![Field::one(), Field::one()],
            i: 0,
        };
        let pi = mvtree.open(&c, &f, Field::from(3));
        assert!(mvtree.verify_opening(&c, &f, Field::from(3), &pi));
    }

    #[test]
    fn test_uvtree() {
        let uvtree = UnvariateVectorTreeCommitment::new(8);
        let c = uvtree.commit(vec![
            Field::from(1), Field::from(2), Field::from(3), Field::from(4),
            Field::from(5), Field::from(6), Field::from(7), Field::from(8)],
            1, 1);
        let f = uvtree::Function {
            f: vec![Field::one(), Field::one()],
            kappa: 1,
            nu: 1,
            s: 0
        };
        let pi = uvtree.open(&c, &f, Field::from(6));
        assert!(uvtree.verify_opening(&c, &f, Field::from(6), &pi));
    }

    #[test]
    fn test_number_to_bin_vector() {
        let n = 4;
        let v = number_to_bin_vector(n, 3);
        assert_eq!(v, vec![false, false, true]);
    }

    #[test]
    fn test_calculate_interpolation_polynomial() {
        let v = vec![Field::from(1), Field::from(2), Field::from(3), Field::from(4)];
        let lagrange_polynomials = calculate_lagrange_polynomials(&vec![Field::from(0), Field::from(1)]);
        let p = calculate_interpolation_polynomial(&v, &lagrange_polynomials, 2, 2, 1);
        assert_eq!(p.evaluate(&vec![Field::from(0), Field::from(0)]), Field::from(1));
        assert_eq!(p.evaluate(&vec![Field::from(1), Field::from(0)]), Field::from(2));
        assert_eq!(p.evaluate(&vec![Field::from(0), Field::from(1)]), Field::from(3));
        assert_eq!(p.evaluate(&vec![Field::from(1), Field::from(1)]), Field::from(4));
    }
}