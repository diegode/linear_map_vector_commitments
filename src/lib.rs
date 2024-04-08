
mod lvc;
mod uvtree;
mod vc;

#[cfg(test)]
mod tests {
    use crate::lvc::*;
    use crate::uvtree::*;
    use ark_bls12_381::Fr as Field;
    use ark_ff::One;

    #[test]
    fn test_lvc() {
        let lvc = LinearMapVectorCommitment::new(8);
        let c = lvc.commit(vec![
            Field::from(1), Field::from(2), Field::from(3), Field::from(4),
            Field::from(5), Field::from(6), Field::from(7), Field::from(8)]);
        let pi = lvc.open(&c, vec![Field::one(); 8], Field::from(36));
        assert!(lvc.verify_opening(&c, vec![Field::one(); 8], Field::from(36), pi));
    }

    #[test]
    fn test_uvtree() {
        let uvtree = UnvariateVectorTreeCommitment::new(8);
        let c = uvtree.commit(vec![
            Field::from(1), Field::from(2), Field::from(3), Field::from(4),
            Field::from(5), Field::from(6), Field::from(7), Field::from(8)]);
        let f = Function {
            f: vec![Field::one(), Field::one()],
            kappa: 1,
            nu: 1,
            s: 0
        };
        let pi = uvtree.open(&c, f, Field::from(3));
        assert!(uvtree.verify_opening(&c, vec![Field::one(); 8], Field::from(3), pi));
    }
}