
mod lvc;

#[cfg(test)]
mod tests {
    use crate::lvc::LinearMapVectorCommitment;
    use ark_bls12_381::Fr as Field;
    use ark_ff::One;

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