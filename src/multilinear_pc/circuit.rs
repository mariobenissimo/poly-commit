/// circuit to verify poly commitment
use ark_ec::{pairing::{Pairing, self}, CurveGroup};
use digest::crypto_common::Iv;
use crate::multilinear_pc::data_structures::{
    Commitment, Proof, VerifierKey,
};
use ark_std::error::Error;
use ark_ec::ScalarMul;
use ark_ff::PrimeField;
use ark_r1cs_std::{prelude::*, fields::fp::FpVar, groups::bls12::G1PreparedVar};
use ark_relations::{
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_std::ops::Sub;
use ark_ec::VariableBaseMSM;
use ark_std::ops::Mul;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ff::BigInteger;
use ark_std::marker::PhantomData;
use ark_std::borrow::Borrow;
use ark_ec::AffineRepr;
/// data structures used by multilinear extension commitment scheme

#[derive(Clone)]
struct MulGtVerificaion<E, IV>
where
    E: Pairing,
    IV: PairingVar<E>,
{
    vk: VerifierKey<E>,
    commitment: Commitment<E>,
    point: Vec<E::ScalarField>,
    value: E::ScalarField,
    proof: Proof<E>,
    _iv: PhantomData<IV>,
}



impl<E, IV> ConstraintSynthesizer<<E as Pairing>::BaseField> for MulGtVerificaion<E, IV>
where
    E: Pairing,
    IV: PairingVar<E>,
    IV::G1Var: CurveVar<E::G1, E::BaseField>,
    IV::G2Var: CurveVar<E::G2, E::BaseField>,
    IV::GTVar: FieldVar<E::TargetField, E::BaseField>,

    {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<<E as Pairing>::BaseField>,
    ) -> Result<(), SynthesisError> {
        
        // allocate verifierkey field
        let vk_g_var  = IV::G1Var::new_witness(cs.clone(), || Ok(self.vk.g))?;
        let vk_h_var = IV::G2Var::new_witness(cs.clone(), || Ok(self.vk.h))?;
        let mut vk_gmask_var = Vec::new();
        for g_mask in self.vk.g_mask_random.clone().into_iter(){
            let g_mask_var = IV::G1Var::new_witness(cs.clone(), || Ok(g_mask))?;
            vk_gmask_var.push(g_mask_var);
        }
        // allocate commitment
        let com_g1_prod_var = IV::G1Var::new_witness(cs.clone(), || Ok(self.commitment.g_product))?;
        // allocate point
        let mut point_var = Vec::new();
        for p in self.point.clone().into_iter(){
            let scalar_in_fq = &E::BaseField::from_bigint(<E::BaseField as PrimeField>::BigInt::from_bits_le(p.into_bigint().to_bits_le().as_slice())).unwrap();
            let p_var = FpVar::new_witness(cs.clone(), || Ok(scalar_in_fq))?;
            point_var.push(p_var);
        }
        // allocate value
        let scalar_in_fq = &E::BaseField::from_bigint(<E::BaseField as PrimeField>::BigInt::from_bits_le(self.value.into_bigint().to_bits_le().as_slice())).unwrap();
        let value_var = FpVar::new_witness(cs.clone(), || Ok(scalar_in_fq))?;
        // allocate proof
        let mut proofs_var = Vec::new();
        for proof in self.proof.proofs.clone().into_iter(){
            let proof_var = IV::G2Var::new_witness(cs.clone(), || Ok(proof))?;
            proofs_var.push(proof_var);
        }
        // start operation on circuit
        let pair_left_op = com_g1_prod_var - (vk_g_var.scalar_mul_le(value_var.to_bits_le()?.iter())?);
        let left_prepared = IV::prepare_g1(&pair_left_op)?;
        let right_prepared = IV::prepare_g2(&vk_h_var)?;
        let left = IV::pairing(left_prepared, right_prepared)?;
        

        let scalar_size = E::ScalarField::MODULUS_BIT_SIZE as usize;
        let window_size = FixedBase::get_mul_window_size(self.vk.nv);

        let g_table = FixedBase::get_window_table(scalar_size, window_size, self.vk.g.into_group());
        let g_mul: Vec<E::G1> = FixedBase::msm(scalar_size, window_size, &g_table, self.point.as_slice());

        let mut g_mul_var = Vec::new();
        for g_m in g_mul.clone().into_iter(){
            let g_m_var = IV::G1Var::new_witness(cs.clone(), || Ok(g_m))?;
            g_mul_var.push(g_m_var);
        }
        
        let pairing_lefts_var: Vec<_> = (0..self.vk.nv)
            .map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())
            .collect();

        let mut pairing_lefts_prep = Vec::new();
        for var in pairing_lefts_var.clone().into_iter(){
            pairing_lefts_prep.push(IV::prepare_g1(&var).unwrap());
        }

        let mut pairing_right_prep = Vec::new();
        for var in proofs_var.clone().into_iter(){
            pairing_right_prep.push(IV::prepare_g2(&var).unwrap());
        }

        let right_ml = IV::miller_loop(&pairing_lefts_prep,&pairing_right_prep)?;
        let right = IV::final_exponentiation(&right_ml).unwrap();
        left.enforce_equal(&right);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ark_std::UniformRand;
    use crate::multilinear_pc::data_structures::UniversalParams;
    use crate::multilinear_pc::{MultilinearPC, circuit};
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension, SparseMultilinearExtension};
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use ark_std::vec::Vec;
    type E = Bls12_381;
    type Fr = <E as Pairing>::ScalarField;
    use super::*;
    type IV = ark_bls12_381::constraints::PairingVar;

    fn test_polynomial<R: RngCore>(
        uni_params: &UniversalParams<E>,
        poly: &impl MultilinearExtension<Fr>,
        rng: &mut R,
    ) {
        let nv = poly.num_vars();
        assert_ne!(nv, 0);
        let (ck, vk) = MultilinearPC::<E>::trim(&uni_params, nv);
        let point: Vec<_> = (0..nv).map(|_| Fr::rand(rng)).collect();
        let com = MultilinearPC::commit(&ck, poly);
        let proof = MultilinearPC::open(&ck, poly, &point);

        let value = poly.evaluate(&point).unwrap();
        let result = MultilinearPC::check(&vk, &com, &point, value, &proof);
        assert!(result);
        let circuit = MulGtVerificaion{
            vk: vk, 
            commitment: com, 
            point: point, 
            value: value, 
            proof: proof,
            _iv: PhantomData::<IV>,
        };
        // let cs =
        //     ConstraintSystem::<<Bls12<ark_bls12_377::Config> as Pairing>::BaseField>::new_ref();
        // let mut rng = ark_std::test_rng();
        // MulVerificaion::<I, IV>::new(&mut rng)
        //     .generate_constraints(cs.clone())
        //     .unwrap();
        // assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn setup_commit_verify_correct_polynomials() {
        let mut rng = test_rng();

        // normal polynomials
        let uni_params = MultilinearPC::setup(10, &mut rng);

        let poly1 = DenseMultilinearExtension::rand(8, &mut rng);
        test_polynomial(&uni_params, &poly1, &mut rng);

        let poly2 = SparseMultilinearExtension::rand_with_config(9, 1 << 5, &mut rng);
        test_polynomial(&uni_params, &poly2, &mut rng);

        // single-variate polynomials

        let poly3 = DenseMultilinearExtension::rand(1, &mut rng);
        test_polynomial(&uni_params, &poly3, &mut rng);

        let poly4 = SparseMultilinearExtension::rand_with_config(1, 1 << 1, &mut rng);
        test_polynomial(&uni_params, &poly4, &mut rng);
    }
}