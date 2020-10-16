use ark_ff::PrimeField;
use core::marker::Sized;
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_r1cs_std::prelude::*;

use crate::data_structures::LabeledCommitment;
use crate::{BTreeMap, BTreeSet, LCTerm, LinearCombination, String, Vec};
use crate::{BatchLCProof, PolynomialCommitment};
use nonnative::NonNativeFieldVar;
use ark_r1cs_std::fields::fp::FpVar;
use std::borrow::Borrow;

/// A generic gadget for the prepared* structures
pub trait PrepareVar<UNPREPARED, ConstraintF: PrimeField>: Sized {
    /// prepare from an unprepared element
    fn prepare(unprepared: &UNPREPARED) -> Result<Self, SynthesisError>;

    /// prepare for a smaller field
    fn prepare_small(_unprepared: &UNPREPARED) -> Result<Self, SynthesisError> {
        unimplemented!();
    }
}

/// An allocated version of `LinearCombination`.
pub struct LinearCombinationVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// The label.
    pub label: String,
    /// The linear combination of `(coeff, poly_label)` pairs.
    pub terms: Vec<(
        Option<NonNativeFieldVar<TargetField, BaseField>>,
        LCTerm,
        bool,
    )>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Clone
    for LinearCombinationVar<TargetField, BaseField>
{
    fn clone(&self) -> Self {
        LinearCombinationVar {
            label: self.label.clone(),
            terms: self.terms.clone(),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField>
    AllocVar<LinearCombination<TargetField>, BaseField>
    for LinearCombinationVar<TargetField, BaseField>
{
    fn new_variable<T>(
        cs: impl Into<Namespace<BaseField>>,
        val: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<LinearCombination<TargetField>>,
    {
        let LinearCombination { label, terms } = val()?.borrow().clone();

        let ns = cs.into();
        let cs = ns.cs();

        let new_terms: Vec<(
            Option<NonNativeFieldVar<TargetField, BaseField>>,
            LCTerm,
            bool,
        )> = terms
            .iter()
            .map(|term| {
                let (f, lc_term) = term;

                let fg =
                    NonNativeFieldVar::new_variable(ark_relations::ns!(cs, "term"), || Ok(f), mode)
                        .unwrap();

                (Some(fg), lc_term.clone(), false)
            })
            .collect();

        Ok(Self {
            label: label.clone(),
            terms: new_terms,
        })
    }
}

/// Describes the interface for a gadget for a `PolynomialCommitment`
/// verifier.
pub trait PCCheckVar<PCF: PrimeField, PC: PolynomialCommitment<PCF>, ConstraintF: PrimeField>:
    Clone
{
    /// An allocated version of `PC::VerifierKey`.
    type VerifierKeyVar: AllocVar<PC::VerifierKey, ConstraintF> + Clone + ToBytesGadget<ConstraintF>;
    /// An allocated version of `PC::PreparedVerifierKey`.
    type PreparedVerifierKeyVar: AllocVar<PC::PreparedVerifierKey, ConstraintF>
        + Clone
        + PrepareVar<Self::VerifierKeyVar, ConstraintF>;
    /// An allocated version of `PC::Commitment`.
    type CommitmentVar: AllocVar<PC::Commitment, ConstraintF> + Clone + ToBytesGadget<ConstraintF>;
    /// An allocated version of `PC::PreparedCommitment`.
    type PreparedCommitmentVar: AllocVar<PC::PreparedCommitment, ConstraintF>
        + PrepareVar<Self::CommitmentVar, ConstraintF>
        + Clone;
    /// An allocated version of `LabeledCommitment<PC::Commitment>`.
    type LabeledCommitmentVar: AllocVar<LabeledCommitment<PC::Commitment>, ConstraintF> + Clone;
    /// A prepared, allocated version of `LabeledCommitment<PC::Commitment>`.
    type PreparedLabeledCommitmentVar: Clone;
    /// An allocated version of `PC::Proof`.
    type ProofVar: AllocVar<PC::Proof, ConstraintF> + Clone;

    /// An allocated version of `PC::BatchLCProof`.
    type BatchLCProofVar: AllocVar<BatchLCProof<PCF, PC>, ConstraintF> + Clone;

    /// Add to `ConstraintSystemRef<ConstraintF>` new constraints that check that `proof_i` is a valid evaluation
    /// proof at `point_i` for the polynomial in `commitment_i`.
    fn batch_check_evaluations(
        cs: ConstraintSystemRef<ConstraintF>,
        verification_key: &Self::VerifierKeyVar,
        commitments: &Vec<Self::LabeledCommitmentVar>,
        query_set: &QuerySetVar<PCF, ConstraintF>,
        evaluations: &EvaluationsVar<PCF, ConstraintF>,
        proofs: &Vec<Self::ProofVar>,
        opening_challenges: &Vec<NonNativeFieldVar<PCF, ConstraintF>>,
        opening_challenges_bits: &Vec<Vec<Boolean<ConstraintF>>>,
        batching_rands: &Vec<NonNativeFieldVar<PCF, ConstraintF>>,
        batching_rands_bits: &Vec<Vec<Boolean<ConstraintF>>>,
    ) -> Result<Boolean<ConstraintF>, SynthesisError>;

    /// Add to `ConstraintSystemRef<ConstraintF>` new constraints that conditionally check that `proof` is a valid evaluation
    /// proof at the points in `query_set` for the combinations `linear_combinations`.
    fn prepared_check_combinations(
        cs: ConstraintSystemRef<ConstraintF>,
        prepared_verification_key: &Self::PreparedVerifierKeyVar,
        linear_combinations: &Vec<LinearCombinationVar<PCF, ConstraintF>>,
        prepared_commitments: &Vec<Self::PreparedLabeledCommitmentVar>,
        query_set: &QuerySetVar<PCF, ConstraintF>,
        evaluations: &EvaluationsVar<PCF, ConstraintF>,
        proof: &Self::BatchLCProofVar,
        opening_challenges: &Vec<NonNativeFieldVar<PCF, ConstraintF>>,
        opening_challenges_bits: &Vec<Vec<Boolean<ConstraintF>>>,
        batching_rands: &Vec<NonNativeFieldVar<PCF, ConstraintF>>,
        batching_rands_bits: &Vec<Vec<Boolean<ConstraintF>>>,
    ) -> Result<Boolean<ConstraintF>, SynthesisError>;

    /// Create the labeled commitment gadget from the commitment gadget
    fn create_labeled_commitment_gadget(
        label: String,
        commitment: Self::CommitmentVar,
        degree_bound: Option<FpVar<ConstraintF>>,
    ) -> Self::LabeledCommitmentVar;

    /// Create the prepared labeled commitment gadget from the commitment gadget
    fn create_prepared_labeled_commitment_gadget(
        label: String,
        commitment: Self::PreparedCommitmentVar,
        degree_bound: Option<FpVar<ConstraintF>>,
    ) -> Self::PreparedLabeledCommitmentVar;
}

/// An allocated version of `QuerySet`.
pub struct QuerySetVar<TargetField: PrimeField, BaseField: PrimeField>(
    pub BTreeSet<(String, (String, NonNativeFieldVar<TargetField, BaseField>))>,
);

/// An allocated version of `Evaluations`.
#[derive(Clone)]
pub struct EvaluationsVar<TargetField: PrimeField, BaseField: PrimeField>(
    pub  BTreeMap<
        (String, NonNativeFieldVar<TargetField, BaseField>),
        NonNativeFieldVar<TargetField, BaseField>,
    >,
);

impl<TargetField: PrimeField, BaseField: PrimeField> EvaluationsVar<TargetField, BaseField> {
    /// find the evaluation result
    pub fn get_lc_eval(
        &self,
        lc_string: &String,
        point: &NonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        let key = (lc_string.clone(), point.clone());
        Ok(self.0.get(&key).map(|v| (*v).clone()).unwrap())
    }
}