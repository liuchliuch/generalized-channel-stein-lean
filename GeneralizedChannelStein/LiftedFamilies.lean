import GeneralizedChannelStein.OutputPreimage
import GeneralizedChannelStein.AuxiliaryExtensions
import QuantumChannelStein.FaithfulDensity
import QuantumChannelStein.StateTensor

/-! Actual auxiliary-output lifting preserves every free-family axiom. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b e : ℕ}

def liftedFamily (F : AlternativeFamily a b) (e : ℕ) : AlternativeFamily a (b*e) :=
  outputPreimageFamily (AuxiliaryExtensions.discard b e) F

def liftedReplacer (ω : State b) (he : 0<e) : State (b*e) :=
  ω.tensor (FaithfulDensity.maximallyMixed e he)

theorem tensorState_posDef {c : ℕ} (ρ : State b) (σ : State c)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) : (ρ.tensor σ).matrix.PosDef := by
  apply (ρ.tensor σ).positive.posDef_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det,State.tensor_matrix,Matrix.det_reindex_self,Matrix.det_kronecker]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hρ.isUnit).pow _ |>.mul
    (((Matrix.isUnit_iff_isUnit_det _).mp hσ.isUnit).pow _)

theorem discard_tensorState (ρ : State b) (σ : State e) :
    (AuxiliaryExtensions.discard b e).onState (ρ.tensor σ)=ρ := by
  apply State.eq_of_matrix_eq
  change (AuxiliaryExtensions.discard b e).apply (ρ.tensor σ).matrix=ρ.matrix
  rw [AuxiliaryExtensions.discard_apply,State.tensor_matrix]
  ext i j
  simp only [KrausChannel.traceEnvironment,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_symm,Equiv.symm_apply_apply,Matrix.kroneckerMap_apply,← Finset.mul_sum]
  change ρ.matrix i j*σ.matrix.trace=ρ.matrix i j
  rw [σ.trace_one,mul_one]

theorem liftedReplacer_posDef (ω : State b) (hω : ω.matrix.PosDef) (he : 0<e) :
    (liftedReplacer ω he).matrix.PosDef :=
  tensorState_posDef ω _ hω (FaithfulDensity.maximallyMixed_posDef e he)

theorem liftedFamily_admissible (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hmem : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1) (he : 0<e) :
    Admissible (liftedFamily F e) :=
  outputPreimage_admissible _ F hF (liftedReplacer ω he) (liftedReplacer_posDef ω hω he)
    ω (discard_tensorState ω _) hmem

theorem liftedFamily_quantitative (F : AlternativeFamily a b) (τ : State a)
    (hF : QuantitativeAt F τ) (e : ℕ) : QuantitativeAt (liftedFamily F e) τ :=
  outputPreimage_quantitative _ F τ hF

end GeneralizedChannelStein
