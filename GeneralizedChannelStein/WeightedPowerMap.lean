import GeneralizedChannelStein.WeightedPowers
import GeneralizedChannelStein.LocalExpansionCompact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The literal weighted partial trace on canonical recursive tensor coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TensorPower ChannelPowerReindex ChannelEntropy MeasureTheory PerfectDiscrimination
open scoped ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.L2Operator
variable {d : ℕ}

def weightedSplitEquiv (d k m : ℕ) : Index (Fin d) (k+m) ≃ Fin (d^k) × Fin (d^m) :=
  (indexAddEquiv (Fin d) k m).symm.trans
    (Equiv.prodCongr (channelIndexEquiv d k) (channelIndexEquiv d m))

def weightedPowerMap (τ : State d) (k m : ℕ) :
    Matrix (Index (Fin d) (k+m)) (Index (Fin d) (k+m)) ℂ →ₗ[ℂ]
      Matrix (Index (Fin d) k) (Index (Fin d) k) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (channelIndexEquiv d k).symm
    (channelIndexEquiv d k).symm).toLinearMap.comp
    ((weightedDiscardMap (d^k) (statePower τ m)).comp
      (Matrix.reindexLinearEquiv ℂ ℂ
        ((weightedSplitEquiv d k m).trans finProdFinEquiv)
        ((weightedSplitEquiv d k m).trans finProdFinEquiv)).toLinearMap)

theorem weightedPowerMap_apply (τ : State d) (k m : ℕ)
    (W : Matrix (Index (Fin d) (k+m)) (Index (Fin d) (k+m)) ℂ) :
    weightedPowerMap τ k m W =
      Matrix.reindex (channelIndexEquiv d k).symm (channelIndexEquiv d k).symm
        (weightedDiscard (statePower τ m)
          (Matrix.reindex (weightedSplitEquiv d k m) (weightedSplitEquiv d k m) W)) := by
  rw [weightedDiscard_eq_map]
  rfl

theorem weightedSplit_tensor (g : Operator d) (k m : ℕ) :
    Matrix.reindex (weightedSplitEquiv d k m) (weightedSplitEquiv d k m)
      (tensorPower g (k+m)) = finiteOperatorPower g k ⊗ₖ finiteOperatorPower g m := by
  rw [← tensorPower_add_reindex g k m]
  ext i j
  simp [weightedSplitEquiv,finiteOperatorPower,Matrix.reindex_apply,Matrix.kronecker_apply]

theorem weightedPowerMap_tensor (τ : State d) (g : Operator d) (k m : ℕ) :
    weightedPowerMap τ k m (tensorPower g (k+m)) =
      ((τ.matrix*g).trace^m) • tensorPower g k := by
  rw [weightedPowerMap_apply,weightedSplit_tensor,weightedDiscard_product_powers]
  ext i j
  simp [finiteOperatorPower,Matrix.reindex_apply]

theorem weightedPowerMap_norm (τ : State d) (k m : ℕ)
    (W : Matrix (Index (Fin d) (k+m)) (Index (Fin d) (k+m)) ℂ) :
    ‖weightedPowerMap τ k m W‖ ≤ ‖W‖ := by
  rw [weightedPowerMap_apply,TensorPower.norm_reindex]
  exact (norm_weightedDiscard_le _ _).trans_eq (TensorPower.norm_reindex _ _ _)

/-- Weighted partial trace commutes with the actual integrable operator representation. -/
theorem weightedPowerMap_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ : State d) (k m : ℕ)
    (g : Ω → Operator d) (f : Ω → ℂ)
    (hfi : Integrable (fun x => f x • tensorPower (g x) (k+m)) μ) :
    weightedPowerMap τ k m (∫ x, f x • tensorPower (g x) (k+m) ∂μ) =
      ∫ x, (f x * (τ.matrix*g x).trace^m) • tensorPower (g x) k ∂μ := by
  let L := (weightedPowerMap τ k m).toContinuousLinearMap
  have hi := L.integral_comp_comm hfi
  change (∫ x, weightedPowerMap τ k m (f x • tensorPower (g x) (k+m)) ∂μ) =
    weightedPowerMap τ k m (∫ x, f x • tensorPower (g x) (k+m) ∂μ) at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_smul,weightedPowerMap_tensor,smul_smul]

/-- The square root in the sandwich is exactly the tensor power of the local square root. -/
theorem sqrt_statePower_matrix (τ : State d) (m : ℕ) :
    CFC.sqrt (statePower τ m).matrix = finiteOperatorPower (CFC.sqrt τ.matrix) m := by
  have hp : (finiteOperatorPower (CFC.sqrt τ.matrix) m).PosSemidef :=
    (PerfectDiscrimination.tensorPower_posSemidef _ (CFC.sqrt_nonneg τ.matrix).posSemidef m).submatrix _
  apply (CFC.sqrt_eq_iff _ _ (statePower τ m).positive.nonneg hp.nonneg).mpr
  rw [← finiteOperatorPower_mul,CFC.sqrt_mul_sqrt_self τ.matrix τ.positive.nonneg]
  rfl

/-- The same physical weighted partial trace in explicit site-function coordinates. -/
def weightedExpectation (τ : State d) (k m : ℕ)
    (W : Matrix (Index (Fin d) (k+m)) (Index (Fin d) (k+m)) ℂ) :
    LocalExpansion.Block (Fin d) k :=
  Matrix.reindex (indexEquiv (Fin d) k) (indexEquiv (Fin d) k) (weightedPowerMap τ k m W)

theorem weightedExpectation_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ : State d) (k m : ℕ)
    (g : Ω → Operator d) (f : Ω → ℂ)
    (hfi : Integrable (fun x => f x • tensorPower (g x) (k+m)) μ) :
    weightedExpectation τ k m (∫ x, f x • tensorPower (g x) (k+m) ∂μ) =
      ∫ x, (f x*(τ.matrix*g x).trace^m) • finTensorPower (g x) k ∂μ := by
  let L := (Matrix.reindexLinearEquiv ℂ ℂ (indexEquiv (Fin d) k)
    (indexEquiv (Fin d) k)).toLinearMap.toContinuousLinearMap
  have hcont := (weightedPowerMap τ k m).toContinuousLinearMap.integrable_comp hfi
  have hsmall : Integrable (fun x => (f x*(τ.matrix*g x).trace^m) • tensorPower (g x) k) μ := by
    change Integrable (fun x => weightedPowerMap τ k m (f x • tensorPower (g x) (k+m))) μ at hcont
    simpa only [map_smul,weightedPowerMap_tensor,smul_smul] using hcont
  unfold weightedExpectation
  rw [weightedPowerMap_integral μ τ k m g f hfi]
  have hi := L.integral_comp_comm hsmall
  change (∫ x, Matrix.reindex (indexEquiv (Fin d) k) (indexEquiv (Fin d) k)
      ((f x*(τ.matrix*g x).trace^m) • tensorPower (g x) k) ∂μ) =
    Matrix.reindex (indexEquiv (Fin d) k) (indexEquiv (Fin d) k)
      (∫ x, (f x*(τ.matrix*g x).trace^m) • tensorPower (g x) k ∂μ) at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rfl

/-- Transport only the equality of the total block length; the physical map is unchanged. -/
def weightedExpectationSplit {n : ℕ} (τ : State d) (k m : ℕ) (hkm : k+m=n)
    (W : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ) : LocalExpansion.Block (Fin d) k :=
  weightedExpectation τ k m (hkm.symm ▸ W)

theorem weightedPowerMap_one (τ : State d) (k m : ℕ) : weightedPowerMap τ k m 1=1 := by
  rw [weightedPowerMap_apply]
  have hi : Matrix.reindex (weightedSplitEquiv d k m) (weightedSplitEquiv d k m)
      (1:Matrix (Index (Fin d) (k+m)) (Index (Fin d) (k+m)) ℂ)=1 :=
    Matrix.reindexLinearEquiv_one ℂ ℂ _
  rw [hi,weightedDiscard_one]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ _

end GeneralizedChannelStein
