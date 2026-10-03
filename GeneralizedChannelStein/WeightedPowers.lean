import GeneralizedChannelStein.WeightedDiscarding
import GeneralizedChannelStein.BranchExtraction

/-! # Weighted conditional expectation: order and tensor-power damping -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex TensorPower PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b d : ℕ}

theorem heisenbergMap_conjTranspose (Φ : KrausChannel a b) (X : Operator b) :
    heisenbergMap Φ Xᴴ = (heisenbergMap Φ X)ᴴ := by
  simp only [heisenbergMap_apply,Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

theorem heisenbergMap_real_smul (Φ : KrausChannel a b) (c : ℝ) (X : Operator b) :
    heisenbergMap Φ (c • X) = c • heisenbergMap Φ X := by
  change heisenbergMap Φ ((c:ℂ) • X) = (c:ℂ) • heisenbergMap Φ X
  exact map_smul _ _ _

theorem heisenbergMap_realPart (Φ : KrausChannel a b) (X : Operator b) :
    heisenbergMap Φ (BranchExtraction.realPart X) = BranchExtraction.realPart (heisenbergMap Φ X) := by
  rw [BranchExtraction.realPart,heisenbergMap_real_smul,map_add,heisenbergMap_conjTranspose]
  rfl

/-- A positive real-part lower bound survives the actual unital CP expectation. -/
theorem heisenbergMap_realPart_lower (Φ : KrausChannel a b) (X : Operator b) (c : ℝ)
    (hX : (BranchExtraction.realPart X-c • (1:Operator b)).PosSemidef) :
    (BranchExtraction.realPart (heisenbergMap Φ X)-c • (1:Operator a)).PosSemidef := by
  have h := MatrixMap.apply_positive (heisenbergMap Φ) (heisenbergMap_cp Φ) hX
  rwa [map_sub,heisenbergMap_realPart,heisenbergMap_real_smul,heisenbergMap_one] at h

/-- The actual tensor power on the canonical finite coordinate space. -/
def finiteOperatorPower (X : Operator d) (n : ℕ) : Operator (d^n) :=
  Matrix.reindex (channelIndexEquiv d n) (channelIndexEquiv d n) (TensorPower.tensorPower X n)

theorem finiteOperatorPower_mul (X Y : Operator d) (n : ℕ) :
    finiteOperatorPower (X*Y) n = finiteOperatorPower X n*finiteOperatorPower Y n := by
  rw [finiteOperatorPower,TensorPower.tensorPower_mul]
  exact (Matrix.reindexLinearEquiv_mul ℂ ℂ _ _ _ _ _).symm

theorem finiteOperatorPower_trace (X : Operator d) (n : ℕ) :
    (finiteOperatorPower X n).trace = X.trace^n := by
  rw [finiteOperatorPower,ChannelEntropy.trace_reindex_equiv,PerfectDiscrimination.trace_tensorPower]

/-- The density tensor power already used by the channel semantics has these same coordinates. -/
theorem statePower_matrix_eq_finiteOperatorPower (τ : State d) (n : ℕ) :
    (statePower τ n).matrix = finiteOperatorPower τ.matrix n := rfl

/-- Weighted discarding of m product factors contributes exactly (Tr τg)^m. -/
theorem weightedDiscard_product_powers (τ : State d) (g : Operator d) (k m : ℕ) :
    weightedDiscard (statePower τ m) (finiteOperatorPower g k ⊗ₖ finiteOperatorPower g m) =
      ((τ.matrix*g).trace^m) • finiteOperatorPower g k := by
  rw [weightedDiscard_tensor,statePower_matrix_eq_finiteOperatorPower,← finiteOperatorPower_mul,
    finiteOperatorPower_trace]

end GeneralizedChannelStein
