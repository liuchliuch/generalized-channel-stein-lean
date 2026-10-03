import GeneralizedChannelStein.TensorRecovery
import GeneralizedChannelStein.PositiveOverlap
import GeneralizedChannelStein.ProjectorSpectral
import GeneralizedChannelStein.CompletionPrecision

/-! A literal finite local correction and its actual isometry approximation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CorrectedBranch
open QuantumChannelStein Matrix LocalExpansion SiteGrouping
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d n : ℕ}

theorem flatten_mul (X Y : Block (Fin d) n) : flatten (X*Y)=flatten X*flatten Y :=
  (Matrix.reindexLinearEquiv_mul ℂ ℂ _ _ _ X Y).symm

theorem flatten_sub (X Y : Block (Fin d) n) : flatten (X-Y)=flatten X-flatten Y := rfl

theorem flatten_one : flatten (1:Block (Fin d) n)=1 := Matrix.reindexLinearEquiv_one ℂ ℂ _

theorem product_image (J : Matrix (Fin d) (Fin a) ℂ) (n : ℕ) :
    flatten (TensorPower.finTensorPower (J*Jᴴ) n)=powerIsometry J n*(powerIsometry J n)ᴴ := by
  have he : flatten (TensorPower.finTensorPower (J*Jᴴ) n)=
      Matrix.reindex (ChannelPowerReindex.channelIndexEquiv d n) (ChannelPowerReindex.channelIndexEquiv d n)
        (TensorPower.tensorPower (J*Jᴴ) n) := by
    ext i j
    simp [flatten,TensorPower.finTensorPower,encode,Matrix.reindex_apply]
  rw [he,TensorPower.tensorPower_mul,TensorPower.tensorPower_conjTranspose]
  exact (Matrix.reindexLinearEquiv_mul ℂ ℂ (ChannelPowerReindex.channelIndexEquiv d n)
    (ChannelPowerReindex.channelIndexEquiv a n) (ChannelPowerReindex.channelIndexEquiv d n)
    (TensorPower.tensorPower J n) (TensorPower.tensorPower J n)ᴴ).symm.trans (by simp [powerIsometry,Matrix.conjTranspose_reindex])

def operator (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a)
    (G : Expansion (Fin a) n) (H : Expansion (Fin d) n) : Expansion (Fin d) n :=
  (TensorLocalLift.expansion (IsometryLift.recovery J hJ z) G).mul H

theorem operator_cost (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a)
    (G : Expansion (Fin a) n) (H : Expansion (Fin d) n) :
    (operator J hJ z G H).cost=G.cost*H.cost := by
  rw [operator,Expansion.cost_mul,TensorLocalLift.expansion_cost]

theorem operator_size (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a)
    (G : Expansion (Fin a) n) (H : Expansion (Fin d) n) {r s : ℕ}
    (hG : G.HasSize r) (hH : H.HasSize s) : (operator J hJ z G H).HasSize (r+s) :=
  Expansion.hasSize_mul _ _ (TensorLocalLift.expansion_size _ _ hG) hH

theorem operator_value (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a)
    (G : Expansion (Fin a) n) (H : Expansion (Fin d) n) :
    flatten (operator J hJ z G H).value =
      heisenbergMap ((IsometryLift.recovery J hJ z).tensorPower n) (flatten G.value)*flatten H.value := by
  rw [operator,Expansion.value_mul,flatten_mul,TensorLocalLift.expansion_value,TensorLocalLift.flatten_action]

theorem operator_error (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (z : Fin a)
    (K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (hK : ‖K‖≤1)
    (G : Expansion (Fin a) n) (H : Expansion (Fin d) n) (M ξ : ℝ)
    (hM : 0≤M) (hξ : 0≤ξ) (hG : ‖G.value‖≤M)
    (hH : ‖H.value-TensorPower.finTensorPower (J*Jᴴ) n‖≤ξ)
    (herror : ‖flatten G.value*((powerIsometry J n)ᴴ*K)-1‖≤(M+1)*ξ) :
    ‖flatten (operator J hJ z G H).value*K-powerIsometry J n‖≤(2*M+1)*ξ := by
  let T := powerIsometry J n
  let A := heisenbergMap ((IsometryLift.recovery J hJ z).tensorPower n) (flatten G.value)
  have hA : ‖A‖≤M := (norm_heisenbergMap_le _ _).trans ((norm_flatten _).trans_le hG)
  have hT : ‖T‖≤1 := BranchExtraction.norm_isometry_le_one _ (powerIsometry_isometry J hJ n)
  have hAT : A*T=T*flatten G.value := TensorRecovery.recovery_power_intertwines J hJ z n _
  have hH' : ‖flatten H.value-T*Tᴴ‖≤ξ := by
    rw [← product_image,← flatten_sub,norm_flatten]
    exact hH
  rw [operator_value]
  change ‖A*flatten H.value*K-T‖≤_
  have he : A*flatten H.value*K-T = A*(flatten H.value-T*Tᴴ)*K+
      T*(flatten G.value*(Tᴴ*K)-1) := by
    have hh : A*(T*Tᴴ)*K=T*(flatten G.value*(Tᴴ*K)) := by
      calc
        _ = (A*T)*(Tᴴ*K) := by simp [Matrix.mul_assoc]
        _ = _ := by rw [hAT]; simp [Matrix.mul_assoc]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one]
    rw [hh]
    abel
  rw [he]
  calc
    _ ≤ ‖A*(flatten H.value-T*Tᴴ)*K‖+‖T*(flatten G.value*(Tᴴ*K)-1)‖ := norm_add_le _ _
    _ ≤ M*ξ+(M+1)*ξ := by
      apply add_le_add
      · calc
          _ ≤ ‖A‖*‖flatten H.value-T*Tᴴ‖*‖K‖ :=
            (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
          _ ≤ M*ξ*1 := by gcongr
          _ = _ := mul_one _
      · exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hT herror (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    _ = _ := by ring

end GeneralizedChannelStein.CorrectedBranch
