import GeneralizedChannelStein.PostprocessingBounds
import GeneralizedChannelStein.BranchExtraction

/-! # Generic background identities for the actual full diamond norm

These extend the special cases used by the numbered results to arbitrary
CP maps, arbitrary rectangular single-Kraus maps, and arbitrary map
precomposition by a genuine CPTP channel.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.GeneralDiamondBounds
open QuantumChannelStein Matrix ChannelEntropy DiamondNorm TraceNorm TestingSDP
  TraceDefectCompletion BranchExtraction PostprocessingBounds
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c : ℕ}

/-- For CP maps the concrete trace-dual matrix is positive and therefore
is literally the Hilbert--Schmidt adjoint applied to identity. -/
theorem adjointIdentity_hilbertSchmidt_pairing (Φ : MatrixMap a b)
    (hΦ : MatrixMap.CompletelyPositive Φ) (X : Operator a) :
    ((adjointIdentity Φ)ᴴ*X).trace=(Φ X).trace := by
  rw [(adjointIdentity_positive Φ hΦ).isHermitian.eq,adjointIdentity_pairing]

/-- The trace-dual pairing is preserved at every actual finite amplification. -/
theorem trace_amplify_pairing (Φ : MatrixMap a b) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    (MatrixMap.amplify Φ r X).trace =
      (((1:Operator r) ⊗ₖ adjointIdentity Φ)*X).trace := by
  have hs : (MatrixMap.amplify Φ r X).trace =
      ∑ i : Fin r, (Φ (fun u v => X (i,u) (i,v))).trace := by
    simp only [Matrix.trace,Matrix.diag,MatrixMap.amplify,Fintype.sum_prod_type]
  rw [hs]
  simp_rw [← adjointIdentity_pairing]
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply,Matrix.one_apply,ite_mul,Finset.sum_ite_irrel]

/-- The CP upper bound uses genuine HP stabilization and the actual trace pairing. -/
theorem diamondNorm_cp_le (Φ : MatrixMap a b) (hΦ : MatrixMap.CompletelyPositive Φ) :
    diamondNorm Φ ≤ ENNReal.ofReal ‖adjointIdentity Φ‖ := by
  rw [diamondNorm_eq_pureDiamondNorm Φ (cp_hermiticityPreserving Φ hΦ)]
  apply iSup_le
  intro ψ
  apply ENNReal.ofReal_le_ofReal
  rw [TraceNorm.traceNorm_of_posSemidef _ (hΦ a _ (pureMatrix_positive ψ.val)),trace_amplify_pairing]
  have ht : TraceNorm.traceNorm (pureMatrix ψ.val)=1 := by
    rw [TraceNorm.traceNorm_of_posSemidef _ (pureMatrix_positive ψ.val),
      trace_pureMatrix_of_norm_one ψ.val ψ.property]
    rfl
  calc
    _ ≤ ‖((((1:Operator a) ⊗ₖ adjointIdentity Φ)*pureMatrix ψ.val).trace)‖ := Complex.re_le_norm _
    _ ≤ ‖(1:Operator a) ⊗ₖ adjointIdentity Φ‖*TraceNorm.traceNorm (pureMatrix ψ.val) :=
      TraceNorm.norm_trace_mul_le _ _
    _ ≤ ‖adjointIdentity Φ‖ := by rw [ht,mul_one]; exact TensorNorm.one_kronecker_opNorm_le _

/-- Actual state expectations recover the positive adjoint norm, including zero input dimension. -/
theorem adjoint_norm_le_diamondNorm (Φ : MatrixMap a b) (hΦ : MatrixMap.CompletelyPositive Φ) :
    ENNReal.ofReal ‖adjointIdentity Φ‖ ≤ diamondNorm Φ := by
  by_cases ha : a=0
  · subst a
    have hz : adjointIdentity Φ=0 := Subsingleton.elim _ _
    rw [hz,norm_zero,ENNReal.ofReal_zero]
    exact zero_le _
  by_cases htop : diamondNorm Φ=⊤
  · rw [htop]; exact le_top
  have hn : ‖adjointIdentity Φ‖ ≤ (diamondNorm Φ).toReal := by
    apply norm_le_of_state_expectations (PureReferenceRecovery.inputDensity
      (unitProductInput (Nat.pos_of_ne_zero ha))) _ (adjointIdentity_positive Φ hΦ)
    intro ρ
    rw [adjointIdentity_pairing]
    have h := norm_trace_map_state_le_diamond Φ ρ
    have hr : ‖(Φ ρ.matrix).trace‖ ≤ (diamondNorm Φ).toReal := by
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.toReal_mono htop h
    exact (Complex.re_le_norm _).trans hr
  exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal htop)

/-- The paper's generic CP-map identity, with the actual adjoint-at-identity. -/
theorem diamondNorm_cp (Φ : MatrixMap a b) (hΦ : MatrixMap.CompletelyPositive Φ) :
    diamondNorm Φ=ENNReal.ofReal ‖adjointIdentity Φ‖ :=
  le_antisymm (diamondNorm_cp_le Φ hΦ) (adjoint_norm_le_diamondNorm Φ hΦ)

/-- In particular every finite-dimensional CP map has finite full diamond norm. -/
theorem diamondNorm_cp_ne_top (Φ : MatrixMap a b) (hΦ : MatrixMap.CompletelyPositive Φ) :
    diamondNorm Φ≠⊤ := by
  rw [diamondNorm_cp Φ hΦ]
  exact ENNReal.ofReal_ne_top

/-- Actual amplification of a rectangular single-Kraus sandwich. -/
theorem amplify_adMap (K : Matrix (Fin b) (Fin a) ℂ) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify (adMap K) r X =
      ((1:Operator r) ⊗ₖ K)*X*((1:Operator r) ⊗ₖ K)ᴴ := by
  rw [adMap,MatrixMap.amplify_ofKraus]
  simp

/-- Arbitrary rectangular single-Kraus continuity on every reference and every matrix input. -/
theorem traceNorm_amplify_adMap_sub_le (K L : Matrix (Fin b) (Fin a) ℂ) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    TraceNorm.traceNorm (MatrixMap.amplify (adMap K-adMap L) r X) ≤
      (‖K‖+‖L‖)*‖K-L‖*TraceNorm.traceNorm X := by
  have heq : MatrixMap.amplify (adMap K-adMap L) r X =
      MatrixMap.amplify (adMap K) r X-MatrixMap.amplify (adMap L) r X := rfl
  rw [heq,amplify_adMap,amplify_adMap]
  have hK : ‖(1:Operator r) ⊗ₖ K‖ ≤ ‖K‖ := TensorNorm.one_kronecker_opNorm_le _
  have hL : ‖(1:Operator r) ⊗ₖ L‖ ≤ ‖L‖ := TensorNorm.one_kronecker_opNorm_le _
  have hd : ‖(1:Operator r) ⊗ₖ K-(1:Operator r) ⊗ₖ L‖ ≤ ‖K-L‖ := by
    have h : (1:Operator r) ⊗ₖ K-(1:Operator r) ⊗ₖ L=(1:Operator r) ⊗ₖ (K-L) := by
      ext i j
      simp [Matrix.kroneckerMap_apply,mul_sub]
    rw [h]
    exact TensorNorm.one_kronecker_opNorm_le _
  apply (TraceNorm.traceNorm_dilation_difference_le _ _ _).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (add_le_add hK hL) hd (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    (TraceNorm.traceNorm_nonneg X)

/-- Literal unhalved diamond estimate (2), with no contraction or isometry assumption on K,L. -/
theorem diamondNorm_adMap_sub_le (K L : Matrix (Fin b) (Fin a) ℂ) :
    diamondNorm (adMap K-adMap L) ≤ ENNReal.ofReal ((‖K‖+‖L‖)*‖K-L‖) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  apply ENNReal.ofReal_le_ofReal
  exact (traceNorm_amplify_adMap_sub_le K L r X.val).trans
    (mul_le_of_le_one_right (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) X.property)

/-- CPTP precomposition contracts the full diamond norm of any complex-linear map. -/
theorem diamondNorm_precompose (Φ : MatrixMap b c) (D : KrausChannel a b) :
    diamondNorm (Φ.comp D.toLinearMap) ≤ diamondNorm Φ := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  rw [amplify_comp]
  let Y := MatrixMap.amplify D.toLinearMap r X.val
  have hY : TraceNorm.traceNorm Y ≤ 1 :=
    (traceNorm_amplify_channel_le D r X.val).trans X.property
  exact le_iSup_of_le r (le_iSup_of_le ⟨Y,hY⟩ le_rfl)

end GeneralizedChannelStein.GeneralDiamondBounds
