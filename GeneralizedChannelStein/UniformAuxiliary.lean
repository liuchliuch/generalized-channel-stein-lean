import QuantumChannelStein.HockeyStickApproximation
import QuantumChannelStein.DiamondTesting
import QuantumChannelStein.TraceNormCoordinates

/-! # Lemma 6: testing and prescribed-environment auxiliary approximation

The dilations and auxiliary spaces are fixed before the existential map.
The diamond norm convention is the full, unhalved completely bounded trace norm.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.UniformAuxiliary
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal HockeyStickApproximation
  DiamondNorm DiamondTesting TraceNorm
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {a b e f : ℕ}

/-- Lemma 6, the single auxiliary matrix uniform over every input. -/
theorem lemma_6_testing (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : dilationMap V = Φ.toLinearMap) (hW : dilationMap W = Ψ.toLinearMap)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ A : Matrix (Fin e) (Fin f) ℂ, ‖A‖ ≤ Real.sqrt t ∧
      ‖V - ((1 : Operator b) ⊗ₖ A) * W‖ ^ 2 ≤ channelHockeyStick Φ Ψ t := by
  obtain ⟨A,hA,herror⟩ := auxiliaryMinimum_attained V W t
  refine ⟨A,hA,?_⟩
  change auxiliaryDistance V W A ^ 2 ≤ _
  rw [herror]
  exact auxiliaryMinimum_sq_le_channelHockeyStick Φ Ψ ha V W hV hW t ht

/-- Lemma 6, exact domination, also at the boundary t=0. -/
theorem lemma_6_exact
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hdom : MatrixMap.CPLe (dilationMap V) ((t : ℂ) • dilationMap W)) :
    ∃ A : Matrix (Fin e) (Fin f) ℂ, ‖A‖ ≤ Real.sqrt t ∧
      V - ((1 : Operator b) ⊗ₖ A) * W = 0 := by
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul,
    choi_dilationMap, choi_dilationMap] at hdom
  obtain ⟨A,hA,hn⟩ := exact_auxiliary_map_of_gram V W ht
    (by simpa only [Complex.real_smul] using hdom)
  exact ⟨A,hn,sub_eq_zero.mpr hA⟩

/-- Lemma 6, the map produced by any auxiliary matrix is genuinely CP and
is dominated by its squared operator norm times the prescribed channel. -/
theorem lemma_6_converse
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ) (A : Matrix (Fin e) (Fin f) ℂ) :
    MatrixMap.CompletelyPositive (dilationMap (((1 : Operator b) ⊗ₖ A) * W)) ∧
    MatrixMap.CPLe (dilationMap (((1 : Operator b) ⊗ₖ A) * W))
      (((‖A‖ ^ 2 : ℝ) : ℂ) • dilationMap W) :=
  ⟨MatrixMap.completelyPositive_ofKraus _,
    DominatedSubchannels.dilationMap_environment_cpLe W A (sq_nonneg _) le_rfl⟩

/-- Centering a binary effect gives the sharp half-unit norm bound. -/
theorem norm_centered_effect {n : ℕ} (T : Effect n) :
    ‖T.matrix - (1 / 2 : ℝ) • (1 : Operator n)‖ ≤ 1 / 2 := by
  rcases n with _ | n
  · rw [Subsingleton.elim (T.matrix - (1 / 2 : ℝ) • (1 : Operator 0)) 0]
    simp
  letI : CStarAlgebra (Operator (n + 1)) := CStarAlgebra.mk
  have hT := T.positive.isHermitian.isSelfAdjoint
  have h := norm_cfc_le (a := T.matrix) (f := fun x : ℝ => x - 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by
      intro x hx
      have hx0 : 0 ≤ x := by
        rw [T.positive.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i,rfl⟩ := hx
        exact T.positive.eigenvalues_nonneg i
      have hx1 : x ≤ 1 := (Real.le_norm_self x).trans
        ((spectrum.norm_le_norm_of_mem hx).trans T.norm_matrix_le_one)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith)
  rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1 / 2) T.matrix,
    cfc_id' ℝ T.matrix hT, cfc_const (1 / 2 : ℝ) T.matrix hT] at h
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- Equal trace is exactly what improves the full trace-norm bound by two. -/
theorem effect_trace_zero_bound {n : ℕ} (T : Effect n) (X : Operator n)
    (hX : X.trace = 0) : (T.matrix * X).trace.re ≤ TraceNorm.traceNorm X / 2 := by
  have heq : ((T.matrix - (1 / 2 : ℝ) • (1 : Operator n)) * X).trace =
      (T.matrix * X).trace := by
    simp [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul, hX]
  calc
    (T.matrix * X).trace.re ≤ ‖(T.matrix * X).trace‖ := Complex.re_le_norm _
    _ = ‖((T.matrix - (1 / 2 : ℝ) • (1 : Operator n)) * X).trace‖ := congrArg norm heq.symm
    _ ≤ ‖T.matrix - (1 / 2 : ℝ) • (1 : Operator n)‖ * TraceNorm.traceNorm X := norm_trace_mul_le _ _
    _ ≤ (1 / 2 : ℝ) * TraceNorm.traceNorm X :=
      mul_le_mul_of_nonneg_right (norm_centered_effect T) (TraceNorm.traceNorm_nonneg X)
    _ = TraceNorm.traceNorm X / 2 := by ring

/-- Channel-versus-channel diamond distance controls each effect by δ/2. -/
theorem probability_sub_le_half_diamond (Φ Λ : KrausChannel a b)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : diamondNorm (Λ.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal δ)
    (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    T.probability (pureOutput Φ ψ) - T.probability (pureOutput Λ ψ) ≤ δ / 2 := by
  let X := pureMatrix ψ.val
  let Y := MatrixMap.amplify (Λ.toLinearMap - Φ.toLinearMap) a X
  have hX : TraceNorm.traceNorm X = 1 := by
    rw [traceNorm_of_posSemidef X (pureMatrix_positive ψ.val),
      trace_pureMatrix_of_norm_one ψ.val ψ.property]
    rfl
  have hbound : ENNReal.ofReal (TraceNorm.traceNorm Y) ≤ diamondNorm (Λ.toLinearMap - Φ.toLinearMap) :=
    le_iSup_of_le a (le_iSup_of_le ⟨X,hX.le⟩ le_rfl)
  have hYn : TraceNorm.traceNorm Y ≤ δ := (ENNReal.ofReal_le_ofReal_iff hδ).mp (hbound.trans hclose)
  have hYe : Y = Λ.amplify a X - Φ.amplify a X := by
    change MatrixMap.amplify Λ.toLinearMap a X - MatrixMap.amplify Φ.toLinearMap a X = _
    rw [MatrixMap.amplify_toLinearMap, MatrixMap.amplify_toLinearMap]
  have htr : Y.trace = 0 := by
    rw [hYe]
    rw [Matrix.trace_sub, Λ.trace_amplify, Φ.trace_amplify, sub_self]
  let Z : Operator (a * b) := Matrix.reindex finProdFinEquiv finProdFinEquiv (-Y)
  have hZtr : Z.trace = 0 := by
    change (Matrix.reindex finProdFinEquiv finProdFinEquiv (-Y)).trace = 0
    rw [trace_reindex_equiv, Matrix.trace_neg, htr, neg_zero]
  have h := effect_trace_zero_bound T Z hZtr
  have hZn : TraceNorm.traceNorm Z = TraceNorm.traceNorm Y := by
    change TraceNorm.traceNorm (Matrix.reindex finProdFinEquiv finProdFinEquiv (-Y)) = TraceNorm.traceNorm Y
    rw [TraceNorm.traceNorm_reindex, TraceNorm.traceNorm_neg]
  have heq : (T.matrix * Z).trace.re =
      T.probability (pureOutput Φ ψ) - T.probability (pureOutput Λ ψ) := by
    dsimp [Z]
    rw [hYe]
    dsimp [X]
    rw [neg_sub]
    simp [Effect.probability, pureOutput, Matrix.reindex_apply,
      Matrix.submatrix_sub, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [heq, hZn] at h
  exact h.trans (div_le_div_of_nonneg_right hYn (by norm_num))

/-- The sharp one-shot testing consequence for a dominated approximating channel. -/
theorem channelHockeyStick_le_half_diamond (Φ Ψ Λ : KrausChannel a b) (ha : 0 < a)
    (t δ : ℝ) (hδ : 0 ≤ δ)
    (hdom : MatrixMap.CPLe Λ.toLinearMap ((t : ℂ) • Ψ.toLinearMap))
    (hclose : diamondNorm (Λ.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal δ) :
    channelHockeyStick Φ Ψ t ≤ δ / 2 := by
  obtain ⟨ψ,T,hmax⟩ := exists_pure_maximizer Φ Ψ ha t
  rw [← hmax]
  have htest := testValue_le_of_cpLe Λ.toLinearMap Ψ t hdom ψ T
  rw [testValue_channel] at htest
  have hdiff := probability_sub_le_half_diamond Φ Λ δ hδ hclose ψ T
  dsimp [pureScore]
  linarith

/-- Lemma 6, its δ/2 conclusion for an actual channel approximation, with
no change to either prescribed auxiliary space. -/
theorem lemma_6_diamond (Φ Ψ Λ : KrausChannel a b) (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : dilationMap V = Φ.toLinearMap) (hW : dilationMap W = Ψ.toLinearMap)
    (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 ≤ δ)
    (hdom : MatrixMap.CPLe Λ.toLinearMap ((t : ℂ) • Ψ.toLinearMap))
    (hclose : diamondNorm (Λ.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal δ) :
    ∃ A : Matrix (Fin e) (Fin f) ℂ, ‖A‖ ≤ Real.sqrt t ∧
      ‖V - ((1 : Operator b) ⊗ₖ A) * W‖ ^ 2 ≤ δ / 2 := by
  obtain ⟨A,hA,herror⟩ := lemma_6_testing Φ Ψ ha V W hV hW t ht
  exact ⟨A,hA,herror.trans (channelHockeyStick_le_half_diamond Φ Ψ Λ ha t δ hδ hdom hclose)⟩

end GeneralizedChannelStein.UniformAuxiliary
