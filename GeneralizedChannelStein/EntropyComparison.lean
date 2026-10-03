import GeneralizedChannelStein.EntropyContinuity
import GeneralizedChannelStein.SupportedLogComparison
import GeneralizedChannelStein.LemmaFour
import GeneralizedChannelStein.SharpEntropyContinuity
import GeneralizedChannelStein.TensorStateLowerBound

/-! # Genuine entropy comparison from a trace-preserving approximation

The actual midpoint channel has a reference-uniform supported logarithm
bound. Combining it with sharp entropy continuity yields the literal
Lemma 10, including its binary-entropy correction and block constants.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace GeneralizedChannelStein.EntropyComparison
open QuantumChannelStein Matrix ChannelEntropy OperationalTesting SharpChannel
  RelativeEntropy EntropyContinuity SupportedLogComparison
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- A genuine finite-branch relative-entropy perturbation estimate; all
reference support and logarithm cancellations have already been proved. -/
theorem state_relative_entropy_comparison_add_two {r b : ℕ}
    (ρ ν σ : State (r*b)) (μ : State r)
    (hρ : marginalLinear r b ρ.matrix = μ.matrix)
    (hν : marginalLinear r b ν.matrix = μ.matrix)
    (c d : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d)
    (hlo : (unflatten (a := r) (b := b) σ.matrix - c • (μ.matrix ⊗ₖ (1 : Operator b))).PosSemidef)
    (hhi : (d • (μ.matrix ⊗ₖ (1 : Operator b)) - unflatten (a := r) (b := b) σ.matrix).PosSemidef)
    (δ : ℝ) (hδ : TraceNorm.traceNorm (ρ.matrix-ν.matrix) ≤ δ) :
    umegaki ρ σ ≤ umegaki ν σ +
      ((δ/2 * (Real.logb 2 (r*b) + (Real.logb 2 d - Real.logb 2 c)) + 2 : ℝ) : EReal) := by
  have hsρ := supportIncluded_of_reference_lower ρ σ μ hρ c hc hlo
  have hsν := supportIncluded_of_reference_lower ν σ μ hν c hc hlo
  rw [umegaki_of_supportIncluded ρ σ hsρ, umegaki_of_supportIncluded ν σ hsν,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  have he := abs_entropy_sub_le_of_traceNorm_le ρ ν δ hδ
  have hl := abs_state_crossEntropy_sub_le ρ ν σ μ (hρ.trans hν.symm) c d hc hc1 hd hlo hhi
  have hwidth : 0 ≤ Real.logb 2 d - Real.logb 2 c := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (Real.log_le_log hc (hc1.trans hd))
      (Real.log_pos (by norm_num)).le
  have hb := mul_le_mul_of_nonneg_right (show TraceNorm.traceNorm (ρ.matrix-ν.matrix)/2 ≤ δ/2 by linarith) hwidth
  have hl' := hl.trans hb
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hl'
  rw [traceFormula_entropy, traceFormula_entropy]
  have he' := neg_le_of_abs_le he
  have hl'' := neg_le_of_abs_le hl'
  simp only [Nat.cast_mul] at he'
  nlinarith

/-- A genuine finite-branch relative-entropy perturbation estimate; all
reference support and logarithm cancellations have already been proved. -/
theorem state_relative_entropy_comparison {r b : ℕ}
    (ρ ν σ : State (r*b)) (μ : State r)
    (hρ : marginalLinear r b ρ.matrix = μ.matrix)
    (hν : marginalLinear r b ν.matrix = μ.matrix)
    (c d : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d)
    (hlo : (unflatten (a := r) (b := b) σ.matrix - c • (μ.matrix ⊗ₖ (1 : Operator b))).PosSemidef)
    (hhi : (d • (μ.matrix ⊗ₖ (1 : Operator b)) - unflatten (a := r) (b := b) σ.matrix).PosSemidef)
    (δ : ℝ) (hδ : TraceNorm.traceNorm (ρ.matrix-ν.matrix) ≤ δ) (hδ1 : δ ≤ 1) :
    umegaki ρ σ ≤ umegaki ν σ +
      ((δ/2 * (Real.logb 2 (r*b) + (Real.logb 2 d - Real.logb 2 c)) + binaryEntropy (δ/2) : ℝ) : EReal) := by
  have hsρ := supportIncluded_of_reference_lower ρ σ μ hρ c hc hlo
  have hsν := supportIncluded_of_reference_lower ν σ μ hν c hc hlo
  rw [umegaki_of_supportIncluded ρ σ hsρ, umegaki_of_supportIncluded ν σ hsν,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  have he := abs_entropy_sub_le_fannes ρ ν δ hδ hδ1
  have hl := abs_state_crossEntropy_sub_le ρ ν σ μ (hρ.trans hν.symm) c d hc hc1 hd hlo hhi
  have hwidth : 0 ≤ Real.logb 2 d - Real.logb 2 c := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (Real.log_le_log hc (hc1.trans hd))
      (Real.log_pos (by norm_num)).le
  have hb := mul_le_mul_of_nonneg_right (show TraceNorm.traceNorm (ρ.matrix-ν.matrix)/2 ≤ δ/2 by linarith) hwidth
  have hl' := hl.trans hb
  simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hl'
  rw [traceFormula_entropy, traceFormula_entropy]
  have he' := neg_le_of_abs_le he
  have hl'' := neg_le_of_abs_le hl'
  simp only [Nat.cast_mul] at he'
  nlinarith

/-- The actual reference marginal of a normalized pure input. -/
def pureReferenceState {r a : ℕ} (ψ : UnitPureInput r a) : State r where
  matrix := KrausChannel.traceOutput (pureMatrix ψ.val)
  positive := TestingSDP.traceOutput_positive (pureMatrix_positive ψ.val)
  trace_one := (TestingSDP.trace_traceOutput _).trans (trace_pureMatrix_of_norm_one ψ.val ψ.property)

/-- Channel trace preservation acts on each reference block, including its
possibly non-Hermitian off-diagonal blocks. -/
theorem traceOutput_amplify {r a b : ℕ} (Φ : KrausChannel a b)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    KrausChannel.traceOutput (Φ.amplify r X) = KrausChannel.traceOutput X := by
  ext i j
  simp only [KrausChannel.traceOutput, KrausChannel.amplify_block]
  exact Φ.trace_apply (fun u v => X (i,u) (j,v))

theorem unflatten_pureOutput {r a b : ℕ} (Φ : KrausChannel a b) (ψ : UnitPureInput r a) :
    unflatten (a := r) (b := b) (pureOutput Φ ψ).matrix = Φ.amplify r (pureMatrix ψ.val) := by
  exact unflatten_flatten _

/-- All channels preserve the same actual reference density for the same input. -/
theorem marginal_pureOutput {r a b : ℕ} (Φ : KrausChannel a b) (ψ : UnitPureInput r a) :
    marginalLinear r b (pureOutput Φ ψ).matrix = (pureReferenceState ψ).matrix := by
  change KrausChannel.traceOutput (unflatten (a := r) (b := b) (pureOutput Φ ψ).matrix) = _
  rw [unflatten_pureOutput, traceOutput_amplify]
  rfl

/-- Replacer outputs on every actual pure input are its reference marginal tensor the prepared state. -/
theorem replacer_pureOutput {r a b : ℕ} (ω : State b) (ψ : UnitPureInput r a) :
    unflatten (a := r) (b := b) (pureOutput (ReplacerChannel.channel a ω) ψ).matrix =
      (pureReferenceState ψ).matrix ⊗ₖ ω.matrix := by
  rw [unflatten_pureOutput]
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [KrausChannel.amplify_block, ReplacerChannel.channel_apply]
  rfl

/-- Full unhalved diamond distance controls the actual output trace norm uniformly. -/
theorem pureOutput_traceNorm_sub_le {r a b : ℕ} (N L : KrausChannel a b)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ)
    (ψ : UnitPureInput r a) :
    TraceNorm.traceNorm ((pureOutput N ψ).matrix-(pureOutput L ψ).matrix) ≤ δ := by
  have hX : TraceNorm.traceNorm (pureMatrix ψ.val) = 1 := by
    rw [TraceNorm.traceNorm_of_posSemidef _ (pureMatrix_positive ψ.val),
      trace_pureMatrix_of_norm_one ψ.val ψ.property]
    rfl
  have hb : ENNReal.ofReal (TraceNorm.traceNorm
      (MatrixMap.amplify (L.toLinearMap-N.toLinearMap) r (pureMatrix ψ.val))) ≤
      DiamondNorm.diamondNorm (L.toLinearMap-N.toLinearMap) :=
    le_iSup_of_le r (le_iSup_of_le ⟨pureMatrix ψ.val,hX.le⟩ le_rfl)
  have hb' := (ENNReal.ofReal_le_ofReal_iff hδ).mp (hb.trans hclose)
  have hraw : MatrixMap.amplify (L.toLinearMap-N.toLinearMap) r (pureMatrix ψ.val) =
      L.amplify r (pureMatrix ψ.val)-N.amplify r (pureMatrix ψ.val) := by
    ext ⟨i,u⟩ ⟨j,v⟩
    simp [MatrixMap.amplify, KrausChannel.amplify_block, KrausChannel.toLinearMap]
  rw [hraw] at hb'
  have hreindex := TraceNorm.traceNorm_reindex finProdFinEquiv
    (L.amplify r (pureMatrix ψ.val)-N.amplify r (pureMatrix ψ.val))
  change TraceNorm.traceNorm ((pureOutput L ψ).matrix-(pureOutput N ψ).matrix) = _ at hreindex
  rw [← hreindex] at hb'
  rw [← neg_sub (pureOutput L ψ).matrix (pureOutput N ψ).matrix, TraceNorm.traceNorm_neg]
  exact hb'

variable {a b : ℕ}

/-- The literal arithmetic mean of the two channel maps. -/
def averageMap (S R : KrausChannel a b) : MatrixMap a b :=
  ((1/2 : ℝ) : ℂ) • S.toLinearMap + ((1/2 : ℝ) : ℂ) • R.toLinearMap

theorem averageMap_cp (S R : KrausChannel a b) : MatrixMap.CompletelyPositive (averageMap S R) :=
  MatrixMap.completelyPositive_add
    (MatrixMap.completelyPositive_smul (by norm_num : (0:ℝ) ≤ 1/2) (MatrixMap.completelyPositive_toLinearMap S))
    (MatrixMap.completelyPositive_smul (by norm_num : (0:ℝ) ≤ 1/2) (MatrixMap.completelyPositive_toLinearMap R))

theorem averageMap_trace (S R : KrausChannel a b) (X : Operator a) :
    ((averageMap S R) X).trace = X.trace := by
  change ((((1/2 : ℝ):ℂ) • S.apply X) + (((1/2 : ℝ):ℂ) • R.apply X)).trace = _
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, S.trace_apply, R.trace_apply]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- An actual normalized Kraus presentation of the same midpoint map. -/
def averageChannel (S R : KrausChannel a b) : KrausChannel a b :=
  (MatrixMap.exists_kraus_of_cptp (averageMap S R) (averageMap_cp S R) (averageMap_trace S R)).choose

theorem averageChannel_map (S R : KrausChannel a b) :
    (averageChannel S R).toLinearMap = averageMap S R :=
  (MatrixMap.exists_kraus_of_cptp (averageMap S R) (averageMap_cp S R) (averageMap_trace S R)).choose_spec.2

/-- Convexity is used on actual Choi maps, with no compactness assumption. -/
theorem averageChannel_mem (F : Set (MatrixMap a b))
    (hF : Convex ℝ (MatrixMap.choi '' F))
    (S R : KrausChannel a b) (hS : S.toLinearMap ∈ F) (hR : R.toLinearMap ∈ F) :
    (averageChannel S R).toLinearMap ∈ F := by
  have hm := hF (show S.choi ∈ MatrixMap.choi '' F from ⟨S.toLinearMap,hS,rfl⟩)
    (show R.choi ∈ MatrixMap.choi '' F from ⟨R.toLinearMap,hR,rfl⟩)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2:ℝ)+1/2=1)
  obtain ⟨M,hM,heq⟩ := hm
  have he : (averageChannel S R).toLinearMap = M := by
    apply MatrixMap.choi_injective
    rw [averageChannel_map, averageMap, MatrixMap.choi_add, MatrixMap.choi_smul, MatrixMap.choi_smul,
      MatrixMap.choi_toLinearMap, MatrixMap.choi_toLinearMap]
    exact heq.symm
  exact he ▸ hM

theorem averageChannel_pureOutput {r : ℕ} (S R : KrausChannel a b) (ψ : UnitPureInput r a) :
    unflatten (a := r) (b := b) (pureOutput (averageChannel S R) ψ).matrix =
      (1/2:ℝ) • unflatten (a := r) (b := b) (pureOutput S ψ).matrix +
      (1/2:ℝ) • unflatten (a := r) (b := b) (pureOutput R ψ).matrix := by
  rw [unflatten_pureOutput, unflatten_pureOutput, unflatten_pureOutput]
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, KrausChannel.amplify_block]
  change ((averageChannel S R).toLinearMap (fun x y => pureMatrix ψ.val (i,x) (j,y))) u v = _
  rw [averageChannel_map]
  rfl

/-- A dominator doubled under midpoint mixing still dominates the approximant. -/
theorem cpLe_averageChannel (L S R : KrausChannel a b) (s : ℝ) (hs : 0 ≤ s)
    (hdom : MatrixMap.CPLe L.toLinearMap ((s:ℂ) • S.toLinearMap)) :
    MatrixMap.CPLe L.toLinearMap (((2*s:ℝ):ℂ) • (averageChannel S R).toLinearMap) := by
  rw [MatrixMap.cpLe_iff_choi_difference] at hdom ⊢
  rw [MatrixMap.choi_smul] at hdom ⊢
  have hp := R.choi_positive.smul (show (0:ℂ) ≤ (s:ℂ) from by exact_mod_cast hs)
  have h := hdom.add hp
  simp only [MatrixMap.choi_toLinearMap] at h
  rw [averageChannel_map, averageMap, MatrixMap.choi_add, MatrixMap.choi_smul,
    MatrixMap.choi_smul, MatrixMap.choi_toLinearMap, MatrixMap.choi_toLinearMap]
  convert h using 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, MatrixMap.choi_toLinearMap]
  push_cast
  ring

/-- The reference-relative logarithmic sandwich for the actual midpoint with a replacer. -/
theorem average_replacer_output_sandwich {r : ℕ} (S : KrausChannel a b)
    (ω : State b) (w : ℝ) (_hw : 0 ≤ w)
    (hω : (ω.matrix - w • (1 : Operator b)).PosSemidef)
    (ψ : UnitPureInput r a) :
    (unflatten (a := r) (b := b) (pureOutput (averageChannel S (ReplacerChannel.channel a ω)) ψ).matrix -
      (w/2) • ((pureReferenceState ψ).matrix ⊗ₖ (1 : Operator b))).PosSemidef ∧
    ((b:ℝ) • ((pureReferenceState ψ).matrix ⊗ₖ (1 : Operator b)) -
      unflatten (a := r) (b := b) (pureOutput (averageChannel S (ReplacerChannel.channel a ω)) ψ).matrix).PosSemidef := by
  constructor
  · have h₁ := ((pureOutput S ψ).positive.submatrix finProdFinEquiv).smul (show (0:ℝ) ≤ 1/2 by norm_num)
    have h₂ := (MatrixMap.posSemidef_kronecker (pureReferenceState ψ).positive hω).smul
      (show (0:ℝ) ≤ 1/2 by norm_num)
    have h := h₁.add h₂
    rw [averageChannel_pureOutput, replacer_pureOutput]
    convert h using 1
    ext ⟨i,u⟩ ⟨j,v⟩
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul, SharpChannel.unflatten, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    push_cast
    ring
  · have h := DimensionDomination.dimension_order
      (unflatten (a := r) (b := b) (pureOutput (averageChannel S (ReplacerChannel.channel a ω)) ψ).matrix)
      ((pureOutput (averageChannel S (ReplacerChannel.channel a ω)) ψ).positive.submatrix finProdFinEquiv)
    change ((b:ℝ) • ((marginalLinear r b (pureOutput (averageChannel S (ReplacerChannel.channel a ω)) ψ).matrix) ⊗ₖ
      (1 : Operator b)) - _).PosSemidef at h
    rwa [marginal_pureOutput] at h

/-- Trace normalization forces every actual state domination constant to be at least one. -/
theorem one_le_state_domination {n : ℕ} (ν σ : State n) (s : ℝ)
    (h : (s • σ.matrix - ν.matrix).PosSemidef) : 1 ≤ s := by
  have ht := (Complex.nonneg_iff.mp h.trace_nonneg).1
  rw [Matrix.trace_sub, Matrix.trace_smul, σ.trace_one, ν.trace_one] at ht
  simpa only [Complex.sub_re, Complex.smul_re, smul_eq_mul, Complex.one_re, mul_one,
    sub_nonneg] using ht

/-- The actual channel comparison, uniform over every optimized pure input.
The dominator is the same midpoint channel for all inputs. -/
theorem channel_entropy_comparison (N L S : KrausChannel a b)
    (hb : 0 < b) (ω : State b) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hω : (ω.matrix - w • (1 : Operator b)).PosSemidef)
    (z δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdom : MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^z) • S.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ) :
    channelD N (averageChannel S (ReplacerChannel.channel a ω)) ≤
      ((z+1 + δ/2 * (Real.logb 2 (a*b) + (Real.logb 2 b - Real.logb 2 w + 1)) +
        binaryEntropy (δ/2) : ℝ) : EReal) := by
  apply iSup_le
  intro ψ
  let ρ := pureOutput N ψ
  let ν := pureOutput L ψ
  let σ := pureOutput (averageChannel S (ReplacerChannel.channel a ω)) ψ
  let μ := pureReferenceState ψ
  have hsand := average_replacer_output_sandwich S ω w hw.le hω ψ
  have htrace := pureOutput_traceNorm_sub_le N L δ hδ0 hclose ψ
  have hc : 0 < w/2 := by positivity
  have hc1 : w/2 ≤ 1 := by linarith
  have hd : 1 ≤ (b:ℝ) := by exact_mod_cast hb
  have hcompare := state_relative_entropy_comparison ρ ν σ μ
    (marginal_pureOutput N ψ) (marginal_pureOutput L ψ)
    (w/2) b hc hc1 hd hsand.1 hsand.2 δ htrace hδ1
  have hcp := cpLe_averageChannel L S (ReplacerChannel.channel a ω) ((2:ℝ)^z) (by positivity) hdom
  have hνdom := pureOutput_domination L (averageChannel S (ReplacerChannel.channel a ω))
    (2*(2:ℝ)^z) hcp ψ
  have hcdom := one_le_state_domination ν σ (2*(2:ℝ)^z) hνdom
  have hνbound := umegaki_le_log2_of_domination ν σ (2*(2:ℝ)^z) hcdom hνdom
  have hlog : Real.logb 2 (2*(2:ℝ)^z) = z+1 := by
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos (by norm_num) z).ne',
      Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
      Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)]
    ring
  rw [hlog] at hνbound
  have hout := hcompare.trans (add_le_add hνbound le_rfl)
  rw [← EReal.coe_add] at hout
  convert hout using 1
  congr 1
  rw [Real.logb_div hw.ne' (by norm_num : (2:ℝ)≠0),
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
  ring

/-- Free-family comparison using only actual Choi convexity and membership
of the single replacer channel; no compactness or tensor-closure premise. -/
theorem family_entropy_comparison (N L S : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (hS : S.toLinearMap ∈ F) (hb : 0 < b)
    (ω : State b) (hR : (ReplacerChannel.channel a ω).toLinearMap ∈ F)
    (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hω : (ω.matrix - w • (1 : Operator b)).PosSemidef)
    (z δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdom : MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^z) • S.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ) :
    familyEntropy N F ≤
      ((z+1 + δ/2 * (Real.logb 2 (a*b) + (Real.logb 2 b - Real.logb 2 w + 1)) +
        binaryEntropy (δ/2) : ℝ) : EReal) :=
  (familyEntropy_le N (averageChannel S (ReplacerChannel.channel a ω)) F
    (averageChannel_mem F hF S _ hS hR)).trans
      (channel_entropy_comparison N L S hb ω w hw hw1 hω z δ hδ0 hδ1 hdom hclose)

/-- **Lemma 10 (Entropy comparison)**, with the literal block constant and
sharp binary-entropy correction. Only convexity at this block and membership
of the faithful replacer power are used from the alternative family. -/
theorem lemma_10 (N : KrausChannel a b) (hb : 0 < b)
    (F : AlternativeFamily a b) (ω : State b) (hω : ω.matrix.PosDef)
    (n : ℕ) (_hn : 0 < n)
    (hF : Convex ℝ (MatrixMap.choi '' F n))
    (hR : ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n)
    (L S : KrausChannel (a^n) (b^n)) (hS : S.toLinearMap ∈ F n)
    (z δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdom : MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^z) • S.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤ ENNReal.ofReal δ) :
    familyEntropy (N.tensorPower n) (F n) ≤
      ((z+1 + δ/2 * ((n:ℝ) * (replacerRate ω hb + Real.logb 2 (a*b)) + 1) +
        binaryEntropy (δ/2) : ℝ) : EReal) := by
  let w := DimensionDomination.minEigenvalue ω hb
  have hw : 0 < w := DimensionDomination.minEigenvalue_pos ω hb hω
  have hw1 : w ≤ 1 := DimensionDomination.minEigenvalue_le_one ω hb
  have hlo : (ω.matrix-w • (1 : Operator b)).PosSemidef :=
    DimensionDomination.scalar_le_of_eigenvalue_lower ω w (DimensionDomination.minEigenvalue_le ω hb)
  have hpow := TensorStateLowerBound.statePower_lower ω w hw.le hlo n
  have hR' : (ReplacerChannel.channel (a^n) (PerfectDiscrimination.statePower ω n)).toLinearMap ∈ F n := by
    rw [ReplacerChannel.channel_map, ← ReplacerChannel.tensorPower_map (n := a) ω n]
    exact hR
  have h := family_entropy_comparison (N.tensorPower n) L S (F n) hF hS (pow_pos hb n)
    (PerfectDiscrimination.statePower ω n) hR' (w^n) (pow_pos hw n)
    (pow_le_one₀ hw.le hw1) hpow z δ hδ0 hδ1 hdom hclose
  have hdim : Real.logb 2 ((a^n:ℝ)*(b^n:ℝ)) = (n:ℝ)*Real.logb 2 ((a:ℝ)*b) := by
    rw [← mul_pow, Real.logb_pow]
  simp only [Nat.cast_pow] at h
  rw [hdim, Real.logb_pow, Real.logb_pow] at h
  convert h using 1
  congr 1
  dsimp [replacerRate, w]
  ring

/-- Convenient specialization to the literal F1--F3 admissible family. -/
theorem lemma_10_of_admissible (N : KrausChannel a b) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n)
    (L S : KrausChannel (a^n) (b^n)) (hS : S.toLinearMap ∈ F n)
    (z δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdom : MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^z) • S.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤ ENNReal.ofReal δ) :
    familyEntropy (N.tensorPower n) (F n) ≤
      ((z+1 + δ/2 * ((n:ℝ) * (replacerRate ω hb + Real.logb 2 (a*b)) + 1) +
        binaryEntropy (δ/2) : ℝ) : EReal) :=
  lemma_10 N hb F ω hω n hn (hF.convex n hn)
    (replacer_power_mem F hF.tensor_closed ω hOne n hn) L S hS z δ hδ0 hδ1 hdom hclose

end GeneralizedChannelStein.EntropyComparison
