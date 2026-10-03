import GeneralizedChannelStein.CanonicalInput
import GeneralizedChannelStein.ProjectorSpectral

/-! Uniform logarithm truncation on genuinely dominated density pairs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.DominatedEntropyContinuity
open QuantumChannelStein RelativeEntropy Matrix CanonicalInput
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {n : ℕ}

def cutoffLog (t x : ℝ) : ℝ := Real.logb 2 (max x t)

theorem continuous_cutoffLog {t : ℝ} (ht : 0<t) : Continuous (cutoffLog t) := by
  unfold cutoffLog Real.logb
  apply Continuous.div_const
  apply Continuous.log (continuous_id.max continuous_const)
  intro x
  exact ne_of_gt (ht.trans_le (le_max_right x t))

/-- The elementary scalar maximum behind the uniform singular-boundary bound. -/
theorem mul_log_ratio_le {t x : ℝ} (ht : 0<t) (hx : 0<x) :
    x * Real.log (t/x) ≤ t * Real.exp (-1) := by
  have h := Real.add_one_le_exp (Real.log (t/x)-1)
  rw [Real.exp_sub,Real.exp_log (div_pos ht hx)] at h
  have h' := mul_le_mul_of_nonneg_left h hx.le
  have heq : x*((t/x)/Real.exp 1) = t*Real.exp (-1) := by
    rw [Real.exp_neg]
    field_simp
  rw [heq] at h'
  nlinarith

def spectralWeight (ρ σ : State n) (i : Fin n) : ℝ :=
  (((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ * ρ.matrix *
    (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) i i).re

theorem spectralWeight_nonneg (ρ σ : State n) (i : Fin n) : 0≤spectralWeight ρ σ i :=
  (Complex.nonneg_iff.mp ((ρ.positive.conjTranspose_mul_mul_same
    (σ.positive.isHermitian.eigenvectorUnitary : Operator n)).diag_nonneg (i:=i))).1

theorem spectralWeight_le (ρ σ : State n) (K : ℝ)
    (hdom : (K•σ.matrix-ρ.matrix).PosSemidef) (i : Fin n) :
    spectralWeight ρ σ i ≤ K*σ.positive.isHermitian.eigenvalues i := by
  letI : Nonempty (Fin n) := ⟨⟨0,MatrixOperatorBridge.state_dimension_pos σ⟩⟩
  have h := (Complex.nonneg_iff.mp ((hdom.conjTranspose_mul_mul_same
    (σ.positive.isHermitian.eigenvectorUnitary : Operator n)).diag_nonneg (i:=i))).1
  have hs := ImageProjector.basisChange_spectral σ.positive.isHermitian
  rw [ImageProjector.basisChange_apply] at hs
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hs,
    Matrix.sub_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,Complex.sub_re,Complex.smul_re,
    Complex.ofReal_re,smul_eq_mul] at h
  exact sub_nonneg.mp h

/-- Each actual spectral weight obeys the same dimension-independent cutoff estimate. -/
theorem weighted_cutoff_error (ρ σ : State n) (K t : ℝ) (hK : 0≤K) (ht : 0<t)
    (hdom : (K•σ.matrix-ρ.matrix).PosSemidef) (i : Fin n) :
    0 ≤ spectralWeight ρ σ i * (cutoffLog t (σ.positive.isHermitian.eigenvalues i) -
      Real.logb 2 (σ.positive.isHermitian.eigenvalues i)) ∧
    spectralWeight ρ σ i * (cutoffLog t (σ.positive.isHermitian.eigenvalues i) -
      Real.logb 2 (σ.positive.isHermitian.eigenvalues i)) ≤ K*t*Real.exp (-1)/Real.log 2 := by
  let x := σ.positive.isHermitian.eigenvalues i
  let w := spectralWeight ρ σ i
  have hx0 : 0≤x := σ.positive.eigenvalues_nonneg i
  have hw0 : 0≤w := spectralWeight_nonneg ρ σ i
  have hwK : w≤K*x := spectralWeight_le ρ σ K hdom i
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  change 0≤w*(cutoffLog t x-Real.logb 2 x) ∧ w*(cutoffLog t x-Real.logb 2 x)≤_
  by_cases hx : x=0
  · have hw : w=0 := by rw [hx,mul_zero] at hwK; linarith
    rw [hw]
    simp only [zero_mul]
    exact ⟨le_rfl,by positivity⟩
  · have hx : 0<x := lt_of_le_of_ne hx0 (Ne.symm hx)
    by_cases hxt : t≤x
    · simp only [cutoffLog,max_eq_left hxt,sub_self,mul_zero]
      constructor
      · rfl
      · positivity
    · have hxt : x<t := lt_of_not_ge hxt
      have heq : cutoffLog t x-Real.logb 2 x = Real.log (t/x)/Real.log 2 := by
        rw [cutoffLog,max_eq_right hxt.le,Real.logb,Real.logb,← sub_div,
          ← Real.log_div ht.ne' hx.ne']
      have hratio : 0≤Real.log (t/x) := Real.log_nonneg ((one_le_div hx).mpr hxt.le)
      rw [heq]
      constructor
      · positivity
      · calc
          w*(Real.log (t/x)/Real.log 2) ≤ (K*x)*(Real.log (t/x)/Real.log 2) :=
            mul_le_mul_of_nonneg_right hwK (div_nonneg hratio hlog.le)
          _ = K*(x*Real.log (t/x))/Real.log 2 := by ring
          _ ≤ K*(t*Real.exp (-1))/Real.log 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_log_ratio_le ht hx) hK) hlog.le
          _ = _ := by ring

def crossEntropy (ρ σ : State n) : ℝ := (ρ.matrix*spectralLog2 σ).trace.re
def cutoffCrossEntropy (t : ℝ) (ρ σ : State n) : ℝ := (ρ.matrix*cfc (cutoffLog t) σ.matrix).trace.re

/-- Uniform trace cutoff bound on every dominated pair, including singular σ. -/
theorem cutoffCrossEntropy_error (ρ σ : State n) (K t : ℝ) (hK : 0≤K) (ht : 0<t)
    (hdom : (K•σ.matrix-ρ.matrix).PosSemidef) :
    0≤cutoffCrossEntropy t ρ σ-crossEntropy ρ σ ∧
      cutoffCrossEntropy t ρ σ-crossEntropy ρ σ≤K*(n:ℝ)*t*Real.exp (-1)/Real.log 2 := by
  have heq : cutoffCrossEntropy t ρ σ-crossEntropy ρ σ =
      ∑ i, spectralWeight ρ σ i * (cutoffLog t (σ.positive.isHermitian.eigenvalues i)-
        Real.logb 2 (σ.positive.isHermitian.eigenvalues i)) := by
    rw [cutoffCrossEntropy,crossEntropy,trace_mul_cfc_eq_spectral,trace_mul_spectralLog2]
    simp only [mul_sub,Finset.sum_sub_distrib,spectralWeight]
  rw [heq]
  constructor
  · exact Finset.sum_nonneg fun i _ => (weighted_cutoff_error ρ σ K t hK ht hdom i).1
  · calc
      _ ≤ ∑ _i : Fin n, K*t*Real.exp (-1)/Real.log 2 :=
        Finset.sum_le_sum fun i _ => (weighted_cutoff_error ρ σ K t hK ht hdom i).2
      _ = _ := by simp; ring

/-- A linear uniform approximation rate transfers continuity without any
pointwise nonsingularity assumption. -/
theorem continuous_of_uniform_linear_error {X : Type*} [TopologicalSpace X]
    (f : X→ℝ) (F : ℝ→X→ℝ) (C : ℝ) (hC : 0≤C)
    (hcont : ∀ t, 0<t → Continuous (F t))
    (herr : ∀ t, 0<t → ∀ x, |F t x-f x|≤C*t) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let t := ε/(4*(C+1))
  have ht : 0<t := div_pos hε (by positivity)
  have hCt : C*t≤ε/4 := by
    dsimp [t]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have hden : 0<4*(C+1) := by positivity
    have hc : C*(ε/(4*(C+1))) = C*ε/(4*(C+1)) := by ring
    rw [hc]
    have hprod := (div_le_iff₀ hden).mpr (show C*ε≤(ε/4)*(4*(C+1)) by nlinarith)
    linarith
  have he := Metric.tendsto_nhds.mp ((hcont t ht).continuousAt (x:=x)) (ε/2) (by positivity)
  filter_upwards [he] with y hy
  rw [Real.dist_eq] at hy ⊢
  have h₁ := herr t ht y
  have h₂ := herr t ht x
  have htri : |f y-f x|≤|F t y-f y|+|F t y-F t x|+|F t x-f x| := by
    have h := abs_add_three (f y-F t y) (F t y-F t x) (F t x-f x)
    rw [abs_sub_comm (f y) (F t y)] at h
    convert h using 1 <;> ring
  linarith

abbrev dominatedPairs (n : ℕ) (K : ℝ) :=
  {p : densitySet n × densitySet n // (K•p.2.val-p.1.val).PosSemidef}

def pairFirst {K : ℝ} (p : dominatedPairs n K) : State n := ofDensity p.val.1
def pairSecond {K : ℝ} (p : dominatedPairs n K) : State n := ofDensity p.val.2

theorem continuous_cutoffCrossEntropy {K t : ℝ} (ht : 0<t) :
    Continuous (fun p : dominatedPairs n K => cutoffCrossEntropy t (pairFirst p) (pairSecond p)) := by
  let H : dominatedPairs n K → HermitianMat (Fin n) ℂ :=
    fun p => ⟨p.val.2.val,p.val.2.property.1.isHermitian⟩
  have hH : Continuous H := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hC := (HermitianMat.cfc_continuous (continuous_cutoffLog ht)).comp hH
  have hmat : Continuous (fun p : dominatedPairs n K => cfc (cutoffLog t) p.val.2.val) :=
    HermitianMat.continuous_mat.comp hC
  unfold cutoffCrossEntropy pairFirst pairSecond ofDensity
  change Continuous (fun p : dominatedPairs n K => (p.val.1.val*cfc (cutoffLog t) p.val.2.val).trace.re)
  have hfirst : Continuous (fun p : dominatedPairs n K => p.val.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  unfold Matrix.trace
  fun_prop

/-- The singular cross-entropy is jointly continuous on every uniformly
PSD-dominated pair domain. The estimate was proved spectrally above. -/
theorem continuous_crossEntropy (K : ℝ) (hK : 0≤K) :
    Continuous (fun p : dominatedPairs n K => crossEntropy (pairFirst p) (pairSecond p)) := by
  apply continuous_of_uniform_linear_error _
    (fun t p => cutoffCrossEntropy t (pairFirst p) (pairSecond p))
    (K*(n:ℝ)*Real.exp (-1)/Real.log 2) (by positivity)
  · intro t ht
    exact continuous_cutoffCrossEntropy ht
  · intro t ht p
    obtain ⟨hl,hu⟩ := cutoffCrossEntropy_error (pairFirst p) (pairSecond p) K t hK ht p.property
    rw [abs_of_nonneg hl]
    convert hu using 1 <;> ring

theorem continuous_density_entropy :
    Continuous (fun ρ : densitySet n => EntropyContinuity.entropy (ofDensity ρ)) := by
  have hM : Continuous (fun ρ : densitySet n => PhyslibStateBridge.toMState (ofDensity ρ)) := by
    apply (MState.toMat_IsEmbedding.isInducing.continuous_iff).mpr
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  simp_rw [EntropyContinuity.entropy_eq_physlib]
  exact (Sᵥₙ_continuous.comp hM).div_const (Real.log 2)

/-- The finite Umegaki trace formula is jointly continuous on genuinely
uniformly dominated state pairs, including singular boundary points. -/
theorem continuous_traceFormula (K : ℝ) (hK : 0≤K) :
    Continuous (fun p : dominatedPairs n K => traceFormula (pairFirst p) (pairSecond p)) := by
  have hS : Continuous (fun p : dominatedPairs n K => EntropyContinuity.entropy (pairFirst p)) :=
    continuous_density_entropy.comp (continuous_fst.comp continuous_subtype_val)
  have hC := continuous_crossEntropy (n:=n) K hK
  have heq : (fun p : dominatedPairs n K => traceFormula (pairFirst p) (pairSecond p)) =
      (fun p => -EntropyContinuity.entropy (pairFirst p)-crossEntropy (pairFirst p) (pairSecond p)) := by
    funext p
    exact EntropyContinuity.traceFormula_entropy _ _
  rw [heq]
  exact hS.neg.sub hC

/-- On this same domain, the actual extended Umegaki function takes the
finite trace-formula branch. -/
theorem umegaki_dominated (K : ℝ) (p : dominatedPairs n K) :
    umegaki (pairFirst p) (pairSecond p) = (traceFormula (pairFirst p) (pairSecond p) : EReal) := by
  apply umegaki_of_supportIncluded
  exact SupportDomination.ker_le_of_posSemidef_smul_sub (pairFirst p).positive p.property

end GeneralizedChannelStein.DominatedEntropyContinuity
