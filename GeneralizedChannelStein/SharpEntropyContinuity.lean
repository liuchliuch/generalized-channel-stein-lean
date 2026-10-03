import GeneralizedChannelStein.EntropyContinuity
import QuantumChannelStein.SpectralDecompositionCFC

/-! Sharp classical mixture continuity and its quantum spectral reduction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.EntropyContinuity
open QuantumChannelStein QuantumChannelStein.RelativeEntropy Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def classicalState (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : State n where
  matrix := Matrix.diagonal (fun i => (p i : ℂ))
  positive := Matrix.PosSemidef.diagonal fun i => RCLike.ofReal_nonneg.mpr (hp i)
  trace_one := by rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hs]; rfl

theorem classical_entropy (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    entropy (classicalState p hp hs) = -∑ i, p i * Real.logb 2 (p i) := by
  rw [entropy, spectralLog2_eq_cfc]
  have hc : cfc (Real.logb 2) (Matrix.diagonal (fun i => (p i : ℂ))) =
      Matrix.diagonal (fun i => (Real.logb 2 (p i) : ℂ)) := by
    simpa using SpectralDecomposition.cfc_of_unitary_diagonalization
      (1 : Matrix.unitaryGroup (Fin n) ℂ) p (Real.logb 2)
  change -(Matrix.diagonal (fun i => (p i : ℂ)) * cfc (Real.logb 2) (Matrix.diagonal (fun i => (p i : ℂ)))).trace.re = _
  rw [hc, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp

theorem entropy_mix_sub_mix_le (ρ σ ω : State n) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    entropy (mix ρ ω t ht.le ht1.le) - entropy (mix σ ω t ht.le ht1.le) ≤
      t * Real.logb 2 n + binaryEntropy t := by
  have hu := entropy_mix_upper ρ ω t ht ht1
  have hl := entropy_mix_lower σ ω t ht ht1
  have hρ := mul_le_mul_of_nonneg_left (entropy_le_log_dimension ρ) ht.le
  have hσ := mul_nonneg ht.le (entropy_nonneg σ)
  linarith

/-- Normalized pointwise common mass proves the sharp classical bound. -/
theorem classical_entropy_sub_le (p q : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    let t := (∑ i, |p i-q i|)/2
    entropy (classicalState p hp hps) - entropy (classicalState q hq hqs) ≤
      t * Real.logb 2 n + binaryEntropy t := by
  let r : Fin n → ℝ := fun i => min (p i) (q i)
  let t : ℝ := (∑ i, |p i-q i|)/2
  have hr (i) : 0 ≤ r i := le_min (hp i) (hq i)
  have hpr (i) : 0 ≤ p i-r i := sub_nonneg.mpr (min_le_left _ _)
  have hqr (i) : 0 ≤ q i-r i := sub_nonneg.mpr (min_le_right _ _)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hrs : ∑ i, r i = 1-t := by
    have hid : (∑ i, |p i-q i|) = (∑ i, p i)+(∑ i, q i)-2*(∑ i, r i) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [r]
      rcases le_total (p i) (q i) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [hps,hqs] at hid
    dsimp [t]; linarith
  have ht1 : t ≤ 1 := by have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hr i); rw [hrs] at h; linarith
  have hprs : ∑ i, (p i-r i) = t := by rw [Finset.sum_sub_distrib,hps,hrs]; ring
  have hqrs : ∑ i, (q i-r i) = t := by rw [Finset.sum_sub_distrib,hqs,hrs]; ring
  change _ ≤ t * Real.logb 2 n + binaryEntropy t
  by_cases hz : t=0
  · have heq : p=q := by
      funext i
      have hsum : ∑ i, |p i-q i| = 0 := by dsimp [t] at hz; linarith
      have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (p j-q j)) (Finset.mem_univ i)
      have hi : |p i-q i| = 0 := le_antisymm (hsum ▸ hle) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hi)
    subst q
    simp [hz,binaryEntropy]
  · by_cases ho : t=1
    · rw [ho]
      have hu := entropy_le_log_dimension (classicalState p hp hps)
      have hl := entropy_nonneg (classicalState q hq hqs)
      simp only [binaryEntropy, Real.logb_one, mul_zero, sub_self, zero_mul, one_mul, add_zero]
      linarith
    · have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
      have ht' : t < 1 := lt_of_le_of_ne ht1 ho
      let a := classicalState (fun i => (p i-r i)/t)
        (fun i => div_nonneg (hpr i) ht.le) (by rw [← Finset.sum_div,hprs]; exact div_self ht.ne')
      let b := classicalState (fun i => (q i-r i)/t)
        (fun i => div_nonneg (hqr i) ht.le) (by rw [← Finset.sum_div,hqrs]; exact div_self ht.ne')
      let w := classicalState (fun i => r i/(1-t))
        (fun i => div_nonneg (hr i) (sub_pos.mpr ht').le)
        (by rw [← Finset.sum_div,hrs]; exact div_self (sub_pos.mpr ht').ne')
      have hmix (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (hus : ∑ i, u i=1)
          (hur : ∀ i, 0 ≤ u i-r i) (hurs : ∑ i, (u i-r i)=t) :
          mix (classicalState (fun i => (u i-r i)/t)
            (fun i => div_nonneg (hur i) ht.le) (by rw [← Finset.sum_div,hurs]; exact div_self ht.ne'))
            w t ht.le ht'.le = classicalState u hu hus := by
        apply (show ∀ (x y : State n), x.matrix = y.matrix → x = y from
          fun ⟨_,_,_⟩ ⟨_,_,_⟩ h => by cases h; rfl)
        ext i j
        by_cases hij : i=j
        · subst j
          simp only [mix,classicalState,w,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,Complex.real_smul]
          have he : t * ((u i-r i)/t) + (1-t) * (r i/(1-t)) = u i := by
            field_simp [ht.ne', (sub_pos.mpr ht').ne']
            ring
          exact_mod_cast he
        · simp [mix,classicalState,w,Matrix.diagonal_apply_ne _ hij]
      have h := entropy_mix_sub_mix_le a b w t ht ht'
      rw [hmix p hp hps hpr hprs,hmix q hq hqs hqr hqrs] at h
      exact h

/-- Spectral entropy is the classical entropy of the actual eigenvalue list. -/
theorem entropy_eq_eigenvalues (ρ : State n) :
    entropy ρ = -∑ i, ρ.positive.isHermitian.eigenvalues i *
      Real.logb 2 (ρ.positive.isHermitian.eigenvalues i) := by
  rw [entropy, trace_mul_spectralLog2]
  have heq : (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ * ρ.matrix *
      (ρ.positive.isHermitian.eigenvectorUnitary : Operator n) =
      Matrix.diagonal (fun i => (ρ.positive.isHermitian.eigenvalues i : ℂ)) := by
    rw [eigenbasis_conjugation]
    simp [eigenbasisChange]
  simp_rw [heq, Matrix.diagonal_apply_eq, Complex.ofReal_re]

/-- Doubly stochastic averaging increases the actual finite-list entropy. -/
theorem entropy_le_averaged_eigenvalues (ρ σ : State n) :
    entropy ρ ≤ -∑ j, (∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j) *
      Real.logb 2 (∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j) := by
  let p := ρ.positive.isHermitian.eigenvalues
  let w := overlapWeight ρ σ
  let q : Fin n → ℝ := fun j => ∑ i, p i * w i j
  have hp (i) : 0 ≤ p i := ρ.positive.eigenvalues_nonneg i
  have hw (i j) : 0 ≤ w i j := overlapWeight_nonneg ρ σ i j
  have hq (j) : 0 ≤ q j := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hw i j)
  have hqs : ∑ j, q j = 1 := by
    dsimp [q]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, show ∀ i, ∑ j, w i j = 1 from sum_overlapWeight_row ρ σ, mul_one]
    exact sum_eigenvalues_eq_one ρ
  have hzero (i j) (hj : q j = 0) : p i * w i j = 0 := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hp k) (hw k j)) (Finset.mem_univ i)
    change p i * w i j ≤ q j at h
    exact le_antisymm (hj ▸ h) (mul_nonneg (hp i) (hw i j))
  have hk := doubly_stochastic_klein_log2 p q w hp hq (sum_eigenvalues_eq_one ρ) hqs hw
    (sum_overlapWeight_row ρ σ) (sum_overlapWeight_col ρ σ) hzero
  have ha : (∑ i, ∑ j, w i j * (p i * Real.logb 2 (p i))) =
      ∑ i, p i * Real.logb 2 (p i) := by
    simp_rw [← Finset.sum_mul, show ∀ i, ∑ j, w i j = 1 from sum_overlapWeight_row ρ σ, one_mul]
  have hb : (∑ i, ∑ j, w i j * (p i * Real.logb 2 (q j))) =
      ∑ j, q j * Real.logb 2 (q j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [q, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hk
  rw [ha,hb] at hk
  rw [entropy_eq_eigenvalues]
  change -(∑ i, p i * Real.logb 2 (p i)) ≤ -(∑ j, q j * Real.logb 2 (q j))
  linarith

/-- Measuring in any fixed basis contracts the real diagonal ℓ¹ norm. -/
theorem sum_abs_re_diagonal_le_traceNorm (X : Operator n) :
    ∑ i, |(X i i).re| ≤ TraceNorm.traceNorm X := by
  let s : Fin n → ℂ := fun i => if 0 ≤ (X i i).re then 1 else -1
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨Matrix.diagonal s, by
    rw [Matrix.mem_unitaryGroup_iff]
    change Matrix.diagonal s * (Matrix.diagonal s)ᴴ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, s]
      split_ifs with hi <;> simp [hi]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]⟩
  have heq : ((U : Operator n) * X).trace.re = ∑ i, |(X i i).re| := by
    simp only [U, Matrix.diagonal_mul, Matrix.trace, Matrix.diag, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  rw [← heq]
  exact (Complex.re_le_norm _).trans ((TraceNorm.norm_trace_mul_le _ _).trans
    (mul_le_of_le_one_left (TraceNorm.traceNorm_nonneg _) (TraceNorm.unitary_opNorm_le_one U)))

/-- The actual eigenbasis measurement does not enlarge trace distance. -/
theorem averaged_eigenvalues_distance_le (ρ σ : State n) :
    (∑ j, |(∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j) -
      σ.positive.isHermitian.eigenvalues j|) ≤ TraceNorm.traceNorm (ρ.matrix-σ.matrix) := by
  let U := σ.positive.isHermitian.eigenvectorUnitary
  let X := (U : Operator n)ᴴ * (ρ.matrix-σ.matrix) * (U : Operator n)
  have hself : (U : Operator n)ᴴ * σ.matrix * (U : Operator n) =
      Matrix.diagonal (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ)) := by
    dsimp [U]
    rw [eigenbasis_conjugation]
    simp [eigenbasisChange]
  have hdiag (j) : (X j j).re =
      (∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j) -
        σ.positive.isHermitian.eigenvalues j := by
    dsimp [X]
    rw [Matrix.mul_sub, Matrix.sub_mul, hself]
    simp only [Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq, Complex.ofReal_re]
    rw [eigenbasis_weight_eq_sum]
  have hnorm : TraceNorm.traceNorm X ≤ TraceNorm.traceNorm (ρ.matrix-σ.matrix) := by
    have hn := TraceNorm.unitary_opNorm_le_one U
    have hn0 := TraceNorm.traceNorm_nonneg (ρ.matrix-σ.matrix)
    calc
      _ ≤ ‖(U : Operator n)ᴴ‖ * TraceNorm.traceNorm (ρ.matrix-σ.matrix) * ‖(U : Operator n)‖ :=
        TraceNorm.traceNorm_sandwich_le _ _ _
      _ ≤ 1 * TraceNorm.traceNorm (ρ.matrix-σ.matrix) * 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        gcongr
      _ = _ := by ring
  have h := (sum_abs_re_diagonal_le_traceNorm X).trans hnorm
  simpa only [hdiag] using h

theorem binaryEntropy_mono_half {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1/2) :
    binaryEntropy s ≤ binaryEntropy t := by
  rw [binaryEntropy_eq,binaryEntropy_eq]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  exact Real.binEntropy_strictMonoOn.monotoneOn
    ⟨hs, by simpa using hst.trans ht⟩ ⟨hs.trans hst, by simpa using ht⟩ hst

/-- The sharp Fannes bound needed by the paper, for half trace distance at
most one half; the states may be noncommuting and singular. -/
theorem entropy_sub_le_fannes (ρ σ : State n) (δ : ℝ)
    (hδ : TraceNorm.traceNorm (ρ.matrix-σ.matrix) ≤ δ) (hδ1 : δ ≤ 1) :
    entropy ρ-entropy σ ≤ δ/2 * Real.logb 2 n + binaryEntropy (δ/2) := by
  let p : Fin n → ℝ := fun j => ∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j
  let q := σ.positive.isHermitian.eigenvalues
  have hp (j) : 0 ≤ p j := Finset.sum_nonneg fun i _ =>
    mul_nonneg (ρ.positive.eigenvalues_nonneg i) (overlapWeight_nonneg ρ σ i j)
  have hq (j) : 0 ≤ q j := σ.positive.eigenvalues_nonneg j
  have hps : ∑ j, p j=1 := by
    dsimp [p]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_overlapWeight_row, mul_one]
    exact sum_eigenvalues_eq_one ρ
  have hqs : ∑ j, q j=1 := sum_eigenvalues_eq_one σ
  have hent : entropy ρ ≤ entropy (classicalState p hp hps) := by
    rw [classical_entropy]
    exact entropy_le_averaged_eigenvalues ρ σ
  have heq : entropy (classicalState q hq hqs) = entropy σ := by
    rw [classical_entropy,entropy_eq_eigenvalues]
  have hc := classical_entropy_sub_le p q hp hq hps hqs
  dsimp only at hc
  rw [heq] at hc
  have hdist : (∑ i, |p i-q i|)/2 ≤ δ/2 := by
    have h := (averaged_eigenvalues_distance_le ρ σ).trans hδ
    change (∑ i, |p i-q i|) ≤ δ at h
    linarith
  have ht0 : 0 ≤ (∑ i, |p i-q i|)/2 := by positivity
  have hlog : 0 ≤ Real.logb 2 n := (entropy_nonneg ρ).trans (entropy_le_log_dimension ρ)
  have hm := mul_le_mul_of_nonneg_right hdist hlog
  have hb := binaryEntropy_mono_half ht0 hdist (by linarith)
  linarith

/-- Uniform sharp continuity at every allowed tolerance, exactly the
entropy-continuity constants used by paper Lemma 10. -/
theorem abs_entropy_sub_le_fannes (ρ σ : State n) (δ : ℝ)
    (hδ : TraceNorm.traceNorm (ρ.matrix-σ.matrix) ≤ δ) (hδ1 : δ ≤ 1) :
    |entropy ρ-entropy σ| ≤ δ/2 * Real.logb 2 n + binaryEntropy (δ/2) := by
  have h₁ := entropy_sub_le_fannes ρ σ δ hδ hδ1
  have hrev : TraceNorm.traceNorm (σ.matrix-ρ.matrix) ≤ δ := by
    rw [← neg_sub ρ.matrix σ.matrix,TraceNorm.traceNorm_neg]
    exact hδ
  have h₂ := entropy_sub_le_fannes σ ρ δ hrev hδ1
  apply abs_le.mpr
  constructor <;> linarith

end GeneralizedChannelStein.EntropyContinuity
