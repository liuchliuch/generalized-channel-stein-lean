import OrdinaryStateStein
import KernelFilledAlternative

noncomputable section
open ComplexOrder Topology Filter
open scoped HermitianMat RealInnerProductSpace InnerProductSpace Prob

namespace StateSteinAudit

variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

/-- Tensor products preserve independent positive-semidefinite upper bounds. -/
lemma kronecker_mono_pair {A A' : HermitianMat d ℂ} {B B' : HermitianMat e ℂ}
    (hA : 0 ≤ A) (hB' : 0 ≤ B') (hAA' : A ≤ A') (hBB' : B ≤ B') :
    A ⊗ₖ B ≤ A' ⊗ₖ B' := by
  apply sub_nonneg.mp
  have hid : A' ⊗ₖ B' - A ⊗ₖ B = A ⊗ₖ (B' - B) + (A' - A) ⊗ₖ B' := by
    ext x y
    simp only [HermitianMat.mat_sub, HermitianMat.kronecker_mat, HermitianMat.mat_add,
      Matrix.sub_apply, Matrix.add_apply, Matrix.kroneckerMap_apply]
    ring
  rw [hid]
  exact add_nonneg (HermitianMat.kronecker_nonneg hA (sub_nonneg.mpr hBB'))
    (HermitianMat.kronecker_nonneg (sub_nonneg.mpr hAA') hB')

lemma reindex_mono {A B : HermitianMat d ℂ} (h : A ≤ B) (e : d ≃ e) :
    A.reindex e ≤ B.reindex e := by
  apply sub_nonneg.mp
  rw [HermitianMat.reindex_sub, HermitianMat.zero_le_iff]
  exact (HermitianMat.zero_le_iff.mp (sub_nonneg.mpr h)).submatrix e.symm

lemma smul_kronecker_smul (A : HermitianMat d ℂ) (B : HermitianMat e ℂ) (a b : ℝ) :
    (a • A) ⊗ₖ (b • B) = (a * b) • (A ⊗ₖ B) := by
  ext x y
  simp only [HermitianMat.kronecker_mat, HermitianMat.mat_smul, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The scalar domination constant tensorizes for actual finite-tuple powers. -/
theorem npow_domination (sigma tau : MState d) {c : ℝ} (hc : 0 ≤ c)
    (hdom : sigma.M ≤ c • tau.M) (n : ℕ) :
    (sigma.npow n).M ≤ c ^ n • (tau.npow n).M := by
  have h1 : (sigma.npow 1).M ≤ c • (tau.npow 1).M := by
    rw [npow_one_relabel, npow_one_relabel, MState.relabel_M, MState.relabel_M]
    simpa only [HermitianMat.reindex_smul] using
      reindex_mono hdom (Equiv.funUnique (Fin 1) d).symm
  induction n with
  | zero =>
    have hh : sigma.npow 0 = tau.npow 0 := Subsingleton.elim _ _
    rw [hh, pow_zero, one_smul]
  | succ n ih =>
    rw [npow_add_relabel sigma n 1, npow_add_relabel tau n 1,
      MState.relabel_M, MState.relabel_M, ← HermitianMat.reindex_smul]
    apply reindex_mono
    change (sigma.npow n).M ⊗ₖ (sigma.npow 1).M ≤
      c ^ (n + 1) • ((tau.npow n).M ⊗ₖ (tau.npow 1).M)
    rw [pow_succ, ← smul_kronecker_smul]
    exact kronecker_mono_pair (sigma.npow n).nonneg
      (smul_nonneg hc (tau.npow 1).nonneg) ih h1

/-- Domination controls the actual expectation of every positive test. -/
theorem npow_test_domination (sigma tau : MState d) {c : ℝ} (hc : 0 ≤ c)
    (hdom : sigma.M ≤ c • tau.M) (n : ℕ) (T : HermitianMat (Fin n → d) ℂ)
    (hT : 0 ≤ T) :
    (sigma.npow n).exp_val T ≤ c ^ n * (tau.npow n).exp_val T := by
  simpa only [MState.exp_val, HermitianMat.inner_smul_left] using
    HermitianMat.inner_mono' hT (npow_domination sigma tau hc hdom n)

/-- The reverse scalar logarithm estimate includes the zero-probability endpoint. -/
lemma prob_le_exp_of_le_negLog {p : Prob} {x : ℝ}
    (h : ENNReal.ofReal x ≤ Prob.negLog p) :
    (p : ℝ) ≤ Real.exp (-x) := by
  by_cases hp : p = 0
  · simp [hp, (Real.exp_pos _).le]
  have hfinite : Prob.negLog p ≠ ⊤ := by simpa using hp
  have hh := ENNReal.toReal_mono hfinite h
  rw [Prob.negLog_pos_Real] at hh
  have hx : x ≤ -Real.log (p : ℝ) := (le_max_left x 0).trans hh
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 (by
    intro hh
    exact hp (Subtype.ext hh.symm))
  rw [← Real.exp_log hp0]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Faithful ordinary Stein gives an actual exponential bound on the optimal
finite-copy type-II probability, at every strictly subcritical rate. -/
theorem faithful_eventually_beta_le_exp (rho sigma : MState d)
    (hfaithful : sigma.m.PosDef) {epsilon : Prob}
    (hepsilon : 0 < epsilon ∧ epsilon < 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (qRelativeEnt rho sigma).toReal) :
    ∀ᶠ n : ℕ in atTop,
      (OptimalHypothesisRate (rho.npow n) epsilon {sigma.npow n} : ℝ) ≤
        Real.exp (-(n : ℝ) * r) := by
  have hfinite : qRelativeEnt rho sigma ≠ ⊤ := by
    apply qRelativeEnt_ne_top_iff.mpr
    let _ : sigma.M.NonSingular := HermitianMat.nonSingular_of_posDef hfaithful
    simp [HermitianMat.nonSingular_ker_bot]
  have hr' : ENNReal.ofReal r < qRelativeEnt rho sigma :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr0 hfinite).mpr hr
  have hevent := (faithful_state_stein rho sigma hfaithful hepsilon).eventually
    (eventually_gt_nhds hr')
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  rw [neg_mul]
  apply prob_le_exp_of_le_negLog
  have hm := (ENNReal.lt_div_iff_mul_lt
    (Or.inl (by exact_mod_cast (ne_of_gt hn0))) (Or.inl (by finiteness))).mp hn
  have hcast : ENNReal.ofReal ((n : ℝ) * r) = ENNReal.ofReal r * (n : ENNReal) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, mul_comm]
  simpa only [hcast] using hm.le

/-- Kernel filling shifts the finite real-valued entropy by precisely ln(c). -/
lemma faithfulFill_entropy_toReal_shift (rho sigma : MState d)
    (hsupport : sigma.M.ker ≤ rho.M.ker) :
    (qRelativeEnt rho (faithfulFill sigma)).toReal =
      (qRelativeEnt rho sigma).toReal + Real.log (fillingConstant sigma) := by
  have h := congrArg EReal.toReal (qRelativeEnt_faithfulFill_shift rho sigma hsupport)
  have hfinite : (qRelativeEnt rho sigma : EReal) ≠ ⊤ := by
    intro hh
    exact (qRelativeEnt_ne_top_iff.mpr hsupport) (EReal.coe_ennreal_eq_top_iff.mp hh)
  simpa only [EReal.toReal_coe_ennreal,
    EReal.toReal_add hfinite (EReal.coe_ennreal_ne_bot _) (EReal.coe_ne_top _)
      (EReal.coe_ne_bot _), EReal.toReal_coe] using h

/-- Singular supported alternatives admit actual positive tests with the
usual direct Stein exponent. The kernel-filled entropy shift cancels exactly
against the tensor domination factor. -/
theorem supported_state_stein_direct (rho sigma : MState d)
    (hsupport : sigma.M.ker ≤ rho.M.ker) {epsilon : Prob}
    (hepsilon : 0 < epsilon ∧ epsilon < 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (qRelativeEnt rho sigma).toReal) :
    ∀ᶠ n : ℕ in atTop, ∃ T : HermitianMat (Fin n → d) ℂ,
      0 ≤ T ∧ T ≤ 1 ∧ (rho.npow n).exp_val (1 - T) ≤ epsilon ∧
        (sigma.npow n).exp_val T ≤ Real.exp (-(n : ℝ) * r) := by
  let c := fillingConstant sigma
  let tau := faithfulFill sigma
  have hc : 0 < c := fillingConstant_pos sigma
  have hlog : 0 ≤ Real.log c := Real.log_nonneg (one_le_fillingConstant sigma)
  have hrate : r + Real.log c < (qRelativeEnt rho tau).toReal := by
    rw [faithfulFill_entropy_toReal_shift rho sigma hsupport]
    change r + Real.log c < (qRelativeEnt rho sigma).toReal + Real.log c
    linarith
  have hevent := faithful_eventually_beta_le_exp rho tau (faithfulFill_posDef sigma)
    hepsilon (add_nonneg hr0 hlog) hrate
  filter_upwards [hevent] with n hn
  obtain ⟨T, hopt, _⟩ := OptimalHypothesisRate.exists_min' (rho.npow n) epsilon {tau.npow n}
  have hopt' : (tau.npow n).exp_val T =
      (OptimalHypothesisRate (rho.npow n) epsilon {tau.npow n} : ℝ) := by
    have hh := congrArg (fun p : Prob => (p : ℝ)) hopt
    simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left] using hh
  refine ⟨T, T.2.2.1, T.2.2.2, T.2.1, ?_⟩
  calc
    (sigma.npow n).exp_val T ≤ c ^ n * (tau.npow n).exp_val T :=
      npow_test_domination sigma tau hc.le (domination_by_faithfulFill sigma) n T T.2.2.1
    _ ≤ c ^ n * Real.exp (-(n : ℝ) * (r + Real.log c)) := by
      rw [hopt']
      exact mul_le_mul_of_nonneg_left hn (pow_nonneg hc.le _)
    _ = Real.exp (-(n : ℝ) * r) := by
      have hp : c ^ n = Real.exp ((n : ℝ) * Real.log c) := by
        rw [Real.exp_nat_mul, Real.exp_log hc]
      rw [hp, ← Real.exp_add]
      congr 1
      ring

/-- The direct state-Stein estimate in base-two units used by the channel paper. -/
theorem supported_state_stein_direct_base_two (rho sigma : MState d)
    (hsupport : sigma.M.ker ≤ rho.M.ker) {epsilon : Prob}
    (hepsilon : 0 < epsilon ∧ epsilon < 1) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < (qRelativeEnt rho sigma).toReal / Real.log 2) :
    ∀ᶠ n : ℕ in atTop, ∃ T : HermitianMat (Fin n → d) ℂ,
      0 ≤ T ∧ T ≤ 1 ∧ (rho.npow n).exp_val (1 - T) ≤ epsilon ∧
        (sigma.npow n).exp_val T ≤ (2 : ℝ) ^ (-(n : ℝ) * R) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := supported_state_stein_direct rho sigma hsupport hepsilon
    (mul_nonneg hR0 hlog.le) ((lt_div_iff₀ hlog).mp hR)
  filter_upwards [h] with n hn
  obtain ⟨T, hT0, hT1, herror, htypeII⟩ := hn
  refine ⟨T, hT0, hT1, herror, ?_⟩
  convert htypeII using 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The optimal testing probability inherits the proved actual-test bound. -/
theorem supported_eventually_beta_le_exp (rho sigma : MState d)
    (hsupport : sigma.M.ker ≤ rho.M.ker) {epsilon : Prob}
    (hepsilon : 0 < epsilon ∧ epsilon < 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (qRelativeEnt rho sigma).toReal) :
    ∀ᶠ n : ℕ in atTop,
      (OptimalHypothesisRate (rho.npow n) epsilon {sigma.npow n} : ℝ) ≤
        Real.exp (-(n : ℝ) * r) := by
  filter_upwards [supported_state_stein_direct rho sigma hsupport hepsilon hr0 hr]
    with n hn
  obtain ⟨T, hT0, hT1, hI, hII⟩ := hn
  have hbeta := OptimalHypothesisRate.singleton_le_exp_val (σ := sigma.npow n) T hI ⟨hT0, hT1⟩
  exact le_trans hbeta hII

end StateSteinAudit
