import GeneralizedChannelStein.DominatedEntropyContinuity
import QuantumChannelStein.MatrixBlockCalculus
import QuantumChannelStein.RelativeEntropyReindex

/-! Literal flagged density operators and their relative entropy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.EntropyFlags
open QuantumChannelStein RelativeEntropy Matrix DominatedEntropyContinuity SpectralDecomposition
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

theorem spectralWeight_sum (ρ σ : State n) : ∑ i, DominatedEntropyContinuity.spectralWeight ρ σ i=1 := by
  have h := congrArg Complex.re (trace_unitary_conjugate σ.positive.isHermitian.eigenvectorUnitary ρ.matrix)
  rw [ρ.trace_one] at h
  simpa only [DominatedEntropyContinuity.spectralWeight,Matrix.trace,Matrix.diag,Complex.re_sum,Complex.one_re] using h

theorem trace_log_smul (ρ σ : State n) (hs : supportIncluded ρ σ) (c : ℝ) (hc : 0<c) :
    (ρ.matrix*cfc (Real.logb 2) (c•σ.matrix)).trace.re = Real.logb 2 c + crossEntropy ρ σ := by
  have hf : ContinuousOn (Real.logb 2) ((fun x : ℝ => c*x) '' spectrum ℝ σ.matrix) :=
    (σ.matrix.finite_real_spectrum.image _).continuousOn _
  have hcomp : cfc (fun x : ℝ => Real.logb 2 (c*x)) σ.matrix = cfc (Real.logb 2) (c•σ.matrix) := by
    exact cfc_comp_smul c (Real.logb 2) σ.matrix hf σ.positive.isHermitian
  rw [← hcomp,trace_mul_cfc_eq_spectral]
  have heq (i : Fin n) : DominatedEntropyContinuity.spectralWeight ρ σ i * Real.logb 2 (c*σ.positive.isHermitian.eigenvalues i) =
      DominatedEntropyContinuity.spectralWeight ρ σ i * (Real.logb 2 c + Real.logb 2 (σ.positive.isHermitian.eigenvalues i)) := by
    by_cases hi : σ.positive.isHermitian.eigenvalues i=0
    · have hw := eigenbasis_weight_eq_zero_of_supportIncluded ρ σ hs i hi
      change DominatedEntropyContinuity.spectralWeight ρ σ i=0 at hw
      simp [hw]
    · rw [Real.logb_mul hc.ne' hi]
  change (∑ i, DominatedEntropyContinuity.spectralWeight ρ σ i * Real.logb 2 (c*σ.positive.isHermitian.eigenvalues i)) = _
  simp_rw [heq,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,spectralWeight_sum,one_mul,crossEntropy,trace_mul_spectralLog2]
  rfl

def rawFormula {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) : ℝ :=
  (A*(cfc (Real.logb 2) A-cfc (Real.logb 2) B)).trace.re

theorem rawFormula_smul (ρ σ : State n) (hs : supportIncluded ρ σ) (c : ℝ) (hc : 0<c) :
    rawFormula (c•ρ.matrix) (c•σ.matrix) = c*traceFormula ρ σ := by
  rw [rawFormula,Matrix.smul_mul,Matrix.mul_sub,Matrix.trace_smul,Matrix.trace_sub]
  simp only [Complex.smul_re,Complex.sub_re,smul_eq_mul]
  rw [trace_log_smul ρ ρ (supportIncluded_refl ρ) c hc,trace_log_smul ρ σ hs c hc]
  simp only [traceFormula,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,crossEntropy]
  ring

theorem rawFormula_state (ρ σ : State n) : rawFormula ρ.matrix σ.matrix=traceFormula ρ σ := by
  simp only [rawFormula,traceFormula,spectralLog2_eq_cfc]

theorem trace_blocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : (Matrix.fromBlocks A 0 0 B).trace=A.trace+B.trace := by
  simp [Matrix.trace,Matrix.diag,Fintype.sum_sum_type]

def flagState (ρ σ : State n) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : State (n+n) where
  matrix := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (p•ρ.matrix) 0 0 ((1-p)•σ.matrix))
  positive := (MatrixBlockCalculus.fromBlocks_positive _ _ (ρ.positive.smul hp)
    (σ.positive.smul (sub_nonneg.mpr hp1))).submatrix _
  trace_one := by
    rw [ChannelEntropy.trace_reindex_equiv,trace_blocks,Matrix.trace_smul,Matrix.trace_smul,
      ρ.trace_one,σ.trace_one]
    simp only [Complex.real_smul,mul_one]
    push_cast
    ring

theorem rawFormula_blocks {A B C D : Operator n}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (hD : D.IsHermitian) :
    rawFormula (Matrix.fromBlocks A 0 0 C) (Matrix.fromBlocks B 0 0 D) = rawFormula A B+rawFormula C D := by
  unfold rawFormula
  rw [MatrixBlockCalculus.cfc_fromBlocks A C hA hC,MatrixBlockCalculus.cfc_fromBlocks B D hB hD]
  have heq : Matrix.fromBlocks A 0 0 C *
      (Matrix.fromBlocks (cfc (Real.logb 2) A) 0 0 (cfc (Real.logb 2) C)-
       Matrix.fromBlocks (cfc (Real.logb 2) B) 0 0 (cfc (Real.logb 2) D)) =
      Matrix.fromBlocks (A*(cfc (Real.logb 2) A-cfc (Real.logb 2) B)) 0 0
        (C*(cfc (Real.logb 2) C-cfc (Real.logb 2) D)) := by
    simp only [Matrix.mul_sub,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero]
    ext i j <;> cases i <;> cases j <;> simp
  rw [heq,trace_blocks,Complex.add_re]

theorem rawFormula_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι≃κ) (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    rawFormula (Matrix.reindex e e A) (Matrix.reindex e e B)=rawFormula A B := by
  unfold rawFormula
  rw [cfc_reindex e A hA,cfc_reindex e B hB]
  change (((reindexHom e) A)*((reindexHom e) (cfc (Real.logb 2) A)-(reindexHom e) (cfc (Real.logb 2) B))).trace.re=_
  rw [← map_sub,← map_mul]
  exact congrArg Complex.re (ChannelEntropy.trace_reindex_equiv e _)

/-- Exact direct-sum trace identity with no invertibility requirement. -/
theorem traceFormula_flag (ρ₁ ρ₂ σ₁ σ₂ : State n)
    (h₁ : supportIncluded ρ₁ σ₁) (h₂ : supportIncluded ρ₂ σ₂)
    (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    traceFormula (flagState ρ₁ ρ₂ p hp.le hp1.le) (flagState σ₁ σ₂ p hp.le hp1.le) =
      p*traceFormula ρ₁ σ₁+(1-p)*traceFormula ρ₂ σ₂ := by
  rw [← rawFormula_state (flagState ρ₁ ρ₂ p hp.le hp1.le) (flagState σ₁ σ₂ p hp.le hp1.le)]
  rw [flagState,flagState,rawFormula_reindex]
  · rw [rawFormula_blocks (ρ₁.positive.smul hp.le).isHermitian (σ₁.positive.smul hp.le).isHermitian
      (ρ₂.positive.smul (sub_pos.mpr hp1).le).isHermitian (σ₂.positive.smul (sub_pos.mpr hp1).le).isHermitian,
      rawFormula_smul ρ₁ σ₁ h₁ p hp,rawFormula_smul ρ₂ σ₂ h₂ (1-p) (sub_pos.mpr hp1)]
  · exact (MatrixBlockCalculus.fromBlocks_positive _ _ (ρ₁.positive.smul hp.le)
      (ρ₂.positive.smul (sub_pos.mpr hp1).le)).isHermitian
  · exact (MatrixBlockCalculus.fromBlocks_positive _ _ (σ₁.positive.smul hp.le)
      (σ₂.positive.smul (sub_pos.mpr hp1).le)).isHermitian

theorem flag_domination_matrix (ρ₁ ρ₂ σ₁ σ₂ : State n) (K p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    K•(flagState σ₁ σ₂ p hp hp1).matrix-(flagState ρ₁ ρ₂ p hp hp1).matrix =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (p•(K•σ₁.matrix-ρ₁.matrix)) 0 0 ((1-p)•(K•σ₂.matrix-ρ₂.matrix))) := by
  ext i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  simp only [flagState,Matrix.sub_apply,Matrix.smul_apply,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  cases i <;> cases j <;> simp [Complex.real_smul,mul_sub,mul_comm,mul_left_comm,mul_assoc]

theorem flag_domination_iff (ρ₁ ρ₂ σ₁ σ₂ : State n) (K p : ℝ) (hp : 0<p) (hp1 : p<1) :
    (K•(flagState σ₁ σ₂ p hp.le hp1.le).matrix-(flagState ρ₁ ρ₂ p hp.le hp1.le).matrix).PosSemidef ↔
      (K•σ₁.matrix-ρ₁.matrix).PosSemidef ∧ (K•σ₂.matrix-ρ₂.matrix).PosSemidef := by
  rw [flag_domination_matrix]
  constructor
  · intro h
    have hL := h.submatrix (fun i : Fin n => finSumFinEquiv (Sum.inl i))
    have hR := h.submatrix (fun i : Fin n => finSumFinEquiv (Sum.inr i))
    have hL' : (p•(K•σ₁.matrix-ρ₁.matrix)).PosSemidef := by
      convert hL using 1
      ext i j
      simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
      rfl
    have hR' : ((1-p)•(K•σ₂.matrix-ρ₂.matrix)).PosSemidef := by
      convert hR using 1
      ext i j
      simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
      rfl
    constructor
    · have h := hL'.smul (inv_nonneg.mpr hp.le)
      simpa only [smul_smul,inv_mul_cancel₀ hp.ne',one_smul] using h
    · have h := hR'.smul (inv_nonneg.mpr (sub_pos.mpr hp1).le)
      simpa only [smul_smul,inv_mul_cancel₀ (sub_pos.mpr hp1).ne',one_smul] using h
  · rintro ⟨hL,hR⟩
    exact (MatrixBlockCalculus.fromBlocks_positive _ _ (hL.smul hp.le)
      (hR.smul (sub_pos.mpr hp1).le)).submatrix _

theorem domination_mono (ρ σ : State n) {K L : ℝ} (hKL : K≤L)
    (h : (K•σ.matrix-ρ.matrix).PosSemidef) : (L•σ.matrix-ρ.matrix).PosSemidef := by
  have hp := h.add (σ.positive.smul (sub_nonneg.mpr hKL))
  convert hp using 1
  module

/-- With positive weights the literal flagged support condition is exactly
the conjunction of its two component support conditions. -/
theorem support_flag_iff (ρ₁ ρ₂ σ₁ σ₂ : State n) (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    supportIncluded (flagState ρ₁ ρ₂ p hp.le hp1.le) (flagState σ₁ σ₂ p hp.le hp1.le) ↔
      supportIncluded ρ₁ σ₁ ∧ supportIncluded ρ₂ σ₂ := by
  constructor
  · intro h
    obtain ⟨K,hK,hdom⟩ := (supportIncluded_iff_exists_domination _ _).mp h
    obtain ⟨h₁,h₂⟩ := (flag_domination_iff ρ₁ ρ₂ σ₁ σ₂ K p hp hp1).mp hdom
    exact ⟨SupportDomination.ker_le_of_posSemidef_smul_sub ρ₁.positive h₁,
      SupportDomination.ker_le_of_posSemidef_smul_sub ρ₂.positive h₂⟩
  · rintro ⟨h₁,h₂⟩
    obtain ⟨K,hK,hdomK⟩ := (supportIncluded_iff_exists_domination _ _).mp h₁
    obtain ⟨L,hL,hdomL⟩ := (supportIncluded_iff_exists_domination _ _).mp h₂
    apply (supportIncluded_iff_exists_domination _ _).mpr
    refine ⟨max K L,hK.trans (le_max_left _ _),?_⟩
    apply (flag_domination_iff ρ₁ ρ₂ σ₁ σ₂ (max K L) p hp hp1).mpr
    exact ⟨domination_mono ρ₁ σ₁ (le_max_left _ _) hdomK,
      domination_mono ρ₂ σ₂ (le_max_right _ _) hdomL⟩

/-- Full flagged Umegaki identity, preserving infinite unsupported branches. -/
theorem umegaki_flag (ρ₁ ρ₂ σ₁ σ₂ : State n) (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    umegaki (flagState ρ₁ ρ₂ p hp.le hp1.le) (flagState σ₁ σ₂ p hp.le hp1.le) =
      (p:EReal)*umegaki ρ₁ σ₁+((1-p:ℝ):EReal)*umegaki ρ₂ σ₂ := by
  have hn₁ : (p:EReal)*umegaki ρ₁ σ₁ ≠ ⊥ := ne_of_gt
    (lt_of_lt_of_le EReal.bot_lt_zero (mul_nonneg (EReal.coe_nonneg.mpr hp.le) (umegaki_nonneg _ _)))
  have hn₂ : ((1-p:ℝ):EReal)*umegaki ρ₂ σ₂ ≠ ⊥ := ne_of_gt
    (lt_of_lt_of_le EReal.bot_lt_zero (mul_nonneg (EReal.coe_nonneg.mpr (sub_pos.mpr hp1).le) (umegaki_nonneg _ _)))
  by_cases h₁ : supportIncluded ρ₁ σ₁
  · by_cases h₂ : supportIncluded ρ₂ σ₂
    · rw [umegaki_of_supportIncluded _ _ ((support_flag_iff ρ₁ ρ₂ σ₁ σ₂ p hp hp1).mpr ⟨h₁,h₂⟩),
        traceFormula_flag ρ₁ ρ₂ σ₁ σ₂ h₁ h₂ p hp hp1,umegaki_of_supportIncluded _ _ h₁,
        umegaki_of_supportIncluded _ _ h₂,EReal.coe_add,EReal.coe_mul,EReal.coe_mul]
    · have hn : ¬supportIncluded (flagState ρ₁ ρ₂ p hp.le hp1.le) (flagState σ₁ σ₂ p hp.le hp1.le) :=
        fun h => h₂ ((support_flag_iff ρ₁ ρ₂ σ₁ σ₂ p hp hp1).mp h).2
      rw [umegaki_of_not_supportIncluded _ _ hn,umegaki_of_not_supportIncluded _ _ h₂,
        EReal.coe_mul_top_of_pos (sub_pos.mpr hp1),EReal.add_top_of_ne_bot hn₁]
  · have hn : ¬supportIncluded (flagState ρ₁ ρ₂ p hp.le hp1.le) (flagState σ₁ σ₂ p hp.le hp1.le) :=
      fun h => h₁ ((support_flag_iff ρ₁ ρ₂ σ₁ σ₂ p hp hp1).mp h).1
    rw [umegaki_of_not_supportIncluded _ _ hn,umegaki_of_not_supportIncluded _ _ h₁,
      EReal.coe_mul_top_of_pos hp,EReal.top_add_of_ne_bot hn₂]

end GeneralizedChannelStein.EntropyFlags
