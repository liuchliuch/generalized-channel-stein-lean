import GeneralizedChannelStein.LocalExpansion
import QuantumChannelStein.TensorExpansion
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

/-! Actual supported contraction expansions for the good-unitary region in Lemma 27. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.LocalTruncation
open QuantumChannelStein TensorPower TensorExpansion LocalExpansion Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def wordSites (k : ℕ) (w : Word k) : Finset (Fin k) :=
  Finset.univ.filter (fun l => indexEquiv Bool k w l = true)

theorem weight_eq_sum (k : ℕ) (w : Word k) :
    weight k w = ∑ l : Fin k, if indexEquiv Bool k w l then 1 else 0 := by
  induction k with
  | zero => simp [weight]
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp [weight, ih]

theorem wordSites_card (k : ℕ) (w : Word k) : (wordSites k w).card = weight k w := by
  rw [weight_eq_sum]
  rw [Finset.card_eq_sum_ones]
  simp only [wordSites, Finset.sum_filter]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem wordTensor_apply_prod (A H : Matrix ι ι ℂ) (k : ℕ) (w : Word k)
    (x y : Index ι k) :
    wordTensor A H k w x y = ∏ l : Fin k,
      (if indexEquiv Bool k w l then H else A) (indexEquiv ι k x l) (indexEquiv ι k y l) := by
  induction k with
  | zero => simp [wordTensor,tensorPower]
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    change (if w.1 then H else A) x.1 y.1 * wordTensor A H k w.2 x.2 y.2 = _
    rw [ih]
    simp

def finWord (H : Matrix ι ι ℂ) (k : ℕ) (w : Word k) : Block ι k :=
  Matrix.reindex (indexEquiv ι k) (indexEquiv ι k) (wordTensor 1 H k w)

omit [Fintype ι] [Nonempty ι] in
theorem finWord_apply (H : Matrix ι ι ℂ) (k : ℕ) (w : Word k) (x y : Fin k → ι) :
    finWord H k w x y = ∏ l : Fin k,
      (if indexEquiv Bool k w l then H (x l) (y l) else if x l=y l then 1 else 0) := by
  simp [finWord, Matrix.reindex_apply, wordTensor_apply_prod, Matrix.ite_apply, Matrix.one_apply]

omit [Nonempty ι] in
theorem finWord_supported (H : Matrix ι ι ℂ) (k : ℕ) (w : Word k) :
    SupportedOn (wordSites k w) (finWord H k w) := by
  let S := wordSites k w
  let B : Matrix (LocalIndex ι S) (LocalIndex ι S) ℂ := fun x y => ∏ i, H (x i) (y i)
  refine ⟨B, ?_⟩
  ext x y
  rw [finWord_apply, embed_apply]
  have hc (l : Fin k) : l ∈ S ↔ indexEquiv Bool k w l = true := by simp [S,wordSites]
  have he : (∏ l : Fin k, if indexEquiv Bool k w l then H (x l) (y l) else
      if x l=y l then 1 else 0) =
      (∏ l : {i // i∈S}, H (x l) (y l)) *
        ∏ l : {i // i∉S}, (if x l=y l then (1:ℂ) else 0) := by
    conv_lhs => rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i∈S)]
    congr 1
    · apply Finset.prod_congr (by ext; simp)
      intro i _
      rw [if_pos ((hc i).1 i.property)]
    · apply Finset.prod_congr (by ext; simp)
      intro i _
      rw [if_neg (fun h => i.property ((hc i).2 h))]
  rw [he]
  dsimp only [B]
  apply congrArg (fun z : ℂ => (∏ l : {i // i∈S}, H (x l) (y l))*z)
  split_ifs with hxy
  · apply Finset.prod_eq_one
    intro i _
    simp [congrFun hxy i]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem finWord_contraction (B : Matrix ι ι ℂ) (hB : ‖B‖ ≤ 1) (k : ℕ) (w : Word k) :
    ‖finWord B k w‖ ≤ 1 := by
  rw [finWord, TensorPower.norm_reindex]
  have hc : wordCost 1 1 k w = 1 := by
    induction k with
    | zero => rfl
    | succ k ih => simpa [wordCost] using ih w.2
  have h := norm_wordTensor_le_cost (1 : Matrix ι ι ℂ) B (by simp : ‖(1:Matrix ι ι ℂ)‖≤1) hB k w
  simpa [hc] using h

omit [Fintype ι] [Nonempty ι] in
theorem wordTensor_residual_smul (B : Matrix ι ι ℂ) (c : ℂ) (k : ℕ) (w : Word k) :
    wordTensor 1 (c • B) k w = c^(weight k w) • wordTensor 1 B k w := by
  induction k with
  | zero => simp [wordTensor,weight]
  | succ k ih =>
    rcases w with ⟨b,w⟩
    cases b <;> simp [wordTensor,weight,ih,Matrix.smul_kronecker,
      Matrix.kronecker_smul,smul_smul,pow_add,mul_comm]

omit [Fintype ι] [Nonempty ι] in
theorem finWord_residual_smul (B : Matrix ι ι ℂ) (c : ℂ) (k : ℕ) (w : Word k) :
    finWord (c • B) k w = c^(weight k w) • finWord B k w := by
  simp [finWord, wordTensor_residual_smul, Matrix.submatrix_smul]

def normalizedResidual (H : Matrix ι ι ℂ) (u : ℝ) : Matrix ι ι ℂ := (u⁻¹:ℂ) • H

omit [Nonempty ι] in
theorem normalizedResidual_contraction (H : Matrix ι ι ℂ) {u : ℝ} (hH : ‖H‖≤u) :
    ‖normalizedResidual H u‖≤1 := by
  have hu : 0 ≤ u := (norm_nonneg H).trans hH
  by_cases hz : u=0
  · simp [normalizedResidual,hz]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    simp only [normalizedResidual,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
    have hm := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hu)
    simpa [inv_mul_cancel₀ hz] using hm

omit [Nonempty ι] in
theorem residual_eq_scaled (H : Matrix ι ι ℂ) {u : ℝ} (hH : ‖H‖≤u) :
    H = (u:ℂ) • normalizedResidual H u := by
  by_cases hz : u=0
  · have hzero : H=0 := norm_le_zero_iff.mp (by simpa [hz] using hH)
    simp [hzero,hz,normalizedResidual]
  · simp [normalizedResidual,smul_smul,hz]

def truncationExpansion (H : Matrix ι ι ℂ) (u : ℝ) (hH : ‖H‖≤u) (k R : ℕ) : Expansion ι k where
  terms := {w : Word k // weight k w≤R}
  finiteTerms := inferInstance
  coeff w := (u:ℂ)^(weight k w.val)
  factor w := finWord (normalizedResidual H u) k w.val
  sites w := wordSites k w.val
  supported _ := finWord_supported _ _ _
  contraction _ := finWord_contraction _ (normalizedResidual_contraction H hH) _ _

theorem truncationExpansion_size (H : Matrix ι ι ℂ) (u : ℝ) (hH : ‖H‖≤u) (k R : ℕ) :
    (truncationExpansion H u hH k R).HasSize R := by
  intro w
  exact (wordSites_card k w.val).le.trans w.property

def truncation (H : Matrix ι ι ℂ) (k R : ℕ) : Block ι k :=
  Matrix.reindex (indexEquiv ι k) (indexEquiv ι k) (truncateAt 1 H k (R:ℝ))

theorem sum_subtype_eq_ite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype {x // p x}] (f : α → M) :
    (∑ x : {x // p x}, f x) = ∑ x, if p x then f x else 0 := by
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter p) (by simp) f).symm

theorem truncationExpansion_value (H : Matrix ι ι ℂ) (u : ℝ) (hH : ‖H‖≤u) (k R : ℕ) :
    (truncationExpansion H u hH k R).value = truncation H k R := by
  have hw (w : Word k) : (u:ℂ)^weight k w • finWord (normalizedResidual H u) k w = finWord H k w := by
    rw [← finWord_residual_smul, ← residual_eq_scaled H hH]
  simp only [Expansion.value,truncationExpansion,hw]
  rw [sum_subtype_eq_ite (fun w : Word k => weight k w≤R) (finWord H k)]
  ext x y
  simp [truncation,truncateAt,finWord,Matrix.reindex_apply,Matrix.sum_apply,
    Finset.sum_filter,Matrix.ite_apply]

theorem wordCost_one (u : ℝ) (k : ℕ) (w : Word k) : wordCost 1 u k w = u^weight k w := by
  induction k with
  | zero => simp [wordCost,weight]
  | succ k ih =>
    rcases w with ⟨b,w⟩
    cases b <;> simp [wordCost,weight,ih,pow_add]

theorem truncationExpansion_cost (H : Matrix ι ι ℂ) (u : ℝ) (hH : ‖H‖≤u) (k R : ℕ) :
    (truncationExpansion H u hH k R).cost ≤ Real.exp ((k:ℝ)*u) := by
  have hu := (norm_nonneg H).trans hH
  simp only [Expansion.cost,truncationExpansion,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hu]
  rw [sum_subtype_eq_ite (fun w : Word k => weight k w≤R) (fun w => u^weight k w)]
  calc
    _ ≤ ∑ w : Word k, u^weight k w := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact le_rfl
      · positivity
    _ = (1+u)^k := by simp only [← wordCost_one, sum_wordCost]
    _ ≤ (Real.exp u)^k := pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp u]) k
    _ = Real.exp ((k:ℝ)*u) := (Real.exp_nat_mul u k).symm

theorem truncation_error (H : Matrix ι ι ℂ) {u h : ℝ} (hH : ‖H‖≤u)
    (hh : 0 ≤ h) (k R : ℕ) (hR : Real.exp 2*(k:ℝ)*u+2*h ≤ (R:ℝ)) :
    ‖finTensorPower (1+H) k - truncation H k R‖ ≤ Real.exp (-h) := by
  have hu : 0 ≤ u := (norm_nonneg H).trans hH
  have he1 : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have he12 : Real.exp (1:ℝ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hbound := operator_truncation_bound (1:Matrix ι ι ℂ) H
    (by simp : ‖(1:Matrix ι ι ℂ)‖≤1) hH he1 k (R:ℝ)
  have hnorm : ‖finTensorPower (1+H) k - truncation H k R‖ =
      ‖tensorPower (1+H) k - truncateAt 1 H k (R:ℝ)‖ := by
    change ‖Matrix.reindex (indexEquiv ι k) (indexEquiv ι k)
      (tensorPower (1+H) k - truncateAt 1 H k (R:ℝ))‖ = _
    exact TensorPower.norm_reindex _ _ _
  rw [hnorm]
  apply hbound.trans
  have hexp : (Real.exp (1:ℝ)) ^ (-(R:ℝ)) = Real.exp (-(R:ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    simp
  rw [hexp]
  calc
    _ ≤ Real.exp (-(R:ℝ)) * (Real.exp (Real.exp 1*u))^k := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp (Real.exp 1*u)]
    _ = Real.exp (-(R:ℝ)+(k:ℝ)*(Real.exp 1*u)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (-h) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right he12 (mul_nonneg (Nat.cast_nonneg k) hu)
      nlinarith

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem finTensorPower_smul (A : Matrix ι ι ℂ) (c : ℂ) (k : ℕ) :
    finTensorPower (c • A) k = c^k • finTensorPower A k := by
  ext x y
  simp [finTensorPower_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

def phaseResidual (U : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ := z⁻¹ • U - 1

omit [Nonempty ι] in
theorem norm_phaseResidual (U : Matrix ι ι ℂ) {z : ℂ} (hz : ‖z‖=1) :
    ‖phaseResidual U z‖ = ‖U-z • (1:Matrix ι ι ℂ)‖ := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have he : phaseResidual U z = z⁻¹ • (U-z • (1:Matrix ι ι ℂ)) := by
    simp [phaseResidual,smul_sub,smul_smul,hz0]
  rw [he,norm_smul,norm_inv,hz]
  simp

def phaseTruncation (U : Matrix ι ι ℂ) (z : ℂ) (k R : ℕ) : Block ι k :=
  z^k • truncation (phaseResidual U z) k R

def phaseExpansion (U : Matrix ι ι ℂ) (z : ℂ) (u : ℝ)
    (hz : ‖z‖=1) (hU : ‖U-z • (1:Matrix ι ι ℂ)‖≤u) (k R : ℕ) : Expansion ι k :=
  (truncationExpansion (phaseResidual U z) u ((norm_phaseResidual U hz).le.trans hU) k R).scale (z^k)

theorem phaseExpansion_value (U : Matrix ι ι ℂ) (z : ℂ) (u : ℝ)
    (hz : ‖z‖=1) (hU : ‖U-z • (1:Matrix ι ι ℂ)‖≤u) (k R : ℕ) :
    (phaseExpansion U z u hz hU k R).value = phaseTruncation U z k R := by
  simp [phaseExpansion,phaseTruncation,truncationExpansion_value]

theorem phaseExpansion_size (U : Matrix ι ι ℂ) (z : ℂ) (u : ℝ)
    (hz : ‖z‖=1) (hU : ‖U-z • (1:Matrix ι ι ℂ)‖≤u) (k R : ℕ) :
    (phaseExpansion U z u hz hU k R).HasSize R :=
  Expansion.hasSize_scale _ (truncationExpansion_size _ _ _ _ _) _

theorem phaseExpansion_cost (U : Matrix ι ι ℂ) (z : ℂ) (u : ℝ)
    (hz : ‖z‖=1) (hU : ‖U-z • (1:Matrix ι ι ℂ)‖≤u) (k R : ℕ) :
    (phaseExpansion U z u hz hU k R).cost ≤ Real.exp ((k:ℝ)*u) := by
  simpa only [phaseExpansion,Expansion.cost_scale,norm_pow,hz,one_pow,one_mul] using
    truncationExpansion_cost (phaseResidual U z) u ((norm_phaseResidual U hz).le.trans hU) k R

theorem phaseTruncation_error (U : Matrix ι ι ℂ) {z : ℂ} {u h : ℝ}
    (hz : ‖z‖=1) (hU : ‖U-z • (1:Matrix ι ι ℂ)‖≤u)
    (hh : 0≤h) (k R : ℕ) (hR : Real.exp 2*(k:ℝ)*u+2*h≤(R:ℝ)) :
    ‖finTensorPower U k-phaseTruncation U z k R‖ ≤ Real.exp (-h) := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have he : U = z • (1+phaseResidual U z) := by
    simp [phaseResidual,smul_smul,hz0]
  have hpow : finTensorPower U k = z^k • finTensorPower (1+phaseResidual U z) k := by
    conv_lhs => rw [he]
    exact finTensorPower_smul _ _ _
  rw [hpow,phaseTruncation,← smul_sub,norm_smul,norm_pow,hz,one_pow,one_mul]
  exact truncation_error _ ((norm_phaseResidual U hz).le.trans hU) hh k R hR

omit [Fintype ι] [Nonempty ι] in
/-- Literal polynomial integrand: no choice of expansion occurs in this map. -/
theorem continuous_finWord (k : ℕ) (w : Word k) :
    Continuous (fun H : Matrix ι ι ℂ => finWord H k w) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  simp only [finWord_apply]
  apply continuous_finset_prod
  intro l _
  split_ifs <;> fun_prop

omit [Fintype ι] [Nonempty ι] in
theorem continuous_truncation (k R : ℕ) :
    Continuous (fun H : Matrix ι ι ℂ => truncation H k R) := by
  have he (H : Matrix ι ι ℂ) : truncation H k R =
      ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => weight k w≤R), finWord H k w := by
    ext x y
    simp [truncation,truncateAt,finWord,Matrix.reindex_apply,Matrix.sum_apply,Finset.sum_filter,Matrix.ite_apply]
  simp_rw [he]
  exact continuous_finset_sum _ (fun w _ => continuous_finWord k w)

omit [Nonempty ι] in
theorem measurable_phaseTruncation (k R : ℕ)
    [MeasurableSpace (Matrix ι ι ℂ)] [BorelSpace (Matrix ι ι ℂ)]
    [MeasurableSpace (Block ι k)] [BorelSpace (Block ι k)] :
    Measurable (fun p : Matrix ι ι ℂ × ℂ => phaseTruncation p.1 p.2 k R) := by
  have ht := (continuous_truncation (ι := ι) k R).measurable
  unfold phaseTruncation
  apply Measurable.smul
  · fun_prop
  · apply ht.comp
    unfold phaseResidual
    fun_prop

/-- Actual unitary input, explicit integrand, literal site supports, and exact budgets. -/
theorem good_unitary_local_approximation (U : Matrix.unitaryGroup ι ℂ)
    {z : ℂ} {u h : ℝ} (hz : ‖z‖=1)
    (hU : ‖U.val-z • (1:Matrix ι ι ℂ)‖≤u) (hh : 0≤h)
    (k R : ℕ) (hR : Real.exp 2*(k:ℝ)*u+2*h≤(R:ℝ)) :
    ∃ E : Expansion ι k, E.value=phaseTruncation U.val z k R ∧
      E.HasSize (min k R) ∧ E.cost≤Real.exp ((k:ℝ)*u) ∧
      ‖finTensorPower U.val k-E.value‖≤Real.exp (-h) := by
  refine ⟨phaseExpansion U.val z u hz hU k R, phaseExpansion_value _ _ _ _ _ _ _,
    Expansion.hasSize_min _ (phaseExpansion_size _ _ _ _ _ _ _),
    phaseExpansion_cost _ _ _ _ _ _ _, ?_⟩
  rw [phaseExpansion_value]
  exact phaseTruncation_error U.val hz hU hh k R hR

/-- The same explicit integrand in the recursive tensor coordinates. -/
def recursivePhaseTruncation (U : Matrix ι ι ℂ) (z : ℂ) (k R : ℕ) :
    Matrix (Index ι k) (Index ι k) ℂ :=
  z^k • truncateAt 1 (phaseResidual U z) k (R:ℝ)

theorem phaseTruncation_reindex (U : Matrix ι ι ℂ) (z : ℂ) (k R : ℕ) :
    phaseTruncation U z k R = Matrix.reindex (indexEquiv ι k) (indexEquiv ι k)
      (recursivePhaseTruncation U z k R) := by
  ext x y
  rfl

theorem recursivePhaseTruncation_error (U : Matrix ι ι ℂ) {z : ℂ} {u h : ℝ}
    (hz : ‖z‖=1) (hU : ‖U-z • (1:Matrix ι ι ℂ)‖≤u)
    (hh : 0≤h) (k R : ℕ) (hR : Real.exp 2*(k:ℝ)*u+2*h≤(R:ℝ)) :
    ‖tensorPower U k-recursivePhaseTruncation U z k R‖ ≤ Real.exp (-h) := by
  have he : ‖finTensorPower U k-phaseTruncation U z k R‖ =
      ‖tensorPower U k-recursivePhaseTruncation U z k R‖ := by
    rw [phaseTruncation_reindex]
    change ‖Matrix.reindex (indexEquiv ι k) (indexEquiv ι k)
      (tensorPower U k-recursivePhaseTruncation U z k R)‖ = _
    exact TensorPower.norm_reindex _ _ _
  rw [← he]
  exact phaseTruncation_error U hz hU hh k R hR

end GeneralizedChannelStein.LocalTruncation
