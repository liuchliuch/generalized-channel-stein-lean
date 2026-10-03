import GeneralizedChannelStein.LocalExpansion
import GeneralizedChannelStein.BranchExtraction

/-! Finite local Neumann correction, with exact support and coefficient cost. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CorrectionPolynomial
open QuantumChannelStein Matrix LocalExpansion
open scoped BigOperators Matrix.Norms.L2Operator
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {k : ℕ}

/-- Multiplication of literal local expansions, including the empty product. -/
def powers (E : Expansion ι k) : ℕ → Expansion ι k
  | 0 => Expansion.one
  | j+1 => (powers E j).mul E

@[simp] theorem powers_value (E : Expansion ι k) (j : ℕ) : (powers E j).value=E.value^j := by
  induction j with
  | zero => simp [powers]
  | succ j ih => simp [powers,ih,pow_succ]

@[simp] theorem powers_cost (E : Expansion ι k) (j : ℕ) : (powers E j).cost=E.cost^j := by
  induction j with
  | zero => simp [powers]
  | succ j ih => simp [powers,ih,pow_succ]

theorem powers_size (E : Expansion ι k) {r : ℕ} (hE : E.HasSize r) (j : ℕ) :
    (powers E j).HasSize (j*r) := by
  induction j with
  | zero => simpa [powers] using Expansion.hasSize_one (ι:=ι) (k:=k) 0
  | succ j ih => simpa [Nat.succ_mul] using Expansion.hasSize_mul _ _ ih hE

def base (E : Expansion ι k) (lam : ℝ) : Expansion ι k :=
  Expansion.one.add (E.scale (-Complex.ofReal lam))

@[simp] theorem base_value (E : Expansion ι k) (lam : ℝ) :
    (base E lam).value=1-lam•E.value := by
  simp [base,sub_eq_add_neg,Complex.real_smul]

@[simp] theorem base_cost (E : Expansion ι k) (lam : ℝ) (hlam : 0≤lam) :
    (base E lam).cost=1+lam*E.cost := by
  simp [base,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlam]

theorem base_size (E : Expansion ι k) {r : ℕ} (hE : E.HasSize r) (lam : ℝ) :
    (base E lam).HasSize r := Expansion.hasSize_add _ _ (Expansion.hasSize_one r) (E.hasSize_scale hE _)

/-- Exact finite geometric correction polynomial of degree L. -/
def correction (E : Expansion ι k) (lam : ℝ) (L : ℕ) : Expansion ι k :=
  (Expansion.sum (fun j : Fin (L+1) => powers (base E lam) j)).scale (Complex.ofReal lam)

theorem correction_value (E : Expansion ι k) (lam : ℝ) (L : ℕ) :
    (correction E lam L).value=lam•∑ j : Fin (L+1), (1-lam•E.value)^j.val := by
  simp [correction,Complex.real_smul]

theorem correction_size (E : Expansion ι k) {r : ℕ} (hE : E.HasSize r) (lam : ℝ) (L : ℕ) :
    (correction E lam L).HasSize (L*r) := by
  apply Expansion.hasSize_scale
  apply Expansion.hasSize_sum
  intro j
  exact (powers_size _ (base_size E hE lam) j).mono (Nat.mul_le_mul_right r (Nat.le_of_lt_succ j.isLt))

theorem correction_cost (E : Expansion ι k) (lam : ℝ) (hlam : 0≤lam) (L : ℕ) :
    (correction E lam L).cost ≤ lam*(L+1)*(1+lam*E.cost)^L := by
  rw [correction,Expansion.cost_scale,Expansion.cost_sum]
  simp only [powers_cost,base_cost E lam hlam,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlam]
  calc
    _ ≤ lam*∑ _j : Fin (L+1), (1+lam*E.cost)^L := by
      apply mul_le_mul_of_nonneg_left _ hlam
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_right₀ (by nlinarith [mul_nonneg hlam E.cost_nonneg]) (Nat.le_of_lt_succ j.isLt)
    _ = _ := by simp; ring


/-- The finite geometric identity has no invertibility or spectral assumption. -/
theorem correction_residual (E : Expansion ι k) (lam : ℝ) (L : ℕ) :
    (correction E lam L).value * E.value - 1 = -(1-lam•E.value)^(L+1) := by
  rw [correction_value,Matrix.smul_mul]
  have h := geom_sum_mul (1-lam•E.value) (L+1)
  rw [← Fin.sum_univ_eq_sum_range] at h
  have hbase : (1-lam•E.value)-1 = -(lam•E.value) := by abel
  rw [hbase,Matrix.mul_neg,Matrix.mul_smul] at h
  have he := congrArg (fun Z => -Z-1) h
  simp only [neg_neg] at he
  rw [he]
  abel

/-- The geometric scalar budget, with no asymptotic or hidden cutoff. -/
theorem geometric_sum_le (q : ℝ) (hq : 0≤q) (hq1 : q<1) (N : ℕ) :
    (∑ j : Fin N, q^j.val) ≤ 1/(1-q) := by
  apply (le_div_iff₀ (by linarith : 0<1-q)).mpr
  have h := geom_sum_mul q N
  rw [← Fin.sum_univ_eq_sum_range] at h
  nlinarith [pow_nonneg hq N]

theorem correction_norm (E : Expansion ι k) (lam q : ℝ) (hlam : 0≤lam)
    (hq : 0≤q) (hq1 : q<1) (hbase : ‖1-lam•E.value‖≤q) (L : ℕ) :
    ‖(correction E lam L).value‖ ≤ lam/(1-q) := by
  rw [correction_value,norm_smul,Real.norm_eq_abs,abs_of_nonneg hlam]
  calc
    _ ≤ lam * ∑ j : Fin (L+1), q^j.val := by
      apply mul_le_mul_of_nonneg_left _ hlam
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
        (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hbase _))
    _ ≤ lam * (1/(1-q)) := mul_le_mul_of_nonneg_left (geometric_sum_le q hq hq1 _) hlam
    _ = _ := by ring

/-- Actual inverse correction against a nearby operator. -/
theorem correction_error (E : Expansion ι k) (X : Block ι k) (lam q ξ : ℝ)
    (hlam : 0≤lam) (hq : 0≤q) (hq1 : q<1) (hbase : ‖1-lam•E.value‖≤q)
    (hclose : ‖X-E.value‖≤ξ) (L : ℕ) (htail : q^(L+1)≤ξ) :
    ‖(correction E lam L).value*X-1‖ ≤ (lam/(1-q)+1)*ξ := by
  let G := (correction E lam L).value
  have hξ : 0≤ξ := (norm_nonneg _).trans hclose
  have heq : G*X-1=G*(X-E.value)+(G*E.value-1) := by noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖G*(X-E.value)‖+‖G*E.value-1‖ := norm_add_le _ _
    _ ≤ (lam/(1-q))*ξ+ξ := by
      apply add_le_add
      · exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul (correction_norm E lam q hlam hq hq1 hbase L) hclose (norm_nonneg _) (div_nonneg hlam (sub_pos.mpr hq1).le))
      · dsimp [G]
        rw [correction_residual,norm_neg]
        exact ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hbase _)).trans htail
    _ = _ := by ring

end GeneralizedChannelStein.CorrectionPolynomial
