import QuantumChannelStein.SandwichedTraceHolder
import QuantumChannelStein.BinaryDataProcessing

/-! # Zero cases, positive log arguments, and actual Rényi bounds

These results certify that the supported state formula never applies the
logarithm to zero. Nonnegativity follows from the proved Rényi DPI applied
to an actual constant binary measurement.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix RelativeEntropy
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

theorem quasi_zero_left (α : ℝ) (hα : α ≠ 0) (B : Operator n) : quasi α 0 B = 0 := by
  simp only [quasi, sandwichedOperator, Matrix.mul_zero, Matrix.zero_mul,
    CFC.zero_rpow hα, Matrix.trace_zero, Complex.zero_re]

theorem quasi_eq_zero_iff_of_support (α : ℝ) (hα : 1 < α) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    quasi α A B = 0 ↔ A = 0 := by
  constructor
  · intro hq
    let X := sandwichedOperator α A B
    have hX : X.PosSemidef := sandwichedOperator_positive α hA
    have hz : X = 0 := (powerTrace_eq_zero_iff X hX α (by linarith)).mp hq
    have ht := trace_sandwiched_cancel α hα A B hB hs
    change (X * CFC.rpow B ((α - 1) / α)).trace = A.trace at ht
    rw [hz, Matrix.zero_mul, Matrix.trace_zero] at ht
    exact hA.trace_eq_zero_iff.mp ht.symm
  · rintro rfl
    exact quasi_zero_left α (by linarith) B

theorem quasi_pos_of_support (α : ℝ) (hα : 1 < α) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hA0 : A ≠ 0)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) : 0 < quasi α A B :=
  lt_of_le_of_ne (quasi_nonneg α A B)
    (Ne.symm (mt (quasi_eq_zero_iff_of_support α hα A B hA hB hs).mp hA0))

theorem state_quasi_pos (α : ℝ) (hα : 1 < α) (ρ σ : State n)
    (hs : supportIncluded ρ σ) : 0 < quasi α ρ.matrix σ.matrix := by
  apply quasi_pos_of_support α hα ρ.matrix σ.matrix ρ.positive σ.positive _ hs
  intro hz
  have ht := ρ.trace_one
  rw [hz, Matrix.trace_zero] at ht
  exact zero_ne_one ht

theorem quasi_self (α : ℝ) (hα : 1 < α) (B : Operator n) (hB : B.PosSemidef) :
    quasi α B B = B.trace.re := by
  have ha0 : 0 < α := by linarith
  have h := CFC.rpow_rpow_of_exponent_nonneg B (1 / α) α
    (one_div_nonneg.mpr ha0.le) ha0.le hB.nonneg
  have hh : CFC.rpow (CFC.rpow B (1 / α)) α = B := by
    simpa only [CFC.rpow_eq_pow, show (1 / α) * α = 1 by field_simp,
      CFC.rpow_one B hB.nonneg] using h
  rw [quasi, sandwich_self_eq_rpow α hα B hB, hh]

@[simp] theorem renyi_self (α : ℝ) (hα : 1 < α) (ρ : State n) : renyi α hα ρ ρ = 0 := by
  rw [renyi_of_supportIncluded _ _ _ _ (supportIncluded_refl ρ), quasi_self α hα ρ.matrix ρ.positive,
    ρ.trace_one]
  simp

theorem renyi_nonneg (α : ℝ) (hα : 1 < α) (ρ σ : State n) : 0 ≤ renyi α hα ρ σ := by
  let T : Effect n := ⟨0, Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one : (1 : Operator n).PosSemidef)⟩
  have h := renyi_data_processing α hα (BinaryMeasurement.channel T) ρ σ
  simpa [BinaryMeasurement.channel_onState, Effect.probability, T] using h

theorem renyi_lt_top_iff (α : ℝ) (hα : 1 < α) (ρ σ : State n) :
    renyi α hα ρ σ < ⊤ ↔ supportIncluded ρ σ := by
  classical
  by_cases hs : supportIncluded ρ σ <;> simp [renyi, hs]

/-- A real quasi-bound becomes a genuine logarithmic Rényi bound. -/
theorem renyi_le_of_quasi_le (α : ℝ) (hα : 1 < α) (ρ σ : State n)
    (hs : supportIncluded ρ σ) (Q : ℝ) (hQ : quasi α ρ.matrix σ.matrix ≤ Q) :
    renyi α hα ρ σ ≤ (Real.logb 2 Q / (α - 1) : ℝ) := by
  rw [renyi_of_supportIncluded _ _ _ _ hs]
  apply EReal.coe_le_coe_iff.mpr
  exact div_le_div_of_nonneg_right
    (Real.logb_le_logb_of_le (by norm_num) (state_quasi_pos α hα ρ σ hs) hQ)
    (sub_pos.mpr hα).le

/-- For orders through two, actual PSD domination gives the explicit Rényi bound. -/
theorem renyi_le_log2_of_domination (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (ρ σ : State n) (t : ℝ) (ht : 1 ≤ t)
    (hdom : (t • σ.matrix - ρ.matrix).PosSemidef) : renyi α hα ρ σ ≤ (Real.logb 2 t : EReal) := by
  have hs : supportIncluded ρ σ := SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive hdom
  have hQ := quasi_le_of_domination α hα hα2 ρ.matrix σ.matrix ρ.positive σ.positive
    t (zero_le_one.trans ht) hdom
  rw [ρ.trace_one, Complex.one_re, mul_one] at hQ
  have h := renyi_le_of_quasi_le α hα ρ σ hs _ hQ
  rw [Real.logb_rpow_eq_mul_logb_of_pos (zero_lt_one.trans_le ht)] at h
  have he : (α - 1) * Real.logb 2 t / (α - 1) = Real.logb 2 t := by
    field_simp [(sub_pos.mpr hα).ne']
  rwa [he] at h

end QuantumChannelStein.SandwichedRenyi
