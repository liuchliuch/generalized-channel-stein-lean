import QuantumChannelStein.GeometricMeanSelf

/-! # Concrete finite witnesses for the supported geometric-mean program -/
noncomputable section
namespace QuantumChannelStein.SharpDivergence
open Matrix SupportedGeometricMean
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n : ℕ}

/-- Scalar domination gives an explicit feasible auxiliary, not just an existence axiom. -/
def feasibleOfDomination (p : ℝ) (hp : 0 < p) (A B : Operator n) (hB : B.PosSemidef)
    (c : ℝ) (hc : 0 < c) (hdom : A ≤ c • B) : Feasible p A B hB where
  matrix := (c ^ (1 / p)) • B
  positive := hB.smul (Real.rpow_nonneg hc.le _)
  supported := by
    intro x hx
    change B *ᵥ x = 0 at hx
    change ((c ^ (1 / p)) • B) *ᵥ x = 0
    rw [Matrix.smul_mulVec, hx, smul_zero]
  dominates := by
    rw [mean_scaled_self p (c ^ (1 / p)) hp (Real.rpow_nonneg hc.le _),
      ← Real.rpow_mul hc.le, one_div_mul_cancel hp.ne', Real.rpow_one]
    exact hdom

theorem quasi_finite_of_domination (p : ℝ) (hp : 0 < p) (A B : Operator n)
    (hB : B.PosSemidef) (c : ℝ) (hc : 0 < c) (hdom : A ≤ c • B) :
    quasi p A B hB < ⊤ :=
  (quasi_le_trace (feasibleOfDomination p hp A B hB c hc hdom)).trans_lt ENNReal.ofReal_lt_top

theorem quasi_finite_of_supported (p : ℝ) (hp : 0 < p) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    quasi p A B hB < ⊤ := by
  obtain ⟨c, hc, hdom⟩ := SupportDomination.exists_domination_of_ker_le hA hB hs
  exact quasi_finite_of_domination p hp A B hB c (zero_lt_one.trans_le hc)
    (sub_nonneg.mp hdom.nonneg)

end QuantumChannelStein.SharpDivergence
