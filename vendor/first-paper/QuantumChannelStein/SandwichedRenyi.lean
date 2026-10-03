import QuantumChannelStein.RelativeEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! # Finite matrix sandwiched quasi-divergence and Rényi divergence above one

The quasi-divergence is the actual unnormalized spectral trace. The Rényi
family is defined on normalized states and explicitly takes `1 < α`; its
extended-real value is infinity when the support condition fails. Scalar
logs are base two. All matrix norms in these definitions are irrelevant to
the numerical trace; they only supply the functional-calculus topology.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix RelativeEntropy
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : ℕ}

/-- Bundle the already specified L2 matrix C*-algebra structures. -/
local instance matrixCStar : CStarAlgebra (Operator n) where

/-- The real exponent in the two sandwich factors. -/
def sandwichExponent (α : ℝ) : ℝ := (1 - α) / (2 * α)

/-- The positive sandwiched operator, for positive input matrices. -/
def sandwichedOperator (α : ℝ) (A B : Operator n) : Operator n :=
  CFC.rpow B (sandwichExponent α) * A * CFC.rpow B (sandwichExponent α)

/-- Actual unnormalized sandwiched quasi-relative entropy. -/
def quasi (α : ℝ) (A B : Operator n) : ℝ :=
  (CFC.rpow (sandwichedOperator α A B) α).trace.re

/-- Support-aware base-two sandwiched Rényi divergence of density matrices,
with its intended domain `α > 1` explicit in the interface. -/
def renyi (α : ℝ) (_hα : 1 < α) (ρ σ : State n) : EReal := by
  classical
  exact if supportIncluded ρ σ then
    ((Real.logb 2 (quasi α ρ.matrix σ.matrix) / (α - 1) : ℝ) : EReal)
  else ⊤

theorem sandwichedOperator_positive (α : ℝ) {A B : Operator n} (hA : A.PosSemidef) :
    (sandwichedOperator α A B).PosSemidef := by
  have hP : (CFC.rpow B (sandwichExponent α)).PosSemidef := CFC.rpow_nonneg.posSemidef
  simpa only [sandwichedOperator, hP.isHermitian.eq] using
    hA.mul_mul_conjTranspose_same (CFC.rpow B (sandwichExponent α))

theorem quasi_nonneg (α : ℝ) (A B : Operator n) : 0 ≤ quasi α A B := by
  exact (Complex.nonneg_iff.mp (CFC.rpow_nonneg.posSemidef.trace_nonneg)).1

theorem renyi_of_supportIncluded (α : ℝ) (hα : 1 < α) (ρ σ : State n)
    (hs : supportIncluded ρ σ) :
    renyi α hα ρ σ = (Real.logb 2 (quasi α ρ.matrix σ.matrix) / (α - 1) : ℝ) := by
  simp only [renyi, if_pos hs]

theorem renyi_of_not_supportIncluded (α : ℝ) (hα : 1 < α) (ρ σ : State n)
    (hs : ¬supportIncluded ρ σ) : renyi α hα ρ σ = ⊤ := by
  simp only [renyi, if_neg hs]

theorem renyi_ne_bot (α : ℝ) (hα : 1 < α) (ρ σ : State n) : renyi α hα ρ σ ≠ ⊥ := by
  classical
  by_cases hs : supportIncluded ρ σ <;> simp [renyi, hs]

end QuantumChannelStein.SandwichedRenyi
