import QuantumChannelStein.CPOrder
import QuantumChannelStein.Testing

/-! # Testing consequences of CP domination -/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder
open Matrix

/-- Complete positivity entails positivity without a reference. -/
theorem MatrixMap.apply_positive {n m : ℕ} (Φ : MatrixMap n m)
    (hΦ : MatrixMap.CompletelyPositive Φ) {X : Operator n} (hX : X.PosSemidef) :
    (Φ X).PosSemidef := by
  obtain ⟨K, rfl⟩ := MatrixMap.exists_ofKraus_of_choi_positive Φ
    (MatrixMap.choi_positive_of_completelyPositive Φ hΦ)
  change (∑ i, K i * X * (K i)ᴴ).PosSemidef
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro i _
    exact hX.mul_mul_conjTranspose_same _

/-- CP domination is preserved when a positive input matrix is supplied. -/
theorem MatrixMap.cpLe_apply {n m : ℕ} {Φ Ψ : MatrixMap n m}
    (h : MatrixMap.CPLe Φ Ψ) {X : Operator n} (hX : X.PosSemidef) :
    (Ψ X - Φ X).PosSemidef :=
  MatrixMap.apply_positive (Ψ - Φ) h hX

/-- A positive effect respects CP domination of the two tested maps. -/
theorem test_bound_of_cp_domination {n m : ℕ} (Φ Ψ : MatrixMap n m)
    (T : Effect m) (ρ : State n) {c : ℝ}
    (h : MatrixMap.CPLe Φ ((c : ℂ) • Ψ)) :
    (T.matrix * Φ ρ.matrix).trace.re ≤ c * (T.matrix * Ψ ρ.matrix).trace.re := by
  have houtput := MatrixMap.cpLe_apply h ρ.positive
  have htest := trace_mul_nonnegative T.positive houtput
  have hre := (Complex.nonneg_iff.mp htest).1
  simpa [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
    Complex.mul_re] using hre

/-- For two trace-preserving maps on a nonempty state space, a domination
constant cannot be smaller than one, as used in Lemma 3.1. -/
theorem one_le_domination_constant {n m : ℕ} (Φ Ψ : MatrixMap n m)
    (hΦ : ∀ X, (Φ X).trace = X.trace) (hΨ : ∀ X, (Ψ X).trace = X.trace)
    (ρ : State n) {c : ℝ} (h : MatrixMap.CPLe Φ ((c : ℂ) • Ψ)) : 1 ≤ c := by
  have ht := (MatrixMap.cpLe_apply h ρ.positive).trace_nonneg
  have hre := (Complex.nonneg_iff.mp ht).1
  simpa [Matrix.trace_sub, Matrix.trace_smul, hΦ, hΨ, ρ.trace_one] using hre

end QuantumChannelStein
