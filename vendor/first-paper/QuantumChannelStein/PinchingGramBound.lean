import QuantumChannelStein.SandwichedSumBound

/-! # The finite Gram-sum inequality underlying spectral pinching -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SpectralPinching
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- A finite sum of Gram factors is dominated by cardinality times the sum of their Grams. -/
theorem gram_sum_le_card {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    [DecidableEq κ] (A : ι → Matrix κ η ℂ) :
    (((Fintype.card ι : ℝ) • ∑ i, A i * (A i)ᴴ) - (∑ i, A i) * (∑ i, A i)ᴴ).PosSemidef := by
  have hsum : (∑ i, ∑ j, (A i - A j) * (A i - A j)ᴴ).PosSemidef := by
    apply Finset.sum_induction
    · intro B C hB hC; exact hB.add hC
    · exact Matrix.PosSemidef.zero
    · intro i _
      apply Finset.sum_induction
      · intro B C hB hC; exact hB.add hC
      · exact Matrix.PosSemidef.zero
      · intro j _; exact Matrix.posSemidef_self_mul_conjTranspose _
  have hd₁ : (∑ i, ∑ _j : ι, A i * (A i)ᴴ) =
      (Fintype.card ι : ℝ) • ∑ i, A i * (A i)ᴴ := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  have hd₂ : (∑ _i : ι, ∑ j, A j * (A j)ᴴ) =
      (Fintype.card ι : ℝ) • ∑ i, A i * (A i)ᴴ := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  have hc₁ : (∑ i, ∑ j, A i * (A j)ᴴ) = (∑ i, A i) * (∑ i, A i)ᴴ := by
    simp only [Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum]
    exact Finset.sum_comm
  have hc₂ : (∑ i, ∑ j, A j * (A i)ᴴ) = (∑ i, A i) * (∑ i, A i)ᴴ := by
    rw [Finset.sum_comm]
    exact hc₁
  have he : (∑ i, ∑ j, (A i - A j) * (A i - A j)ᴴ) =
      (2 : ℝ) • (((Fintype.card ι : ℝ) • ∑ i, A i * (A i)ᴴ) - (∑ i, A i) * (∑ i, A i)ᴴ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
      Finset.sum_sub_distrib]
    rw [hd₁, hd₂, hc₁, hc₂]
    module
  have h := hsum.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [he, smul_smul] at h
  norm_num at h
  exact h

end QuantumChannelStein.SpectralPinching
