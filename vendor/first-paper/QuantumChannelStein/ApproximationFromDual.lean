import QuantumChannelStein.PositiveSplitting
import QuantumChannelStein.ExactComparison
import QuantumChannelStein.TestingSDP

/-! # Fixed-environment approximation from any feasible dual matrix
This proves the constructive lower-bound direction of Proposition 4.2
before taking the dual optimum. No duality theorem is assumed.
-/
noncomputable section
namespace QuantumChannelStein
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker

/-- Inverse of the fixed-environment column reshaping. -/
def columnsDilation {a b e : ℕ} (F : Matrix (Fin a × Fin b) (Fin e) ℂ) :
    Matrix (Fin b × Fin e) (Fin a) ℂ := fun x i => F (i, x.1) x.2

@[simp] theorem dilationColumns_columnsDilation {a b e : ℕ}
    (F : Matrix (Fin a × Fin b) (Fin e) ℂ) :
    dilationColumns (columnsDilation F) = F := rfl

theorem approximation_of_dual_feasible {a b eN eM : ℕ}
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (t : ℝ) (ht : 0 ≤ t)
    (Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hY : Y.PosSemidef)
    (hdom : (Y - (dilationColumns VN * (dilationColumns VN)ᴴ -
      t • (dilationColumns VM * (dilationColumns VM)ᴴ))).PosSemidef) :
    ∃ C : Matrix (Fin eN) (Fin eM) ℂ, ‖C‖ ≤ Real.sqrt t ∧
      ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖ ^ 2 ≤ ‖KrausChannel.traceOutput Y‖ := by
  let FN := dilationColumns VN
  let FM := dilationColumns VM
  have hA : (t • (FM * FMᴴ)).PosSemidef :=
    (posSemidef_self_mul_conjTranspose FM).smul ht
  obtain ⟨F₀, F₁, hF, h₀, h₁⟩ := exists_positive_gram_splitting FN
    (t • (FM * FMᴴ)) Y hA hY (by convert hdom using 1; dsimp [FN, FM]; abel)
  let V₀ := columnsDilation F₀
  let V₁ := columnsDilation F₁
  obtain ⟨C, hC, hnorm⟩ := exact_auxiliary_map_of_gram V₀ VM ht h₀
  refine ⟨C, hnorm, ?_⟩
  have hsplit : VN = V₀ + V₁ := by
    apply dilationColumns_injective
    exact hF
  have herr : VN - ((1 : Operator b) ⊗ₖ C) * VM = V₁ := by rw [← hC, hsplit]; abel
  rw [herr, ← norm_traceOutput_columns_gram V₁]
  change ‖KrausChannel.traceOutput (F₁ * F₁ᴴ)‖ ≤ ‖KrausChannel.traceOutput Y‖
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
  · exact (TestingSDP.traceOutput_positive (posSemidef_self_mul_conjTranspose F₁)).nonneg
  · have hh := TestingSDP.traceOutput_positive h₁
    have heq : KrausChannel.traceOutput (Y - F₁ * F₁ᴴ) =
        KrausChannel.traceOutput Y - KrausChannel.traceOutput (F₁ * F₁ᴴ) := by
      ext i j
      simp [KrausChannel.traceOutput, Finset.sum_sub_distrib]
    rw [heq] at hh
    exact sub_nonneg.mp hh.nonneg
end QuantumChannelStein
