import QuantumChannelStein.ChannelRepresentation

/-! # Completely positive order and Choi domination -/
noncomputable section
namespace QuantumChannelStein.MatrixMap
open scoped ComplexOrder
open Matrix
variable {n m : ℕ}

@[simp] theorem choi_add (Φ Ψ : MatrixMap n m) : choi (Φ + Ψ) = choi Φ + choi Ψ := rfl
@[simp] theorem choi_sub (Φ Ψ : MatrixMap n m) : choi (Φ - Ψ) = choi Φ - choi Ψ := rfl
@[simp] theorem choi_smul (c : ℂ) (Φ : MatrixMap n m) : choi (c • Φ) = c • choi Φ := rfl
@[simp] theorem choi_zero : choi (0 : MatrixMap n m) = 0 := rfl

/-- Complete-positive domination is positivity of the difference at every reference. -/
def CPLe (Φ Ψ : MatrixMap n m) : Prop := CompletelyPositive (Ψ - Φ)

/-- CP order is exactly the positive-semidefinite Choi difference condition. -/
theorem cpLe_iff_choi_difference (Φ Ψ : MatrixMap n m) :
    CPLe Φ Ψ ↔ (choi Ψ - choi Φ).PosSemidef := by
  rw [CPLe, completelyPositive_iff_choi_positive, choi_sub]

theorem cpLe_refl (Φ : MatrixMap n m) : CPLe Φ Φ := by
  rw [cpLe_iff_choi_difference, sub_self]
  exact Matrix.PosSemidef.zero

theorem cpLe_trans {Φ Ψ Ω : MatrixMap n m} (h₁ : CPLe Φ Ψ) (h₂ : CPLe Ψ Ω) :
    CPLe Φ Ω := by
  rw [cpLe_iff_choi_difference] at h₁ h₂ ⊢
  simpa only [sub_add_sub_cancel] using h₂.add h₁

theorem cpLe_antisymm {Φ Ψ : MatrixMap n m} (h₁ : CPLe Φ Ψ) (h₂ : CPLe Ψ Φ) :
    Φ = Ψ := by
  apply choi_injective
  open scoped MatrixOrder in
    exact le_antisymm ((cpLe_iff_choi_difference Φ Ψ).mp h₁)
      ((cpLe_iff_choi_difference Ψ Φ).mp h₂)

theorem cpLe_add {Φ₁ Φ₂ Ψ₁ Ψ₂ : MatrixMap n m}
    (h₁ : CPLe Φ₁ Ψ₁) (h₂ : CPLe Φ₂ Ψ₂) : CPLe (Φ₁ + Φ₂) (Ψ₁ + Ψ₂) := by
  rw [cpLe_iff_choi_difference] at h₁ h₂ ⊢
  rw [choi_add, choi_add]
  convert h₁.add h₂ using 1; abel

end QuantumChannelStein.MatrixMap
