import QuantumChannelStein.ChannelLocality
import QuantumChannelStein.ChannelPowerReindex
import QuantumChannelStein.RelativeEntropyReindex

/-! # Concrete serial composition and coordinate-control channels -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein
open Matrix
open scoped BigOperators Kronecker ComplexOrder

theorem State.eq_of_matrix_eq {d : ℕ} {ρ σ : State d} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

namespace KrausChannel
variable {a b c : ℕ}

/-- Actual serial composition, with paired products of normalized Kraus matrices. -/
def compose (Ψ : KrausChannel b c) (Φ : KrausChannel a b) : KrausChannel a c where
  rank := Ψ.rank * Φ.rank
  kraus k := Ψ.kraus (finProdFinEquiv.symm k).1 * Φ.kraus (finProdFinEquiv.symm k).2
  normalized := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Matrix.conjTranspose_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have h (j : Fin Φ.rank) :
        (∑ i : Fin Ψ.rank, (Φ.kraus j)ᴴ * (Ψ.kraus i)ᴴ * (Ψ.kraus i * Φ.kraus j)) =
          (Φ.kraus j)ᴴ * Φ.kraus j := by
      calc
        _ = (Φ.kraus j)ᴴ * (∑ i, (Ψ.kraus i)ᴴ * Ψ.kraus i) * Φ.kraus j := by
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = _ := by rw [Ψ.normalized, Matrix.mul_one]
    simp_rw [h]
    exact Φ.normalized

@[simp] theorem compose_apply (Ψ : KrausChannel b c) (Φ : KrausChannel a b) (X : Operator a) :
    (Ψ.compose Φ).apply X = Ψ.apply (Φ.apply X) := by
  unfold compose apply
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

@[simp] theorem compose_onState (Ψ : KrausChannel b c) (Φ : KrausChannel a b) (ρ : State a) :
    (Ψ.compose Φ).onState ρ = Ψ.onState (Φ.onState ρ) := by
  apply State.eq_of_matrix_eq
  exact compose_apply Ψ Φ ρ.matrix

/-- An actual one-Kraus coordinate permutation, implementing a Hilbert-space relabeling. -/
def coordinateChange (e : Fin a ≃ Fin b) : KrausChannel a b :=
  ChannelPowerReindex.reindexChannel (Equiv.refl _) e (identity a)

@[simp] theorem coordinateChange_apply (e : Fin a ≃ Fin b) (X : Operator a) :
    (coordinateChange e).apply X = Matrix.reindex e e X := by
  simpa only [coordinateChange, Matrix.reindex_refl_refl, identity_apply] using
    ChannelPowerReindex.reindexChannel_apply (Equiv.refl _) e (identity a) X

@[simp] theorem coordinateChange_onState (e : Fin a ≃ Fin b) (ρ : State a) :
    (coordinateChange e).onState ρ = ρ.reindex e := by
  apply State.eq_of_matrix_eq
  exact coordinateChange_apply e ρ.matrix

end KrausChannel
end QuantumChannelStein
