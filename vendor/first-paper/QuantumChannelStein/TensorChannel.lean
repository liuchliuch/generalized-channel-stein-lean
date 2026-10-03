import QuantumChannelStein.Kraus
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Concrete tensor products of quantum channels -/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder Kronecker
open Matrix

/-- Kronecker products commute with two finite sums. -/
theorem sum_kronecker_sum {ι κ m n r s : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Matrix m n ℂ) (B : κ → Matrix r s ℂ) :
    (∑ i, A i) ⊗ₖ (∑ j, B j) = ∑ i, ∑ j, A i ⊗ₖ B j := by
  ext ⟨a,c⟩ ⟨b,d⟩
  simp [Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

namespace KrausChannel
variable {n m a b : ℕ}

/-- Paired Kraus operators before canonical finite-index flattening. -/
def tensorKraus (Φ : KrausChannel n m) (Ψ : KrausChannel a b)
    (k : Fin Φ.rank × Fin Ψ.rank) :
    Matrix (Fin m × Fin b) (Fin n × Fin a) ℂ := Φ.kraus k.1 ⊗ₖ Ψ.kraus k.2

theorem tensorKraus_normalized (Φ : KrausChannel n m) (Ψ : KrausChannel a b) :
    (∑ k : Fin Φ.rank × Fin Ψ.rank, (tensorKraus Φ Ψ k)ᴴ * tensorKraus Φ Ψ k) = 1 := by
  simp only [tensorKraus, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Fintype.sum_prod_type]
  rw [← sum_kronecker_sum, Φ.normalized, Ψ.normalized, Matrix.one_kronecker_one]

/-- Actual independent tensor product channel, with paired Kraus slots and
canonical bijections `Fin p × Fin q ≃ Fin (p*q)`. -/
def tensor (Φ : KrausChannel n m) (Ψ : KrausChannel a b) : KrausChannel (n * a) (m * b) where
  rank := Φ.rank * Ψ.rank
  kraus k := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (tensorKraus Φ Ψ (finProdFinEquiv.symm k))
  normalized := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply, Matrix.conjTranspose_reindex]
    change (∑ k : Fin Φ.rank × Fin Ψ.rank,
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (tensorKraus Φ Ψ k)ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (tensorKraus Φ Ψ k)) = 1
    simp_rw [Matrix.reindexLinearEquiv_mul]
    rw [← map_sum, tensorKraus_normalized]
    exact Matrix.reindexLinearEquiv_one ℂ ℂ finProdFinEquiv


/-- Independent product inputs give the product of the two channel outputs. -/
theorem tensor_apply_product (Φ : KrausChannel n m) (Ψ : KrausChannel a b)
    (X : Operator n) (Y : Operator a) :
    (tensor Φ Ψ).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.apply X ⊗ₖ Ψ.apply Y) := by
  unfold apply
  change (∑ k : Fin (Φ.rank * Ψ.rank),
    Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorKraus Φ Ψ (finProdFinEquiv.symm k)) *
      Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y) *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorKraus Φ Ψ (finProdFinEquiv.symm k)))ᴴ) = _
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Matrix.conjTranspose_reindex]
  change (∑ k : Fin Φ.rank × Fin Ψ.rank,
    Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (tensorKraus Φ Ψ k) *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y) *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (tensorKraus Φ Ψ k)ᴴ) = _
  simp_rw [Matrix.reindexLinearEquiv_mul]
  rw [← map_sum]
  apply congrArg (fun M : Matrix (Fin m × Fin b) (Fin m × Fin b) ℂ =>
    Matrix.reindex finProdFinEquiv finProdFinEquiv M)
  change (∑ k : Fin Φ.rank × Fin Ψ.rank,
    tensorKraus Φ Ψ k * (X ⊗ₖ Y) * (tensorKraus Φ Ψ k)ᴴ) =
    (∑ i, Φ.kraus i * X * (Φ.kraus i)ᴴ) ⊗ₖ (∑ j, Ψ.kraus j * Y * (Ψ.kraus j)ᴴ)
  simp only [tensorKraus, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Fintype.sum_prod_type]
  exact (sum_kronecker_sum (fun i : Fin Φ.rank => Φ.kraus i * X * (Φ.kraus i)ᴴ)
    (fun j : Fin Ψ.rank => Ψ.kraus j * Y * (Ψ.kraus j)ᴴ)).symm


/-- Identity channel with one Kraus slot. -/
def identity (n : ℕ) : KrausChannel n n where
  rank := 1
  kraus _ := 1
  normalized := by simp

@[simp] theorem identity_apply (n : ℕ) (X : Operator n) : (identity n).apply X = X := by
  simp [identity, apply]

/-- Transport only the numerical dimension equalities; matrix entries and
Kraus slots are unchanged. -/
def cast {n' m' : ℕ} (Φ : KrausChannel n m) (hn : n = n') (hm : m = m') : KrausChannel n' m' := by
  cases hn
  cases hm
  exact Φ

@[simp] theorem cast_rank {n' m' : ℕ} (Φ : KrausChannel n m) (hn : n = n') (hm : m = m') :
    (Φ.cast hn hm).rank = Φ.rank := by cases hn; cases hm; rfl

/-- Independent repeated channel uses, with a one-dimensional identity for
zero uses and actual tensor products at each successor. -/
def tensorPower (Φ : KrausChannel n m) : (k : ℕ) → KrausChannel (n ^ k) (m ^ k)
  | 0 => identity 1
  | k + 1 => (tensor Φ (tensorPower Φ k)).cast (by rw [Nat.pow_succ']) (by rw [Nat.pow_succ'])

@[simp] theorem tensorPower_rank (Φ : KrausChannel n m) (k : ℕ) :
    (tensorPower Φ k).rank = Φ.rank ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tensorPower, tensor, ih, Nat.pow_succ']

end KrausChannel


end QuantumChannelStein
