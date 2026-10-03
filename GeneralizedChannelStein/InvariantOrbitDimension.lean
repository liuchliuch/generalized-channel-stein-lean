import QuantumChannelStein.PermutationHistogram
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds

/-! # The sharp stars-and-bars dimension bound for the actual permutation commutant -/
noncomputable section
namespace GeneralizedChannelStein.InvariantOrbitDimension
open QuantumChannelStein TensorPower TensorPermutation Matrix
open scoped BigOperators

/-- A word's actual multiset, retaining its exact length. -/
def wordSym {α : Type*} {n : ℕ} (x : Fin n → α) : Sym α n :=
  ⟨Finset.univ.val.map x, by simp⟩

theorem count_wordSym {α : Type*} [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (a : α) :
    (wordSym x : Multiset α).count a = Fintype.card {i // x i = a} := by
  change Multiset.count a (Finset.univ.val.map x) = _
  rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def]
  congr 1
  exact Multiset.filter_congr (fun i hi => eq_comm)

theorem histogram_eq_of_wordSym_eq {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x y : Fin n → α) (h : wordSym x = wordSym y) : histogram x = histogram y := by
  funext a
  apply Fin.ext
  have hc := congrArg (fun s : Sym α n => (s : Multiset α).count a) h
  simpa only [count_wordSym] using hc

def pairSym {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (i j : Index ι n) : Sym (ι × ι) n :=
  wordSym (fun l => (indexEquiv ι n i l, indexEquiv ι n j l))

theorem invariant_entry_eq_of_pairSym {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : invariantAlgebra ι n) (i j i' j' : Index ι n)
    (h : pairSym n i j = pairSym n i' j') : A.val i j = A.val i' j' :=
  invariant_entry_eq_of_histogram n A i j i' j' (histogram_eq_of_wordSym_eq _ _ h)

/-- One actual entry per realizable multiset; impossible multisets contribute zero. -/
def symEvaluation (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    invariantAlgebra ι n →ₗ[ℂ] (Sym (ι × ι) n → ℂ) where
  toFun A h := if hx : ∃ ij : Index ι n × Index ι n, pairSym n ij.1 ij.2 = h then
    A.val (Classical.choose hx).1 (Classical.choose hx).2 else 0
  map_add' A B := by
    funext h
    simp only [Pi.add_apply]
    split_ifs <;> simp only [Subalgebra.coe_add, Matrix.add_apply, add_zero]
  map_smul' c A := by
    funext h
    simp only [Pi.smul_apply]
    split_ifs <;> simp only [Subalgebra.coe_smul, Matrix.smul_apply, smul_zero, RingHom.id_apply]

theorem symEvaluation_apply_pairSym {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : invariantAlgebra ι n) (i j : Index ι n) :
    symEvaluation ι n A (pairSym n i j) = A.val i j := by
  have hx : ∃ ij : Index ι n × Index ι n, pairSym n ij.1 ij.2 = pairSym n i j := ⟨⟨i,j⟩,rfl⟩
  simp only [symEvaluation, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
  exact invariant_entry_eq_of_pairSym n A _ _ i j (Classical.choose_spec hx)

theorem symEvaluation_injective (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    Function.Injective (symEvaluation ι n) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have hh := congrFun h (pairSym n i j)
  simpa only [symEvaluation_apply_pairSym] using hh

/-- Sharp commutant dimension, with the all-dimensions stars-and-bars convention. -/
theorem finrank_invariantAlgebra_le_choose (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    Module.finrank ℂ (invariantAlgebra ι n) ≤
      (Fintype.card ι * Fintype.card ι + n - 1).choose n := by
  have h := LinearMap.finrank_le_finrank_of_injective (symEvaluation_injective ι n)
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one, Sym.card_sym_eq_choose,
    Fintype.card_prod] using h

/-- The literal binomial constant in the paper for a positive local dimension. -/
theorem finrank_invariantAlgebra_le_binomial (d n : ℕ) (hd : 0 < d) :
    Module.finrank ℂ (invariantAlgebra (Fin d) n) ≤
      (n+d^2-1).choose (d^2-1) := by
  have h := finrank_invariantAlgebra_le_choose (Fin d) n
  simp only [Fintype.card_fin, ← pow_two] at h
  have hpos : 0 < d^2 := pow_pos hd _
  have heq : d^2+n-1 = n+(d^2-1) := by omega
  have heq' : n+d^2-1 = n+(d^2-1) := by omega
  rw [heq, Nat.choose_symm_add] at h
  simpa only [heq'] using h

/-- Positivity of the literal coefficient mass, including all boundary cases. -/
theorem binomial_mass_pos (d n : ℕ) :
    0 < (n+d^2-1).choose (d^2-1) :=
  Nat.choose_pos (Nat.sub_le_sub_right (Nat.le_add_left _ _) _)

/-- The elementary polynomial majorant used after the exact orbit count. -/
theorem binomial_mass_le_polynomial (d n : ℕ) :
    (n+d^2-1).choose (d^2-1) ≤ (n+d^2+1)^(d^2-1) := by
  exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)

/-- Positivity in the real scalar convention used for Haar coefficient bounds. -/
theorem binomial_mass_real_pos (d n : ℕ) :
    0 < (((n+d^2-1).choose (d^2-1) : ℕ) : ℝ) := by
  exact_mod_cast binomial_mass_pos d n

/-- The paper's polynomial majorant in real scalars. -/
theorem binomial_mass_real_le_polynomial (d n : ℕ) :
    (((n+d^2-1).choose (d^2-1) : ℕ) : ℝ) ≤
      ((n : ℝ)+(d : ℝ)^2+1)^(d^2-1) := by
  have h := binomial_mass_le_polynomial d n
  exact_mod_cast h

end GeneralizedChannelStein.InvariantOrbitDimension
