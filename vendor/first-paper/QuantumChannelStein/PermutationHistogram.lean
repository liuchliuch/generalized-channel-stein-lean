import QuantumChannelStein.TensorPermutation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Polynomially many simultaneous tensor-coordinate orbits
The histogram records the number of occurrences of each row/column pair.
Equal histograms are realized by a genuine permutation of the tensor factors.
-/
noncomputable section
namespace QuantumChannelStein.TensorPermutation
open TensorPower Matrix

/-- A word's multiplicity histogram, with the exact finite bound on counts. -/
def histogram {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (x : Fin k → ι) : ι → Fin (k + 1) := fun a =>
  ⟨Fintype.card {i // x i = a}, by
    have h := Fintype.card_subtype_le (fun i : Fin k => x i = a)
    simpa using Nat.lt_succ_of_le h⟩

/-- Equal multiplicities give a coordinate permutation matching both words. -/
theorem exists_permutation_of_histogram_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (x y : Fin k → ι) (h : histogram x = histogram y) :
    ∃ p : Equiv.Perm (Fin k), ∀ i, y (p i) = x i := by
  have hc (a : ι) : Fintype.card {i // x i = a} = Fintype.card {i // y i = a} :=
    congrArg Fin.val (congrFun h a)
  let e := fun a => Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- Histograms of pairs classify simultaneous row/column permutation orbits. -/
def pairHistogram {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (i j : Index ι k) : (ι × ι) → Fin (k + 1) :=
  histogram (fun l => (indexEquiv ι k i l, indexEquiv ι k j l))

theorem exists_permutation_of_pairHistogram_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (i j i' j' : Index ι k)
    (h : pairHistogram k i j = pairHistogram k i' j') :
    ∃ p : Equiv.Perm (Fin k),
      factorPermutation ι k p i = i' ∧ factorPermutation ι k p j = j' := by
  obtain ⟨p, hp⟩ := exists_permutation_of_histogram_eq
    (fun l => (indexEquiv ι k i l, indexEquiv ι k j l))
    (fun l => (indexEquiv ι k i' l, indexEquiv ι k j' l)) h
  refine ⟨p, ?_, ?_⟩
  · apply (indexEquiv ι k).injective
    funext l
    have hh := congrArg Prod.fst (hp (p.symm l))
    simpa using hh.symm
  · apply (indexEquiv ι k).injective
    funext l
    have hh := congrArg Prod.snd (hp (p.symm l))
    simpa using hh.symm

/-- An invariant matrix's entries depend only on the pair histogram. -/
theorem invariant_entry_eq_of_histogram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : invariantAlgebra ι k) (i j i' j' : Index ι k)
    (h : pairHistogram k i j = pairHistogram k i' j') : A.val i j = A.val i' j' := by
  obtain ⟨p, hi, hj⟩ := exists_permutation_of_pairHistogram_eq k i j i' j' h
  have ha := congrArg (fun M => M i' j') (A.property p)
  simpa [conjugation, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, ← hi, ← hj] using ha

/-- Sample one entry for each realizable histogram, zero for impossible ones. -/
def histogramEvaluation (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    invariantAlgebra ι k →ₗ[ℂ] (((ι × ι) → Fin (k + 1)) → ℂ) where
  toFun A h := if hx : ∃ ij : Index ι k × Index ι k,
      pairHistogram k ij.1 ij.2 = h then
    A.val (Classical.choose hx).1 (Classical.choose hx).2 else 0
  map_add' A B := by
    funext h
    simp only [Pi.add_apply]
    split_ifs <;> simp only [Subalgebra.coe_add, Matrix.add_apply, add_zero]
  map_smul' c A := by
    funext h
    simp only [Pi.smul_apply]
    split_ifs <;> simp only [Subalgebra.coe_smul, Matrix.smul_apply, smul_zero, RingHom.id_apply]

theorem histogramEvaluation_apply_histogram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : invariantAlgebra ι k) (i j : Index ι k) :
    histogramEvaluation ι k A (pairHistogram k i j) = A.val i j := by
  have hx : ∃ ij : Index ι k × Index ι k,
      pairHistogram k ij.1 ij.2 = pairHistogram k i j := ⟨⟨i,j⟩, rfl⟩
  simp only [histogramEvaluation, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
  exact invariant_entry_eq_of_histogram k A _ _ i j (Classical.choose_spec hx)

theorem histogramEvaluation_injective (ι : Type*) [Fintype ι] [DecidableEq ι]
    (k : ℕ) : Function.Injective (histogramEvaluation ι k) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have hh := congrFun h (pairHistogram k i j)
  simpa only [histogramEvaluation_apply_histogram] using hh

/-- The invariant operator algebra has polynomial, rather than exponential,
dimension in the number of tensor copies. -/
theorem finrank_invariantAlgebra_le (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Module.finrank ℂ (invariantAlgebra ι k) ≤
      (k + 1) ^ (Fintype.card ι * Fintype.card ι) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (histogramEvaluation_injective ι k)
  simpa [Module.finrank_pi, Fintype.card_fun, Fintype.card_prod] using h

end QuantumChannelStein.TensorPermutation
