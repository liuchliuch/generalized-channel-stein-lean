import QuantumChannelStein.PermutationHistogram
import QuantumChannelStein.InvariantSpectralBound
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! The literal span of unitary tensor powers and the permutation-invariant algebra. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.UnitaryPowerSpan
open QuantumChannelStein TensorPower TensorPermutation Matrix
open scoped BigOperators Matrix.Norms.L2Operator

abbrev TensorOperator (d n : ℕ) := Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ

def unitarySpan (d n : ℕ) : Submodule ℂ (TensorOperator d n) :=
  Submodule.span ℂ (Set.range (fun U : Matrix.unitaryGroup (Fin d) ℂ => tensorPower U.val n))

theorem functional_matrix_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (L : Matrix ι κ ℂ →ₗ[ℂ] ℂ) (A : Matrix ι κ ℂ) :
    L A = ∑ i, ∑ j, A i j * L (Matrix.single i j 1) := by
  have he : A = ∑ i, ∑ j, A i j • Matrix.single i j 1 := by
    ext i j
    simp [Matrix.sum_apply, Matrix.single, ite_and]
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, smul_eq_mul]

variable {σ : Type*}

def tensorScalarPolynomial (d n : ℕ) (L : TensorOperator d n →ₗ[ℂ] ℂ)
    (A : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)) : MvPolynomial σ ℂ :=
  ∑ i, ∑ j, (∏ l : Fin n, A (indexEquiv (Fin d) n i l) (indexEquiv (Fin d) n j l)) *
    MvPolynomial.C (L (Matrix.single i j 1))

theorem eval_tensorScalarPolynomial (d n : ℕ) (L : TensorOperator d n →ₗ[ℂ] ℂ)
    (A : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    MvPolynomial.eval z (tensorScalarPolynomial d n L A) =
      L (tensorPower (fun i j => MvPolynomial.eval z (A i j)) n) := by
  rw [functional_matrix_expansion]
  simp [tensorScalarPolynomial, tensorPower_apply_eq_prod]

def circlePoint (t : ℝ) : ℂ := (1+(t:ℂ)*Complex.I)/(1-(t:ℂ)*Complex.I)

private theorem circle_den_ne_zero (t : ℝ) : (1-(t:ℂ)*Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem norm_circlePoint (t : ℝ) : ‖circlePoint t‖ = 1 := by
  have hc : (1+(t:ℂ)*Complex.I : ℂ) = star (1-(t:ℂ)*Complex.I) := by simp
  rw [circlePoint, norm_div, hc, norm_star]
  exact div_self (norm_ne_zero_iff.mpr (circle_den_ne_zero t))

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro s t h
  have hh := (div_eq_div_iff (circle_den_ne_zero s) (circle_den_ne_zero t)).1 h
  have hi := congrArg Complex.im hh
  simp only [Complex.mul_im, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
    sub_zero, Complex.add_im, Complex.one_im, mul_one,
    Complex.sub_re, Complex.sub_im] at hi
  linarith

theorem unit_circle_infinite : Set.Infinite {z : ℂ | ‖z‖ = 1} := by
  exact (Set.infinite_range_of_injective circlePoint_injective).mono
    (by rintro z ⟨t,rfl⟩; exact norm_circlePoint t)

theorem diagonal_unitary {d : ℕ} (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    Matrix.diagonal z ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal z * (Matrix.diagonal z)ᴴ = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have he : (fun i => z i*star z i) = fun _ => (1:ℂ) := by
    funext i
    have := Complex.mul_conj (z i)
    simpa [Complex.normSq_eq_norm_sq, hz i] using this
  rw [he, Matrix.diagonal_one]

theorem diagonal_power_annihilated {d n : ℕ} (L : TensorOperator d n →ₗ[ℂ] ℂ)
    (hL : ∀ U : Matrix.unitaryGroup (Fin d) ℂ, L (tensorPower U.val n) = 0)
    (z : Fin d → ℂ) : L (tensorPower (Matrix.diagonal z) n) = 0 := by
  let P := tensorScalarPolynomial d n L (Matrix.diagonal (fun i => MvPolynomial.X i))
  have hP : P = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin d => {z : ℂ | ‖z‖ = 1})
      (fun _ => unit_circle_infinite)
    intro w hw
    rw [map_zero]
    have hd : (fun i j => MvPolynomial.eval w ((Matrix.diagonal (fun i => MvPolynomial.X i)) i j)) =
        Matrix.diagonal w := by
      ext i j
      by_cases h : i=j <;> simp [h]
    change MvPolynomial.eval w (tensorScalarPolynomial d n L _) = 0
    rw [eval_tensorScalarPolynomial, hd]
    exact hL ⟨Matrix.diagonal w, diagonal_unitary w (fun i => hw i (Set.mem_univ i))⟩
  have he := congrArg (MvPolynomial.eval z) hP
  change MvPolynomial.eval z (tensorScalarPolynomial d n L _) = _ at he
  rw [eval_tensorScalarPolynomial, map_zero] at he
  convert he using 1
  congr 2
  ext i j
  by_cases h : i=j <;> simp [h]

theorem diagonal_power_mem (d n : ℕ) (z : Fin d → ℂ) :
    tensorPower (Matrix.diagonal z) n ∈ unitarySpan d n := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).1
  intro L hL
  apply diagonal_power_annihilated L
  intro U
  exact (Submodule.mem_dualAnnihilator L).1 hL _ (Submodule.subset_span ⟨U,rfl⟩)

theorem unitary_power_mem (d n : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    tensorPower U.val n ∈ unitarySpan d n := Submodule.subset_span ⟨U,rfl⟩

theorem left_unitary_mul_mem {d n : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    {A : TensorOperator d n} (hA : A ∈ unitarySpan d n) :
    tensorPower U.val n*A ∈ unitarySpan d n := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨V,rfl⟩ := hA
    rw [← tensorPower_mul]
    exact unitary_power_mem d n (U*V)
  | zero => simp
  | add A B hA hB ihA ihB =>
    rw [Matrix.mul_add]
    exact (unitarySpan d n).add_mem ihA ihB
  | smul c A hA ih =>
    rw [Matrix.mul_smul]
    exact (unitarySpan d n).smul_mem c ih

theorem right_unitary_mul_mem {d n : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    {A : TensorOperator d n} (hA : A ∈ unitarySpan d n) :
    A*tensorPower U.val n ∈ unitarySpan d n := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨V,rfl⟩ := hA
    rw [← tensorPower_mul]
    exact unitary_power_mem d n (V*U)
  | zero => simp
  | add A B hA hB ihA ihB =>
    rw [Matrix.add_mul]
    exact (unitarySpan d n).add_mem ihA ihB
  | smul c A hA ih =>
    rw [Matrix.smul_mul]
    exact (unitarySpan d n).smul_mem c ih

theorem hermitian_power_mem {d : ℕ} (n : ℕ) (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : tensorPower A n ∈ unitarySpan d n := by
  have hs := hA.spectral_theorem
  change A = (hA.eigenvectorUnitary.val * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) *
    hA.eigenvectorUnitary.valᴴ at hs
  rw [hs, tensorPower_mul, tensorPower_mul]
  exact right_unitary_mul_mem (star hA.eigenvectorUnitary)
    (left_unitary_mul_mem hA.eigenvectorUnitary (diagonal_power_mem d n _))

theorem hermitian_pencil_annihilated {d n : ℕ}
    (L : TensorOperator d n →ₗ[ℂ] ℂ)
    (hL : ∀ A : Matrix (Fin d) (Fin d) ℂ, A.IsHermitian → L (tensorPower A n) = 0)
    (A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (z : ℂ) : L (tensorPower (A+z • B) n) = 0 := by
  let Q : Matrix (Fin d) (Fin d) (MvPolynomial Unit ℂ) := fun i j =>
    MvPolynomial.C (A i j) + MvPolynomial.X () * MvPolynomial.C (B i j)
  have hQ (w : Unit → ℂ) : (fun i j => MvPolynomial.eval w (Q i j)) = A+w () • B := by
    ext i j
    simp [Q]
  have hP : tensorScalarPolynomial d n L Q = 0 := by
    apply MvPolynomial.funext_set (fun _ : Unit => Set.range ((↑) : ℝ → ℂ))
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro w hw
    rw [map_zero, eval_tensorScalarPolynomial, hQ]
    obtain ⟨r,hr⟩ := hw () (Set.mem_univ ())
    rw [← hr]
    apply hL
    have hs : ((r:ℂ) • B).IsHermitian := by
      change (((r:ℂ) • B)ᴴ) = _
      simp [Matrix.conjTranspose_smul, hB.eq]
    exact hA.add hs
  have he := congrArg (MvPolynomial.eval (fun _ : Unit => z)) hP
  rw [eval_tensorScalarPolynomial, hQ, map_zero] at he
  exact he

theorem arbitrary_power_mem {d : ℕ} (n : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    tensorPower X n ∈ unitarySpan d n := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).1
  intro L hL
  have hh : ∀ A : Matrix (Fin d) (Fin d) ℂ, A.IsHermitian → L (tensorPower A n) = 0 := by
    intro A hA
    exact (Submodule.mem_dualAnnihilator L).1 hL _ (hermitian_power_mem n A hA)
  have h := hermitian_pencil_annihilated L hh (realPart X) (imaginaryPart X)
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr (realPart X).property)
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr (imaginaryPart X).property) Complex.I
  rwa [realPart_add_I_smul_imaginaryPart] at h

def occupation (d n : ℕ) (i j : Index (Fin d) n) : (Fin d × Fin d) →₀ ℕ :=
  ∑ l : Fin n, Finsupp.single (indexEquiv (Fin d) n i l, indexEquiv (Fin d) n j l) 1

theorem occupation_apply (d n : ℕ) (i j : Index (Fin d) n) (p : Fin d × Fin d) :
    occupation d n i j p = (pairHistogram n i j p : ℕ) := by
  simp [occupation, pairHistogram, histogram, Finsupp.single_apply,
    Fintype.card_subtype, eq_comm]

theorem occupation_eq_iff (d n : ℕ) (i j i' j' : Index (Fin d) n) :
    occupation d n i j = occupation d n i' j' ↔ pairHistogram n i j = pairHistogram n i' j' := by
  constructor
  · intro h
    funext p
    apply Fin.ext
    simpa only [occupation_apply] using congrArg (fun f => f p) h
  · intro h
    ext p
    simp only [occupation_apply, h]

def orbitMatrix (d n : ℕ) (h : (Fin d × Fin d) → Fin (n+1)) : TensorOperator d n :=
  fun i j => if pairHistogram n i j = h then 1 else 0

theorem prod_variables_eq_monomial (d n : ℕ) (i j : Index (Fin d) n) :
    (∏ l : Fin n, (MvPolynomial.X (indexEquiv (Fin d) n i l, indexEquiv (Fin d) n j l) :
      MvPolynomial (Fin d × Fin d) ℂ)) = MvPolynomial.monomial (occupation d n i j) 1 := by
  rw [occupation, MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro l _
  simpa using (MvPolynomial.X_pow_eq_monomial (n := (indexEquiv (Fin d) n i l,
    indexEquiv (Fin d) n j l)) (e := 1) (R := ℂ))

theorem orbit_functional_eq_coeff (d n : ℕ) (L : TensorOperator d n →ₗ[ℂ] ℂ)
    (i j : Index (Fin d) n) :
    L (orbitMatrix d n (pairHistogram n i j)) =
      MvPolynomial.coeff (occupation d n i j)
        (tensorScalarPolynomial d n L (fun a b => MvPolynomial.X (a,b))) := by
  rw [functional_matrix_expansion]
  simp only [tensorScalarPolynomial, MvPolynomial.coeff_sum,
    prod_variables_eq_monomial, mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro i' _
  apply Finset.sum_congr rfl
  intro j' _
  simp only [orbitMatrix, occupation_eq_iff]
  split_ifs <;> simp_all [eq_comm]

theorem orbit_power_mem (d n : ℕ) (i j : Index (Fin d) n) :
    orbitMatrix d n (pairHistogram n i j) ∈ unitarySpan d n := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).1
  intro L hL
  have hP : tensorScalarPolynomial d n L (fun a b => MvPolynomial.X (a,b)) = 0 := by
    apply MvPolynomial.funext
    intro z
    rw [eval_tensorScalarPolynomial, map_zero]
    apply (Submodule.mem_dualAnnihilator L).1 hL
    exact arbitrary_power_mem n _
  rw [orbit_functional_eq_coeff, hP]
  simp

theorem orbitMatrix_mem (d n : ℕ) (h : (Fin d × Fin d) → Fin (n+1)) :
    orbitMatrix d n h ∈ unitarySpan d n := by
  by_cases he : ∃ i j : Index (Fin d) n, pairHistogram n i j = h
  · obtain ⟨i,j,rfl⟩ := he
    exact orbit_power_mem d n i j
  · have hz : orbitMatrix d n h = 0 := by
      ext i j
      have hij : pairHistogram n i j ≠ h := fun hij => he ⟨i,j,hij⟩
      simp [orbitMatrix,hij]
    rw [hz]
    exact (unitarySpan d n).zero_mem

theorem invariant_orbit_expansion (d n : ℕ) (A : invariantAlgebra (Fin d) n) :
    A.val = ∑ h : (Fin d × Fin d) → Fin (n+1),
      histogramEvaluation (Fin d) n A h • orbitMatrix d n h := by
  ext i j
  simp [orbitMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    histogramEvaluation_apply_histogram]

theorem invariant_mem_unitarySpan (d n : ℕ) (A : invariantAlgebra (Fin d) n) :
    A.val ∈ unitarySpan d n := by
  rw [invariant_orbit_expansion]
  apply Submodule.sum_mem
  intro h _
  exact (unitarySpan d n).smul_mem _ (orbitMatrix_mem d n h)

/-- Genuine finite-dimensional unitary tensor-power spanning, with no
Schur–Weyl or spanning hypothesis. Zero local dimension and zero copies
are both included. -/
theorem unitarySpan_eq_invariant (d n : ℕ) :
    unitarySpan d n = (invariantAlgebra (Fin d) n).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro A ⟨U,rfl⟩
    change ∀ p, conjugation (Fin d) n p (tensorPower U.val n) = tensorPower U.val n
    intro p
    exact conjugation_tensorPower U.val n p
  · intro A hA
    exact invariant_mem_unitarySpan d n ⟨A,hA⟩

/-- Expanded endpoint for consumers using the original first-paper types. -/
theorem span_unitary_tensor_powers (d n : ℕ) :
    Submodule.span ℂ (Set.range (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      TensorPower.tensorPower U.val n)) =
      (TensorPermutation.invariantAlgebra (Fin d) n).toSubmodule :=
  unitarySpan_eq_invariant d n

end GeneralizedChannelStein.UnitaryPowerSpan
