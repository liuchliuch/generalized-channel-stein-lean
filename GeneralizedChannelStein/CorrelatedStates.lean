import GeneralizedChannelStein.SeparableStates
import GeneralizedChannelStein.CovariantFamilies
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Explicit heterogeneous product states and independent Bernoulli block flags.
These are finite constructions used to represent labeled set partitions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b : ℕ}

/-- A genuine product of possibly different local density matrices. -/
def productState : (n : ℕ) → (Fin n → State b) → State (b^n)
  | 0, _ => scalarState
  | n+1, ρ => ((ρ 0).tensor (productState n (fun i => ρ i.succ))).reindex
      (finCongr (show b*b^n=b^(n+1) by rw [Nat.pow_succ']))

theorem productState_entry (n : ℕ) (ρ : Fin n → State b)
    (i j : Index (Fin b) n) :
    (productState n ρ).matrix (channelIndexEquiv b n i) (channelIndexEquiv b n j) =
      ∏ s : Fin n, (ρ s).matrix (indexEquiv (Fin b) n i s) (indexEquiv (Fin b) n j s) := by
  induction n with
  | zero => simpa [productState,scalarState,Matrix.one_apply] using (Subsingleton.elim i j)
  | succ n ih =>
    simp only [productState,State.reindex_matrix,State.tensor_matrix,channelIndexEquiv,
      Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.trans_apply,Equiv.prodCongr_apply,
      Equiv.refl_apply,Equiv.symm_apply_apply,Matrix.kronecker_apply,Fin.prod_univ_succ,
      indexEquiv_succ_zero,indexEquiv_succ_succ]
    change (ρ 0).matrix i.1 j.1 * (productState n (fun l => ρ l.succ)).matrix
      (channelIndexEquiv b n i.2) (channelIndexEquiv b n j.2) = _
    rw [ih]

theorem productState_const (ρ : State b) (n : ℕ) : productState n (fun _ => ρ)=statePower ρ n := by
  apply State.eq_of_matrix_eq
  ext i j
  obtain ⟨i,rfl⟩ := (channelIndexEquiv b n).surjective i
  obtain ⟨j,rfl⟩ := (channelIndexEquiv b n).surjective j
  rw [productState_entry]
  simp only [statePower,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    tensorPower_apply_eq_prod]

theorem productState_add (n m : ℕ) (ρ : Fin (n+m) → State b) :
    productState (n+m) ρ =
      ((productState n (fun i => ρ (Fin.castAdd m i))).tensor
        (productState m (fun i => ρ (Fin.natAdd n i)))).reindex (channelAddEquiv b n m) := by
  apply State.eq_of_matrix_eq
  ext i j
  obtain ⟨⟨i₁,i₂⟩,rfl⟩ := (channelConcatEquiv b n m).surjective i
  obtain ⟨⟨j₁,j₂⟩,rfl⟩ := (channelConcatEquiv b n m).surjective j
  obtain ⟨i₁,rfl⟩ := (channelIndexEquiv b n).surjective i₁
  obtain ⟨i₂,rfl⟩ := (channelIndexEquiv b m).surjective i₂
  obtain ⟨j₁,rfl⟩ := (channelIndexEquiv b n).surjective j₁
  obtain ⟨j₂,rfl⟩ := (channelIndexEquiv b m).surjective j₂
  simp only [channelConcatEquiv_apply,productState_entry,Fin.prod_univ_add,
    indexEquiv_indexAddEquiv_left,indexEquiv_indexAddEquiv_right,
    State.reindex_matrix,State.tensor_matrix,Matrix.reindex_apply,Matrix.submatrix_apply]
  simp only [channelAddEquiv,channelConcatEquiv,Equiv.symm_trans_apply,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,Equiv.apply_symm_apply,Equiv.symm_apply_apply,Equiv.symm_symm,Prod.map_apply,Matrix.kronecker_apply]
  rw [productState_entry,productState_entry]

theorem productState_permutation (n : ℕ) (ρ : Fin n → State b) (π : Equiv.Perm (Fin n)) :
    (productState n ρ).reindex (sitePermutation b n π)=productState n (fun i => ρ (π.symm i)) := by
  apply State.eq_of_matrix_eq
  ext i j
  obtain ⟨i,rfl⟩ := (channelIndexEquiv b n).surjective i
  obtain ⟨j,rfl⟩ := (channelIndexEquiv b n).surjective j
  simp only [State.reindex_matrix,Matrix.reindex_apply,Matrix.submatrix_apply,sitePermutation,
    Equiv.symm_trans_apply,Equiv.apply_symm_apply,Equiv.symm_apply_apply,Equiv.symm_symm,productState_entry,
    TensorPermutation.factorPermutation_symm_coordinates]
  have h := Equiv.prod_comp π (fun l => (ρ (π.symm l)).matrix
    (indexEquiv (Fin b) n i l) (indexEquiv (Fin b) n j l))
  simpa only [Equiv.symm_apply_apply] using h

/-- The genuine last-output marginal in the same block coordinates. -/
def discardState (n : ℕ) (ρ : State (b^(n+1))) : State (b^n) :=
  (discardRight (b^n) (b^1)).onState (ρ.reindex (channelAddEquiv b n 1).symm)

theorem discardState_product (n : ℕ) (ρ : Fin (n+1) → State b) :
    discardState n (productState (n+1) ρ)=productState n (fun i => ρ (Fin.castAdd 1 i)) := by
  rw [productState_add n 1]
  apply State.eq_of_matrix_eq
  change (discardRight (b^n) (b^1)).apply (Matrix.reindex (channelAddEquiv b n 1).symm
    (channelAddEquiv b n 1).symm (Matrix.reindex (channelAddEquiv b n 1) (channelAddEquiv b n 1) _)) = _
  simp only [Matrix.reindex_apply,Matrix.submatrix_submatrix,Function.comp_def,
    Equiv.apply_symm_apply,Matrix.submatrix_id_id]
  change (discardRight (b^n) (b^1)).apply ((productState n (fun i => ρ (Fin.castAdd 1 i))).tensor
    (productState 1 (fun i => ρ (Fin.natAdd n i)))).matrix = _
  rw [State.tensor_matrix,discardRight_apply_product,(productState _ _).trace_one,one_smul]

/-- A finite convex ensemble, with explicit nonnegative normalized weights. -/
def ensembleState {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0≤w i)
    (hsum : ∑ i, w i=1) {d : ℕ} (ρ : ι → State d) : State d where
  matrix := ∑ i, w i • (ρ i).matrix
  positive := by
    apply Finset.sum_induction
    · intro X Y hX hY; exact hX.add hY
    · exact Matrix.PosSemidef.zero
    · intro i hi; exact (ρ i).positive.smul (hw i)
  trace_one := by
    simp only [Matrix.trace_sum,Matrix.trace_smul,fun i => (ρ i).trace_one,← Finset.sum_smul,hsum,one_smul]

def bernoulliWeight {ι : Type*} [Fintype ι] (p : ι → ℝ) (ξ : ι → Bool) : ℝ :=
  ∏ i, if ξ i then p i else 1-p i

theorem bernoulliWeight_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1) (ξ : ι → Bool) : 0≤bernoulliWeight p ξ := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact hp i
  · exact sub_nonneg.mpr (hp1 i)

theorem sum_bernoulliWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    ∑ ξ : ι → Bool, bernoulliWeight p ξ=1 := by
  have h := Fintype.prod_sum (κ:=fun _ : ι => Bool) (fun i (x:Bool) => if x then p i else 1-p i)
  simpa [bernoulliWeight,Fintype.sum_bool] using h.symm

/-- A block-label map describes a partition by its nonempty fibers.
Each label independently chooses rho or omega, with p=0 forcing omega. -/
def partitionState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ ω : State b) (n : ℕ) (f : Fin n → ι) (p : ι → ℝ)
    (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1) : State (b^n) :=
  ensembleState (bernoulliWeight p) (bernoulliWeight_nonneg p hp hp1) (sum_bernoulliWeight p)
    (fun ξ => productState n (fun i => if ξ (f i) then ρ else ω))

theorem partitionState_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ ω : State b) (n : ℕ) (f : Fin n → ι) (p : ι → ℝ)
    (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1) (π : Equiv.Perm (Fin n)) :
    (partitionState ρ ω n f p hp hp1).reindex (sitePermutation b n π) =
      partitionState ρ ω n (fun i => f (π.symm i)) p hp hp1 := by
  apply State.eq_of_matrix_eq
  change Matrix.reindex _ _ (∑ ξ, bernoulliWeight p ξ • (productState n _).matrix) = _
  have he : Matrix.reindex (sitePermutation b n π) (sitePermutation b n π)
      (∑ ξ, bernoulliWeight p ξ • (productState n (fun i => if ξ (f i) then ρ else ω)).matrix) =
      ∑ ξ, bernoulliWeight p ξ • ((productState n (fun i => if ξ (f i) then ρ else ω)).reindex (sitePermutation b n π)).matrix := by
    ext i j; simp [State.reindex_matrix,Matrix.reindex_apply,Matrix.sum_apply]
  rw [he]
  simp_rw [productState_permutation]
  rfl

end GeneralizedChannelStein.Correlated
