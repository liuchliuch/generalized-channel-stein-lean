import GeneralizedChannelStein.CorrelatedStates

/-! Removing unused block labels and concatenating labeled partitions are proved
on their finite Bernoulli ensembles, including singleton deletion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b : ℕ}

theorem bernoulliWeight_insert {k : ℕ} (p : Fin (k+1) → ℝ) (j : Fin (k+1))
    (x : Bool) (ξ : Fin k → Bool) :
    bernoulliWeight p (Fin.insertNth (α := fun _ : Fin (k+1) => Bool) j x ξ) =
      (if x then p j else 1-p j)*bernoulliWeight (fun i => p (j.succAbove i)) ξ := by
  unfold bernoulliWeight
  rw [Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]

/-- An unused block label integrates to one, exactly, even when its Bernoulli parameter is 0. -/
theorem bernoulli_delete_unused {E : Type*} [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (p : Fin (k+1) → ℝ) (j : Fin (k+1)) (H : (Fin k → Bool) → E) :
    (∑ ξ : Fin (k+1) → Bool, bernoulliWeight p ξ • H (fun i => ξ (j.succAbove i))) =
      ∑ ξ : Fin k → Bool, bernoulliWeight (fun i => p (j.succAbove i)) ξ • H ξ := by
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin (k+1) => Bool) j)]
  simp only [Fintype.sum_prod_type]
  change (∑ x : Bool, ∑ ξ : Fin k → Bool, bernoulliWeight p (Fin.insertNth (α := fun _ : Fin (k+1) => Bool) j x ξ) •
    H (fun i => Fin.insertNth (α := fun _ : Fin (k+1) => Bool) j x ξ (j.succAbove i))) = _
  simp only [bernoulliWeight_insert,Fin.insertNth_apply_succAbove]
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [← add_smul]
  congr 1
  ring

/-- The marginal distribution of any one block flag is its chosen Bernoulli law. -/
theorem bernoulli_one_coordinate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (p : Fin (k+1) → ℝ) (j : Fin (k+1)) (H : Bool → E) :
    (∑ ξ : Fin (k+1) → Bool, bernoulliWeight p ξ • H (ξ j)) =
      p j • H true+(1-p j) • H false := by
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin (k+1) => Bool) j)]
  simp only [Fintype.sum_prod_type]
  change (∑ x : Bool, ∑ ξ : Fin k → Bool, bernoulliWeight p (Fin.insertNth (α := fun _ : Fin (k+1) => Bool) j x ξ) •
    H (Fin.insertNth (α := fun _ : Fin (k+1) => Bool) j x ξ j)) = _
  simp only [bernoulliWeight_insert,Fin.insertNth_apply_same]
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true,ite_false,ite_true,← Finset.sum_smul,← Finset.mul_sum,
    sum_bernoulliWeight,mul_one]

theorem partitionState_delete_unused {k : ℕ} (ρ ω : State b) (n : ℕ)
    (g : Fin n → Fin k) (p : Fin (k+1) → ℝ) (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1)
    (j : Fin (k+1)) :
    partitionState ρ ω n (fun i => j.succAbove (g i)) p hp hp1 =
      partitionState ρ ω n g (fun i => p (j.succAbove i)) (fun i => hp _) (fun i => hp1 _) := by
  apply State.eq_of_matrix_eq
  exact bernoulli_delete_unused p j (fun ξ => (productState n (fun i => if ξ (g i) then ρ else ω)).matrix)

/-- One nonempty block yields exactly c rho^n+(1-c) omega^n. -/
theorem partitionState_constant {k : ℕ} (ρ ω : State b) (n : ℕ)
    (p : Fin (k+1) → ℝ) (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1) (j : Fin (k+1)) :
    (partitionState ρ ω n (fun _ => j) p hp hp1).matrix =
      p j • (statePower ρ n).matrix+(1-p j) • (statePower ω n).matrix := by
  change (∑ ξ, bernoulliWeight p ξ • (productState n (fun _ => if ξ j then ρ else ω)).matrix) = _
  have h := bernoulli_one_coordinate p j (fun x => (productState n (fun _ => if x then ρ else ω)).matrix)
  simpa only [ite_true,Bool.false_eq_true,ite_false,productState_const] using h

/-- Removing a site keeps exactly the same block-label assignment on the other sites. -/
theorem discard_partitionState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ ω : State b) (n : ℕ) (f : Fin (n+1) → ι) (p : ι → ℝ)
    (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1) :
    discardState n (partitionState ρ ω (n+1) f p hp hp1) =
      partitionState ρ ω n (fun i => f (Fin.castAdd 1 i)) p hp hp1 := by
  apply State.eq_of_matrix_eq
  have he : ∀ (w : (ι → Bool) → ℝ) (A : (ι → Bool) → State (b^(n+1))),
      (discardRight (b^n) (b^1)).apply
        (Matrix.reindex (channelAddEquiv b n 1).symm (channelAddEquiv b n 1).symm
          (∑ ξ, w ξ • (A ξ).matrix)) =
      ∑ ξ, w ξ • (discardState n (A ξ)).matrix := by
    intro w A
    have hr : Matrix.reindex (channelAddEquiv b n 1).symm (channelAddEquiv b n 1).symm
        (∑ ξ, w ξ • (A ξ).matrix) =
        ∑ ξ, w ξ • Matrix.reindex (channelAddEquiv b n 1).symm (channelAddEquiv b n 1).symm (A ξ).matrix := by
      ext i j; simp [Matrix.reindex_apply,Matrix.sum_apply]
    rw [hr]
    change (discardRight _ _).toLinearMap (∑ ξ, w ξ • _) = _
    rw [map_sum]
    simp only [LinearMap.map_smul_of_tower]
    rfl
  change (discardRight _ _).apply (Matrix.reindex _ _ (∑ ξ, bernoulliWeight p ξ • _)) = _
  rw [he]
  simp_rw [discardState_product]
  rfl

/-- An explicit equivalence concatenating finite assignments, used for tensor closure. -/
def appendAssignment (n m : ℕ) : (Fin n → Bool) × (Fin m → Bool) ≃ (Fin (n+m) → Bool) where
  toFun ξ := Fin.addCases ξ.1 ξ.2
  invFun ξ := (fun i => ξ (Fin.castAdd m i),fun i => ξ (Fin.natAdd n i))
  left_inv ξ := by ext i <;> simp
  right_inv ξ := by funext i; exact Fin.addCases (fun j => by simp) (fun j => by simp) i

theorem bernoulli_append (n m : ℕ) (p : Fin n → ℝ) (q : Fin m → ℝ)
    (ξ : Fin n → Bool) (η : Fin m → Bool) :
    bernoulliWeight (Fin.addCases p q) (Fin.addCases ξ η)=bernoulliWeight p ξ*bernoulliWeight q η := by
  unfold bernoulliWeight
  rw [Fin.prod_univ_add]
  simp

/-- The block labels of a tensor product are the disjoint union of the old labels. -/
def appendLabels (n m : ℕ) (f : Fin n → Fin n) (g : Fin m → Fin m) : Fin (n+m) → Fin (n+m) :=
  Fin.addCases (fun i => Fin.castAdd m (f i)) (fun i => Fin.natAdd n (g i))

theorem partitionState_tensor (ρ ω : State b) (n m : ℕ) (f : Fin n → Fin n) (g : Fin m → Fin m)
    (p : Fin n → ℝ) (q : Fin m → ℝ) (hp : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1)
    (hq : ∀ i, 0≤q i) (hq1 : ∀ i, q i≤1) :
    partitionState ρ ω (n+m) (appendLabels n m f g) (Fin.addCases p q)
      (fun i => Fin.addCases (fun j => by simpa using hp j) (fun j => by simpa using hq j) i)
      (fun i => Fin.addCases (fun j => by simpa using hp1 j) (fun j => by simpa using hq1 j) i) =
      ((partitionState ρ ω n f p hp hp1).tensor (partitionState ρ ω m g q hq hq1)).reindex (channelAddEquiv b n m) := by
  apply State.eq_of_matrix_eq
  change (∑ ξ, bernoulliWeight (Fin.addCases p q) ξ • (productState (n+m) _).matrix)=_
  rw [← Equiv.sum_comp (appendAssignment n m)]
  simp only [Fintype.sum_prod_type]
  change (∑ ξ : Fin n → Bool, ∑ η : Fin m → Bool,
    bernoulliWeight (Fin.addCases p q) (Fin.addCases ξ η) •
      (productState (n+m) (fun i => if (Fin.addCases ξ η (appendLabels n m f g i):Bool) then ρ else ω)).matrix) = _
  simp only [bernoulli_append]
  have hprod (ξ : Fin n → Bool) (η : Fin m → Bool) :
      productState (n+m) (fun i => if (Fin.addCases ξ η (appendLabels n m f g i) : Bool) then ρ else ω) =
      ((productState n (fun i => if ξ (f i) then ρ else ω)).tensor
        (productState m (fun i => if η (g i) then ρ else ω))).reindex (channelAddEquiv b n m) := by
    rw [productState_add]
    simp only [appendLabels,Fin.addCases_left,Fin.addCases_right]
  simp_rw [hprod]
  ext i j
  simp [partitionState,ensembleState,State.reindex_matrix,State.tensor_matrix,
    Matrix.reindex_apply,Matrix.sum_apply,Finset.sum_mul,Finset.mul_sum,smul_smul,
    Matrix.smul_apply,Complex.real_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro ξ hξ
  apply Finset.sum_congr rfl; intro η hη
  push_cast
  ring

end GeneralizedChannelStein.Correlated
