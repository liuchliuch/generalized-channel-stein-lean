import TupleCoherence
import SingletonTheory

noncomputable section
open ComplexOrder
open scoped HermitianMat BigOperators

namespace StateSteinAudit

universe u
variable {d : Type u} [Fintype d] [DecidableEq d]

/-- The concrete entries of the independent finite-tuple state product. -/
lemma npow_entries (rho : MState d) (n : ℕ) (x y : Fin n → d) :
    (rho.npow n).m x y = ∏ i : Fin n, rho.m (x i) (y i) := rfl

/-- One independent copy is the original state under the canonical tuple-coordinate equivalence. -/
lemma npow_one_relabel (rho : MState d) :
    rho.npow 1 = rho.relabel (Equiv.funUnique (Fin 1) d) := by
  apply MState.m_inj
  ext x y
  rw [npow_entries, MState.relabel_m]
  change (∏ i : Fin 1, rho.m (x i) (y i)) = rho.m (x default) (y default)
  simp

/-- Independent state products obey the actual finite-tuple concatenation law. -/
lemma npow_add_relabel (rho : MState d) (m n : ℕ) :
    rho.npow (m + n) = ((rho.npow m) ⊗ᴹ (rho.npow n)).relabel (Fin.appendEquiv m n).symm := by
  apply MState.m_inj
  ext x y
  change (∏ i : Fin (m + n), rho.m (x i) (y i)) =
    (∏ i : Fin m, rho.m (x (Fin.castAdd n i)) (y (Fin.castAdd n i))) *
      (∏ j : Fin n, rho.m (x (Fin.natAdd m j)) (y (Fin.natAdd m j)))
  exact Fin.prod_univ_add _

/-- Faithfulness is preserved by every actual finite-tuple state product. -/
lemma npow_posDef (sigma : MState d) (hfaithful : sigma.m.PosDef) (n : ℕ) :
    (sigma.npow n).m.PosDef := by
  induction n with
  | zero => exact MState.posDef_of_unique _
  | succ n ih =>
    rw [npow_add_relabel sigma n 1]
    apply MState.PosDef.relabel
    apply MState.PosDef.kron ih
    rw [npow_one_relabel]
    exact MState.PosDef.relabel hfaithful _

/-- Transporting a density matrix by a type equality preserves it heterogeneously. -/
lemma relabel_cast_heq {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] (rho : MState d₁) (h : d₂ = d₁) :
    HEq (rho.relabel (Equiv.cast h)) rho := by
  rw [MState.relabel_cast]
  exact cast_heq _ _

/-- Right tensor-unit law in explicit finite-tuple coordinates. -/
lemma tuple_prod_right_unit (n : ℕ) (rho : MState (Fin n → d)) :
    HEq ((rho ⊗ᴹ (default : MState (Fin 0 → d))).relabel (Fin.appendEquiv n 0).symm) rho := by
  apply heq_of_eq
  apply MState.m_inj
  ext x y
  simp only [MState.relabel_m, Matrix.submatrix_apply]
  change rho.m (fun i => x (Fin.castAdd 0 i)) (fun i => y (Fin.castAdd 0 i)) *
    (default : MState (Fin 0 → d)).m _ _ = rho.m x y
  have hd : (default : MState (Fin 0 → d)).m = 1 := by
    change (default : MState (Fin 0 → d)).M.mat = 1
    rw [MState.M_default]
    rfl
  rw [hd, Matrix.one_apply, if_pos (Subsingleton.elim _ _), mul_one]
  congr 1

/-- Left tensor-unit law in explicit finite-tuple coordinates, including the
transport from `0+n` to `n`. -/
lemma tuple_prod_left_unit (n : ℕ) (rho : MState (Fin n → d)) :
    HEq (((default : MState (Fin 0 → d)) ⊗ᴹ rho).relabel (Fin.appendEquiv 0 n).symm) rho := by
  let T := ((default : MState (Fin 0 → d)) ⊗ᴹ rho).relabel (Fin.appendEquiv 0 n).symm
  let e : (Fin n → d) ≃ (Fin (0 + n) → d) :=
    Equiv.cast (congrArg (fun k : ℕ => Fin k → d) (Nat.zero_add n).symm)
  have he (x : Fin n → d) (j : Fin (0 + n)) : e x j = x (Fin.cast (Nat.zero_add n) j) := by
    exact congrFun (cast_tuple (Nat.zero_add n).symm x) j
  have hsuffix (x : Fin n → d) : (fun j : Fin n => e x (Fin.natAdd 0 j)) = x := by
    funext j
    rw [he]
    apply congrArg x
    apply Fin.ext
    simp
  have hd : (default : MState (Fin 0 → d)).m = 1 := by
    change (default : MState (Fin 0 → d)).M.mat = 1
    rw [MState.M_default]
    rfl
  have heq : T.relabel e = rho := by
    apply MState.m_inj
    ext x y
    change (default : MState (Fin 0 → d)).m
        (fun i : Fin 0 => e x (Fin.castAdd n i)) (fun i : Fin 0 => e y (Fin.castAdd n i)) *
        rho.m (fun j : Fin n => e x (Fin.natAdd 0 j)) (fun j : Fin n => e y (Fin.natAdd 0 j)) =
      rho.m x y
    rw [hd, Matrix.one_apply, if_pos (Subsingleton.elim _ _), one_mul, hsuffix, hsuffix]
  exact (relabel_cast_heq T (congrArg (fun k : ℕ => Fin k → d) (Nat.zero_add n).symm)).symm.trans (heq_of_eq heq)

/-- The concrete unital tensor coordinate system on finite tuples. All
associativity and unit coherence fields are proved. -/
@[instance_reducible]
def tupleUnitalPretheory (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    UnitalPretheory (TensorLabel d) where
  toResourcePretheory := tupleResourcePretheory d
  one := ⟨0⟩
  one_mul i := by cases i; change TensorLabel.mk (0 + _) = _; simp
  mul_one i := by cases i; rfl
  toUnique := by change Unique (Fin 0 → d); infer_instance
  prod_default := by
    intro i rho
    cases i with
    | mk n => exact tuple_prod_right_unit n rho
  default_prod := by
    intro i rho
    cases i with
    | mk n => exact tuple_prod_left_unit n rho

end StateSteinAudit
