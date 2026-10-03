import QuantumInfo.ResourceTheory.FreeState

noncomputable section

namespace StateSteinAudit

universe u

/-- Explicit transport of a finite tuple across a length equality. -/
lemma cast_tuple {d : Type u} {m n : ℕ} (h : m = n) (x : Fin m → d) :
    Equiv.cast (congrArg (fun k : ℕ => Fin k → d) h) x =
      fun i => x (Fin.cast h.symm i) := by
  subst h
  rfl

/-- The finite-tuple splitting equivalences satisfy the exact associator
coherence required by `ResourcePretheory`. -/
lemma tuple_split_assoc (d : Type u) (m n p : ℕ) :
    (((((Fin.appendEquiv (α := d) (m + n) p).symm.trans
      ((Fin.appendEquiv (α := d) m n).symm.prodCongr (Equiv.refl (Fin p → d)))).trans
      (Equiv.prodAssoc (Fin m → d) (Fin n → d) (Fin p → d))).trans
      ((Equiv.refl (Fin m → d)).prodCongr (Fin.appendEquiv (α := d) n p))).trans
      (Fin.appendEquiv (α := d) m (n + p))) =
      Equiv.cast (congrArg (fun k : ℕ => Fin k → d) (Nat.add_assoc m n p)) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨ab, c⟩, rfl⟩ := (Fin.appendEquiv (α := d) (m + n) p).surjective x
  obtain ⟨⟨a, b⟩, rfl⟩ := (Fin.appendEquiv (α := d) m n).surjective ab
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    Equiv.prodAssoc_apply, Equiv.symm_apply_apply]
  rw [cast_tuple (Nat.add_assoc m n p)]
  simp only [Fin.appendEquiv_apply]
  funext i
  change Fin.append a (Fin.append b c) i =
    Fin.append (Fin.append a b) c (Fin.cast (Nat.add_assoc m n p).symm i)
  rw [Fin.append_assoc]
  apply congrArg (Fin.append a (Fin.append b c))
  apply Fin.ext
  rfl

/-- A natural tensor-length label retains the base coordinate type as a
parameter, so the concrete resource-theory instance is unambiguous. -/
structure TensorLabel (d : Type u) where
  length : ℕ

instance {d : Type u} : Mul (TensorLabel d) := ⟨fun i j => ⟨i.length + j.length⟩⟩
instance {d : Type u} : One (TensorLabel d) := ⟨⟨0⟩⟩
instance {d : Type u} : Semigroup (TensorLabel d) where
  mul i j := ⟨i.length + j.length⟩
  mul_assoc i j k := by cases i; cases j; cases k; simp only [HMul.hMul, Mul.mul]; congr 1; omega
instance {d : Type u} : MulOneClass (TensorLabel d) where
  mul i j := ⟨i.length + j.length⟩
  one := ⟨0⟩
  one_mul i := by cases i; change TensorLabel.mk (0 + _) = _; simp
  mul_one i := by cases i; rfl

/-- The concrete finite-tuple tensor coordinate system. -/
@[instance_reducible]
def tupleResourcePretheory (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    ResourcePretheory (TensorLabel d) where
  toSemigroup := inferInstance
  H i := Fin i.length → d
  FinH _ := inferInstance
  DecEqH _ := inferInstance
  NonemptyH _ := inferInstance
  prodEquiv i j := (Fin.appendEquiv (α := d) i.length j.length).symm
  hAssoc i j k := by
    cases i with | mk m =>
      cases j with | mk n =>
        cases k with | mk p =>
          exact tuple_split_assoc d m n p

end StateSteinAudit
