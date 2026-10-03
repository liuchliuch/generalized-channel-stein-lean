import TupleStates
import SingletonSteinBridge

noncomputable section
open ComplexOrder
open Topology Filter ResourcePretheory FreeStateTheory UnitalPretheory
open scoped Prob OptimalHypothesisRate

namespace StateSteinAudit

universe u

/-- A coherent family has its resource tensor powers equal to the family at
powers of the underlying object. -/
lemma statePow_coherent {ι : Type*} [UnitalPretheory ι]
    (f : (i : ι) → MState (H i))
    (hprod : ∀ i j, f (i * j) = f i ⊗ᵣ f j) (i : ι) (n : ℕ) :
    statePow (f i) n = f (i ^ n) := by
  induction n with
  | zero =>
    change (default : MState (H (1 : ι))) = f 1
    exact Subsingleton.elim _ _
  | succ n ih => rw [statePow_succ, ih, ← hprod]; rfl

/-- The actual singleton theory of tensor copies of a faithful density matrix. -/
@[instance_reducible]
def ordinaryStateTheory {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (sigma : MState d) (hfaithful : sigma.m.PosDef) :
    UnitalFreeStateTheory (TensorLabel d) := by
  letI := tupleUnitalPretheory d
  exact singletonFreeStateTheory (fun i => sigma.npow i.length)
    (fun i => npow_posDef sigma hfaithful i.length)
    (fun i j => npow_add_relabel sigma i.length j.length)

/-- Concrete tuple-coordinate ordinary quantum Stein limit for faithful
alternative states. No abstract resource realization is an input. -/
theorem faithful_state_stein {d : Type u} [Fintype d] [DecidableEq d]
    (rho sigma : MState d) (hfaithful : sigma.m.PosDef)
    {epsilon : Prob} (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    Tendsto (fun n : ℕ => Prob.negLog
      (OptimalHypothesisRate (rho.npow n) epsilon {sigma.npow n}) / n)
      atTop (𝓝 (qRelativeEnt rho sigma)) := by
  letI : Nonempty d := rho.nonempty
  letI := ordinaryStateTheory sigma hfaithful
  let i : TensorLabel d := ⟨1⟩
  have hfamily (tau : MState d) (n : ℕ) :
      statePow (i := i) (tau.npow 1) n = tau.npow (i ^ n).length :=
    statePow_coherent (fun j : TensorLabel d => tau.npow j.length)
      (fun j k => npow_add_relabel tau j.length k.length) i n
  have hsingle (n : ℕ) :
      (IsFree (i := i ^ n) : Set (MState (H (i ^ n)))) =
        {statePow (i := i) (sigma.npow 1) n} := by
    rw [hfamily]
    rfl
  have h := singleton_state_stein (i := i) (rho.npow 1) (sigma.npow 1) hsingle hepsilon
  have hent : qRelativeEnt (rho.npow 1) (sigma.npow 1) = qRelativeEnt rho sigma := by
    rw [npow_one_relabel, npow_one_relabel, qRelativeEnt_relabel]
  rw [hent] at h
  have hlength (n : ℕ) : (i ^ n).length = n := by
    induction n with
    | zero => rfl
    | succ n ih => change (i ^ n).length + 1 = n + 1; rw [ih]
  have htest (n : ℕ) :
      OptimalHypothesisRate (statePow (i := i) (rho.npow 1) n) epsilon
          {statePow (i := i) (sigma.npow 1) n} =
        OptimalHypothesisRate (rho.npow n) epsilon {sigma.npow n} := by
    rw [hfamily, hfamily]
    exact congrArg (fun k => OptimalHypothesisRate (rho.npow k) epsilon {sigma.npow k})
      (hlength n)
  simpa only [htest] using h

end StateSteinAudit
