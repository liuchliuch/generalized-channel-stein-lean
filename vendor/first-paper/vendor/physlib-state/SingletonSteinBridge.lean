import QuantumInfo.ResourceTheory.SteinsLemma

/-!
# Singleton specialization under an explicit resource-theory realization

This is a bridge for the audited Physlib theorem. It does not construct the
resource-theory instance or remove its full-rank-free-state requirement.
The singleton tensor-power hypothesis is explicit and must be realized by a
coherent ordinary-state model before this becomes an ordinary state-Stein
application.
-/


noncomputable section
open Topology Filter
open ResourcePretheory FreeStateTheory UnitalPretheory UnitalFreeStateTheory
open scoped Prob OptimalHypothesisRate

namespace StateSteinAudit

variable {ι : Type*} [UnitalFreeStateTheory ι] {i : ι}

/-- Singleton tensor-power alternatives make resource regularization equal
to the ordinary two-state relative entropy. -/
theorem singleton_regularized_resource (ρ σ : MState (H i))
    (hsingleton : ∀ n : ℕ, (IsFree (i := i ^ n) : Set (MState (H (i ^ n)))) = {σ ⊗ᵣ^[n]}) :
    (RegularizedRelativeEntResource ρ : ENNReal) = qRelativeEnt ρ σ := by
  have hevent : (fun n : ℕ => (⨅ τ ∈ (IsFree (i := i ^ n)), qRelativeEnt (ρ ⊗ᵣ^[n]) τ) / n) =ᶠ[atTop]
      (fun _ : ℕ => qRelativeEnt ρ σ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [hsingleton n]
    simp only [iInf_singleton, qRelEntropy_statePow]
    rw [mul_comm (n : ENNReal)]
    exact ENNReal.mul_div_cancel_right (by positivity) (by finiteness)
  exact tendsto_nhds_unique (RelativeEntResource.tendsto_ennreal ρ)
    (tendsto_const_nhds.congr' hevent.symm)

/-- The generalized theorem specialized to an explicitly realized singleton
tensor-power family. Values remain in `ENNReal` and use natural logarithms. -/
theorem singleton_state_stein (ρ σ : MState (H i))
    (hsingleton : ∀ n : ℕ, (IsFree (i := i ^ n) : Set (MState (H (i ^ n)))) = {σ ⊗ᵣ^[n]})
    {epsilon : Prob} (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    Tendsto (fun n : ℕ => Prob.negLog (OptimalHypothesisRate (ρ ⊗ᵣ^[n]) epsilon {σ ⊗ᵣ^[n]}) / n)
      atTop (𝓝 (qRelativeEnt ρ σ)) := by
  have h := SteinsLemma.GeneralizedQSteinsLemma ρ hepsilon
  rw [singleton_regularized_resource ρ σ hsingleton] at h
  simpa only [hsingleton] using h

end StateSteinAudit
