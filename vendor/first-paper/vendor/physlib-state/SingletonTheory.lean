import QuantumInfo.ResourceTheory.FreeState

/-!
# A singleton free-state theory from a coherent faithful family

This constructor proves the closedness, convexity, tensor stability, and
full-rank requirements. A concrete coherent tensor pretheory and family are
still inputs; this file does not assert that the ordinary state model has
already been instantiated.
-/


noncomputable section
open ResourcePretheory UnitalPretheory ComplexOrder

namespace StateSteinAudit

variable {ι : Type*} [UnitalPretheory ι]

/-- A coherent faithful state in each object defines a singleton resource
theory with all four free-state conditions proved. -/
@[instance_reducible]
def singletonFreeStateTheory (sigma : (i : ι) → MState (H i))
    (hfaithful : ∀ i, (sigma i).m.PosDef)
    (hproduct : ∀ i j, sigma (i * j) = sigma i ⊗ᵣ sigma j) :
    UnitalFreeStateTheory ι where
  toUnitalPretheory := inferInstance
  IsFree := fun {i} => {sigma i}
  free_closed := isClosed_singleton
  free_convex := by
    intro i
    simpa only [Set.image_singleton] using (convex_singleton (𝕜 := ℝ) (sigma i).M)
  free_prod := by
    intro i j rho tau hrho htau
    change rho = sigma i at hrho
    change tau = sigma j at htau
    change rho ⊗ᵣ tau = sigma (i * j)
    rw [hrho, htau, hproduct]
  free_fullRank := fun i => ⟨sigma i, hfaithful i, rfl⟩

end StateSteinAudit
