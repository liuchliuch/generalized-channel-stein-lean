import GeneralizedChannelStein.CorrelatedHull

/-! Closure proofs for the literal partition hull; no closure properties are
assumed as fields of the example construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b : ℕ}

/-- A linear map sends a generated convex hull into any convex target containing its generators. -/
theorem map_hull {E H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]
    (f : E →ₗ[ℝ] H) (S : Set E) (T : Set H) (hT : Convex ℝ T)
    (hf : ∀ x∈S, f x∈T) : ∀ x∈convexHull ℝ S, f x∈T :=
  convexHull_min hf (hT.linear_preimage f)

theorem hull_permutation (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (π : Equiv.Perm (Fin n)) {X : Operator (b^n)}
    (hX : X∈partitionHull ρ ω c hc hc1 n) :
    Matrix.reindex (sitePermutation b n π) (sitePermutation b n π) X∈partitionHull ρ ω c hc hc1 n := by
  apply map_hull ((Matrix.reindexLinearEquiv ℂ ℂ (sitePermutation b n π) (sitePermutation b n π)).toLinearMap.restrictScalars ℝ)
    _ _ (convex_convexHull ℝ _) ?_ X hX
  rintro Y ⟨d,rfl⟩
  apply subset_convexHull
  refine ⟨(fun i => d.1 (π.symm i),d.2),?_⟩
  exact (congrArg State.matrix (generator_permutation ρ ω c hc hc1 n d π)).symm

def discardMatrix (n : ℕ) : Operator (b^(n+1)) →ₗ[ℝ] Operator (b^n) :=
  ((discardRight (b^n) (b^1)).toLinearMap.restrictScalars ℝ).comp
    ((Matrix.reindexLinearEquiv ℂ ℂ (channelAddEquiv b n 1).symm (channelAddEquiv b n 1).symm).toLinearMap.restrictScalars ℝ)

theorem hull_marginal (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) {X : Operator (b^(n+1))} (hX : X∈partitionHull ρ ω c hc hc1 (n+1)) :
    discardMatrix n X∈partitionHull ρ ω c hc hc1 n := by
  apply map_hull (discardMatrix n) _ _ (convex_convexHull ℝ _) ?_ X hX
  rintro Y ⟨d,rfl⟩
  obtain ⟨e,he⟩ := generator_marginal ρ ω c hc hc1 n d
  apply subset_convexHull
  exact ⟨e,(congrArg State.matrix he).symm⟩

def tensorMatrix (n m : ℕ) (X : Operator (b^n)) (Y : Operator (b^m)) : Operator (b^(n+m)) :=
  Matrix.reindex (channelAddEquiv b n m) (channelAddEquiv b n m)
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y))

theorem tensorMatrix_mix_left (n m : ℕ) (X X' : Operator (b^n)) (Y : Operator (b^m)) (r s : ℝ) :
    tensorMatrix n m (r • X+s • X') Y = r • tensorMatrix n m X Y+s • tensorMatrix n m X' Y := by
  ext i j
  simp [tensorMatrix,Matrix.reindex_apply,add_mul]
  ring

theorem tensorMatrix_mix_right (n m : ℕ) (X : Operator (b^n)) (Y Y' : Operator (b^m)) (r s : ℝ) :
    tensorMatrix n m X (r • Y+s • Y') = r • tensorMatrix n m X Y+s • tensorMatrix n m X Y' := by
  ext i j
  simp [tensorMatrix,Matrix.reindex_apply,mul_add]
  ring

theorem hull_tensor (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n m : ℕ) {X : Operator (b^n)} {Y : Operator (b^m)}
    (hX : X∈partitionHull ρ ω c hc hc1 n) (hY : Y∈partitionHull ρ ω c hc hc1 m) :
    tensorMatrix n m X Y∈partitionHull ρ ω c hc hc1 (n+m) := by
  have hg (d : PartitionDescription n) : ∀ Y∈partitionHull ρ ω c hc hc1 m,
      tensorMatrix n m (partitionGenerator ρ ω c hc hc1 n d).matrix Y ∈ partitionHull ρ ω c hc hc1 (n+m) := by
    apply convexHull_min
    · rintro Z ⟨e,rfl⟩
      apply subset_convexHull
      refine ⟨(appendLabels n m d.1 e.1,Fin.addCases d.2 e.2),?_⟩
      exact (congrArg State.matrix (generator_tensor ρ ω c hc hc1 n m d e)).symm
    · intro Y hY Y' hY' r s hr hs hrs
      change tensorMatrix n m (partitionGenerator ρ ω c hc hc1 n d).matrix (r • Y+s • Y') ∈ partitionHull ρ ω c hc hc1 (n+m)
      rw [tensorMatrix_mix_right]
      exact (convex_convexHull ℝ _ ) hY hY' hr hs hrs
  have hgen : ∀ X∈partitionHull ρ ω c hc hc1 n,
      ∀ Y∈partitionHull ρ ω c hc hc1 m,
      tensorMatrix n m X Y∈partitionHull ρ ω c hc hc1 (n+m) := by
    apply convexHull_min
    · rintro Z ⟨d,rfl⟩
      exact hg d
    · intro X hX X' hX' r s hr hs hrs Y hY
      rw [tensorMatrix_mix_left]
      exact (convex_convexHull ℝ _) (hX Y hY) (hX' Y hY) hr hs hrs
  exact hgen X hX Y hY

end GeneralizedChannelStein.Correlated
