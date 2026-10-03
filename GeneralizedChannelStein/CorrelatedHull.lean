import GeneralizedChannelStein.CorrelatedPartitions

/-! Literal finite hull of labeled-site partitions, with an independent choice
of zeta-block or omega-block on every nonempty fiber. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b : ℕ}

/-- Fibers of the first function are the blocks. Unused labels have no effect.
The second function chooses a zeta block (true) or an omega block (false). -/
abbrev PartitionDescription (n : ℕ) := (Fin n → Fin n) × (Fin n → Bool)

def blockProbability (c : ℝ) {n : ℕ} (tag : Fin n → Bool) (i : Fin n) : ℝ :=
  if tag i then c else 0

theorem blockProbability_nonneg (c : ℝ) (hc : 0≤c) {n : ℕ} (tag : Fin n → Bool) (i : Fin n) :
    0≤blockProbability c tag i := by unfold blockProbability; split_ifs <;> positivity

theorem blockProbability_le_one (c : ℝ) (hc : c≤1) {n : ℕ} (tag : Fin n → Bool) (i : Fin n) :
    blockProbability c tag i≤1 := by unfold blockProbability; split_ifs <;> linarith

def partitionGenerator (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (d : PartitionDescription n) : State (b^n) :=
  partitionState ρ ω n d.1 (blockProbability c d.2)
    (blockProbability_nonneg c hc d.2) (blockProbability_le_one c hc1 d.2)

def partitionGenerators (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) : Set (Operator (b^n)) :=
  Set.range (fun d : PartitionDescription n => (partitionGenerator ρ ω c hc hc1 n d).matrix)

def partitionHull (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) : Set (Operator (b^n)) :=
  convexHull ℝ (partitionGenerators ρ ω c hc hc1 n)

theorem partitionHull_compact (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) :
    IsCompact (partitionHull ρ ω c hc hc1 n) :=
  (Set.finite_range _).isCompact_convexHull ℝ

theorem partitionHull_density (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ)
    {X : Operator (b^n)} (hX : X ∈ partitionHull ρ ω c hc hc1 n) : X.PosSemidef ∧ X.trace=1 := by
  have hs : Convex ℝ {X : Operator (b^n) | X.PosSemidef ∧ X.trace=1} := by
    intro X hX Y hY r s hr hs hrs
    refine ⟨(hX.1.smul hr).add (hY.1.smul hs),?_⟩
    rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,hX.2,hY.2,←add_smul,hrs,one_smul]
  apply (convexHull_min ?_ hs) hX
  rintro X ⟨d,rfl⟩
  exact ⟨(partitionGenerator ρ ω c hc hc1 n d).positive,(partitionGenerator ρ ω c hc hc1 n d).trace_one⟩

theorem generator_permutation (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (d : PartitionDescription n) (π : Equiv.Perm (Fin n)) :
    (partitionGenerator ρ ω c hc hc1 n d).reindex (sitePermutation b n π) =
      partitionGenerator ρ ω c hc hc1 n (fun i => d.1 (π.symm i),d.2) :=
  partitionState_permutation ρ ω n d.1 _ _ _ π

/-- There are more old labels than surviving sites, so an unused label can be removed. -/
theorem generator_marginal (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (d : PartitionDescription (n+1)) :
    ∃ e : PartitionDescription n,
      discardState n (partitionGenerator ρ ω c hc hc1 (n+1) d) = partitionGenerator ρ ω c hc hc1 n e := by
  let f : Fin n → Fin (n+1) := fun i => d.1 (Fin.castAdd 1 i)
  have hns : ¬Function.Surjective f := by
    intro h
    have hcard := Fintype.card_le_of_surjective f h
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨j,hj⟩ : ∃ j : Fin (n+1), ∀ i, f i≠j := by simpa only [Function.Surjective,not_forall,not_exists] using hns
  have hg : ∀ i, ∃ k : Fin n, j.succAbove k=f i := fun i => Fin.exists_succAbove_eq (hj i)
  choose g hg using hg
  refine ⟨(g,fun i => d.2 (j.succAbove i)),?_⟩
  change discardState n (partitionState ρ ω (n+1) d.1 _ _ _) = _
  rw [discard_partitionState]
  have he : (fun i => d.1 (Fin.castAdd 1 i)) = (fun i => j.succAbove (g i)) := by
    funext i; exact (hg i).symm
  rw [he,partitionState_delete_unused]
  rfl

theorem generator_tensor (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n m : ℕ) (d : PartitionDescription n) (e : PartitionDescription m) :
    ((partitionGenerator ρ ω c hc hc1 n d).tensor (partitionGenerator ρ ω c hc hc1 m e)).reindex
      (channelAddEquiv b n m) =
    partitionGenerator ρ ω c hc hc1 (n+m) (appendLabels n m d.1 e.1,Fin.addCases d.2 e.2) := by
  have hp : blockProbability c (Fin.addCases d.2 e.2) = Fin.addCases (blockProbability c d.2) (blockProbability c e.2) := by
    funext i
    exact Fin.addCases (fun j => by simp [blockProbability]) (fun j => by simp [blockProbability]) i
  have h := partitionState_tensor ρ ω n m d.1 e.1 (blockProbability c d.2) (blockProbability c e.2)
    (blockProbability_nonneg c hc d.2) (blockProbability_le_one c hc1 d.2)
    (blockProbability_nonneg c hc e.2) (blockProbability_le_one c hc1 e.2)
  apply State.eq_of_matrix_eq
  have hh := congrArg State.matrix h.symm
  simpa only [partitionGenerator,hp] using hh

/-- The all-inactive, single-block generator is the faithful product state. -/
theorem omega_power_generator (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (hn : 0<n) : ∃ d : PartitionDescription n,
      partitionGenerator ρ ω c hc hc1 n d=statePower ω n := by
  cases n with
  | zero => omega
  | succ k =>
    refine ⟨(fun _ => 0,fun _ => false),?_⟩
    apply State.eq_of_matrix_eq
    rw [partitionGenerator,partitionState_constant]
    simp [blockProbability]

/-- A single active block is exactly the persistent target mixture. -/
theorem zeta_generator (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (hn : 0<n) : ∃ d : PartitionDescription n,
      (partitionGenerator ρ ω c hc hc1 n d).matrix =
        c • (statePower ρ n).matrix+(1-c) • (statePower ω n).matrix := by
  cases n with
  | zero => omega
  | succ k =>
    refine ⟨(fun _ => 0,fun _ => true),?_⟩
    rw [partitionGenerator,partitionState_constant]
    simp [blockProbability]

end GeneralizedChannelStein.Correlated
