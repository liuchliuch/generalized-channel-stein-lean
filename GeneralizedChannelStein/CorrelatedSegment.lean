import GeneralizedChannelStein.CorrelatedExample

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix PerfectDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b : ℕ}

/-- The one-site generator set has exactly the two endpoints displayed in Example 24. -/
theorem partitionGenerators_one (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) :
    partitionGenerators ρ ω c hc hc1 1 =
      {(statePower ω 1).matrix, c • (statePower ρ 1).matrix+(1-c) • (statePower ω 1).matrix} := by
  ext X
  constructor
  · rintro ⟨d,rfl⟩
    have hf : d.1=(fun _ : Fin 1 => 0) := by funext i; exact Subsingleton.elim _ _
    change (partitionState ρ ω 1 d.1 _ _ _).matrix∈_
    rw [hf,partitionState_constant]
    by_cases htag : d.2 0=true
    · simp [blockProbability,htag]
    · have hf' : d.2 0=false := Bool.eq_false_iff.mpr htag
      simp [blockProbability,hf']
  · intro hX
    rcases (Set.mem_insert_iff.mp hX) with hX | hX
    · obtain ⟨d,hd⟩ := omega_power_generator ρ ω c hc hc1 1 (by norm_num)
      exact ⟨d,(congrArg State.matrix hd).trans hX.symm⟩
    · have hx := Set.mem_singleton_iff.mp hX
      obtain ⟨d,hd⟩ := zeta_generator ρ ω c hc hc1 1 (by norm_num)
      exact ⟨d,hd.trans hx.symm⟩

/-- Literal exact one-site state convex hull. -/
theorem partitionHull_one (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) :
    partitionHull ρ ω c hc hc1 1 = convexHull ℝ
      {(statePower ω 1).matrix, c • (statePower ρ 1).matrix+(1-c) • (statePower ω 1).matrix} := by
  rw [partitionHull,partitionGenerators_one]

/-- Preparation is linear in its unnormalized output matrix. -/
def prepareMatrix (a b : ℕ) : Operator b →ₗ[ℝ] MatrixMap a b where
  toFun B :=
    { toFun := fun X => X.trace • B
      map_add' := by intro X Y; simp [Matrix.trace_add,add_smul]
      map_smul' := by intro z X; simp [Matrix.trace_smul,smul_smul] }
  map_add' B C := by ext X i j; simp [smul_add]
  map_smul' s B := by ext X i j; simp [mul_comm]; ring

/-- The example's actual channel family is the preparation image of its literal state hull. -/
theorem alternativeFamily_eq_prepare_image (ρ ω : State b) (c : ℝ) (hc : 0≤c)
    (hc1 : c≤1) (n : ℕ) : alternativeFamily ρ ω c hc hc1 n =
      prepareMatrix (1^n) (b^n) '' partitionHull ρ ω c hc hc1 n := by
  ext Φ
  constructor
  · rintro ⟨σ,hσ,rfl⟩
    exact ⟨σ.matrix,hσ,rfl⟩
  · rintro ⟨X,hX,rfl⟩
    have hd := partitionHull_density ρ ω c hc hc1 n hX
    exact ⟨⟨X,hd.1,hd.2⟩,hX,rfl⟩

/-- Example 24's displayed F₁=conv{ω,ζ₁}, now on actual preparation-channel maps. -/
theorem alternativeFamily_one (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) :
    alternativeFamily ρ ω c hc hc1 1 = convexHull ℝ
      {ReplacerChannel.linearMap (1^1) (statePower ω 1),
        c • ReplacerChannel.linearMap (1^1) (statePower ρ 1)+
          (1-c) • ReplacerChannel.linearMap (1^1) (statePower ω 1)} := by
  rw [alternativeFamily_eq_prepare_image,partitionHull_one,LinearMap.image_convexHull]
  simp only [Set.image_insert_eq,Set.image_singleton,map_add,map_smul]
  rfl

end GeneralizedChannelStein.Correlated
