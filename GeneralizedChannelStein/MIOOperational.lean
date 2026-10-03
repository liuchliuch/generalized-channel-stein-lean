import GeneralizedChannelStein.CoherenceFamilies

/-! Supplemental operational bridge for the MIO definition.

The existing family definition and Proposition 20 are unchanged. This connects
the literal all-matrix equation to preservation of every normalized diagonal
density operator, including the actual tensor-power coordinate bridge.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.MIOOperational
open QuantumChannelStein Matrix ChannelPowerReindex
open scoped BigOperators Kronecker ComplexOrder
variable {a b : ℕ}

/-- Literal coordinate diagonality, with no channel equation in the definition. -/
def IsDiagonal {d : ℕ} (X : Operator d) : Prop :=
  ∀ i j, i ≠ j → X i j = 0

/-- Every diagonal normalized density operator is sent to a diagonal output. -/
def PreservesDiagonalStates (Φ : KrausChannel a b) : Prop :=
  ∀ ρ : State a, IsDiagonal ρ.matrix → IsDiagonal (Φ.onState ρ).matrix

theorem diagonalChannel_fixed_iff {d : ℕ} (X : Operator d) :
    (SharpDivergence.diagonalChannel d).apply X = X ↔ IsDiagonal X := by
  rw [SharpDivergence.diagonalChannel_apply]
  constructor
  · intro h i j hij
    have he := congrArg (fun Y : Operator d => Y i j) h
    simpa [Matrix.diagonal_apply, hij] using he.symm
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.diag]
    · simp [hij, h i j hij]

/-- A computational-basis projection is a genuine normalized input state. -/
def basisState {d : ℕ} (i : Fin d) : State d where
  matrix := Matrix.diagonal (fun j => if j = i then (1 : ℂ) else 0)
  positive := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    split_ifs <;> simp
  trace_one := by simp [Matrix.trace, Matrix.diag]

theorem basisState_diagonal {d : ℕ} (i : Fin d) : IsDiagonal (basisState i).matrix := by
  intro j k hjk
  simp [basisState, hjk]

/-- Arbitrary complex diagonal matrices are in the complex span of basis states. -/
theorem diagonal_expansion {d : ℕ} (X : Operator d) :
    Matrix.diagonal X.diag = ∑ i : Fin d, X i i • (basisState i).matrix := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [basisState, Matrix.sum_apply, Matrix.smul_apply, Matrix.diag]
  · simp [basisState, Matrix.sum_apply, Matrix.smul_apply, hjk]

/-- Operational MIO is equivalent to the dephasing equation on all matrices. -/
theorem equation_iff_preservesDiagonalStates (Φ : KrausChannel a b) :
    (∀ X : Operator a,
      (SharpDivergence.diagonalChannel b).apply
          (Φ.apply ((SharpDivergence.diagonalChannel a).apply X)) =
        Φ.apply ((SharpDivergence.diagonalChannel a).apply X)) ↔
      PreservesDiagonalStates Φ := by
  constructor
  · intro h ρ hρ
    have hfix := (diagonalChannel_fixed_iff ρ.matrix).mpr hρ
    apply (diagonalChannel_fixed_iff (Φ.apply ρ.matrix)).mp
    simpa only [hfix] using h ρ.matrix
  · intro h X
    have hb (i : Fin a) :
        (SharpDivergence.diagonalChannel b).toLinearMap
            (Φ.toLinearMap (basisState i).matrix) =
          Φ.toLinearMap (basisState i).matrix :=
      (diagonalChannel_fixed_iff (Φ.apply (basisState i).matrix)).mpr
        (h (basisState i) (basisState_diagonal i))
    have hX : (SharpDivergence.diagonalChannel a).apply X =
        ∑ i : Fin a, X i i • (basisState i).matrix :=
      (SharpDivergence.diagonalChannel_apply X).trans (diagonal_expansion X)
    rw [hX]
    change (SharpDivergence.diagonalChannel b).toLinearMap
        (Φ.toLinearMap (∑ i : Fin a, X i i • (basisState i).matrix)) =
      Φ.toLinearMap (∑ i : Fin a, X i i • (basisState i).matrix)
    simp only [map_sum, map_smul, hb]

/-- Product dephasing is exactly dephasing in the flattened product basis. -/
theorem diagonalChannel_tensor (d e : ℕ) :
    ((SharpDivergence.diagonalChannel d).tensor
      (SharpDivergence.diagonalChannel e)).toLinearMap =
      (SharpDivergence.diagonalChannel (d * e)).toLinearMap := by
  apply matrixMap_ext_product
  intro X Y
  change ((SharpDivergence.diagonalChannel d).tensor
      (SharpDivergence.diagonalChannel e)).apply
        (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
    (SharpDivergence.diagonalChannel (d * e)).apply
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y))
  rw [KrausChannel.tensor_apply_product]
  simp only [SharpDivergence.diagonalChannel_apply]
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂
  all_goals
    simp [Matrix.reindex_apply, Matrix.diag, Prod.mk.injEq, h₁, h₂]

theorem cast_map_congr {d e : ℕ} (h : d = e) (Φ Ψ : KrausChannel d d)
    (hΦ : Φ.toLinearMap = Ψ.toLinearMap) :
    (Φ.cast h h).toLinearMap = (Ψ.cast h h).toLinearMap := by
  cases h
  exact hΦ

theorem diagonalChannel_cast {d e : ℕ} (h : d = e) :
    ((SharpDivergence.diagonalChannel d).cast h h).toLinearMap =
      (SharpDivergence.diagonalChannel e).toLinearMap := by
  cases h
  rfl

/-- The actual recursive tensor power has exactly the full block dephasing action. -/
theorem diagonalChannel_tensorPower (d n : ℕ) :
    ((SharpDivergence.diagonalChannel d).tensorPower n).toLinearMap =
      (SharpDivergence.diagonalChannel (d ^ n)).toLinearMap := by
  induction n with
  | zero =>
      change (KrausChannel.identity 1).toLinearMap =
        (SharpDivergence.diagonalChannel 1).toLinearMap
      ext X i j
      change (KrausChannel.identity 1).apply X i j =
        (SharpDivergence.diagonalChannel 1).apply X i j
      rw [KrausChannel.identity_apply, SharpDivergence.diagonalChannel_apply]
      simp [Matrix.diag, Subsingleton.elim i j]
  | succ n ih =>
      have ht : ((SharpDivergence.diagonalChannel d).tensor
          ((SharpDivergence.diagonalChannel d).tensorPower n)).toLinearMap =
          (SharpDivergence.diagonalChannel (d * d ^ n)).toLinearMap := by
        rw [← MatrixMap.tensor_kraus_toLinearMap, ih,
          MatrixMap.tensor_kraus_toLinearMap]
        exact diagonalChannel_tensor d (d ^ n)
      let hdim : d * d ^ n = d ^ (n + 1) := by rw [Nat.pow_succ']
      exact (cast_map_congr hdim _ _ ht).trans (diagonalChannel_cast hdim)

/-- Membership in the existing full MIO family is exactly the operational
diagonal-density preservation property, for every blocklength. -/
theorem mem_MIOFamily_iff (n : ℕ) (Φ : KrausChannel (a ^ n) (b ^ n)) :
    Φ.toLinearMap ∈ MIOFamily a b n ↔ PreservesDiagonalStates Φ := by
  have hA (X : Operator (a ^ n)) :
      ((SharpDivergence.diagonalChannel a).tensorPower n).apply X =
        (SharpDivergence.diagonalChannel (a ^ n)).apply X :=
    congrArg (fun f : MatrixMap (a ^ n) (a ^ n) => f X)
      (diagonalChannel_tensorPower a n)
  have hB (Y : Operator (b ^ n)) :
      ((SharpDivergence.diagonalChannel b).tensorPower n).apply Y =
        (SharpDivergence.diagonalChannel (b ^ n)).apply Y :=
    congrArg (fun f : MatrixMap (b ^ n) (b ^ n) => f Y)
      (diagonalChannel_tensorPower b n)
  constructor
  · intro h
    apply (equation_iff_preservesDiagonalStates Φ).mp
    intro X
    simpa only [hA, hB] using h.2 X
  · intro h
    refine ⟨(isChannel_iff_kraus _).mpr ⟨Φ, rfl⟩, ?_⟩
    intro X
    simpa only [hA, hB] using (equation_iff_preservesDiagonalStates Φ).mpr h X

/-- The same operational characterization directly for the original linear-map
family, without requiring callers to choose a Kraus representation. -/
theorem mem_MIOFamily_iff_map (n : ℕ) (Φ : MatrixMap (a ^ n) (b ^ n)) :
    Φ ∈ MIOFamily a b n ↔ IsChannel Φ ∧
      ∀ ρ : State (a ^ n), IsDiagonal ρ.matrix → IsDiagonal (Φ ρ.matrix) := by
  by_cases hΦ : IsChannel Φ
  · obtain ⟨Ψ, rfl⟩ := (isChannel_iff_kraus Φ).mp hΦ
    constructor
    · intro h
      exact ⟨hΦ, (mem_MIOFamily_iff n Ψ).mp h⟩
    · rintro ⟨_, h⟩
      exact (mem_MIOFamily_iff n Ψ).mpr h
  · constructor
    · intro h
      exact False.elim (hΦ h.1)
    · rintro ⟨h, _⟩
      exact False.elim (hΦ h)

end GeneralizedChannelStein.MIOOperational
