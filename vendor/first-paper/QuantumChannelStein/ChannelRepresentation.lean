import QuantumChannelStein.ChoiConverse

/-!
# Choi reconstruction and finite Kraus representation of linear maps

The Choi matrix determines a complex-linear matrix map. A positive Choi matrix
and trace preservation therefore yield an actual normalized Kraus
representation of that map, with at most `n*m` Kraus slots.
-/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder Kronecker
open Matrix

/-- A complex-linear map between finite matrix spaces. -/
abbrev MatrixMap (n m : ℕ) := Operator n →ₗ[ℂ] Operator m

namespace MatrixMap
variable {n m : ℕ}

/-- Input-first unnormalized Choi matrix of an arbitrary complex-linear map. -/
def choi (Ψ : MatrixMap n m) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun x y => Ψ (Matrix.single x.1 y.1 1) x.2 y.2

/-- A linear matrix map is reconstructed from its values on matrix units. -/
theorem apply_eq_sum (Ψ : MatrixMap n m) (X : Operator n) :
    Ψ X = ∑ i, ∑ j, X i j • Ψ (Matrix.single i j 1) := by
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j 1 := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      Matrix.matrix_eq_sum_single X
  calc
    Ψ X = Ψ (∑ i, ∑ j, X i j • Matrix.single i j 1) := congrArg Ψ hX
    _ = _ := by simp only [map_sum, map_smul]

/-- Entrywise reconstruction from the Choi matrix. -/
theorem apply_eq_sum_choi (Ψ : MatrixMap n m) (X : Operator n)
    (a b : Fin m) :
    Ψ X a b = ∑ i, ∑ j, X i j * choi Ψ (i, a) (j, b) := by
  rw [apply_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, choi]

/-- No information about a complex-linear map is lost in its Choi matrix. -/
theorem choi_injective : Function.Injective (choi (n := n) (m := m)) := by
  intro Ψ Θ h
  apply LinearMap.ext
  intro X
  ext a b
  rw [apply_eq_sum_choi, apply_eq_sum_choi, h]

@[simp] theorem choi_toLinearMap (Φ : KrausChannel n m) :
    choi Φ.toLinearMap = Φ.choi := rfl

/-- Trace preservation is precisely the output marginal identity. -/
theorem traceOutput_choi_of_trace_preserving (Ψ : MatrixMap n m)
    (htr : ∀ X, (Ψ X).trace = X.trace) :
    KrausChannel.traceOutput (choi Ψ) = 1 := by
  ext i j
  change (Ψ (Matrix.single i j 1)).trace = (1 : Operator n) i j
  rw [htr]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]


/-- The output marginal identity forces trace preservation on every input. -/
theorem trace_preserving_of_traceOutput_choi (Ψ : MatrixMap n m)
    (htr : KrausChannel.traceOutput (choi Ψ) = 1) :
    ∀ X, (Ψ X).trace = X.trace := by
  have hunit : ∀ i j, (Ψ (Matrix.single i j 1)).trace = (1 : Operator n) i j := by
    intro i j
    exact congrFun (congrFun htr i) j
  intro X
  rw [apply_eq_sum]
  simp only [Matrix.trace_sum, Matrix.trace_smul, hunit, smul_eq_mul]
  simp [Matrix.one_apply, Matrix.trace, Matrix.diag]

/-- Trace preservation and the unnormalized output marginal identity agree
without any positivity hypothesis. -/
theorem trace_preserving_iff_traceOutput_choi (Ψ : MatrixMap n m) :
    (∀ X, (Ψ X).trace = X.trace) ↔ KrausChannel.traceOutput (choi Ψ) = 1 :=
  ⟨traceOutput_choi_of_trace_preserving Ψ, trace_preserving_of_traceOutput_choi Ψ⟩

/-- A linear matrix map with positive Choi matrix and trace preservation has
an actual normalized Kraus representation, with `n*m` Kraus slots. -/
theorem exists_kraus_of_choi_positive (Ψ : MatrixMap n m)
    (hpos : (choi Ψ).PosSemidef)
    (htr : ∀ X, (Ψ X).trace = X.trace) :
    ∃ Φ : KrausChannel n m, Φ.rank = n * m ∧ Φ.toLinearMap = Ψ := by
  obtain ⟨Φ, hrank, hchoi⟩ := KrausChannel.exists_of_choi (choi Ψ) hpos
    (traceOutput_choi_of_trace_preserving Ψ htr)
  exact ⟨Φ, hrank, choi_injective ((choi_toLinearMap Φ).trans hchoi)⟩

/-- Exact finite-dimensional criterion for a linear map to admit a normalized
Kraus representation. -/
theorem exists_kraus_iff (Ψ : MatrixMap n m) :
    (∃ Φ : KrausChannel n m, Φ.toLinearMap = Ψ) ↔
      (choi Ψ).PosSemidef ∧ (∀ X, (Ψ X).trace = X.trace) := by
  constructor
  · rintro ⟨Φ, rfl⟩
    exact ⟨Φ.choi_positive, Φ.trace_apply⟩
  · rintro ⟨hpos, htr⟩
    obtain ⟨Φ, _, hΦ⟩ := exists_kraus_of_choi_positive Ψ hpos htr
    exact ⟨Φ, hΦ⟩

/-- Apply a linear matrix map to every block of an arbitrary reference system. -/
def amplify (Ψ : MatrixMap n m) (r : ℕ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    Matrix (Fin r × Fin m) (Fin r × Fin m) ℂ :=
  fun x y => Ψ (fun i j => X (x.1, i) (y.1, j)) x.2 y.2

/-- Complete positivity on every finite reference system, defined directly from
an arbitrary linear map rather than from a Kraus presentation. -/
def CompletelyPositive (Ψ : MatrixMap n m) : Prop :=
  ∀ (r : ℕ) (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ),
    X.PosSemidef → (amplify Ψ r X).PosSemidef

/-- The unnormalized maximally-entangled positive matrix on two input copies. -/
def maximallyEntangled (n : ℕ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  let v : Fin n × Fin n → ℂ := fun x => if x.1 = x.2 then 1 else 0
  Matrix.vecMulVec v (star v)

/-- Positivity follows from an explicit rank-one outer product. -/
theorem maximallyEntangled_positive (n : ℕ) :
    (maximallyEntangled n).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

/-- Applying the map to one half of the entangled matrix gives its Choi matrix. -/
theorem amplify_maximallyEntangled (Ψ : MatrixMap n m) :
    amplify Ψ n (maximallyEntangled n) = choi Ψ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change Ψ (fun k l => maximallyEntangled n (i, k) (j, l)) a b =
    Ψ (Matrix.single i j 1) a b
  have hblock : (fun k l => maximallyEntangled n (i, k) (j, l)) =
      Matrix.single i j 1 := by
    ext k l
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [maximallyEntangled, Matrix.vecMulVec, Pi.star_apply, Matrix.single,
        hik, hjl]
  rw [hblock]

/-- Complete positivity of a general linear matrix map forces Choi positivity. -/
theorem choi_positive_of_completelyPositive (Ψ : MatrixMap n m)
    (hΨ : CompletelyPositive Ψ) : (choi Ψ).PosSemidef := by
  rw [← amplify_maximallyEntangled]
  exact hΨ n (maximallyEntangled n) (maximallyEntangled_positive n)

/-- The blockwise arbitrary-map extension agrees exactly with the Kraus extension. -/
@[simp] theorem amplify_toLinearMap (Φ : KrausChannel n m) (r : ℕ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    amplify Φ.toLinearMap r X = Φ.amplify r X := by
  ext ⟨a, u⟩ ⟨b, v⟩
  exact (Φ.amplify_block r X a b u v).symm

/-- Every normalized Kraus channel is completely positive as an arbitrary map. -/
theorem completelyPositive_toLinearMap (Φ : KrausChannel n m) :
    CompletelyPositive Φ.toLinearMap := by
  intro r X hX
  rw [amplify_toLinearMap]
  exact Φ.amplify_positive r hX


/-- An arbitrary finite Kraus family defines a linear map, without imposing
trace normalization. -/
def ofKraus {r : ℕ} (K : Fin r → Matrix (Fin m) (Fin n) ℂ) : MatrixMap n m where
  toFun X := ∑ k, K k * X * (K k)ᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The unnormalized Kraus Choi matrix is the Gram matrix of its columns. -/
theorem choi_ofKraus {r : ℕ} (K : Fin r → Matrix (Fin m) (Fin n) ℂ) :
    choi (ofKraus K) =
      let V : Matrix (Fin n × Fin m) (Fin r) ℂ := fun x k => K k x.2 x.1
      V * Vᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [choi, ofKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single, ite_and]

/-- Blockwise amplification of an arbitrary Kraus map has the expected tensor
Kraus operators, including before trace normalization. -/
theorem amplify_ofKraus {s : ℕ} (K : Fin s → Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    amplify (ofKraus K) r X =
      ∑ k, ((1 : Operator r) ⊗ₖ K k) * X * ((1 : Operator r) ⊗ₖ K k)ᴴ := by
  ext ⟨a, u⟩ ⟨b, v⟩
  simp [amplify, ofKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

/-- Every finite Kraus family defines a completely positive map, independently
of any trace-preserving assumption. -/
theorem completelyPositive_ofKraus {r : ℕ}
    (K : Fin r → Matrix (Fin m) (Fin n) ℂ) : CompletelyPositive (ofKraus K) := by
  intro s X hX
  rw [amplify_ofKraus]
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro k _
    exact hX.mul_mul_conjTranspose_same _

/-- A positive Choi matrix gives an unnormalized finite Kraus representation,
without a trace-preserving assumption. -/
theorem exists_ofKraus_of_choi_positive (Ψ : MatrixMap n m)
    (hpos : (choi Ψ).PosSemidef) :
    ∃ K : Fin (n * m) → Matrix (Fin m) (Fin n) ℂ, ofKraus K = Ψ := by
  obtain ⟨V, hV⟩ := KrausChannel.exists_columns_of_positive (choi Ψ) hpos
  let K : Fin (n * m) → Matrix (Fin m) (Fin n) ℂ := fun k a i => V (i, a) k
  refine ⟨K, choi_injective ?_⟩
  rw [choi_ofKraus]
  exact hV.symm

/-- The full finite-dimensional Choi criterion for arbitrary complex-linear
matrix maps. Complete positivity is quantified over all finite references. -/
theorem completelyPositive_iff_choi_positive (Ψ : MatrixMap n m) :
    CompletelyPositive Ψ ↔ (choi Ψ).PosSemidef := by
  constructor
  · exact choi_positive_of_completelyPositive Ψ
  · intro hpos
    obtain ⟨K, rfl⟩ := exists_ofKraus_of_choi_positive Ψ hpos
    exact completelyPositive_ofKraus K

/-- Every completely positive trace-preserving linear map has a finite normalized
Kraus representation. Neither complete positivity nor factorization is assumed
through a Kraus presentation in this statement. -/
theorem exists_kraus_of_cptp (Ψ : MatrixMap n m)
    (hcp : CompletelyPositive Ψ) (htr : ∀ X, (Ψ X).trace = X.trace) :
    ∃ Φ : KrausChannel n m, Φ.rank = n * m ∧ Φ.toLinearMap = Ψ :=
  exists_kraus_of_choi_positive Ψ (choi_positive_of_completelyPositive Ψ hcp) htr

/-- A linear map is completely positive and trace preserving exactly when it
admits a finite normalized Kraus representation. -/
theorem cptp_iff_exists_kraus (Ψ : MatrixMap n m) :
    (CompletelyPositive Ψ ∧ (∀ X, (Ψ X).trace = X.trace)) ↔
      ∃ Φ : KrausChannel n m, Φ.toLinearMap = Ψ := by
  constructor
  · rintro ⟨hcp, htr⟩
    obtain ⟨Φ, _, hΦ⟩ := exists_kraus_of_cptp Ψ hcp htr
    exact ⟨Φ, hΦ⟩
  · rintro ⟨Φ, rfl⟩
    exact ⟨completelyPositive_toLinearMap Φ, Φ.trace_apply⟩

end MatrixMap
end QuantumChannelStein
