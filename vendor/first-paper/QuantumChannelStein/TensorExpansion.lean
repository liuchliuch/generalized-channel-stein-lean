import QuantumChannelStein.TensorPower
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuantumChannelStein.BinomialBounds

/-! # Actual operator-valued tensor expansions -/
noncomputable section
namespace QuantumChannelStein.TensorExpansion
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower

/-- A binary word specifies which factors use the residual. -/
abbrev Word (k : ℕ) := Index Bool k

/-- Number of residual factors. -/
def weight : (k : ℕ) → Word k → ℕ
  | 0, _ => 0
  | k + 1, w => (if w.1 then 1 else 0) + weight k w.2

/-- A genuine ordered tensor word; factors are not multiplied as endomorphisms. -/
def wordTensor {m n : Type*} (A H : Matrix m n ℂ) :
    (k : ℕ) → Word k → Matrix (Index m k) (Index n k) ℂ
  | 0, _ => tensorPower A 0
  | k + 1, w => (if w.1 then H else A) ⊗ₖ wordTensor A H k w.2

/-- Exact noncommutative tensor-binomial expansion. No commutativity of A and H
is required; every factor occupies its own tensor slot. -/
theorem tensorPower_add {m n : Type*} [Fintype m] [Fintype n]
    (A H : Matrix m n ℂ) (k : ℕ) :
    tensorPower (A + H) k = ∑ w : Word k, wordTensor A H k w := by
  induction k with
  | zero => simp [tensorPower, wordTensor, Index]
  | succ k ih =>
    rw [tensorPower_succ, ih]
    ext ⟨i,x⟩ ⟨j,y⟩
    simp [wordTensor, Word, Index, Fintype.sum_prod_type, Matrix.sum_apply,
      Finset.mul_sum, add_mul, Finset.sum_add_distrib, add_comm]

/-- The residual count never exceeds the number of tensor factors. -/
theorem weight_le (k : ℕ) (w : Word k) : weight k w ≤ k := by
  induction k with
  | zero => simp [weight]
  | succ k ih =>
    rcases w with ⟨b,w⟩
    cases b with
    | false => simpa [weight] using (ih w).trans (Nat.le_succ k)
    | true => simpa [weight, Nat.add_comm] using Nat.succ_le_succ (ih w)


/-- Each ordered tensor word has the product norm bound dictated by its
number of residual factors. -/
theorem norm_wordTensor_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ) (k : ℕ) (w : Word k) :
    ‖wordTensor A H k w‖ ≤ ‖A‖ ^ (k - weight k w) * ‖H‖ ^ weight k w := by
  induction k with
  | zero => simpa only [wordTensor, weight, Nat.sub_zero, pow_zero, one_mul]
      using (norm_tensorPower_zero A).le
  | succ k ih =>
    rcases w with ⟨b,w⟩
    cases b with
    | false =>
      have h := (TensorAlgebra.kronecker_opNorm_le A (wordTensor A H k w)).trans
        (mul_le_mul_of_nonneg_left (ih w) (norm_nonneg A))
      have hexp : k + 1 - weight k w = (k - weight k w) + 1 := by
        have := weight_le k w
        omega
      simpa [wordTensor, weight, hexp, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
    | true =>
      have h := (TensorAlgebra.kronecker_opNorm_le H (wordTensor A H k w)).trans
        (mul_le_mul_of_nonneg_left (ih w) (norm_nonneg H))
      have hexp : k + 1 - (1 + weight k w) = k - weight k w := by omega
      simpa [wordTensor, weight, hexp, pow_add, mul_assoc, mul_comm, mul_left_comm] using h


/-- Multiplicative scalar weight of an ordered residual word. -/
def wordCost (a b : ℝ) : (k : ℕ) → Word k → ℝ
  | 0, _ => 1
  | k + 1, w => (if w.1 then b else a) * wordCost a b k w.2

theorem wordCost_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℕ) (w : Word k) : 0 ≤ wordCost a b k w := by
  induction k with
  | zero => simp [wordCost]
  | succ k ih =>
    rcases w with ⟨b',w⟩
    cases b' <;> simp only [wordCost, Bool.false_eq_true, ↓reduceIte]
    · exact mul_nonneg ha (ih w)
    · exact mul_nonneg hb (ih w)

/-- Sum over actual ordered words, without assuming a combinatorial count. -/
theorem sum_wordCost (a b : ℝ) (k : ℕ) :
    (∑ w : Word k, wordCost a b k w) = (a + b) ^ k := by
  induction k with
  | zero => simp [wordCost, Index]
  | succ k ih =>
    change (∑ w : Bool × Word k, (if w.1 then b else a) * wordCost a b k w.2) = _
    simp only [Fintype.sum_prod_type, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte, ← Finset.mul_sum, ih, pow_succ]
    ring

/-- A uniform factor bound controls each genuine tensor word. -/
theorem norm_wordTensor_le_cost {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ)
    {a b : ℝ} (ha : ‖A‖ ≤ a) (hb : ‖H‖ ≤ b) (k : ℕ) (w : Word k) :
    ‖wordTensor A H k w‖ ≤ wordCost a b k w := by
  have ha0 := (norm_nonneg A).trans ha
  have hb0 := (norm_nonneg H).trans hb
  induction k with
  | zero => simpa only [wordTensor, wordCost] using (norm_tensorPower_zero A).le
  | succ k ih =>
    rcases w with ⟨b',w⟩
    cases b' <;> simp only [wordTensor, wordCost, Bool.false_eq_true, ↓reduceIte]
    · exact (TensorAlgebra.kronecker_opNorm_le _ _).trans
        (mul_le_mul ha (ih w) (norm_nonneg _) ha0)
    · exact (TensorAlgebra.kronecker_opNorm_le _ _).trans
        (mul_le_mul hb (ih w) (norm_nonneg _) hb0)

/-- Truncate the actual tensor expansion by the number of residual slots. -/
def truncate {m n : Type*} (A H : Matrix m n ℂ) (k t : ℕ) :
    Matrix (Index m k) (Index n k) ℂ :=
  ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => weight k w ≤ t),
    wordTensor A H k w

/-- The error is exactly the omitted operator sum. -/
theorem tensorPower_sub_truncate {m n : Type*} [Fintype m] [Fintype n]
    (A H : Matrix m n ℂ) (k t : ℕ) :
    tensorPower (A + H) k - truncate A H k t =
      ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => t < weight k w),
        wordTensor A H k w := by
  rw [tensorPower_add]
  have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Word k)))
    (p := fun w => weight k w ≤ t) (f := wordTensor A H k)
  simp only [not_le] at h
  rw [← h]
  simp [truncate]

/-- The true operator truncation error is bounded by the sum of omitted scalar weights. -/
theorem norm_tensorPower_sub_truncate_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ)
    {a b : ℝ} (ha : ‖A‖ ≤ a) (hb : ‖H‖ ≤ b) (k t : ℕ) :
    ‖tensorPower (A + H) k - truncate A H k t‖ ≤
      ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => t < weight k w),
        wordCost a b k w := by
  rw [tensorPower_sub_truncate]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => norm_wordTensor_le_cost A H ha hb k w)


/-- Exponential tilting multiplies each word by its residual-count weight. -/
theorem wordCost_scaled (a b z : ℝ) (k : ℕ) (w : Word k) :
    wordCost a (z * b) k w = z ^ weight k w * wordCost a b k w := by
  induction k with
  | zero => simp [wordCost, weight]
  | succ k ih =>
    rcases w with ⟨b',w⟩
    cases b' <;> simp [wordCost, weight, ih, pow_add] <;> ring

/-- A real cutoff retains precisely those actual words within its residual budget. -/
def truncateAt {m n : Type*} (A H : Matrix m n ℂ) (k : ℕ) (u : ℝ) :
    Matrix (Index m k) (Index n k) ℂ :=
  ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => (weight k w : ℝ) ≤ u),
    wordTensor A H k w

theorem tensorPower_sub_truncateAt {m n : Type*} [Fintype m] [Fintype n]
    (A H : Matrix m n ℂ) (k : ℕ) (u : ℝ) :
    tensorPower (A + H) k - truncateAt A H k u =
      ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => u < (weight k w : ℝ)),
        wordTensor A H k w := by
  rw [tensorPower_add]
  have h := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Word k)))
    (p := fun w => (weight k w : ℝ) ≤ u) (f := wordTensor A H k)
  simp only [not_le] at h
  rw [← h]
  simp [truncateAt]

/-- Operator-valued Chernoff truncation bound. Both the tensor expansion and
its Hilbert-operator-norm estimate have been proved; no scalar tail oracle is assumed. -/
theorem operator_truncation_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ)
    {a b z : ℝ} (ha : ‖A‖ ≤ a) (hb : ‖H‖ ≤ b) (hz : 1 ≤ z)
    (k : ℕ) (u : ℝ) :
    ‖tensorPower (A + H) k - truncateAt A H k u‖ ≤ z ^ (-u) * (a + z * b) ^ k := by
  have ha0 := (norm_nonneg A).trans ha
  have hb0 := (norm_nonneg H).trans hb
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  let s := (Finset.univ : Finset (Word k)).filter (fun w => u < (weight k w : ℝ))
  have hnorm : ‖tensorPower (A + H) k - truncateAt A H k u‖ ≤
      ∑ w ∈ s, wordCost a b k w := by
    rw [tensorPower_sub_truncateAt]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun w _ => norm_wordTensor_le_cost A H ha hb k w)
  have hweighted : z ^ u * (∑ w ∈ s, wordCost a b k w) ≤ (a + z * b) ^ k := by
    rw [Finset.mul_sum]
    calc
      (∑ w ∈ s, z ^ u * wordCost a b k w) ≤ ∑ w ∈ s, wordCost a (z * b) k w := by
        apply Finset.sum_le_sum
        intro w hw
        rw [wordCost_scaled]
        apply mul_le_mul_of_nonneg_right _ (wordCost_nonneg ha0 hb0 k w)
        have hw' : u ≤ (weight k w : ℝ) := (Finset.mem_filter.mp hw).2.le
        simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hz hw'
      _ ≤ ∑ w : Word k, wordCost a (z * b) k w := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro w _ _
        exact wordCost_nonneg ha0 (mul_nonneg hzpos.le hb0) k w
      _ = (a + z * b) ^ k := sum_wordCost a (z * b) k
  have hdiv : (∑ w ∈ s, wordCost a b k w) ≤ (a + z * b) ^ k / z ^ u := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hzpos u)).mpr
    simpa only [mul_comm] using hweighted
  rw [Real.rpow_neg hzpos.le]
  exact hnorm.trans (by simpa only [div_eq_mul_inv, mul_comm] using hdiv)


/-- The exponentially small *operator* tail from the fixed-block construction
in Lemma 4.5, with the paper's exact choice of tilting weight. -/
theorem operator_truncation_half_pow {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η)
    (hA : ‖A‖ ≤ 1 + ε) (hH : ‖H‖ ≤ ε)
    (hsmall : ε ≤ 1 / (1 + (4 : ℝ) ^ (1 / η))) (k : ℕ) :
    ‖tensorPower (A + H) k - truncateAt A H k (η * k)‖ ≤ (1 / 2 : ℝ) ^ k := by
  let z : ℝ := (4 : ℝ) ^ (1 / η)
  have hz : 1 ≤ z := Real.one_le_rpow (by norm_num) (by positivity)
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hzη : z ^ η = 4 := by
    dsimp [z]
    simpa only [one_div] using Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 4) hη.ne'
  have hden : 0 < 1 + z := by positivity
  have hsmall' : ε * (1 + z) ≤ 1 := (le_div_iff₀ hden).mp hsmall
  have hbase : 1 + ε + z * ε ≤ 2 := by nlinarith
  have hbase0 : 0 ≤ 1 + ε + z * ε := by positivity
  have hratio : (z ^ η)⁻¹ * (1 + ε + z * ε) ≤ 1 / 2 := by
    rw [hzη]
    nlinarith
  calc
    ‖tensorPower (A + H) k - truncateAt A H k (η * k)‖ ≤
        z ^ (-(η * k)) * (1 + ε + z * ε) ^ k :=
      operator_truncation_bound A H hA hH hz k (η * k)
    _ = ((z ^ η)⁻¹ * (1 + ε + z * ε)) ^ k := by
      rw [Real.rpow_neg hzpos.le, Real.rpow_mul_natCast hzpos.le, ← inv_pow, mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hzpos.le _)) hbase0) hratio k


/-- Closed form of a word's multiplicative scalar weight. -/
theorem wordCost_eq (a b : ℝ) (k : ℕ) (w : Word k) :
    wordCost a b k w = a ^ (k - weight k w) * b ^ weight k w := by
  induction k with
  | zero => simp [wordCost, weight]
  | succ k ih =>
    rcases w with ⟨b',w⟩
    cases b' with
    | false =>
      have hexp : k + 1 - weight k w = (k - weight k w) + 1 := by
        have := weight_le k w
        omega
      simp [wordCost, weight, ih, hexp, pow_succ, mul_comm, mul_left_comm]
    | true =>
      have hexp : k + 1 - (1 + weight k w) = k - weight k w := by omega
      simp [wordCost, weight, ih, hexp, pow_add, mul_assoc, mul_comm]

/-- The cost factor `3^k` counts the actual retained tensor words. -/
theorem sum_two_pow_weight (k : ℕ) :
    (∑ w : Word k, (2 : ℝ) ^ weight k w) = 3 ^ k := by
  simpa only [wordCost_eq, one_pow, one_mul, show (1 : ℝ) + 2 = 3 by norm_num] using
    sum_wordCost 1 2 k

/-- Turning a uniform rate bound for each word into the operator cost estimate. -/
theorem norm_truncateAt_le_weighted {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ) (k : ℕ) (u B : ℝ)
    (hB : 0 ≤ B)
    (hword : ∀ w : Word k, (weight k w : ℝ) ≤ u →
      ‖wordTensor A H k w‖ ≤ (2 : ℝ) ^ weight k w * B) :
    ‖truncateAt A H k u‖ ≤ 3 ^ k * B := by
  unfold truncateAt
  calc
    ‖∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => (weight k w : ℝ) ≤ u),
        wordTensor A H k w‖ ≤
        ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => (weight k w : ℝ) ≤ u),
          (2 : ℝ) ^ weight k w * B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => hword w (Finset.mem_filter.mp hw).2)
    _ ≤ ∑ w : Word k, (2 : ℝ) ^ weight k w * B := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro w _ _
      positivity
    _ = 3 ^ k * B := by rw [← Finset.sum_mul, sum_two_pow_weight]


/-- The fixed-block retained operator has the paper's actual `3^k` rate cost,
not merely an abstract scalar sum bound. -/
theorem operator_truncation_rate_cost {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A H : Matrix m n ℂ)
    (l k : ℕ) (S L η : ℝ) (hSL : S ≤ L)
    (hA : ‖A‖ ≤ (2 : ℝ) ^ ((l : ℝ) * S / 2))
    (hH : ‖H‖ ≤ 2 * (2 : ℝ) ^ ((l : ℝ) * L / 2)) :
    ‖truncateAt A H k (η * k)‖ ≤
      3 ^ k * (2 : ℝ) ^ ((l : ℝ) * k * (S + η * (L - S)) / 2) := by
  apply norm_truncateAt_le_weighted A H k (η * k) _ (by positivity)
  intro w hw
  have hword := norm_wordTensor_le_cost A H hA hH k w
  rw [wordCost_eq] at hword
  have hrewrite : ((2 : ℝ) ^ ((l : ℝ) * S / 2)) ^ (k - weight k w) *
      (2 * (2 : ℝ) ^ ((l : ℝ) * L / 2)) ^ weight k w =
      (2 : ℝ) ^ weight k w *
        (2 : ℝ) ^ ((l : ℝ) * (((k - weight k w : ℕ) : ℝ) * S + weight k w * L) / 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ∀ x y z : ℝ, x * (y * z) = y * (x * z) from fun x y z => by ring]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  rw [hrewrite] at hword
  exact hword.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (truncated_rate_exponent_le l k (weight k w) S L η (weight_le k w) hw hSL))
    (by positivity))

end QuantumChannelStein.TensorExpansion






