import GeneralizedChannelStein.WeightedDiscardingScalars

noncomputable section
namespace GeneralizedChannelStein.Lemma27Parameters
open WeightedDiscardingScalars

def m (n : ℕ) (ξ : ℝ) : ℕ := discardCount n ξ
def k (n : ℕ) (ξ : ℝ) : ℕ := n - m n ξ
def u (d t ξ : ℝ) (n : ℕ) : ℝ := dampingParameter d n ξ t (m n ξ)
def h (d ξ : ℝ) (n : ℕ) : ℝ := dampingExponent d n ξ
def R (d t ξ : ℝ) (n : ℕ) : ℕ := supportDegree d n ξ t (m n ξ) (k n ξ)

/-- Numerical interfaces for the literal natural-number split in Lemma 27. -/
structure Parameters (d t ξ : ℝ) (n : ℕ) : Prop where
  n_pos : 0 < n
  m_pos : 0 < m n ξ
  k_pos : 0 < k n ξ
  split : k n ξ + m n ξ = n
  cast_k : (k n ξ : ℝ) = (n : ℝ) - m n ξ
  h_nonneg : 0 ≤ h d ξ n
  u_nonneg : 0 ≤ u d t ξ n
  u_lt_one : u d t ξ n < 1
  cancellation : h d ξ n = (m n ξ : ℝ) * (t * (u d t ξ n)^2 / 2)
  cutoff : Real.exp 2 * (k n ξ : ℝ) * u d t ξ n + 2 * h d ξ n ≤ R d t ξ n
  support_bound : (R d t ξ n : ℝ) ≤ supportConstant d t * (n : ℝ)^(2/3:ℝ)
  support_lt : R d t ξ n < k n ξ
  mass_bound : ∀ v : ℝ, v ≤ ((n:ℝ)+d^2+1)^(d^2-1) →
    v * Real.exp ((k n ξ : ℝ)*u d t ξ n) ≤
      Real.exp (supportConstant d t * (n:ℝ)^(2/3:ℝ))
  error_bound : ∀ v : ℝ, 0 ≤ v → v ≤ ((n:ℝ)+d^2+1)^(d^2-1) →
    v * Real.exp (-h d ξ n) ≤ ξ

theorem paper_parameters {d t ξ : ℝ} {n : ℕ}
    (ht : 0 < t) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hn : blockThreshold d t ≤ n)
    (hma : (discardCount n ξ : ℝ) ≤ (n:ℝ)/2) : Parameters d t ξ n := by
  have hs := cube_root_ge_threshold hn
  have hs1 : 1 ≤ (n:ℝ)^(1/3:ℝ) := (le_max_left _ _).trans hs
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := by omega
    subst n
    norm_num at hs1
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hnpos
  have he := one_le_ell hnr.le hξ hξu
  have hmp : 0 < (m n ξ : ℝ) := by
    have hc : (n:ℝ)^(2/3:ℝ)*ell n ξ ≤ (m n ξ : ℝ) := Nat.le_ceil _
    have hp : 0 < (n:ℝ)^(2/3:ℝ)*ell n ξ := mul_pos (Real.rpow_pos_of_pos hnr _) (by linarith)
    exact hp.trans_le hc
  have hmn : m n ξ ≤ n := by
    have : (m n ξ : ℝ) ≤ n := by change (discardCount n ξ : ℝ) ≤ n; linarith
    exact_mod_cast this
  have hcast : (k n ξ : ℝ) = (n:ℝ)-m n ξ := Nat.cast_sub hmn
  have hkp : 0 < k n ξ := by
    have : 0 < (k n ξ : ℝ) := by rw [hcast]; change 0 < (n:ℝ)-discardCount n ξ; linarith
    exact_mod_cast this
  have hh := dampingExponent_nonneg (d := d) hnr.le hξ hξu
  have hb := paper_scalar_bounds ht hξ hξu hn hma
  dsimp only at hb
  refine ⟨hnpos, by exact_mod_cast hmp, hkp, Nat.sub_add_cancel hmn, hcast,
    hh, Real.sqrt_nonneg _, ?_, ?_, Nat.le_ceil _, ?_, ?_, ?_, ?_⟩
  · exact hb.2.2.1
  · unfold h u dampingParameter
    rw [Real.sq_sqrt (by positivity)]
    have hmne := ne_of_gt hmp
    field_simp
  · simpa only [R, hcast, m] using hb.2.1
  · have hh' : (R d t ξ n : ℝ) < (k n ξ : ℝ) := by
      simpa only [R, hcast, m] using hb.2.2.2
    exact_mod_cast hh'
  · intro v hv
    simpa only [hcast, u, m] using paper_coefficient_mass_bound ht hξ hξu hn hma hv
  · intro v hv hvb
    have he := polynomial_damping_error hnr.le hξ hξu hv hvb
    have hp : 0 ≤ 2*v*Real.exp (-2*dampingExponent d n ξ) := by positivity
    change v * Real.exp (-dampingExponent d n ξ) ≤ ξ
    linarith

end GeneralizedChannelStein.Lemma27Parameters
