import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Scalar estimates for weighted discarding, Lemma 27 of arXiv:2609.30762.
The active regime `m ≤ n/2` is a hypothesis, never asserted uniformly in ξ. -/
noncomputable section
namespace GeneralizedChannelStein.WeightedDiscardingScalars
open Real

def ell (n ξ : ℝ) : ℝ := Real.log ((n + 1) / ξ)
def dampingExponent (d n ξ : ℝ) : ℝ :=
  (d ^ 2 + 2) * Real.log (n + d ^ 2 + 1) + Real.log (4 / ξ)
def logConstant (d : ℝ) : ℝ := (d ^ 2 + 2) * (d ^ 2 + 1) + 2

theorem log_four_ge_one : 1 ≤ Real.log 4 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  have he : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  norm_num at h
  linarith

theorem log_four_le_ell {n ξ : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) : Real.log 4 ≤ ell n ξ := by
  apply Real.log_le_log (by norm_num)
  apply (le_div_iff₀ hξ).2
  linarith

theorem one_le_ell {n ξ : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) : 1 ≤ ell n ξ :=
  log_four_ge_one.trans (log_four_le_ell hn hξ hξu)

theorem dampingExponent_le {d n ξ : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) : dampingExponent d n ξ ≤ logConstant d * ell n ξ := by
  have he := one_le_ell hn hξ hξu
  have hnp : 0 < n + 1 := by linarith
  have hdp : 0 < d^2 + 1 := by positivity
  have hnl : Real.log (n + 1) ≤ ell n ξ := by
    apply Real.log_le_log hnp
    apply (le_div_iff₀ hξ).2
    nlinarith
  have hil : Real.log (1 / ξ) ≤ ell n ξ := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hξ.le
    linarith
  have hdl := Real.log_le_sub_one_of_pos hdp
  have hN : Real.log (n + d^2 + 1) ≤ Real.log (n+1) + d^2 := by
    calc
      _ ≤ Real.log ((n+1)*(d^2+1)) := by
        apply Real.log_le_log (by positivity)
        nlinarith [sq_nonneg d, mul_nonneg hn (sq_nonneg d)]
      _ = Real.log (n+1) + Real.log (d^2+1) := Real.log_mul hnp.ne' hdp.ne'
      _ ≤ _ := by linarith
  have hNh : Real.log (n+d^2+1) ≤ (d^2+1) * ell n ξ := by
    nlinarith [mul_nonneg (sq_nonneg d) (show 0 ≤ ell n ξ - 1 by linarith)]
  have hξl : Real.log (4/ξ) ≤ 2 * ell n ξ := by
    rw [show (4:ℝ)/ξ = 4*(1/ξ) by ring, Real.log_mul (by norm_num) (by positivity)]
    linarith [log_four_le_ell hn hξ hξu]
  unfold dampingExponent logConstant
  nlinarith [mul_le_mul_of_nonneg_left hNh (show 0 ≤ d^2+2 by positivity)]

theorem dampingExponent_nonneg {d n ξ : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) : 0 ≤ dampingExponent d n ξ := by
  have hN : 0 ≤ Real.log (n+d^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg d])
  have hx : 0 ≤ Real.log (4/ξ) := Real.log_nonneg ((le_div_iff₀ hξ).2 (by linarith))
  unfold dampingExponent
  positivity

theorem polynomial_damping_error {d n ξ v : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) (hv : 0 ≤ v)
    (hvb : v ≤ (n+d^2+1) ^ (d^2-1)) :
    v * Real.exp (-dampingExponent d n ξ) +
      2 * v * Real.exp (-2 * dampingExponent d n ξ) ≤ ξ := by
  have hNp : 0 < n+d^2+1 := by positivity
  have hNl : 0 ≤ Real.log (n+d^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg d])
  have hpow : (n+d^2+1) ^ (d^2-1) = Real.exp ((d^2-1)*Real.log (n+d^2+1)) := by
    rw [Real.rpow_def_of_pos hNp, mul_comm]
  have hmain : v * Real.exp (-dampingExponent d n ξ) ≤ ξ/4 := by
    calc
      _ ≤ Real.exp ((d^2-1)*Real.log (n+d^2+1)) *
          Real.exp (-dampingExponent d n ξ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        simpa [hpow] using hvb
      _ = Real.exp (-3*Real.log (n+d^2+1)) * Real.exp (-Real.log (4/ξ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold dampingExponent
        ring
      _ ≤ 1 * Real.exp (-Real.log (4/ξ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact Real.exp_le_one_iff.mpr (by linarith)
      _ = ξ/4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have htail : Real.exp (-2*dampingExponent d n ξ) ≤
      Real.exp (-dampingExponent d n ξ) := by
    apply Real.exp_le_exp.mpr
    linarith [dampingExponent_nonneg hn hξ hξu (d := d)]
  have := mul_le_mul_of_nonneg_left htail hv
  nlinarith

def dampingScale (d t : ℝ) : ℝ := Real.sqrt (2 * logConstant d / t)
def supportConstant (d t : ℝ) : ℝ :=
  Real.exp 2 * dampingScale d t + logConstant d + 1

theorem logConstant_pos (d : ℝ) : 0 < logConstant d := by
  unfold logConstant
  positivity

theorem active_log_bound {n ξ s m : ℝ} (hs : 0 < s) (hn : n = s^3)
    (hm : s^2 * ell n ξ ≤ m) (hma : m ≤ n/2) : ell n ξ ≤ s/2 := by
  have hsq : 0 < s^2 := sq_pos_of_pos hs
  nlinarith

theorem dampingScale_pos {d t : ℝ} (ht : 0 < t) : 0 < dampingScale d t := by
  unfold dampingScale
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (by norm_num) (logConstant_pos d)) ht

theorem damping_parameter_bound {d n ξ s m t : ℝ}
    (hn0 : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hs : 0 < s) (ht : 0 < t) (hm : s^2 * ell n ξ ≤ m) :
    Real.sqrt (2*dampingExponent d n ξ/(t*m)) ≤ dampingScale d t / s := by
  have he := one_le_ell hn0 hξ hξu
  have hmp : 0 < m := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hs) (by linarith)) hm
  have hC := dampingScale_pos (d := d) ht
  have hCsq : dampingScale d t ^ 2 = 2 * logConstant d / t := by
    apply Real.sq_sqrt
    exact (div_pos (mul_pos (by norm_num) (logConstant_pos d)) ht).le
  apply Real.sqrt_le_iff.2
  refine ⟨(div_pos hC hs).le, ?_⟩
  rw [div_pow, hCsq]
  apply (div_le_div_iff₀ (mul_pos ht hmp) (sq_pos_of_pos hs)).2
  have hh := dampingExponent_le (d := d) hn0 hξ hξu
  have hA := logConstant_pos d
  have ht0 : t ≠ 0 := ht.ne'
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg s),
    mul_le_mul_of_nonneg_left hm hA.le]

def dampingParameter (d n ξ t m : ℝ) : ℝ :=
  Real.sqrt (2*dampingExponent d n ξ/(t*m))
def supportDegree (d n ξ t m k : ℝ) : ℕ :=
  ⌈Real.exp 2 * k * dampingParameter d n ξ t m + 2*dampingExponent d n ξ⌉₊

theorem block_damping_bound {d n ξ s m t k : ℝ}
    (hn0 : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hs : 0 < s) (ht : 0 < t) (hn : n = s^3)
    (hm : s^2 * ell n ξ ≤ m) (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    k * dampingParameter d n ξ t m ≤ dampingScale d t * s^2 := by
  have hu := damping_parameter_bound hn0 hξ hξu hs ht hm (d := d)
  change dampingParameter d n ξ t m ≤ dampingScale d t / s at hu
  calc
    _ ≤ k * (dampingScale d t / s) := mul_le_mul_of_nonneg_left hu hk0
    _ ≤ n * (dampingScale d t / s) := mul_le_mul_of_nonneg_right hkn (by positivity [dampingScale_pos (d := d) ht])
    _ = dampingScale d t * s^2 := by rw [hn]; field_simp

theorem support_degree_bound {d n ξ s m t k : ℝ}
    (hn0 : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hs : 1 ≤ s) (ht : 0 < t) (hn : n = s^3)
    (hm : s^2 * ell n ξ ≤ m) (hma : m ≤ n/2)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    (supportDegree d n ξ t m k : ℝ) ≤ supportConstant d t * s^2 := by
  have hsp : 0 < s := by linarith
  have hku := block_damping_bound hn0 hξ hξu hsp ht hn hm hk0 hkn (d := d)
  have hel := active_log_bound hsp hn hm hma
  have hh := dampingExponent_le (d := d) hn0 hξ hξu
  have hA := logConstant_pos d
  have hexp := Real.exp_pos (2:ℝ)
  have hnonneg : 0 ≤ Real.exp 2*k*dampingParameter d n ξ t m +
      2*dampingExponent d n ξ := by
    have := dampingExponent_nonneg (d := d) hn0 hξ hξu
    unfold dampingParameter
    positivity
  have hc := Nat.ceil_lt_add_one hnonneg
  change (supportDegree d n ξ t m k : ℝ) < _ at hc
  have hhs : 2*dampingExponent d n ξ ≤ logConstant d*s := by
    nlinarith [mul_le_mul_of_nonneg_left hel hA.le]
  have hs2 : s ≤ s^2 := by nlinarith
  have h1s2 : 1 ≤ s^2 := by nlinarith
  unfold supportConstant
  nlinarith [mul_le_mul_of_nonneg_left hku hexp.le,
    mul_le_mul_of_nonneg_left hs2 hA.le]

theorem polynomial_mass_le_exp {d n ξ v : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) (hvb : v ≤ (n+d^2+1) ^ (d^2-1)) :
    v ≤ Real.exp (dampingExponent d n ξ) := by
  have hNp : 0 < n+d^2+1 := by positivity
  have hNl : 0 ≤ Real.log (n+d^2+1) := Real.log_nonneg (by nlinarith [sq_nonneg d])
  have hξl : 0 ≤ Real.log (4/ξ) := Real.log_nonneg ((le_div_iff₀ hξ).2 (by linarith))
  apply hvb.trans
  rw [Real.rpow_def_of_pos hNp]
  apply Real.exp_le_exp.mpr
  unfold dampingExponent
  nlinarith

theorem coefficient_mass_bound {d n ξ s m t k v : ℝ}
    (hn0 : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hs : 1 ≤ s) (ht : 0 < t) (hn : n = s^3)
    (hm : s^2 * ell n ξ ≤ m) (hma : m ≤ n/2)
    (hk0 : 0 ≤ k) (hkn : k ≤ n)
    (hvb : v ≤ (n+d^2+1) ^ (d^2-1)) :
    v * Real.exp (k*dampingParameter d n ξ t m) ≤
      Real.exp ((logConstant d + dampingScale d t)*s^2) := by
  have hsp : 0 < s := by linarith
  have hel := active_log_bound hsp hn hm hma
  have hh := dampingExponent_le (d := d) hn0 hξ hξu
  have hA := logConstant_pos d
  have hku := block_damping_bound hn0 hξ hξu hsp ht hn hm hk0 hkn (d := d)
  calc
    _ ≤ Real.exp (dampingExponent d n ξ) *
        Real.exp (k*dampingParameter d n ξ t m) :=
      mul_le_mul_of_nonneg_right (polynomial_mass_le_exp hn0 hξ hξu hvb) (Real.exp_pos _).le
    _ = Real.exp (dampingExponent d n ξ + k*dampingParameter d n ξ t m) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs2 : s/2 ≤ s^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hel hA.le,
        mul_le_mul_of_nonneg_left hs2 hA.le]

theorem damping_lt_one {d n ξ s m t : ℝ}
    (hn0 : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hs : 0 < s) (ht : 0 < t) (hm : s^2*ell n ξ ≤ m)
    (hlarge : dampingScale d t < s) : dampingParameter d n ξ t m < 1 := by
  exact (damping_parameter_bound hn0 hξ hξu hs ht hm).trans_lt
    ((div_lt_one hs).2 hlarge)

theorem support_degree_lt_remaining {d n ξ s m t k : ℝ}
    (hn0 : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hs : 1 ≤ s) (ht : 0 < t) (hn : n = s^3)
    (hm : s^2*ell n ξ ≤ m) (hma : m ≤ n/2)
    (hk : k = n-m) (hlarge : 2*supportConstant d t < s) :
    (supportDegree d n ξ t m k : ℝ) < k := by
  have hsp : 0 < s := by linarith
  have he := one_le_ell hn0 hξ hξu
  have hm0 : 0 ≤ m := le_trans (mul_nonneg (sq_nonneg s) (by linarith)) hm
  have hk0 : 0 ≤ k := by linarith
  have hkn : k ≤ n := by linarith
  have hb := support_degree_bound hn0 hξ hξu hs ht hn hm hma hk0 hkn (d := d)
  have hsq : 0 < s^2 := sq_pos_of_pos hsp
  have := mul_lt_mul_of_pos_right hlarge hsq
  nlinarith

theorem cube_root_id {n : ℝ} (hn : 0 ≤ n) : (n ^ (1/3:ℝ))^3 = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

theorem cube_root_sq {n : ℝ} (hn : 0 ≤ n) : (n ^ (1/3:ℝ))^2 = n ^ (2/3:ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

def scaleThreshold (d t : ℝ) : ℝ :=
  max 1 (max (dampingScale d t + 1) (2*supportConstant d t + 1))
def blockThreshold (d t : ℝ) : ℕ := ⌈scaleThreshold d t ^ 3⌉₊
def discardCount (n ξ : ℝ) : ℕ := ⌈n ^ (2/3:ℝ) * ell n ξ⌉₊

theorem cube_root_ge_threshold {d t : ℝ} {n : ℕ}
    (hn : blockThreshold d t ≤ n) : scaleThreshold d t ≤ (n:ℝ) ^ (1/3:ℝ) := by
  have hT : 0 ≤ scaleThreshold d t := le_trans (by norm_num) (le_max_left _ _)
  have hn0 : 0 ≤ (n:ℝ) := by positivity
  apply (pow_le_pow_iff_left₀ hT (Real.rpow_nonneg hn0 _) (by decide : (3:ℕ) ≠ 0)).1
  rw [cube_root_id hn0]
  exact (Nat.le_ceil (scaleThreshold d t ^ 3)).trans (by exact_mod_cast hn)

/-- Explicit uniform numerical bounds, with the paper's active-regime assumption. -/
theorem paper_scalar_bounds {d t ξ : ℝ} {n : ℕ}
    (ht : 0 < t) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hn : blockThreshold d t ≤ n)
    (hma : (discardCount n ξ : ℝ) ≤ (n:ℝ)/2) :
    let m : ℝ := discardCount n ξ
    let k : ℝ := n-m
    let u := dampingParameter d n ξ t m
    let R : ℝ := supportDegree d n ξ t m k
    u ≤ dampingScale d t * (n:ℝ) ^ (-(1/3:ℝ)) ∧
    R ≤ supportConstant d t * (n:ℝ) ^ (2/3:ℝ) ∧ u < 1 ∧ R < k := by
  dsimp only
  let s : ℝ := (n:ℝ) ^ (1/3:ℝ)
  have hn0 : 0 ≤ (n:ℝ) := by positivity
  have hsT := cube_root_ge_threshold hn
  change scaleThreshold d t ≤ s at hsT
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hsT
  have hsp : 0 < s := by linarith
  have hns : (n:ℝ) = s^3 := (cube_root_id hn0).symm
  have hss : s^2 = (n:ℝ) ^ (2/3:ℝ) := cube_root_sq hn0
  have hm : s^2*ell n ξ ≤ (discardCount n ξ : ℝ) := by
    rw [hss]
    exact Nat.le_ceil _
  have hm0 : 0 ≤ (discardCount n ξ : ℝ) := by positivity
  have hk0 : 0 ≤ (n:ℝ) - discardCount n ξ := by linarith
  have hkn : (n:ℝ) - discardCount n ξ ≤ n := by linarith
  have hC : dampingScale d t < s := by
    have := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hsT
    linarith
  have hB : 2*supportConstant d t < s := by
    have := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hsT
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hu := damping_parameter_bound hn0 hξ hξu hsp ht hm (d := d)
    simpa [dampingParameter, Real.rpow_neg hn0, div_eq_mul_inv, s] using hu
  · simpa [hss] using support_degree_bound hn0 hξ hξu hs1 ht hns hm hma hk0 hkn (d := d)
  · exact damping_lt_one hn0 hξ hξu hsp ht hm hC
  · exact support_degree_lt_remaining hn0 hξ hξu hs1 ht hns hm hma rfl hB

theorem coefficient_constant_le_support {d t : ℝ} (ht : 0 < t) :
    logConstant d + dampingScale d t ≤ supportConstant d t := by
  have hC := dampingScale_pos (d := d) ht
  have he : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp (by norm_num)
  unfold supportConstant
  nlinarith [mul_nonneg (show 0 ≤ Real.exp (2:ℝ)-1 by linarith) hC.le]

theorem paper_coefficient_mass_bound {d t ξ v : ℝ} {n : ℕ}
    (ht : 0 < t) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16)
    (hn : blockThreshold d t ≤ n)
    (hma : (discardCount n ξ : ℝ) ≤ (n:ℝ)/2)
    (hvb : v ≤ ((n:ℝ)+d^2+1) ^ (d^2-1)) :
    v * Real.exp (((n:ℝ)-discardCount n ξ) *
      dampingParameter d n ξ t (discardCount n ξ)) ≤
      Real.exp (supportConstant d t * (n:ℝ) ^ (2/3:ℝ)) := by
  let s : ℝ := (n:ℝ) ^ (1/3:ℝ)
  have hn0 : 0 ≤ (n:ℝ) := by positivity
  have hsT := cube_root_ge_threshold hn
  change scaleThreshold d t ≤ s at hsT
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hsT
  have hns : (n:ℝ) = s^3 := (cube_root_id hn0).symm
  have hss : s^2 = (n:ℝ) ^ (2/3:ℝ) := cube_root_sq hn0
  have hm : s^2*ell n ξ ≤ (discardCount n ξ : ℝ) := by
    rw [hss]
    exact Nat.le_ceil _
  have hm0 : 0 ≤ (discardCount n ξ : ℝ) := by positivity
  have hk0 : 0 ≤ (n:ℝ) - discardCount n ξ := by linarith
  have hkn : (n:ℝ) - discardCount n ξ ≤ n := by linarith
  have hc := coefficient_mass_bound hn0 hξ hξu hs1 ht hns hm hma hk0 hkn hvb
  apply hc.trans
  apply Real.exp_le_exp.mpr
  rw [← hss]
  exact mul_le_mul_of_nonneg_right (coefficient_constant_le_support ht) (sq_nonneg s)

theorem two_h_le_support_degree {d n ξ t m k : ℝ} (hk : 0 ≤ k) :
    2*dampingExponent d n ξ ≤ (supportDegree d n ξ t m k : ℝ) := by
  apply le_trans _ (Nat.le_ceil _)
  have : 0 ≤ Real.exp 2*k*dampingParameter d n ξ t m := by
    unfold dampingParameter
    positivity
  linarith

theorem exp_scale_le_support_degree {d n ξ t m k : ℝ}
    (hn : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16) :
    Real.exp 2*k*dampingParameter d n ξ t m ≤ (supportDegree d n ξ t m k : ℝ) := by
  apply le_trans _ (Nat.le_ceil _)
  linarith [dampingExponent_nonneg (d := d) hn hξ hξu]

theorem truncated_error_le {d n ξ t m k v : ℝ}
    (hn : 0 ≤ n) (hξ : 0 < ξ) (hξu : ξ ≤ 1/16) (hk : 0 ≤ k)
    (hv : 0 ≤ v) (hvb : v ≤ (n+d^2+1) ^ (d^2-1)) :
    v * Real.exp (-dampingExponent d n ξ) +
      2*v*Real.exp (-(supportDegree d n ξ t m k : ℝ)) ≤ ξ := by
  have hR := two_h_le_support_degree (d := d) (n := n) (ξ := ξ) (t := t) (m := m) hk
  have he : Real.exp (-(supportDegree d n ξ t m k : ℝ)) ≤
      Real.exp (-2*dampingExponent d n ξ) := Real.exp_le_exp.mpr (by linarith)
  have := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*v by positivity)
  linarith [polynomial_damping_error hn hξ hξu hv hvb]

theorem truncated_binomial_mass_le_exp (k R : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hR : R ≤ k) :
    (∑ r ∈ Finset.range (R+1), (k.choose r : ℝ)*u^r) ≤ Real.exp ((k:ℝ)*u) := by
  calc
    _ ≤ ∑ r ∈ Finset.range (k+1), (k.choose r : ℝ)*u^r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hR 1))
      intro r _ _
      positivity
    _ = (u+1)^k := by
      rw [add_pow]
      simp [mul_comm]
    _ ≤ (Real.exp u)^k := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp u) k
    _ = Real.exp ((k:ℝ)*u) := (Real.exp_nat_mul u k).symm

theorem weighted_truncated_mass_le (k R : ℕ) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hR : R ≤ k) :
    v*(∑ r ∈ Finset.range (R+1), (k.choose r : ℝ)*u^r) ≤ v*Real.exp ((k:ℝ)*u) :=
  mul_le_mul_of_nonneg_left (truncated_binomial_mass_le_exp k R hu hR) hv

end GeneralizedChannelStein.WeightedDiscardingScalars
