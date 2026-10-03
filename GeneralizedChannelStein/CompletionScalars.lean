import GeneralizedChannelStein.WeightedDiscardingScalars
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section
namespace GeneralizedChannelStein.CompletionScalars
open Real WeightedDiscardingScalars

/-- Fixed geometric truncation index. -/
def correctionDegree (q ξ : ℝ) : ℕ := ⌈Real.log (1/ξ) / (-Real.log q)⌉₊
def correctionRate (q : ℝ) : ℝ := 1 / (-Real.log q) + 2

theorem correctionDegree_bounds {q ξ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1/16) :
    q ^ (correctionDegree q ξ + 1) ≤ ξ ∧
    (correctionDegree q ξ + 1 : ℕ) ≤ correctionRate q * Real.log (1/ξ) := by
  have hlogq : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hlogξ : 1 ≤ Real.log (1/ξ) := by
    have := one_le_ell (n := 0) (by norm_num) hξ hξ1
    simpa [ell] using this
  have hc : Real.log (1/ξ) / (-Real.log q) ≤ (correctionDegree q ξ : ℝ) := Nat.le_ceil _
  have hcu : (correctionDegree q ξ : ℝ) < Real.log (1/ξ) / (-Real.log q) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  constructor
  · have hex : ((correctionDegree q ξ : ℝ)+1)*Real.log q ≤ -Real.log (1/ξ) := by
      have hh := (div_le_iff₀ hlogq).mp hc
      have hl : Real.log q < 0 := by linarith
      nlinarith
    have he := Real.exp_le_exp.mpr hex
    rw [Real.exp_neg, Real.exp_log (by positivity)] at he
    rw [add_mul, Real.exp_add, Real.exp_nat_mul, Real.exp_log hq] at he
    simpa [pow_succ, Real.exp_log hq] using he
  · push_cast
    unfold correctionRate
    simp only [div_eq_mul_inv, one_mul] at hcu hlogξ ⊢
    nlinarith

/-- Replacing δ by the fixed multiple κδ changes the logarithm only by a fixed factor. -/
def precisionFactor (κ : ℝ) : ℝ := 1 + Real.log (1/κ)

theorem precision_log_bounds {κ δ n : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/16) (hn : 0 ≤ n) :
    1 ≤ ell n δ ∧ 1 ≤ precisionFactor κ ∧
    ell n (κ*δ) ≤ precisionFactor κ * ell n δ ∧
    Real.log (1/(κ*δ)) ≤ precisionFactor κ * ell n δ ∧
    Real.log (2/(κ*δ)) ≤ (precisionFactor κ+1) * ell n δ := by
  have he := one_le_ell hn hδ hδ1
  have hlκ : 0 ≤ Real.log (1/κ) := Real.log_nonneg ((le_div_iff₀ hκ).mpr (by simpa using hκ1))
  have hsplit : ell n (κ*δ) = ell n δ + Real.log (1/κ) := by
    unfold ell
    rw [show (n+1)/(κ*δ) = ((n+1)/δ)*(1/κ) by ring]
    exact Real.log_mul (by positivity) (by positivity)
  have hb : ell n (κ*δ) ≤ precisionFactor κ * ell n δ := by
    rw [hsplit]
    unfold precisionFactor
    nlinarith
  have h1 : Real.log (1/(κ*δ)) ≤ ell n (κ*δ) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h2 : Real.log 2 ≤ (1:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this ⊢
    exact this
  have hh2 : Real.log (2/(κ*δ)) = Real.log 2 + Real.log (1/(κ*δ)) := by
    rw [show (2:ℝ)/(κ*δ) = 2*(1/(κ*δ)) by ring]
    exact Real.log_mul (by norm_num) (by positivity)
  refine ⟨he, by unfold precisionFactor; linarith, hb, h1.trans hb, ?_⟩
  rw [hh2]
  nlinarith [h1.trans hb]


def blockScale (n : ℕ) : ℝ := (n:ℝ)^(2/3:ℝ)
def projectorDegree (k : ℕ) (ξ : ℝ) : ℕ := ⌈Real.sqrt k * Real.log (2/ξ)⌉₊

theorem blockScale_ge_one {n : ℕ} (hn : 0 < n) : 1 ≤ blockScale n := by
  unfold blockScale
  exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)

theorem sqrt_le_blockScale {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Real.sqrt k ≤ blockScale n := by
  apply (Real.sqrt_le_sqrt (show (k:ℝ) ≤ (n:ℝ) by exact_mod_cast hk)).trans
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

theorem truncation_indices_bound {κ δ : ℝ} {n k : ℕ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/16)
    (hn : 0 < n) (hk : k ≤ n) :
    (discardCount n (κ*δ) : ℝ) ≤ (precisionFactor κ+1)*blockScale n*ell n δ ∧
    (projectorDegree k (κ*δ) : ℝ) ≤ (precisionFactor κ+2)*blockScale n*ell n δ := by
  obtain ⟨he,hA,hlog,hlog1,hlog2⟩ := precision_log_bounds hκ hκ1 hδ hδ1 (by positivity : 0 ≤ (n:ℝ))
  have hs := blockScale_ge_one hn
  have hx : 0 < κ*δ := mul_pos hκ hδ
  have hxu : κ*δ ≤ 1/16 := (mul_le_of_le_one_left hδ.le hκ1).trans hδ1
  have hell := one_le_ell (by positivity : 0 ≤ (n:ℝ)) hx hxu
  have hlog2pos : 0 ≤ Real.log (2/(κ*δ)) := Real.log_nonneg ((le_div_iff₀ hx).mpr (by linarith))
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ blockScale n * ell n (κ*δ) by positivity)
  change (discardCount n (κ*δ) : ℝ) < blockScale n * ell n (κ*δ) + 1 at hceil
  have hproj := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt k * Real.log (2/(κ*δ)) by positivity)
  change (projectorDegree k (κ*δ) : ℝ) < Real.sqrt k * Real.log (2/(κ*δ)) + 1 at hproj
  have hse : 1 ≤ blockScale n * ell n δ := by nlinarith
  constructor
  · have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ blockScale n by linarith)
    nlinarith
  · have hp := mul_le_mul (sqrt_le_blockScale hn hk) hlog2 hlog2pos (by linarith : 0 ≤ blockScale n)
    nlinarith


def correctionCost (lam MP : ℝ) (L : ℕ) : ℝ := lam*(L+1)*(1+lam*MP)^L

def logarithmicCost (A B D b : ℝ) : ℝ :=
  A*(1+Real.log 2+B) + D*Real.log 15 + (A*B+D)*Real.log b

/-- A literal correction polynomial has exponentially bounded coefficient cost. -/
theorem correctionCost_le_exp {lam MP B s e A : ℝ} {L : ℕ}
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hMP : 0 ≤ MP)
    (hMPb : MP ≤ Real.exp (B*s)) (hB : 0 ≤ B) (hs : 1 ≤ s) (_he : 1 ≤ e)
    (hL : (L:ℝ)+1 ≤ A*e) :
    correctionCost lam MP L ≤ Real.exp (A*(1+Real.log 2+B)*s*e) := by
  have hs0 : 0 ≤ s := by linarith
  have hbase : 1+lam*MP ≤ Real.exp (Real.log 2+B*s) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
    have hmul := mul_le_of_le_one_left hMP hlam1
    have hex : 1 ≤ Real.exp (B*s) := Real.one_le_exp (mul_nonneg hB hs0)
    linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1+lam*MP by positivity) hbase L
  rw [← Real.exp_nat_mul] at hp
  have hpre : lam*((L:ℝ)+1) ≤ Real.exp ((L:ℝ)+1) := by
    have hm := mul_le_of_le_one_left (show 0 ≤ (L:ℝ)+1 by positivity) hlam1
    have hx := Real.add_one_le_exp ((L:ℝ)+1)
    linarith
  have hcost : correctionCost lam MP L ≤
      Real.exp (((L:ℝ)+1)+(L:ℝ)*(Real.log 2+B*s)) := by
    rw [Real.exp_add]
    exact mul_le_mul hpre hp (by positivity) (Real.exp_pos _).le
  apply hcost.trans (Real.exp_le_exp.mpr ?_)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcoef : 0 ≤ 1+Real.log 2+B := by positivity
  have hsmall : 1+Real.log 2+B*s ≤ (1+Real.log 2+B)*s := by
    nlinarith [mul_nonneg hlog (show 0 ≤ s-1 by linarith)]
  have hfirst := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (L:ℝ)+1 by positivity)
  have hlast := mul_le_mul_of_nonneg_right hL (mul_nonneg hcoef hs0)
  nlinarith [mul_nonneg (show 0 ≤ Real.log 2+B*s by positivity) (show (0:ℝ) ≤ 1 by norm_num)]

/-- The exact projector and support weights preserve the uniform exponential budget. -/
theorem weighted_cost_le_exp {lam MP B s e A D b : ℝ} {L R S : ℕ}
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hMP : 0 ≤ MP)
    (hMPb : MP ≤ Real.exp (B*s)) (hB : 0 ≤ B) (hs : 1 ≤ s) (he : 1 ≤ e)
    (hA : 0 ≤ A) (_hD : 0 ≤ D) (hb : 1 ≤ b)
    (hL : (L:ℝ)+1 ≤ A*e) (hR : (R:ℝ) ≤ B*s) (hS : (S:ℝ) ≤ D*s*e) :
    correctionCost lam MP L * 15^S * b^(L*R+S) ≤
      Real.exp (logarithmicCost A B D b * s * e) := by
  have hs0 : 0 ≤ s := by linarith
  have he0 : 0 ≤ e := by linarith
  have hLc : (L:ℝ) ≤ A*e := by linarith
  have hLR := mul_le_mul hLc hR (by positivity : (0:ℝ) ≤ R) (mul_nonneg hA he0)
  have hsupport : ((L*R+S : ℕ):ℝ) ≤ (A*B+D)*s*e := by
    push_cast
    nlinarith
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  have hl15 : 0 ≤ Real.log 15 := Real.log_nonneg (by norm_num)
  have hproject : (15:ℝ)^S ≤ Real.exp (D*Real.log 15*s*e) := by
    conv_lhs => rw [← Real.exp_log (by norm_num : (0:ℝ)<15), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hS hl15]
  have hweight : b^(L*R+S) ≤ Real.exp ((A*B+D)*Real.log b*s*e) := by
    conv_lhs => rw [← Real.exp_log hb0, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hsupport hlb]
  have hcorr := correctionCost_le_exp hlam hlam1 hMP hMPb hB hs he hL
  calc
    _ ≤ (Real.exp (A*(1+Real.log 2+B)*s*e) * Real.exp (D*Real.log 15*s*e)) *
        Real.exp ((A*B+D)*Real.log b*s*e) :=
      mul_le_mul (mul_le_mul hcorr hproject (by positivity) (Real.exp_pos _).le)
        hweight (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold logarithmicCost; ring


def uniformCost (κ q B b r : ℝ) : ℝ :=
  Real.log 2 + 2*logarithmicCost (correctionRate q * precisionFactor κ) B
    (precisionFactor κ+2) b + (precisionFactor κ+1)*Real.log r

theorem logarithmicCost_nonneg {A B D b : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hb : 1 ≤ b) : 0 ≤ logarithmicCost A B D b := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h15 : 0 ≤ Real.log 15 := Real.log_nonneg (by norm_num)
  have hb' : 0 ≤ Real.log b := Real.log_nonneg hb
  unfold logarithmicCost
  positivity

/-- Converting an actual weighted coefficient budget to the paper's base-two loss. -/
theorem loss_of_exp_bound {H C M s e r : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hs : 1 ≤ s) (he : 1 ≤ e) (hr : 1 ≤ r)
    (hH : H ≤ Real.exp (C*s*e)) (hm : (m:ℝ) ≤ M*s*e) :
    1+2*Real.logb 2 (max 1 H)+(m:ℝ)*Real.logb 2 r ≤
      (Real.log 2+2*C+M*Real.log r)*s*(e/Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hse : 1 ≤ s*e := by nlinarith
  have hmax : max 1 H ≤ Real.exp (C*s*e) := max_le
    (Real.one_le_exp (by positivity)) hH
  have hlog : Real.log (max 1 H) ≤ C*s*e := by
    have := Real.log_le_log (show (0:ℝ) < max 1 H by exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hmax
    simpa only [Real.log_exp] using this
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hml := mul_le_mul_of_nonneg_right hm hlr
  have hnumer : Real.log 2 + 2*Real.log (max 1 H)+(m:ℝ)*Real.log r ≤
      (Real.log 2+2*C+M*Real.log r)*s*e := by
    nlinarith [mul_le_mul_of_nonneg_left hse h2.le]
  have hdiv := (div_le_div_iff_of_pos_right h2).mpr hnumer
  convert hdiv using 1 <;> (try simp only [Real.logb]) <;> field_simp

/-- Uniform active-regime cost, with all constants fixed before n and δ. -/
theorem active_completion_loss {κ q B b r lam MP δ H : ℝ} {n k R : ℕ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hq : 0 < q) (hq1 : q < 1)
    (hB : 0 ≤ B) (hb : 1 ≤ b) (hr : 1 ≤ r)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hMP : 0 ≤ MP)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/16) (hn : 0 < n) (hk : k ≤ n)
    (hMPb : MP ≤ Real.exp (B*blockScale n)) (hR : (R:ℝ) ≤ B*blockScale n)
    (hH : H ≤ correctionCost lam MP (correctionDegree q (κ*δ)) *
      15^(projectorDegree k (κ*δ)) *
      b^(correctionDegree q (κ*δ)*R+projectorDegree k (κ*δ))) :
    1+2*Real.logb 2 (max 1 H)+(discardCount n (κ*δ):ℝ)*Real.logb 2 r ≤
      uniformCost κ q B b r * blockScale n * Real.logb 2 (((n:ℝ)+1)/δ) := by
  obtain ⟨he,hA,hlog,hlog1,hlog2⟩ := precision_log_bounds hκ hκ1 hδ hδ1 (by positivity : 0 ≤ (n:ℝ))
  have hs := blockScale_ge_one hn
  have hqlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hrate : 0 ≤ correctionRate q := by unfold correctionRate; positivity
  have hξ : 0 < κ*δ := mul_pos hκ hδ
  have hξ1 : κ*δ ≤ 1/16 := (mul_le_of_le_one_left hδ.le hκ1).trans hδ1
  have hL := (correctionDegree_bounds hq hq1 hξ hξ1).2
  have hL' : (correctionDegree q (κ*δ):ℝ)+1 ≤
      (correctionRate q*precisionFactor κ)*ell n δ := by
    push_cast at hL
    have := mul_le_mul_of_nonneg_left hlog1 hrate
    nlinarith
  obtain ⟨hm,hS⟩ := truncation_indices_bound hκ hκ1 hδ hδ1 hn hk
  have hAA : 0 ≤ correctionRate q*precisionFactor κ := mul_nonneg hrate (by linarith)
  have hDD : 0 ≤ precisionFactor κ+2 := by linarith
  have hcost := weighted_cost_le_exp hlam hlam1 hMP hMPb hB hs he hAA hDD hb hL' hR hS
  have hfinal := loss_of_exp_bound (logarithmicCost_nonneg hAA hB hDD hb) hs he hr (hH.trans hcost) hm
  simpa only [uniformCost, Real.logb, ell] using hfinal


def fallbackCost (κ r : ℝ) (N : ℕ) : ℝ :=
  ((N:ℝ)+2*(precisionFactor κ+1)+4)*Real.log r

def totalUniformCost (κ q B b r : ℝ) (N : ℕ) : ℝ :=
  uniformCost κ q B b r + fallbackCost κ r N

/-- Outside the active range, the faithful replacer has the same uniform scaling. -/
theorem inactive_completion_loss {κ δ r : ℝ} {n N : ℕ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/16)
    (hn : 0 < n) (hr : 1 ≤ r)
    (hbad : n < N ∨ (n:ℝ)/2 < (discardCount n (κ*δ):ℝ) ∨
      n-discardCount n (κ*δ) < 2) :
    (n:ℝ)*Real.logb 2 r ≤
      fallbackCost κ r N * blockScale n * Real.logb 2 (((n:ℝ)+1)/δ) := by
  obtain ⟨he,hA,hlog,hlog1,hlog2⟩ := precision_log_bounds hκ hκ1 hδ hδ1 (by positivity : 0 ≤ (n:ℝ))
  have hs := blockScale_ge_one hn
  have hse : 1 ≤ blockScale n*ell n δ := by nlinarith
  have hm := (truncation_indices_bound hκ hκ1 hδ hδ1 hn (le_refl n)).1
  have hM : 0 ≤ precisionFactor κ+1 := by linarith
  have hmain : (n:ℝ) ≤ ((N:ℝ)+2*(precisionFactor κ+1)+4)*blockScale n*ell n δ := by
    rcases hbad with hsmall | hlarge | hk
    · have hnN : (n:ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hsmall)
      have := mul_le_mul_of_nonneg_left hse (show (0:ℝ) ≤ N by positivity)
      have hp : 0 ≤ (2*(precisionFactor κ+1)+4)*(blockScale n*ell n δ) := by positivity
      nlinarith
    · have hN : 0 ≤ (N:ℝ)*(blockScale n*ell n δ) := by positivity
      nlinarith
    · by_cases hmactive : (discardCount n (κ*δ):ℝ) ≤ (n:ℝ)/2
      · have hmle : discardCount n (κ*δ) ≤ n := by
          have : (discardCount n (κ*δ):ℝ) ≤ n := by linarith
          exact_mod_cast this
        have hkreal : ((n:ℝ)-(discardCount n (κ*δ):ℝ)) < 2 := by
          rw [← Nat.cast_sub hmle]
          exact_mod_cast hk
        have hn4 : (n:ℝ) < 4 := by linarith
        have hp : 0 ≤ ((N:ℝ)+2*(precisionFactor κ+1))*(blockScale n*ell n δ) := by positivity
        nlinarith
      · have hlarge := lt_of_not_ge hmactive
        have hN : 0 ≤ (N:ℝ)*(blockScale n*ell n δ) := by positivity
        nlinarith
  have hlr := Real.log_nonneg hr
  have hmul := mul_le_mul_of_nonneg_right hmain hlr
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right h2).mpr hmul
  convert hdiv using 1 <;> simp only [Real.logb, fallbackCost, ell] <;> ring

 theorem uniformCost_pos {κ q B b r : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 ≤ B) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    0 < uniformCost κ q B b r := by
  have hA : 1 ≤ precisionFactor κ := by
    unfold precisionFactor
    have := Real.log_nonneg ((le_div_iff₀ hκ).mpr (by simpa using hκ1))
    linarith
  have hrate : 0 ≤ correctionRate q := by
    unfold correctionRate
    have : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
    positivity
  have hC := logarithmicCost_nonneg (mul_nonneg hrate (by linarith : 0 ≤ precisionFactor κ))
    hB (by linarith : 0 ≤ precisionFactor κ+2) hb
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlr := Real.log_nonneg hr
  unfold uniformCost
  positivity

 theorem fallbackCost_nonneg {κ r : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hr : 1 ≤ r) (N : ℕ) : 0 ≤ fallbackCost κ r N := by
  have hA : 0 ≤ Real.log (1/κ) := Real.log_nonneg ((le_div_iff₀ hκ).mpr (by simpa using hκ1))
  have hlr := Real.log_nonneg hr
  unfold fallbackCost precisionFactor
  positivity


/-- One explicit positive constant covers both branches before choosing n and δ. -/
theorem totalUniformCost_bounds {κ q B b r : ℝ} (N : ℕ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hq : 0 < q) (hq1 : q < 1)
    (hB : 0 ≤ B) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    0 < totalUniformCost κ q B b r N ∧
    uniformCost κ q B b r ≤ totalUniformCost κ q B b r N ∧
    fallbackCost κ r N ≤ totalUniformCost κ q B b r N := by
  have hU := uniformCost_pos hκ hκ1 hq hq1 hB hb hr
  have hF := fallbackCost_nonneg hκ hκ1 hr N
  unfold totalUniformCost
  constructor
  · linarith
  constructor <;> linarith

end GeneralizedChannelStein.CompletionScalars
