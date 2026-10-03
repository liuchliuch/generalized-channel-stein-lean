import GeneralizedChannelStein.TestingRates
import GeneralizedChannelStein.RoughApproximation

/-! # Discharged numerical bounds for square-block rate improvement -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy ParallelExponent Filter
open scoped Topology

/-- Finite operational exponents agree with the literal base-two expression. -/
theorem testingExponent_eq_real (n : ℕ) (β : ENNReal) (hβ : 0 < β) (htop : β ≠ ⊤) :
    testingExponent n β = ((-Real.logb 2 β.toReal/(n:ℝ) : ℝ):EReal) := by
  rw [← ENNReal.ofReal_toReal htop, testingExponent_ofReal (ENNReal.toReal_pos hβ.ne' htop)]
  rw [ENNReal.toReal_ofReal (ENNReal.toReal_nonneg)]
  congr 1
  unfold Real.logb
  ring

/-- An exponent below r gives the positive lower testing coefficient used in truncation. -/
theorem beta_lower_of_exponent_lt (n : ℕ) (hn : 0 < n) (β : ENNReal)
    (hβ : 0 < β) (htop : β ≠ ⊤) (r : ℝ) (hr : testingExponent n β < (r:EReal)) :
    (2:ℝ)^(-(n:ℝ)*r) < β.toReal := by
  rw [testingExponent_eq_real n β hβ htop] at hr
  have hreal := EReal.coe_lt_coe_iff.mp hr
  apply (Real.lt_logb_iff_rpow_lt (by norm_num) (ENNReal.toReal_pos hβ.ne' htop)).mp
  have h := (div_lt_iff₀ (Nat.cast_pos.mpr hn)).mp hreal
  linarith

/-- A strict scalar rate margin absorbs the common-dominator factor two. -/
theorem rough_cost_bound (n : ℕ) (ε β r₀ r : ℝ)
    (hε : ε ≤ 1) (hβ : 0 < β) (hlow : (2:ℝ)^(-(n:ℝ)*r₀) ≤ β)
    (hmargin : 1 ≤ (n:ℝ)*(r-r₀)) :
    Real.sqrt (2*(ε/β)) ≤ (2:ℝ)^((n:ℝ)*r/2) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have hrecip : 1/β ≤ (2:ℝ)^((n:ℝ)*r₀) := by
    rw [show -(n:ℝ)*r₀ = -((n:ℝ)*r₀) by ring, Real.rpow_neg (by norm_num : (0:ℝ)≤2), ← one_div] at hlow
    have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((n:ℝ)*r₀)
    apply (div_le_iff₀ hβ).mpr
    have h := (div_le_iff₀ hp).mp hlow
    nlinarith
  have heps : ε/β ≤ (2:ℝ)^((n:ℝ)*r₀) :=
    (div_le_div_of_nonneg_right hε hβ.le).trans hrecip
  have hpow : 2*(2:ℝ)^((n:ℝ)*r₀) ≤ (2:ℝ)^((n:ℝ)*r) := by
    conv_lhs => lhs; rw [show (2:ℝ)=(2:ℝ)^(1:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hsq : ((2:ℝ)^((n:ℝ)*r/2))^2 = (2:ℝ)^((n:ℝ)*r) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [hsq]
  linarith

/-- An exponentially small one-block error, before tensor repetition. -/
def strongBlockError (K γ : ℝ) (n : ℕ) : ℝ := Real.sqrt K * Real.exp (-(γ/2)*(n:ℝ))

theorem strongBlockError_nonneg (K γ : ℝ) (n : ℕ) : 0 ≤ strongBlockError K γ n := by
  unfold strongBlockError
  positivity

theorem strongBlockError_sq (K γ : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    strongBlockError K γ n ^ 2 = K*Real.exp (-γ*(n:ℝ)) := by
  unfold strongBlockError
  rw [mul_pow,Real.sq_sqrt hK, ← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem strongBlockError_tendsto (K γ : ℝ) (hγ : 0 < γ) :
    Tendsto (strongBlockError K γ) atTop (𝓝 0) := by
  simpa only [strongBlockError,Real.rpow_one] using
    TwoRateScalars.stretched_error_tendsto_zero (Real.sqrt K)
      (show 0 < γ/2 by linarith) (by norm_num : (0:ℝ)<1)

/-- The polynomial factor from repeating n blocks is dominated by the exponential. -/
theorem scaled_strongBlockError_tendsto (K γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n : ℕ => (n:ℝ)*strongBlockError K γ n) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (γ/2)
    (by linarith)).comp tendsto_natCast_atTop_atTop).const_mul (Real.sqrt K)
  convert h using 1
  · funext n
    simp only [strongBlockError,Function.comp_def,Real.rpow_one]
    ring
  · simp

/-- A finite tensor telescoping loss has a simple exponential envelope. -/
theorem telescoping_error_envelope (n : ℕ) (e : ℝ) (he : 0 ≤ e) :
    (n:ℝ)*e*(1+e)^(n-1) ≤ (n:ℝ)*e*Real.exp ((n:ℝ)*e) := by
  have hbase : 1+e ≤ Real.exp e := by simpa only [add_comm] using Real.add_one_le_exp e
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1+e) hbase (n-1)
  rw [← Real.exp_nat_mul] at hp
  have hnm : ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hle := hp.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnm he))
  exact mul_le_mul_of_nonneg_left hle (mul_nonneg (Nat.cast_nonneg n) he)

/-- The complete square-block error envelope tends to zero. -/
theorem square_block_error_tendsto (K γ κ : ℝ) (hγ : 0 < γ) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => Real.exp (-κ*(n:ℝ))+
      (n:ℝ)*strongBlockError K γ n*Real.exp ((n:ℝ)*strongBlockError K γ n)) atTop (𝓝 0) := by
  have he := scaled_strongBlockError_tendsto K γ hγ
  have h1 : Tendsto (fun n : ℕ => Real.exp (-κ*(n:ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul,Real.rpow_one] using
      TwoRateScalars.stretched_error_tendsto_zero 1 hκ (by norm_num : (0:ℝ)<1)
  simpa only [Real.exp_zero,zero_mul,add_zero] using h1.add (he.mul (Real.continuous_exp.tendsto 0 |>.comp he))

/-- Retained tensor cost has only a linear overhead beyond the square-block rate. -/
theorem square_cost_bound (n : ℕ) (q : ℝ) :
    (3^n*(2:ℝ)^((n:ℝ)*n*q/2))^2 ≤ (2:ℝ)^((n:ℝ)*n*q+4*n) := by
  have hp : (3:ℝ)^n ≤ (4:ℝ)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h4 : (4:ℝ)^n = (2:ℝ)^(2*(n:ℝ)) := by
    rw [show (4:ℝ)=(2:ℝ)^(2:ℝ) by norm_num, ← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  calc
    _ ≤ ((4:ℝ)^n*(2:ℝ)^((n:ℝ)*n*q/2))^2 := by gcongr
    _ = _ := by
      rw [h4, ← Real.rpow_add (by norm_num : (0:ℝ)<2),
        ← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
      congr 1
      ring

/-- Completion's additional unit is absorbed by any fixed positive rate margin. -/
theorem square_cost_add_one_le (n : ℕ) (hn : 0 < n) (q R : ℝ)
    (hq : 0 ≤ q) (hgap : 5 ≤ (n:ℝ)*(R-q)) :
    (2:ℝ)^((n:ℝ)*n*q+4*n)+1 ≤ (2:ℝ)^((n:ℝ)*n*R) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc : 1 ≤ (2:ℝ)^((n:ℝ)*n*q+4*n) := Real.one_le_rpow (by norm_num) (by positivity)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  calc
    _ ≤ 2*(2:ℝ)^((n:ℝ)*n*q+4*n) := by linarith
    _ = (2:ℝ)^(1+((n:ℝ)*n*q+4*n)) := by
      conv_lhs => lhs; rw [show (2:ℝ)=(2:ℝ)^(1:ℝ) by norm_num]
      exact (Real.rpow_add (by norm_num : (0:ℝ)<2) 1 ((n:ℝ)*n*q+4*n)).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hgap hn0]

theorem eventually_nat_mul_ge (g c : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, c ≤ (n:ℝ)*g := by
  have h : ∀ᶠ n : ℕ in atTop, c/g ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (c/g))
  exact h.mono fun n hn => (div_le_iff₀ hg).mp hn

theorem strong_cost_bound (n : ℕ) (s S : ℝ) (hmargin : 1 ≤ (n:ℝ)*(S-s)) :
    Real.sqrt (2*(2:ℝ)^((n:ℝ)*s)) ≤ (2:ℝ)^((n:ℝ)*S/2) := by
  have h := rough_cost_bound n 1 ((2:ℝ)^(-((n:ℝ)*s))) s S le_rfl
    (Real.rpow_pos_of_pos (by norm_num) _) (by rw [neg_mul]) hmargin
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),one_div,inv_inv] at h
  exact h

end GeneralizedChannelStein
