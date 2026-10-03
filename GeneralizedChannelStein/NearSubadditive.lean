import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! A balanced-halving proof of the near-subadditivity lemma (Lemma 34).
The power-error result is slightly stronger than the paper's logarithmic error.
All sequence indices in hypotheses are positive; the value at zero is immaterial. -/

noncomputable section
open Filter Set Asymptotics
open scoped Topology

namespace GeneralizedChannelStein.NearSubadditive

private theorem power_gap {x y q : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hq : q < 1) (hxy : x ≤ (2 / 3 : ℝ) * (x+y))
    (hyx : y ≤ (2 / 3 : ℝ) * (x+y)) :
    (2 / 3 : ℝ) ^ (q-1) * (x+y)^q ≤ x^q+y^q := by
  have h1 := Real.rpow_le_rpow_of_nonpos hx hxy (by linarith : q-1 ≤ 0)
  have h2 := Real.rpow_le_rpow_of_nonpos hy hyx (by linarith : q-1 ≤ 0)
  have he (z : ℝ) (hz : 0 < z) : z * z^(q-1) = z^q := by
    rw [Real.rpow_sub_one hz.ne']; field_simp
  have hs : 0 < x+y := add_pos hx hy
  have hm := add_le_add (mul_le_mul_of_nonneg_left h1 hx.le)
    (mul_le_mul_of_nonneg_left h2 hy.le)
  rw [he x hx, he y hy] at hm
  rw [← add_mul, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2/3) hs.le] at hm
  calc
    (2/3:ℝ)^(q-1)*(x+y)^q = (x+y)*((2/3:ℝ)^(q-1)*(x+y)^(q-1)) := by
      rw [← he (x+y) hs]; ring
    _ ≤ x^q+y^q := hm

/-- Balanced splits control the cumulative error by a concave-power potential. -/
theorem multiples_bound {a : ℕ → ℝ} {K q : ℝ} (hK : 0 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hadd : ∀ n m, 0 < n → 0 < m →
      a (n+m) ≤ a n + a m + K * ((n+m:ℕ):ℝ)^q) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k m : ℕ, 0 < k → 0 < m →
      a (m*k) ≤ (m:ℝ)*a k + D * ((m:ℝ)-(m:ℝ)^q) * (k:ℝ)^q := by
  let B : ℝ := (2/3:ℝ)^(q-1)
  have hB : 1 < B := Real.one_lt_rpow_of_pos_of_lt_one_of_neg
    (by norm_num) (by norm_num) (by linarith)
  let D := K / (B-1)
  have hD : 0 ≤ D := div_nonneg hK (by linarith)
  have hDK : D*(B-1) = K := div_mul_cancel₀ K (by linarith)
  refine ⟨D,hD,?_⟩
  intro k m hk hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst m; simp
    have hm2 : 2 ≤ m := by omega
    let u := m/2
    let v := m-u
    have hu : 0 < u := by dsimp [u]; omega
    have hv : 0 < v := by dsimp [v,u]; omega
    have hum : u < m := Nat.div_lt_self hm (by norm_num)
    have hvm : v < m := by dsimp [v]; omega
    have huv : u+v=m := by dsimp [v]; omega
    have hbal1 : (u:ℝ) ≤ (2/3:ℝ)*((u:ℝ)+v) := by
      have : 3*u ≤ 2*m := by dsimp [u]; omega
      have hr : (3:ℝ)*u ≤ 2*m := by exact_mod_cast this
      have he : (u:ℝ)+v=m := by exact_mod_cast huv
      linarith
    have hbal2 : (v:ℝ) ≤ (2/3:ℝ)*((u:ℝ)+v) := by
      have : 3*v ≤ 2*m := by dsimp [v,u]; omega
      have hr : (3:ℝ)*v ≤ 2*m := by exact_mod_cast this
      have he : (u:ℝ)+v=m := by exact_mod_cast huv
      linarith
    have hgap := power_gap (by exact_mod_cast hu) (by exact_mod_cast hv) hq1 hbal1 hbal2
    have he : (u:ℝ)+(v:ℝ)=(m:ℝ) := by exact_mod_cast huv
    rw [he] at hgap
    change B*(m:ℝ)^q ≤ (u:ℝ)^q+(v:ℝ)^q at hgap
    have hp : 0 ≤ (k:ℝ)^q := Real.rpow_nonneg (by positivity) _
    have hleft := ih u hum hu
    have hright := ih v hvm hv
    have hadd' := hadd (u*k) (v*k) (Nat.mul_pos hu hk) (Nat.mul_pos hv hk)
    have hnat : u*k+v*k=m*k := by rw [← Nat.add_mul, huv]
    rw [hnat, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)] at hadd'
    have hcost : K*(m:ℝ)^q ≤ D*((u:ℝ)^q+(v:ℝ)^q-(m:ℝ)^q) := by
      calc
        K*(m:ℝ)^q = D*(B*(m:ℝ)^q-(m:ℝ)^q) := by rw [← hDK]; ring
        _ ≤ D*((u:ℝ)^q+(v:ℝ)^q-(m:ℝ)^q) := by gcongr
    have hcost' := mul_le_mul_of_nonneg_right hcost hp
    calc
      a (m*k) ≤ ((u:ℝ)*a k + D*((u:ℝ)-(u:ℝ)^q)*(k:ℝ)^q) +
          ((v:ℝ)*a k + D*((v:ℝ)-(v:ℝ)^q)*(k:ℝ)^q) + K*((m:ℝ)^q*(k:ℝ)^q) :=
        hadd'.trans (add_le_add (add_le_add hleft hright) le_rfl)
      _ ≤ ((u:ℝ)*a k + D*((u:ℝ)-(u:ℝ)^q)*(k:ℝ)^q) +
          ((v:ℝ)*a k + D*((v:ℝ)-(v:ℝ)^q)*(k:ℝ)^q) +
          D*((u:ℝ)^q+(v:ℝ)^q-(m:ℝ)^q)*(k:ℝ)^q := by nlinarith only [hcost']
      _ = (m:ℝ)*a k + D*((m:ℝ)-(m:ℝ)^q)*(k:ℝ)^q := by rw [← he]; ring

private theorem rpow_div_tendsto_zero {q : ℝ} (hq : q < 1) :
    Tendsto (fun x : ℝ => x^q/x) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (by linarith : 0 < 1-q)
  have he : -(1-q)=q-1 := by ring
  rw [he] at h
  exact h.congr' ((eventually_gt_atTop (0:ℝ)).mono fun x hx =>
    Real.rpow_sub_one hx.ne' q)

/-- The all-multiples bound implies the appropriate eventual bound at every length. -/
theorem eventually_rate_lt {a : ℕ → ℝ} {K q D L : ℝ} (hK : 0 ≤ K)
    (hq : q < 1) (hD : 0 ≤ D)
    (hadd : ∀ n m, 0 < n → 0 < m →
      a (n+m) ≤ a n + a m + K * ((n+m:ℕ):ℝ)^q)
    (hmul : ∀ k m : ℕ, 0 < k → 0 < m →
      a (m*k) ≤ (m:ℝ)*a k + D*((m:ℝ)-(m:ℝ)^q)*(k:ℝ)^q)
    {k : ℕ} (hk : 0 < k) (hL : a k/(k:ℝ)+D*(k:ℝ)^q/(k:ℝ) < L) :
    ∀ᶠ n in atTop, a n/(n:ℝ) < L := by
  let B : ℝ := a k+D*(k:ℝ)^q
  have hm (m : ℕ) (hmp : 0 < m) : a (m*k) ≤ (m:ℝ)*B := by
    have hh := hmul k m hk hmp
    have hp : 0 ≤ D*(m:ℝ)^q*(k:ℝ)^q := by positivity
    dsimp [B]; nlinarith only [hh,hp]
  refine .atTop_of_arithmetic hk.ne' fun r hr => ?_
  let c : ℝ := max (a r) 0
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have A : Tendsto (fun x : ℝ => (B+c/x)/((k:ℝ)+(r:ℝ)/x)) atTop
      (𝓝 ((B+0)/((k:ℝ)+0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)) (by positivity)
  have A' : Tendsto (fun x : ℝ => (x*B+c)/(x*k+r)) atTop (𝓝 (B/k)) := by
    simp only [add_zero] at A
    refine A.congr' ((eventually_ne_atTop (0:ℝ)).mono fun x hx => ?_)
    simp only [add_div' _ _ _ hx, div_div_div_cancel_right₀ hx, mul_comm]
  have ht : Tendsto (fun m : ℕ => ((m*k+r:ℕ):ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun m : ℕ => by nlinarith : ∀ m : ℕ, m ≤ m*k+r) tendsto_id)
  have H : Tendsto (fun m : ℕ => ((m:ℝ)*B+c)/((m*k+r:ℕ):ℝ) +
      K*(((m*k+r:ℕ):ℝ)^q/((m*k+r:ℕ):ℝ))) atTop (𝓝 (B/k)) := by
    have h := (A'.comp tendsto_natCast_atTop_atTop).add
      ((tendsto_const_nhds (x := K)).mul ((rpow_div_tendsto_zero hq).comp ht))
    simpa only [Nat.cast_add,Nat.cast_mul,mul_zero,add_zero,Function.comp_def] using h
  have hBL : B/(k:ℝ)<L := by dsimp [B]; rwa [add_div]
  filter_upwards [H.eventually (gt_mem_nhds hBL), eventually_gt_atTop 0] with m hlt hmp
  rw [mul_comm k m]
  have hnp : (0:ℝ) < ((m*k+r:ℕ):ℝ) := by exact_mod_cast (by nlinarith : 0<m*k+r)
  have hh : a (m*k+r) ≤ (m:ℝ)*B+c+K*((m*k+r:ℕ):ℝ)^q := by
    by_cases hz : r=0
    · subst r
      have hnon : 0 ≤ c+K*((m*k+0:ℕ):ℝ)^q := by dsimp [c]; positivity
      simpa only [Nat.add_zero, add_assoc] using (hm m hmp).trans (le_add_of_nonneg_right hnon)
    · have ha := hadd (m*k) r (Nat.mul_pos hmp hk) (Nat.pos_of_ne_zero hz)
      have hc : a r ≤ c := le_max_left _ _
      exact ha.trans (by linarith [hm m hmp])
  apply lt_of_le_of_lt _ hlt
  calc
    a (m*k+r)/((m*k+r:ℕ):ℝ) ≤ ((m:ℝ)*B+c+K*((m*k+r:ℕ):ℝ)^q)/((m*k+r:ℕ):ℝ) :=
      div_le_div_of_nonneg_right hh hnp.le
    _ = _ := by ring

/-- Near-subadditivity with any fixed strictly sublinear positive power implies convergence. -/
theorem exists_limit_of_power_error {a : ℕ → ℝ} {K q C₀ C₁ : ℝ}
    (hK : 0 ≤ K) (hq0 : 0 < q) (hq1 : q < 1)
    (ha0 : ∀ n, 0 < n → 0 ≤ a n)
    (haB : ∀ n, 0 < n → a n ≤ C₀*n+C₁)
    (hadd : ∀ n m, 0 < n → 0 < m →
      a (n+m) ≤ a n+a m+K*((n+m:ℕ):ℝ)^q) :
    ∃ R : ℝ, 0 ≤ R ∧ Tendsto (fun n : ℕ => a n/(n:ℝ)) atTop (𝓝 R) := by
  obtain ⟨D,hD,hmul⟩ := multiples_bound hK hq0 hq1 hadd
  have hlow : ∀ᶠ n in atTop, 0 ≤ a n/(n:ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_nonneg (ha0 n hn) (by positivity)
  have hupp : ∀ᶠ n in atTop, a n/(n:ℝ) ≤ |C₀|+|C₁| := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n)).2
    have h0 : C₀*(n:ℝ) ≤ |C₀| *n := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h1 : C₁ ≤ |C₁| *(n:ℝ) := (le_abs_self _).trans (by nlinarith [abs_nonneg C₁])
    nlinarith [haB n hn]
  have herror : Tendsto (fun n : ℕ => D*(n:ℝ)^q/(n:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x:=D)).mul
      ((rpow_div_tendsto_zero hq1).comp tendsto_natCast_atTop_atTop)
    simpa only [mul_zero,Function.comp_def,mul_div_assoc] using h
  have hno : ∀ x ∈ (Set.univ : Set ℝ), ∀ y ∈ (Set.univ : Set ℝ), x<y →
      ¬ ((∃ᶠ n in atTop, a n/(n:ℝ)<x) ∧ (∃ᶠ n in atTop, y<a n/(n:ℝ))) := by
    intro x hx y hy hxy
    rintro ⟨hfreq,hhigh⟩
    have he : ∀ᶠ n : ℕ in atTop, D*(n:ℝ)^q/(n:ℝ) < y-x :=
      herror.eventually (gt_mem_nhds (by linarith))
    obtain ⟨k,hkx,hke,hkp⟩ := (hfreq.and_eventually (he.and (eventually_gt_atTop 0))).exists
    have hevent := eventually_rate_lt hK hq1 hD hadd hmul hkp (by linarith :
      a k/(k:ℝ)+D*(k:ℝ)^q/(k:ℝ)<y)
    obtain ⟨n,hn1,hn2⟩ := (hhigh.and_eventually hevent).exists
    exact (lt_asymm hn1 hn2)
  obtain ⟨R,hR⟩ := tendsto_of_no_upcrossings (u := fun n : ℕ => a n/(n:ℝ))
    (s := Set.univ) dense_univ hno
    (isBoundedUnder_of_eventually_le hupp) (isBoundedUnder_of_eventually_ge hlow)
  exact ⟨R,ge_of_tendsto hR hlow,hR⟩

/-- A concrete global power bound for the paper's logarithmic overhead. -/
theorem logarithmic_error_le_power (n : ℕ) (hn : 0 < n) :
    (n:ℝ)^((2:ℝ)/3) * (Real.log ((n:ℝ)+1)/Real.log 2) ≤
      (6*(2:ℝ)^((1:ℝ)/6)/Real.log 2) * (n:ℝ)^((5:ℝ)/6) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hl := Real.log_le_rpow_div (by positivity : (0:ℝ)≤(n:ℝ)+1)
    (by norm_num : (0:ℝ)<1/6)
  have hp : ((n:ℝ)+1)^((1:ℝ)/6) ≤ (2*(n:ℝ))^((1:ℝ)/6) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hnp.le] at hp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : (n:ℝ)^((2:ℝ)/3) * (n:ℝ)^((1:ℝ)/6) = (n:ℝ)^((5:ℝ)/6) := by
    rw [← Real.rpow_add hnp]; norm_num
  have hb : Real.log ((n:ℝ)+1) ≤ 6*((2:ℝ)^((1:ℝ)/6)*(n:ℝ)^((1:ℝ)/6)) := by
    linarith
  calc
    (n:ℝ)^((2:ℝ)/3) * (Real.log ((n:ℝ)+1)/Real.log 2) ≤
      (n:ℝ)^((2:ℝ)/3) * ((6*((2:ℝ)^((1:ℝ)/6)*(n:ℝ)^((1:ℝ)/6)))/Real.log 2) := by gcongr
    _ = (6*(2:ℝ)^((1:ℝ)/6)/Real.log 2) *
      ((n:ℝ)^((2:ℝ)/3)*(n:ℝ)^((1:ℝ)/6)) := by ring
    _ = _ := by rw [hmul]

/-- Lemma 34: the exact paper error class gives an ordinary finite normalized limit.
The hypotheses of nonnegativity and monotonicity of `F` are retained for correspondence,
although the stronger power-envelope argument does not need them. -/
theorem lemma_34 {a F : ℕ → ℝ} {C₀ C₁ : ℝ}
    (ha0 : ∀ n, 0 < n → 0 ≤ a n)
    (haB : ∀ n, 0 < n → a n ≤ C₀*n+C₁)
    (hF0 : ∀ n, 0 ≤ F n) (hFmono : Monotone F)
    (hFO : F =O[atTop] (fun n : ℕ =>
      (n:ℝ)^((2:ℝ)/3) * (Real.log ((n:ℝ)+1)/Real.log 2)))
    (hadd : ∀ n m, 0 < n → 0 < m → a (n+m) ≤ a n+a m+F (n+m)) :
    ∃ R : ℝ, 0 ≤ R ∧ Tendsto (fun n : ℕ => a n/(n:ℝ)) atTop (𝓝 R) := by
  obtain ⟨C,hC,hbound⟩ := bound_of_isBigO_nat_atTop hFO
  let K : ℝ := C*(6*(2:ℝ)^((1:ℝ)/6)/Real.log 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply exists_limit_of_power_error hK (by norm_num : (0:ℝ)<5/6)
    (by norm_num : (5:ℝ)/6<1) ha0 haB
  intro n m hn hm
  have hs : 0 < n+m := by omega
  have hsp : (0:ℝ)<(n+m:ℕ) := by exact_mod_cast hs
  have hlog : 0 < Real.log (((n+m:ℕ):ℝ)+1) := Real.log_pos (by linarith)
  have hg : 0 < ((n+m:ℕ):ℝ)^((2:ℝ)/3) *
      (Real.log (((n+m:ℕ):ℝ)+1)/Real.log 2) := by positivity
  have hB := hbound hg.ne'
  rw [Real.norm_eq_abs,abs_of_nonneg (hF0 _),Real.norm_eq_abs,abs_of_pos hg] at hB
  have hE := mul_le_mul_of_nonneg_left (logarithmic_error_le_power (n+m) hs) hC.le
  calc
    a (n+m) ≤ a n+a m+F (n+m) := hadd n m hn hm
    _ ≤ a n+a m+K*((n+m:ℕ):ℝ)^((5:ℝ)/6) := by dsimp [K]; nlinarith only [hB,hE]

end GeneralizedChannelStein.NearSubadditive
