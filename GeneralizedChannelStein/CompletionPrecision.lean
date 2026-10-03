import GeneralizedChannelStein.CompletionScalars

noncomputable section
namespace GeneralizedChannelStein.CompletionPrecision

def lam (c : ℝ) : ℝ := c/2
def q0 (c : ℝ) : ℝ := Real.sqrt (1-3*c^2/4)
def q1 (c : ℝ) : ℝ := (1+q0 c)/2
def Mc (c : ℝ) : ℝ := lam c/(1-q1 c)
def kappa (c : ℝ) : ℝ := min (1/16) (min ((q1 c-q0 c)/(2*lam c))
  (1/(16*(2*Mc c+1))))

structure Bounds (c : ℝ) : Prop where
  lam_pos : 0 < lam c
  lam_le_one : lam c ≤ 1
  q0_nonneg : 0 ≤ q0 c
  q0_lt_q1 : q0 c < q1 c
  q1_lt_one : q1 c < 1
  Mc_pos : 0 < Mc c
  kappa_pos : 0 < kappa c
  kappa_le : kappa c ≤ 1/16
  gap_bound : lam c*kappa c ≤ q1 c-q0 c
  error_bound : (2*Mc c+1)*kappa c ≤ 1/16

theorem fixed_precision_bounds {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : Bounds c := by
  have hlam : 0 < lam c := by unfold lam; positivity
  have hlam1 : lam c ≤ 1 := by unfold lam; linarith
  have hrad : 0 ≤ 1-3*c^2/4 := by nlinarith [sq_nonneg c]
  have hq0 : 0 ≤ q0 c := Real.sqrt_nonneg _
  have hq02 : (q0 c)^2 = 1-3*c^2/4 := Real.sq_sqrt hrad
  have hq01 : q0 c < 1 := by nlinarith [sq_pos_of_pos hc]
  have hgap : q0 c < q1 c := by unfold q1; linarith
  have hq1 : q1 c < 1 := by unfold q1; linarith
  have hMc : 0 < Mc c := div_pos hlam (by linarith)
  have hden : 0 < 16*(2*Mc c+1) := by positivity
  have hk : 0 < kappa c := by
    unfold kappa
    exact lt_min (by norm_num) (lt_min (div_pos (by linarith) (by positivity)) (by positivity))
  have hk16 : kappa c ≤ 1/16 := min_le_left _ _
  have hkgap : kappa c ≤ (q1 c-q0 c)/(2*lam c) := (min_le_right _ _).trans (min_le_left _ _)
  have hkerr : kappa c ≤ 1/(16*(2*Mc c+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hg := (le_div_iff₀ (show 0 < 2*lam c by positivity)).mp hkgap
  have herr := (le_div_iff₀ hden).mp hkerr
  refine ⟨hlam,hlam1,hq0,hgap,hq1,hMc,hk,hk16,?_,?_⟩
  · nlinarith [mul_pos hlam hk]
  · nlinarith

theorem scaled_precision_bounds {c δ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/16) :
    0 < kappa c*δ ∧ kappa c*δ ≤ 1/16 ∧
    (2*Mc c+1)*(kappa c*δ) ≤ δ/16 := by
  have h := fixed_precision_bounds hc hc1
  have hm := mul_le_mul_of_nonneg_right h.error_bound hδ.le
  have hx := mul_le_mul_of_nonneg_right h.kappa_le hδ.le
  exact ⟨mul_pos h.kappa_pos hδ, by nlinarith, by nlinarith⟩

end GeneralizedChannelStein.CompletionPrecision
