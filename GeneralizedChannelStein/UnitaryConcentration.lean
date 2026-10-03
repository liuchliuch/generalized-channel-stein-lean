import GeneralizedChannelStein.WeightedDiscarding
import QuantumChannelStein.DiamondNormChannel

/-! # Faithful-state concentration of a unitary near a scalar phase -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {d : ℕ}

/-- The normalized state expectation is conjugated when the unitary is adjointed. -/
theorem state_unitary_trace_star (τ : State d) (U : unitary (Operator d)) :
    (τ.matrix*(U:Operator d)ᴴ).trace = star ((τ.matrix*(U:Operator d)).trace) := by
  rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,τ.positive.isHermitian.eq,
    Matrix.trace_mul_comm]

/-- Exact phase-centered quadratic expectation. -/
theorem phase_quadratic_trace (τ : State d) (U : unitary (Operator d))
    (z : ℂ) (hz : ‖z‖=1) :
    (τ.matrix*((U:Operator d)-z • 1)ᴴ*((U:Operator d)-z • 1)).trace.re =
      2*(1-(star z*(τ.matrix*(U:Operator d)).trace).re) := by
  have hzz : star z*z = 1 := by
    rw [Complex.star_def,Complex.conj_mul',hz]
    norm_num
  have hU : (U:Operator d)ᴴ*(U:Operator d)=1 := Unitary.coe_star_mul_self U
  have hquad : ((U:Operator d)-z • 1)ᴴ*((U:Operator d)-z • 1) =
      (2:ℂ) • (1:Operator d)-z • (U:Operator d)ᴴ-star z • (U:Operator d) := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
      Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hU,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul,Matrix.one_mul,
      smul_smul,hzz,one_smul]
    module
  rw [Matrix.mul_assoc,hquad]
  simp only [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,Matrix.trace_smul,
    τ.trace_one,smul_eq_mul,mul_one,state_unitary_trace_star]
  simp only [Complex.sub_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  norm_num
  ring

/-- Faithfulness bounds the full operator norm, without any commuting assumption. -/
theorem faithful_phase_concentration (τ : State d) (t : ℝ) (ht : 0 ≤ t)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (U : unitary (Operator d)) (z : ℂ) (hz : ‖z‖=1) :
    t*‖(U:Operator d)-z • 1‖^2 ≤
      2*(1-(star z*(τ.matrix*(U:Operator d)).trace).re) := by
  let D := (U:Operator d)-z • 1
  have hD := Matrix.posSemidef_conjTranspose_mul_self D
  have hnorm : ‖D‖^2 ≤ (Dᴴ*D).trace.re := by
    rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self]
    exact TestingSDP.positive_norm_le_trace hD
  have htrace := (Complex.nonneg_iff.mp (TestingSDP.trace_pairing_nonnegative hτ hD)).1
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul,
    Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at htrace
  have hquad := phase_quadratic_trace τ U z hz
  change (τ.matrix*Dᴴ*D).trace.re = _ at hquad
  rw [Matrix.mul_assoc] at hquad
  have hbound := mul_le_mul_of_nonneg_left hnorm ht
  change t*‖D‖^2 ≤ _
  linarith

/-- The canonical phase of a nonzero complex scalar has unit norm. -/
theorem normalized_phase_norm (x : ℂ) (hx : x ≠ 0) : ‖x/(‖x‖:ℂ)‖=1 := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x),div_self (norm_ne_zero_iff.mpr hx)]

/-- The same phase aligns the scalar's expectation with its nonnegative modulus. -/
theorem normalized_phase_pairing (x : ℂ) (hx : x ≠ 0) :
    (star (x/(‖x‖:ℂ))*x).re=‖x‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [Complex.star_def,map_div₀,Complex.conj_ofReal]
  rw [div_mul_eq_mul_div,Complex.conj_mul']
  simp only [Complex.div_ofReal_re, ← Complex.ofReal_pow,Complex.ofReal_re]
  field_simp

/-- The precise concentration estimate used on the good unitaries of Lemma27. -/
theorem good_unitary_near_phase (τ : State d) (t u : ℝ) (ht : 0 < t) (hu : 0 ≤ u)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef) (U : unitary (Operator d))
    (hgood : 1-t*u^2/2 ≤ ‖(τ.matrix*(U:Operator d)).trace‖)
    (hnonzero : (τ.matrix*(U:Operator d)).trace ≠ 0) :
    ‖(U:Operator d)-((τ.matrix*(U:Operator d)).trace/
      (‖(τ.matrix*(U:Operator d)).trace‖:ℂ)) • 1‖ ≤ u := by
  have h := faithful_phase_concentration τ t ht.le hτ U
    ((τ.matrix*(U:Operator d)).trace/(‖(τ.matrix*(U:Operator d)).trace‖:ℂ))
    (normalized_phase_norm _ hnonzero)
  rw [normalized_phase_pairing _ hnonzero] at h
  have hs : t*‖(U:Operator d)-((τ.matrix*(U:Operator d)).trace/
      (‖(τ.matrix*(U:Operator d)).trace‖:ℂ)) • 1‖^2 ≤ t*u^2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) hu).mp ((mul_le_mul_iff_right₀ ht).mp hs)

/-- A unitary's normalized faithful-state expectation never has modulus above one. -/
theorem state_unitary_trace_norm_le_one (τ : State d) (U : unitary (Operator d)) :
    ‖(τ.matrix*(U:Operator d)).trace‖ ≤ 1 := by
  rw [Matrix.trace_mul_comm]
  have h := TraceNorm.norm_trace_mul_le (U:Operator d) τ.matrix
  rw [TraceNorm.traceNorm_of_posSemidef τ.matrix τ.positive,τ.trace_one] at h
  simp only [Complex.one_re,mul_one] at h
  exact h.trans (TraceNorm.unitary_opNorm_le_one U)

/-- In the active regime, the good-set threshold itself proves the phase exists. -/
theorem good_unitary_near_phase_of_small (τ : State d) (t u : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hu : 0 ≤ u) (hu1 : u < 1)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef) (U : unitary (Operator d))
    (hgood : 1-t*u^2/2 ≤ ‖(τ.matrix*(U:Operator d)).trace‖) :
    ∃ z : ℂ, ‖z‖=1 ∧ ‖(U:Operator d)-z • 1‖ ≤ u := by
  have husq : u^2 < 1 := by nlinarith
  have htu : t*u^2 < 1 := by
    have h := mul_le_mul_of_nonneg_right ht1 (sq_nonneg u)
    nlinarith
  have hp : 0 < ‖(τ.matrix*(U:Operator d)).trace‖ := by linarith
  have hn : (τ.matrix*(U:Operator d)).trace ≠ 0 := norm_ne_zero_iff.mp hp.ne'
  exact ⟨(τ.matrix*(U:Operator d)).trace/(‖(τ.matrix*(U:Operator d)).trace‖:ℂ),
    normalized_phase_norm _ hn,good_unitary_near_phase τ t u ht hu hτ U hgood hn⟩

end GeneralizedChannelStein
