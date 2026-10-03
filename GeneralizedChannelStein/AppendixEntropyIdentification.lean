import GeneralizedChannelStein.NearSubadditiveEntropy
import GeneralizedChannelStein.RealRates
import GeneralizedChannelStein.BinomialOverhead

/-! # Independent Appendix B entropy identification from a common testing limit

The operational limit is an intermediate input, discharged by the separate
near-subadditivity construction. This proof invokes only finite bounds 4 and
33, not either main entropy/testing limit endpoint.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.AppendixEntropyIdentification
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

def smallError (j : ℕ) : ℝ := 1/((j:ℝ)+2)

theorem smallError_pos (j : ℕ) : 0<smallError j := by unfold smallError; positivity

theorem smallError_lt_one (j : ℕ) : smallError j<1 := by
  unfold smallError
  apply (div_lt_one (by positivity : (0:ℝ)<(j:ℝ)+2)).mpr
  have hj := Nat.cast_nonneg (α:=ℝ) j
  linarith

theorem smallError_tendsto_zero : Tendsto smallError atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 1)
  simpa only [smallError,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

/-- Bounds on the entropy sequence use only its finite faithful-replacer comparison. -/
theorem entropy_bounded (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    atTop.IsBoundedUnder (·≤·) (entropyRateReal N F) ∧
      atTop.IsBoundedUnder (·≥·) (entropyRateReal N F) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  constructor
  · refine ⟨replacerRate ω hb,?_⟩
    change ∀ᶠ n : ℕ in atTop, entropyRateReal N F n≤replacerRate ω hb
    exact Eventually.of_forall fun n => (entropyRateReal_bounds N ha hb F hF ω hω hOne n).2
  · refine ⟨0,?_⟩
    change ∀ᶠ n : ℕ in atTop, 0≤entropyRateReal N F n
    exact Eventually.of_forall fun n => (entropyRateReal_bounds N ha hb F hF ω hω hOne n).1

/-- First take n→∞ with a fixed error in the finite weak converse. -/
theorem liminf_ge_fixed_error (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (R ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (hlim : Tendsto (testingRateReal N F ε) atTop (𝓝 R)) :
    (1-ε)*R ≤ liminf (entropyRateReal N F) atTop := by
  have hlim' : Tendsto (fun n : ℕ => (1-ε)*testingRateReal N F ε n-1/(n:ℝ)) atTop
      (𝓝 ((1-ε)*R)) := by
    simpa only [sub_zero] using (hlim.const_mul (1-ε)).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (1-ε)*testingRateReal N F ε n-1/(n:ℝ)≤entropyRateReal N F n := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact normalized_weak_converse N ha hb F hF ε hε hε1 n hn
  have h := liminf_le_liminf hevent hlim'.isBoundedUnder_ge
    (entropy_bounded N ha hb F hF).1.isCobounded_flip
  rwa [hlim'.liminf_eq] at h

/-- Lemma 33 normalized by the actual integer blocklength. -/
theorem normalized_large_error (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (n : ℕ) (hn : 0<n)
    (hperm : ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap∈F n → (permuteChannel n π M).toLinearMap∈F n)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    entropyRateReal N F n ≤ ε*testingRateReal N F ε n+(1-ε)*replacerRate ω hb+
      1/(n:ℝ)+BinomialOverhead.overhead (a*b) n/(n:ℝ) := by
  have h := NearSubadditiveEntropy.lemma_33_entropy_form N ha hb F hF ω hω hOne n hn hperm ε hε hε1
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
  have hn0 : (n:ℝ)≠0 := (Nat.cast_pos.mpr hn).ne'
  convert hh using 1
  dsimp [testingRateReal,BinomialOverhead.overhead,BinomialOverhead.mass]
  field_simp
  ring

/-- The exact binomial term vanishes before the testing tolerance is varied. -/
theorem limsup_le_fixed_error (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (hperm : ∀ n : ℕ, 0<n → ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap∈F n → (permuteChannel n π M).toLinearMap∈F n)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (R ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (hlim : Tendsto (testingRateReal N F ε) atTop (𝓝 R)) :
    limsup (entropyRateReal N F) atTop ≤ ε*R+(1-ε)*replacerRate ω hb := by
  have hup : Tendsto (fun n : ℕ => ε*testingRateReal N F ε n+(1-ε)*replacerRate ω hb+
      1/(n:ℝ)+BinomialOverhead.overhead (a*b) n/(n:ℝ)) atTop
      (𝓝 (ε*R+(1-ε)*replacerRate ω hb)) := by
    have h := (((hlim.const_mul ε).add_const ((1-ε)*replacerRate ω hb)).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))).add
      (BinomialOverhead.normalized_overhead_tendsto_zero (a*b))
    simpa only [add_zero] using h
  have hev : ∀ᶠ n : ℕ in atTop, entropyRateReal N F n ≤
      ε*testingRateReal N F ε n+(1-ε)*replacerRate ω hb+
        1/(n:ℝ)+BinomialOverhead.overhead (a*b) n/(n:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact normalized_large_error N ha hb F hF ω hω hOne n hn (hperm n hn) ε hε hε1
  have h := limsup_le_limsup hev (entropy_bounded N ha hb F hF).2.isCobounded_flip hup.isBoundedUnder_le
  rwa [hup.limsup_eq] at h

/-- Appendix B entropy identification, using only the common operational limit and finite bounds. -/
theorem entropy_limit_of_common_testing_limit (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (hperm : ∀ n : ℕ, 0<n → ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap∈F n → (permuteChannel n π M).toLinearMap∈F n)
    (R : ℝ) (hlim : ∀ ε : ℝ, 0<ε → ε<1 → Tendsto (testingRateReal N F ε) atTop (𝓝 R)) :
    Tendsto (entropyRateReal N F) atTop (𝓝 R) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  have hlo : R≤liminf (entropyRateReal N F) atTop := by
    have ht : Tendsto (fun j : ℕ => (1-smallError j)*R) atTop (𝓝 R) := by
      simpa only [sub_zero,one_mul] using
        ((tendsto_const_nhds (x:=(1:ℝ))).sub smallError_tendsto_zero).mul_const R
    apply le_of_tendsto ht
    exact Eventually.of_forall fun j => liminf_ge_fixed_error N ha hb F hF R (smallError j)
      (smallError_pos j) (smallError_lt_one j) (hlim _ (smallError_pos j) (smallError_lt_one j))
  have hhi : limsup (entropyRateReal N F) atTop≤R := by
    have ht : Tendsto (fun j : ℕ => (1-smallError j)*R+
        (1-(1-smallError j))*replacerRate ω hb) atTop (𝓝 R) := by
      have h := (((tendsto_const_nhds (x:=(1:ℝ))).sub smallError_tendsto_zero).mul_const R).add
        (((tendsto_const_nhds (x:=(1:ℝ))).sub ((tendsto_const_nhds (x:=(1:ℝ))).sub smallError_tendsto_zero)).mul_const (replacerRate ω hb))
      simpa only [sub_zero,one_mul,sub_self,zero_mul,add_zero] using h
    apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro j
    have he0 : 0<1-smallError j := sub_pos.mpr (smallError_lt_one j)
    have he1 : 1-smallError j<1 := by linarith [smallError_pos j]
    exact limsup_le_fixed_error N ha hb F hF hperm ω hω hOne R (1-smallError j) he0 he1 (hlim _ he0 he1)
  exact tendsto_of_le_liminf_of_limsup_le hlo hhi
    (entropy_bounded N ha hb F hF).1 (entropy_bounded N ha hb F hF).2

/-- The common rate's nonnegativity and faithful-replacer bound also follow from finite bounds. -/
theorem common_rate_bounds (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (hperm : ∀ n : ℕ, 0<n → ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap∈F n → (permuteChannel n π M).toLinearMap∈F n)
    (R : ℝ) (hlim : ∀ ε : ℝ, 0<ε → ε<1 → Tendsto (testingRateReal N F ε) atTop (𝓝 R))
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1) :
    0≤R ∧ R≤replacerRate ω hb := by
  have ht := entropy_limit_of_common_testing_limit N ha hb F hF hperm R hlim
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n =>
      (entropyRateReal_bounds N ha hb F hF ω hω hOne n).1),
    le_of_tendsto ht (Eventually.of_forall fun n =>
      (entropyRateReal_bounds N ha hb F hF ω hω hOne n).2)⟩

end GeneralizedChannelStein.AppendixEntropyIdentification
