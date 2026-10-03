import GeneralizedChannelStein.FaithfulPreservingExamples
import GeneralizedChannelStein.CovariantFamilies

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.HamiltonianCovariance
open QuantumChannelStein Matrix FaithfulPreservingExamples
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {d a b : ℕ}

def phase (H : Operator d) (hH : H.IsHermitian) (s : ℝ) (i : Fin d) : ℂ :=
  Complex.exp ((-s*hH.eigenvalues i:ℝ)*Complex.I)

theorem phase_norm (H : Operator d) (hH : H.IsHermitian) (s : ℝ) (i : Fin d) :
    ‖phase H hH s i‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem phase_add (H : Operator d) (hH : H.IsHermitian) (s t : ℝ) (i : Fin d) :
    phase H hH (s+t) i=phase H hH s i*phase H hH t i := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def diagonalTime (H : Operator d) (hH : H.IsHermitian) (s : ℝ) : Matrix.unitaryGroup (Fin d) ℂ := by
  refine ⟨Matrix.diagonal (phase H hH s),?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal _*(Matrix.diagonal _)ᴴ=1
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  have he : (fun i => phase H hH s i*star (phase H hH s i))=fun _ => (1:ℂ) := by
    funext i
    simpa [Complex.normSq_eq_norm_sq,phase_norm] using Complex.mul_conj (phase H hH s i)
  simp only [Pi.star_apply] at *
  rw [he,Matrix.diagonal_one]

def diagonalRepresentation (H : Operator d) (hH : H.IsHermitian) :
    Multiplicative ℝ →* Matrix.unitaryGroup (Fin d) ℂ where
  toFun s := diagonalTime H hH s.toAdd
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (phase H hH 0)=1
    have he : phase H hH 0=fun _ => (1:ℂ) := by funext i; simp [phase]
    rw [he,Matrix.diagonal_one]
  map_mul' s t := by
    apply Subtype.ext
    change Matrix.diagonal (phase H hH (s.toAdd+t.toAdd)) =
      Matrix.diagonal (phase H hH s.toAdd)*Matrix.diagonal (phase H hH t.toAdd)
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact phase_add H hH _ _ i

/-- The actual spectral time-translation representation exp(-isH). -/
def timeTranslation (H : Operator d) (hH : H.IsHermitian) :
    Multiplicative ℝ →* Matrix.unitaryGroup (Fin d) ℂ :=
  (MulAut.conj hH.eigenvectorUnitary).toMonoidHom.comp (diagonalRepresentation H hH)

theorem timeTranslation_matrix (H : Operator d) (hH : H.IsHermitian) (s : ℝ) :
    (timeTranslation H hH (Multiplicative.ofAdd s)).val =
      Unitary.conjStarAlgAut ℂ (Operator d) hH.eigenvectorUnitary (Matrix.diagonal (phase H hH s)) := by
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem timeTranslation_add (H : Operator d) (hH : H.IsHermitian) (s t : ℝ) :
    timeTranslation H hH (Multiplicative.ofAdd (s+t)) =
      timeTranslation H hH (Multiplicative.ofAdd s)*timeTranslation H hH (Multiplicative.ofAdd t) :=
  map_mul _ _ _

theorem timeTranslation_unitary (H : Operator d) (hH : H.IsHermitian) (s : ℝ) :
    (timeTranslation H hH (Multiplicative.ofAdd s)).valᴴ*
      (timeTranslation H hH (Multiplicative.ofAdd s)).val=1 :=
  (timeTranslation H hH (Multiplicative.ofAdd s)).property.1

theorem continuous_timeTranslation_matrix (H : Operator d) (hH : H.IsHermitian) :
    Continuous (fun s : ℝ => (timeTranslation H hH (Multiplicative.ofAdd s)).val) := by
  simp only [timeTranslation_matrix,Unitary.conjStarAlgAut_apply]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun s : ℝ => ∑ x : Fin d,
    (hH.eigenvectorUnitary.val*Matrix.diagonal (phase H hH s)) i x *
      star hH.eigenvectorUnitary.val x j)
  simp only [Matrix.mul_diagonal]
  unfold phase
  fun_prop

theorem continuous_timeTranslation (H : Operator d) (hH : H.IsHermitian) :
    Continuous (fun s : ℝ => timeTranslation H hH (Multiplicative.ofAdd s)) :=
  continuous_induced_rng.mpr (continuous_timeTranslation_matrix H hH)

theorem gibbsWeight_commutes (H : Operator d) (hH : H.IsHermitian) (β s : ℝ) :
    (timeTranslation H hH (Multiplicative.ofAdd s)).val*gibbsWeight H hH β =
      gibbsWeight H hH β*(timeTranslation H hH (Multiplicative.ofAdd s)).val := by
  rw [timeTranslation_matrix,gibbsWeight,Matrix.IsHermitian.cfc,← map_mul,← map_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem gibbsState_invariant (hd : 0<d) (H : Operator d) (hH : H.IsHermitian) (β : ℝ)
    (s : Multiplicative ℝ) :
    (timeTranslation H hH s).val*(gibbsState hd H hH β).matrix*(timeTranslation H hH s).valᴴ =
      (gibbsState hd H hH β).matrix := by
  rw [gibbsState_matrix,Matrix.mul_smul,Matrix.smul_mul]
  have hc := gibbsWeight_commutes H hH β s.toAdd
  change (timeTranslation H hH s).val*gibbsWeight H hH β = _ at hc
  rw [hc,Matrix.mul_assoc]
  change _ • (gibbsWeight H hH β*((timeTranslation H hH s).val*star (timeTranslation H hH s).val))=_
  rw [(timeTranslation H hH s).property.2,Matrix.mul_one]


def timeCovariantFamily (HA : Operator a) (hA : HA.IsHermitian)
    (HB : Operator b) (hB : HB.IsHermitian) : AlternativeFamily a b :=
  unitaryCovariantFamily (timeTranslation HA hA) (timeTranslation HB hB)

theorem timeCovariant_all_axioms (ha : 0<a) (hb : 0<b)
    (HA : Operator a) (hA : HA.IsHermitian) (HB : Operator b) (hB : HB.IsHermitian) (βA βB : ℝ) :
    Admissible (timeCovariantFamily HA hA HB hB) ∧
      QuantitativeAt (timeCovariantFamily HA hA HB hB) (gibbsState ha HA hA βA) :=
  proposition_21 (timeTranslation HA hA) (timeTranslation HB hB)
    (gibbsState ha HA hA βA) (gibbsState hb HB hB βB)
    (gibbsState_faithful ha HA hA βA) (gibbsState_faithful hb HB hB βB)
    (gibbsState_invariant ha HA hA βA) (gibbsState_invariant hb HB hB βB)

/-- The literal intersection of the full time-covariant and Gibbs-preserving block families. -/
def gibbsCovariantFamily (ha : 0<a) (hb : 0<b)
    (HA : Operator a) (hA : HA.IsHermitian) (HB : Operator b) (hB : HB.IsHermitian) (βA βB : ℝ) :
    AlternativeFamily a b := familyIntersection (fun tag : Bool => if tag then
      statePreservingFamily (gibbsState ha HA hA βA) (gibbsState hb HB hB βB)
      else timeCovariantFamily HA hA HB hB)

theorem gibbsCovariant_mem_iff (ha : 0<a) (hb : 0<b)
    (HA : Operator a) (hA : HA.IsHermitian) (HB : Operator b) (hB : HB.IsHermitian) (βA βB : ℝ)
    (n : ℕ) (Φ : MatrixMap (a^n) (b^n)) :
    Φ∈gibbsCovariantFamily ha hb HA hA HB hB βA βB n ↔
      Φ∈statePreservingFamily (gibbsState ha HA hA βA) (gibbsState hb HB hB βB) n ∧
      Φ∈timeCovariantFamily HA hA HB hB n := by
  constructor
  · intro h
    exact ⟨h.2 true,h.2 false⟩
  · rintro ⟨hpres,hcov⟩
    refine ⟨hpres.1,?_⟩
    intro tag
    cases tag
    · exact hcov
    · exact hpres

/-- Both constraints satisfy F1--F5 with the same faithful Gibbs witnesses. -/
theorem gibbsCovariant_all_axioms (ha : 0<a) (hb : 0<b)
    (HA : Operator a) (hA : HA.IsHermitian) (HB : Operator b) (hB : HB.IsHermitian) (βA βB : ℝ) :
    Admissible (gibbsCovariantFamily ha hb HA hA HB hB βA βB) ∧
      QuantitativeAt (gibbsCovariantFamily ha hb HA hA HB hB βA βB) (gibbsState ha HA hA βA) := by
  let τ := gibbsState ha HA hA βA
  let ω := gibbsState hb HB hB βB
  let F : Bool → AlternativeFamily a b := fun tag => if tag then statePreservingFamily τ ω
    else timeCovariantFamily HA hA HB hB
  have hτ : τ.matrix.PosDef := gibbsState_faithful ha HA hA βA
  have hω : ω.matrix.PosDef := gibbsState_faithful hb HB hB βB
  have htime := timeCovariant_all_axioms ha hb HA hA HB hB βA βB
  have hF : ∀ tag, Admissible (F tag) := by
    intro tag
    cases tag
    · exact htime.1
    · exact statePreserving_admissible τ ω hω
  have hQ : ∀ tag, QuantitativeAt (F tag) τ := by
    intro tag
    cases tag
    · exact htime.2
    · exact statePreserving_quantitative τ ω hτ
  have hR : ∀ tag, ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F tag 1 := by
    intro tag
    cases tag
    · apply replacer_mem_covariant
      intro s
      apply State.eq_of_matrix_eq
      exact (SharpDivergence.unitaryChannel_apply _ _).trans (gibbsState_invariant hb HB hB βB s)
    · exact replacer_power_preserving τ ω 1
  exact ⟨intersection_admissible F hF ω hω hR,intersection_quantitative F τ hτ hQ⟩

end GeneralizedChannelStein.HamiltonianCovariance
