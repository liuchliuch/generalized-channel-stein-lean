import QuantumChannelStein.ParallelConverse

noncomputable section
namespace GeneralizedChannelStein.FixedDilation
open QuantumChannelStein ParallelConverse Matrix
variable {a b : ℕ}

/-- The auxiliary dimension a*b is fixed by the local dimensions, not by a supplied Kraus rank. -/
theorem exists_fixed_dilation (N : KrausChannel a b) :
    ∃ V : Matrix (Fin b × Fin (a*b)) (Fin a) ℂ,
      Vᴴ*V=1 ∧ dilationMap V=N.toLinearMap := by
  obtain ⟨M,hRank,hM⟩ := MatrixMap.exists_kraus_of_cptp N.toLinearMap
    (MatrixMap.completelyPositive_toLinearMap N) N.trace_apply
  have hv : ∃ V : Matrix (Fin b × Fin M.rank) (Fin a) ℂ,
      Vᴴ*V=1 ∧ dilationMap V=N.toLinearMap :=
    ⟨M.stinespring,M.stinespring_isometry,(dilationMap_stinespring M).trans hM⟩
  exact Eq.mp (congrArg (fun r : ℕ => ∃ V : Matrix (Fin b × Fin r) (Fin a) ℂ,
    Vᴴ*V=1 ∧ dilationMap V=N.toLinearMap) hRank) hv

def fixedDilation (N : KrausChannel a b) : Matrix (Fin b × Fin (a*b)) (Fin a) ℂ :=
  Classical.choose (exists_fixed_dilation N)

theorem fixedDilation_isometry (N : KrausChannel a b) :
    (fixedDilation N)ᴴ*fixedDilation N=1 := (Classical.choose_spec (exists_fixed_dilation N)).1

theorem fixedDilation_map (N : KrausChannel a b) :
    dilationMap (fixedDilation N)=N.toLinearMap := (Classical.choose_spec (exists_fixed_dilation N)).2

end GeneralizedChannelStein.FixedDilation
