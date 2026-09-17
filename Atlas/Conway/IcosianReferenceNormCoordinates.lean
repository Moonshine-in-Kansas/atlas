import Atlas.Conway.IcosianRootLocalOrbits
import Atlas.Conway.IcosianEqualCoordinateSwaps

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Actual root representatives, retaining their integral coordinates. -/
def icosianRootLocalVector : Fin 4 → IcosianRoot :=
  ![icosianAxisRoot (0,1),icosianLocalBRoot,icosianLocalCRoot,icosianLocalDRoot]

theorem icosianRootLocalVector_toPoint (i : Fin 4) :
    icosianRootToPoint (icosianRootLocalVector i)=icosianRootLocalRepresentative i := by
  fin_cases i <;> rfl

/-- In the four selected references, equality of coordinate norms is already
coordinate equality. This is the small geometric reason that restricting to
one axis introduces no additional hidden local orbits. -/
theorem icosianRootLocalVector_equal_norm (a : Fin 4) (i j : Fin 3)
    (h : icosianRootNormWord (icosianRootLocalVector a) i=
      icosianRootNormWord (icosianRootLocalVector a) j) :
    (icosianRootLocalVector a).val i=(icosianRootLocalVector a).val j := by
  fin_cases a
  · have hw (k : Fin 3) : icosianRootNormWord (icosianAxisRoot (0,1)) k=
        if k=0 then 4 else 0 := by
      apply icosianRootNormWord_of_norm
      by_cases hk : k=0
      · subst k
        simpa only [ite_true,map_ofNat] using
          icosianRoot_single_norm (icosianAxisRoot (0,1)) 0
            (fun j hj => by simp [icosianAxisRoot,icosianSingle,hj])
      · simp [icosianAxisRoot,icosianSingle,hk,icosianNorm]
    change icosianRootNormWord (icosianAxisRoot (0,1)) i=
      icosianRootNormWord (icosianAxisRoot (0,1)) j at h
    rw [hw,hw] at h
    fin_cases i <;> fin_cases j <;>
      simp_all [icosianRootLocalVector,icosianAxisRoot,icosianSingle]
  · change icosianRootNormWord icosianLocalBRoot i=
      icosianRootNormWord icosianLocalBRoot j at h
    rw [icosianLocalBRoot_word,icosianLocalBRoot_word] at h
    fin_cases i <;> fin_cases j <;>
      simp_all [icosianRootLocalVector,icosianLocalBRoot,icosianEdgeRootBase,
        icosianLocalBPair]
  · change icosianRootNormWord icosianLocalCRoot i=
      icosianRootNormWord icosianLocalCRoot j at h
    rw [icosianLocalCRoot_word,icosianLocalCRoot_word] at h
    fin_cases i <;> fin_cases j <;>
      simp_all [icosianRootLocalVector,icosianLocalCRoot,icosianLocalCVector]
  · exact congrArg (icosianLocalDRoot.val) (icosianLocalDRoot_word_injective h)

end Atlas.Conway
