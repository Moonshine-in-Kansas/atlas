import Atlas.Fischer.Cocode
import Atlas.Codes.BinaryCounting

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- The cocode class of one actual marked coordinate. -/
def coordinateCocode (i : Omega) : Cocode := golay.mkQ (Pi.single i 1)

theorem cocodePairing_coordinate (c : golay) (i : Omega) :
    cocodePairing c (coordinateCocode i) = c.val i := by
  classical
  change cocodeDualEquiv (Submodule.Quotient.mk (Pi.single i 1)) c = c.val i
  rw [cocodeDualEquiv_mk]
  simp [binaryDot_apply,Pi.single_apply,mul_ite]

theorem coordinateCocode_parity (i : Omega) : cocodeParity (coordinateCocode i) = 1 := by
  change cocodePairing golayOne (coordinateCocode i) = 1
  rw [cocodePairing_coordinate]
  rfl

theorem coordinateCocode_sum (S : Finset Omega) :
    (∑ i ∈ S, coordinateCocode i) = golay.mkQ (binarySupportEquiv.symm S) := by
  classical
  unfold coordinateCocode
  rw [← map_sum]
  apply congrArg golay.mkQ
  funext j
  simp [binarySupportEquiv,Finset.sum_apply,Pi.single_apply]

/-- The complete relation space of the marked cocode generators is exactly Golay. -/
theorem coordinateCocode_sum_eq_zero (S : Finset Omega) :
    (∑ i ∈ S, coordinateCocode i) = 0 ↔ binarySupportEquiv.symm S ∈ golay := by
  rw [coordinateCocode_sum]
  exact Submodule.Quotient.mk_eq_zero golay

theorem coordinateCocode_representation (d : Cocode) :
    ∃ S : Finset Omega, d = ∑ i ∈ S, coordinateCocode i := by
  obtain ⟨w,rfl⟩ := golay.mkQ_surjective d
  refine ⟨binarySupportEquiv w,?_⟩
  rw [coordinateCocode_sum,binarySupportEquiv.symm_apply_apply]

theorem coordinateCocode_generate : AddSubgroup.closure (Set.range coordinateCocode) = ⊤ := by
  apply top_unique
  intro d _
  obtain ⟨S,rfl⟩ := coordinateCocode_representation d
  exact AddSubgroup.sum_mem _ (fun i _ => AddSubgroup.subset_closure ⟨i,rfl⟩)

end Atlas.Fischer
