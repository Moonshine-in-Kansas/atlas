import Atlas.Conway.EisensteinSuborbitFamilies

set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

private theorem repeatedIndices (i j : Fin 13) (hij : i≠j)
    (hd : eisensteinSubdegree i=eisensteinSubdegree j) :
    (i=3 ∧ j=4) ∨ (i=4 ∧ j=3) ∨ (i=6 ∧ j=7) ∨ (i=7 ∧ j=6) ∨
    (i=9 ∧ j=10) ∨ (i=9 ∧ j=11) ∨ (i=10 ∧ j=9) ∨
    (i=10 ∧ j=11) ∨ (i=11 ∧ j=9) ∨ (i=11 ∧ j=10) := by
  revert hd hij j i
  decide +kernel

/-- Equal subdegrees retain their separate geometric invariants. -/
theorem eisensteinSuborbitFrames_repeated_disjoint (i j : Fin 13) (hij : i≠j)
    (hd : eisensteinSubdegree i=eisensteinSubdegree j) :
    Disjoint (eisensteinSuborbitFrames i) (eisensteinSuborbitFrames j) := by
  rcases repeatedIndices i j hij hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Finset.disjoint_coe.mpr
        (eisensteinNineHexadFamily_disjoint 1 (by decide) 2 (by decide) (by decide))
  · exact (Finset.disjoint_coe.mpr
        (eisensteinNineHexadFamily_disjoint 1 (by decide) 2 (by decide) (by decide))).symm
  · exact eisensteinPairUnitFrames_disjoint
  · exact eisensteinPairUnitFrames_disjoint.symm
  · exact eisensteinTriadUnitFrames_disjoint 0 1 (by decide)
  · exact eisensteinTriadUnitFrames_disjoint 0 2 (by decide)
  · exact eisensteinTriadUnitFrames_disjoint 1 0 (by decide)
  · exact eisensteinTriadUnitFrames_disjoint 1 2 (by decide)
  · exact eisensteinTriadUnitFrames_disjoint 2 0 (by decide)
  · exact eisensteinTriadUnitFrames_disjoint 2 1 (by decide)

end Atlas.Conway
