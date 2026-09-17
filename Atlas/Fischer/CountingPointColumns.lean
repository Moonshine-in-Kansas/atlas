import Atlas.Fischer.CountingColumnRule
import Atlas.Fischer.OctadDiamond

noncomputable section
namespace Atlas.Fischer
open scoped symmDiff
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- The actual row subset of any point set in a retained tetrad. -/
def countingPointColumn (G : Finset Omega) (i : Fin 6) : Finset CountingFour :=
  Finset.univ.filter (fun z => countingPointCoordinates.symm (i,z) ∈ G)

theorem countingPointColumn_source (t : CountingSourceParameters) (i : Fin 6) :
    countingPointColumn (countingSourceOctadEquiv t).val i=countingSourceColumn t i := by
  ext z
  simp [countingPointColumn,countingSourceColumn_membership]

theorem countingPointColumn_inter (G H : Finset Omega) (i : Fin 6) :
    countingPointColumn (G ∩ H) i=countingPointColumn G i ∩ countingPointColumn H i := by
  ext z
  simp [countingPointColumn]

theorem countingPointColumn_compl (G : Finset Omega) (i : Fin 6) :
    countingPointColumn Gᶜ i=(countingPointColumn G i)ᶜ := by
  ext z
  simp [countingPointColumn]

theorem countingPointColumn_symmDiff (G H : Finset Omega) (i : Fin 6) :
    countingPointColumn (G ∆ H) i=countingPointColumn G i ∆ countingPointColumn H i := by
  ext z
  simp [countingPointColumn,Finset.mem_symmDiff]

/-- Counting the six actual column fibers recovers the cardinality of the point set. -/
theorem countingPointColumn_card_sum (G : Finset Omega) :
    ∑ i : Fin 6, (countingPointColumn G i).card=G.card := by
  have hf (i : Fin 6) :
      (G.filter (fun p => (countingPointCoordinates p).1=i)).card=(countingPointColumn G i).card := by
    let f := fun p : Omega => (countingPointCoordinates p).2
    have he : (G.filter (fun p => (countingPointCoordinates p).1=i)).image f=countingPointColumn G i := by
      ext z
      constructor
      · rintro hz
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have he : (i,f p)=countingPointCoordinates p := Prod.ext hi.symm rfl
        rw [he,Equiv.symm_apply_apply]
        exact hp
      · intro hz
        have hp := (Finset.mem_filter.mp hz).2
        refine Finset.mem_image.mpr ⟨countingPointCoordinates.symm (i,z),?_,?_⟩
        · exact Finset.mem_filter.mpr ⟨hp,by simp⟩
        · simp [f]
    have hinj : Set.InjOn f ↑(G.filter (fun p => (countingPointCoordinates p).1=i)) := by
      intro p hp q hq he
      apply countingPointCoordinates.injective
      apply Prod.ext
      · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      · exact he
    rw [← he,Finset.card_image_of_injOn hinj]
  simp_rw [← hf]
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

/-- Every actual column has four rows. -/
theorem countingPointColumn_compl_card (G : Finset Omega) (i : Fin 6) :
    (countingPointColumn Gᶜ i).card=4-(countingPointColumn G i).card := by
  rw [countingPointColumn_compl,Finset.card_compl,goldenFour_card]

end Atlas.Fischer
