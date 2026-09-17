import Atlas.Fischer.OctadTetradFibres

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadTetradFibre_intersection (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D E : OctadTetradFibre O T) (hDE : D ≠ E) : D.val.val ∩ E.val.val = T := by
  have hTD : T ⊆ D.val.val := by
    simpa only [D.property] using (Finset.inter_subset_left : D.val.val ∩ O.val ⊆ D.val.val)
  have hTE : T ⊆ E.val.val := by
    simpa only [E.property] using (Finset.inter_subset_left : E.val.val ∩ O.val ⊆ E.val.val)
  have hsub := Finset.subset_inter hTD hTE
  have hlo := Finset.card_le_card hsub
  rw [hT] at hlo
  have hne : (D.val.val ∩ E.val.val).card ≠ 8 := by
    intro h
    have hD : D.val.val ∩ E.val.val = D.val.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h, octad_size _ D.val.property])
    have hE : D.val.val ∩ E.val.val = E.val.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h, octad_size _ E.val.property])
    exact hDE (Subtype.ext (Subtype.ext (hD.symm.trans hE)))
  have hc := octad_intersection_sizes _ _ D.val.property E.val.property
  have hcard : (D.val.val ∩ E.val.val).card = 4 := by omega
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hT])).symm

def octadTetradExterior (O : Octad) (T : Finset Omega) (D : OctadTetradFibre O T) : Finset Omega :=
  D.val.val \ O.val

theorem octadTetradExterior_card (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D : OctadTetradFibre O T) : (octadTetradExterior O T D).card = 4 := by
  rw [octadTetradExterior, Finset.card_sdiff, Finset.inter_comm, D.property,
    octad_size _ D.val.property, hT]

theorem octadTetradExterior_disjoint (O : Octad) (T : Finset Omega) (hT : T.card = 4)
    (D E : OctadTetradFibre O T) (hDE : D ≠ E) :
    Disjoint (octadTetradExterior O T D) (octadTetradExterior O T E) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hd := Finset.mem_sdiff.mp hi
  have he := Finset.mem_sdiff.mp hj
  have ht : i ∈ T := by
    rw [← octadTetradFibre_intersection O T hT D E hDE]
    exact Finset.mem_inter.mpr ⟨hd.1, he.1⟩
  exact hd.2 ((D.property ▸ Finset.inter_subset_right) ht)

/-- The four actual exterior tetrads partition the marked affine sixteen-space. -/
theorem octadTetradExterior_partition (O : Octad) (T : Finset Omega)
    (hTO : T ⊆ O.val) (hT : T.card = 4) :
    Finset.univ.biUnion (octadTetradExterior O T) = O.valᶜ := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨D, _, hd⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hd).2
  · rw [Finset.card_biUnion (by
      intro D hD E hE hDE
      exact octadTetradExterior_disjoint O T hT D E hDE)]
    simp only [octadTetradExterior_card O T hT, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Finset.card_compl]
    have hc : Fintype.card (OctadTetradFibre O T) = 4 := by
      simpa only [Nat.card_eq_fintype_card] using octadTetradFibre_card O T hTO hT
    have hI : Fintype.card Omega = 24 := by decide
    rw [hc, hI, octad_size _ O.property]

end Atlas.Fischer
