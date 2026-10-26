import Atlas.LinearGroups.ReeF4.IntrinsicGroup
import Atlas.LinearGroups.ReeF4.PartialCandidate
import Atlas.LinearGroups.ReeF4.RootProductTables

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem model_fixed_cross {m : ℕ} (g : Model F m) {u v : TraceZero F}
    (hu : g.val u=u) (hv : g.val v=v) :
    g.val (traceZeroCross u v)=traceZeroCross u v := by
  obtain ⟨hp,_⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  have hc := traceZeroCross_of_forms g.val (traceZeroStabilizer_quadratic ⟨g.val,hp⟩)
    (traceZeroStabilizer_cubic ⟨g.val,hp⟩) u v
  rw [hu,hv] at hc
  exact hc.symm

private theorem model_fixed_partial {m : ℕ} (g : Model F m) {u v : TraceZero F}
    (hu : g.val u=u) (hv : g.val v=v) (hd : StarDomain u v) :
    g.val (proposedPartialProduct (thetaInv F m).toRingHom u v hd)=
      proposedPartialProduct (thetaInv F m).toRingHom u v hd := by
  obtain ⟨hp,hg⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  have he := hg u v hd
  simpa only [hu,hv] using he.symm

private theorem model_fixed_cross_root {m : ℕ} (g : Model F m) (r s t : ShortRootLabel)
    (hr : g.val (rootVector r)=rootVector r) (hs : g.val (rootVector s)=rootVector s)
    (hadd : scaledShortRoot r+scaledShortRoot s=scaledShortRoot t) :
    g.val (rootVector t)=rootVector t := by
  simpa only [rootCross_shortSum r s t hadd] using model_fixed_cross g hr hs

private theorem model_fixed_star_root {m : ℕ} (g : Model F m) (r s t : ShortRootLabel)
    (hr : g.val (rootVector r)=rootVector r) (hs : g.val (rootVector s)=rootVector s)
    (hperp : rootDot (scaledShortRoot r) (scaledShortRoot s)=0)
    (ht : starRootTarget r s=t) : g.val (rootVector t)=rootVector t := by
  have he := model_fixed_partial g hr hs (rootDomain_perpendicular r s hperp)
  simpa only [proposedPartialProduct_perpendicular (thetaInv F m).toRingHom r s hperp,ht] using he

/-- Six actual vectors generate the entire26-dimensional algebraic structure
under cross and admissible partial-star products. Vector fixation is essential:
fixing their projective lines alone does not imply this conclusion. -/
theorem model_eq_one_of_fix_six {m : ℕ} (g : Model F m)
    (h9 : g.val (rootVector (0,7))=rootVector (0,7))
    (h2 : g.val (rootVector (0,0))=rootVector (0,0))
    (h18 : g.val (rootVector (2,0))=rootVector (2,0))
    (h10 : g.val (rootVector (1,0))=rootVector (1,0))
    (h11 : g.val (rootVector (1,1))=rootVector (1,1))
    (h19 : g.val (rootVector (2,1))=rootVector (2,1)) : g=1 := by
  have h0 : g.val (diagonalVector 0)=diagonalVector 0 := by
    have he := model_fixed_cross g h9 h2
    have hc : traceZeroCross (rootVector (F := F) (0,7)) (rootVector (0,0))=diagonalVector 0 :=
      rootCross_opposite (0,7)
    simpa only [hc] using he
  have h14 : g.val (rootVector (1,4))=rootVector (1,4) :=
    model_fixed_cross_root g (0,7) (2,0) (1,4) h9 h18 (by decide)
  have h21 : g.val (rootVector (2,3))=rootVector (2,3) :=
    model_fixed_cross_root g (0,7) (1,0) (2,3) h9 h10 (by decide)
  have h23 : g.val (rootVector (2,5))=rootVector (2,5) :=
    model_fixed_cross_root g (0,7) (1,1) (2,5) h9 h11 (by decide)
  have h15 : g.val (rootVector (1,5))=rootVector (1,5) :=
    model_fixed_cross_root g (0,7) (2,1) (1,5) h9 h19 (by decide)
  have h12 : g.val (rootVector (1,2))=rootVector (1,2) :=
    model_fixed_star_root g (2,0) (2,3) (1,2) h18 h21 (by decide) (by decide)
  have h20 : g.val (rootVector (2,2))=rootVector (2,2) :=
    model_fixed_star_root g (2,0) (2,5) (2,2) h18 h23 (by decide) (by decide)
  have h3 : g.val (rootVector (0,1))=rootVector (0,1) :=
    model_fixed_cross_root g (2,0) (1,5) (0,1) h18 h15 (by decide)
  have h22 : g.val (rootVector (2,4))=rootVector (2,4) :=
    model_fixed_star_root g (1,0) (1,5) (2,4) h10 h15 (by decide) (by decide)
  have h13 : g.val (rootVector (1,3))=rootVector (1,3) :=
    model_fixed_star_root g (1,1) (1,5) (1,3) h11 h15 (by decide) (by decide)
  have h8 : g.val (rootVector (0,6))=rootVector (0,6) :=
    model_fixed_star_root g (1,4) (1,5) (0,6) h14 h15 (by decide) (by decide)
  have h24 : g.val (rootVector (2,6))=rootVector (2,6) :=
    model_fixed_cross_root g (0,7) (1,2) (2,6) h9 h12 (by decide)
  have h16 : g.val (rootVector (1,6))=rootVector (1,6) :=
    model_fixed_cross_root g (0,7) (2,2) (1,6) h9 h20 (by decide)
  have h17 : g.val (rootVector (1,7))=rootVector (1,7) :=
    model_fixed_cross_root g (0,7) (2,4) (1,7) h9 h22 (by decide)
  have h25 : g.val (rootVector (2,7))=rootVector (2,7) :=
    model_fixed_cross_root g (0,7) (1,3) (2,7) h9 h13 (by decide)
  have h4 : g.val (rootVector (0,2))=rootVector (0,2) :=
    model_fixed_star_root g (1,4) (1,2) (0,2) h14 h12 (by decide) (by decide)
  have h5 : g.val (rootVector (0,3))=rootVector (0,3) :=
    model_fixed_cross_root g (1,4) (2,4) (0,3) h14 h22 (by decide)
  have h1 : g.val (diagonalVector 1)=diagonalVector 1 := by
    have he := model_fixed_cross g h14 h13
    have hc : traceZeroCross (rootVector (F := F) (1,4)) (rootVector (1,3))=diagonalVector 1 :=
      rootCross_opposite (1,4)
    simpa only [hc] using he
  have h6 : g.val (rootVector (0,4))=rootVector (0,4) :=
    model_fixed_cross_root g (2,3) (1,3) (0,4) h21 h13 (by decide)
  have h7 : g.val (rootVector (0,5))=rootVector (0,5) :=
    model_fixed_cross_root g (2,5) (1,3) (0,5) h23 h13 (by decide)
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply markedBasis.ext
  intro i
  change g.val (markedBasis i)=markedBasis i
  rcases i with i | ⟨b,j⟩
  · fin_cases i
    · rw [markedBasis_diagonal]
      simp only [Fin.reduceFinMk]
      have he : Fin.castLE (by decide : 2 ≤ 3) (0 : Fin 2) = 0 := by decide
      rw [he]
      exact h0
    · rw [markedBasis_diagonal]
      simp only [Fin.reduceFinMk]
      have he : Fin.castLE (by decide : 2 ≤ 3) (1 : Fin 2) = 1 := by decide
      rw [he]
      exact h1
  · fin_cases b <;> fin_cases j
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h2
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h3
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h4
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h5
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h6
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h7
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h8
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h9
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h10
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h11
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h12
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h13
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h14
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h15
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h16
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h17
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h18
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h19
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h20
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h21
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h22
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h23
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h24
    · simpa only [markedBasis_root,Fin.reduceFinMk] using h25

/-- Agreement on the six generators determines an arbitrary intrinsic model
automorphism, before any full-order or displayed-generation theorem. -/
theorem model_ext_six {m : ℕ} (g h : Model F m)
    (h9 : g.val (rootVector (0,7))=h.val (rootVector (0,7)))
    (h2 : g.val (rootVector (0,0))=h.val (rootVector (0,0)))
    (h18 : g.val (rootVector (2,0))=h.val (rootVector (2,0)))
    (h10 : g.val (rootVector (1,0))=h.val (rootVector (1,0)))
    (h11 : g.val (rootVector (1,1))=h.val (rootVector (1,1)))
    (h19 : g.val (rootVector (2,1))=h.val (rootVector (2,1))) : g=h := by
  have fix (w : TraceZero F) (he : g.val w=h.val w) : (h⁻¹*g).val w=w := by
    change h.val.symm (g.val w)=w
    rw [he,h.val.symm_apply_apply]
  have hk := model_eq_one_of_fix_six (h⁻¹*g) (fix _ h9) (fix _ h2)
    (fix _ h18) (fix _ h10) (fix _ h11) (fix _ h19)
  exact (inv_mul_eq_one.mp hk).symm
end Atlas.ReeF4
