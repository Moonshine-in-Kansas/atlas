import Atlas.Rudvalis.CoordinateReferenceDozen
import Atlas.Rudvalis.HeavyBlockTransport
import Atlas.Rudvalis.CoordinateCrossLocalAction
import Atlas.Rudvalis.CoordinateCrossStabilizer

namespace Atlas.Rudvalis

theorem quartet_subset_canonicalBase (Q : Set MinimalCross) (hQ : IsQuartet Q) : Q⊆canonicalBase Q := by
  obtain ⟨c,hc,hcard⟩ := Set.exists_subset_card_eq (show 2≤Q.ncard by rw [hQ.1]; decide)
  intro x hx
  exact ⟨c,⟨hcard,hQ.2.1.mono hc⟩,hc,Q,hQ,hc,hx⟩

/-- Every coordinate cross occurs in a dozen of a couple of each coordinate row. -/
theorem coordinateFrame_subset_row_canonicalBase (p : Point) :
    coordinateFrame⊆canonicalBase (coordinateRowFrame p) := by
  intro c hc
  obtain ⟨⟨q,x⟩,rfl⟩ := coordinateFrame_rep c hc
  by_cases hpq : p=q
  · subst q
    exact quartet_subset_canonicalBase _ (coordinateRowFrame_isQuartet p) ⟨x,rfl⟩
  · let s : CoordinateRowPair := ⟨{p,q},by simp [hpq]⟩
    let a := coordinateRowPairNormal s
    have hap : dot a.val p.val=0 := coordinateRowPairNormal_spec s p (by simp [s])
    have haq : dot a.val q.val=0 := coordinateRowPairNormal_spec s q (by simp [s])
    let d := coordinatePlaneSlice p a 0
    let Q := coordinatePlaneQuartet p q a 0 (dot a.val x)
    have hd : IsCouple d := by
      refine ⟨?_,?_⟩
      · change Nat.card (coordinatePlaneSlice p a 0)=2
        exact coordinatePlaneSlice_card p a hap 0
      · exact (coordinateRowFrame_isQuartet p).2.1.mono (coordinatePlaneSlice_subset p a 0)
    have hdQ : d⊆Q := Set.subset_union_left
    exact ⟨d,hd,coordinatePlaneSlice_subset p a 0,Q,
      coordinatePlaneQuartet_isQuartet p q a hpq hap haq 0 (dot a.val x),hdQ,
      Or.inr ⟨x,rfl,rfl⟩⟩

/-- The actual monomial group transports the reference ordered couple to any same-row ordered pair. -/
theorem referenceCouple_same_row_transport (p : Point) (x y : E)
    (hxy : coordinateCross (p,x)≠coordinateCross (p,y)) :
    ∃g : codeGroup,g • localReferenceCross=coordinateCross (p,x) ∧
      g • referenceSecondCross=coordinateCross (p,y) := by
  have ho : coordinateCross (p,x)∈MulAction.orbit codeGroup localReferenceCross := by
    rw [coordinateCross_orbit _ (coordinateCross_mem _)]
    exact coordinateCross_mem _
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ho
  have hrow : codeRowImage g (rowLabel 0)=p := by
    have he := hg
    rw [localReferenceCross_eq,coordinateCross_action] at he
    have hr := coordinateCross_row_of_eq he
    rwa [codeRowImage_coordinates] at hr
  let z := (g.val.right (rowLabel 0,binaryLabel 2)).2
  have hsecond : g • referenceSecondCross=coordinateCross (p,z) := by
    rw [referenceSecondCross_eq,coordinateCross_action]
    congr 1
    exact Prod.ext ((codeRowImage_coordinates g _).trans hrow) rfl
  have hzx : coordinateCross (p,z)≠coordinateCross (p,x) := by
    rw [←hsecond,←hg]
    exact fun h=>reference_crosses_ne (MulAction.injective g h).symm
  obtain ⟨k,hk⟩ := coordinateCross_same_row_transitive p x z y hzx hxy.symm
  refine ⟨k.val*g,?_,?_⟩
  · rw [mul_smul,hg]; exact k.prop
  · rw [mul_smul,hsecond,hk]

theorem referenceCouple_same_row_set_transport (p : Point) (c : Set MinimalCross)
    (hc : IsCouple c) (hp : c⊆coordinateRowFrame p) :
    ∃g : codeGroup,gaussianImage (codeGaussianHom g) referenceCouple=c := by
  obtain ⟨a,b,hab,he⟩ := Set.ncard_eq_two.mp hc.1
  have ha : a∈c := by rw [he]; simp
  have hb : b∈c := by rw [he]; simp
  obtain ⟨x,rfl⟩ := hp ha
  obtain ⟨y,rfl⟩ := hp hb
  obtain ⟨g,hg0,hg2⟩ := referenceCouple_same_row_transport p x y hab
  refine ⟨g,?_⟩
  rw [he]
  simp only [gaussianImage,referenceCouple,Set.image_pair,codeGaussianHom_cross,hg0,hg2]

/-- This conditional endpoint isolates precisely the pending intrinsic reference-dozen equality. -/
theorem coordinateRow_canonicalBase_eq_of_reference_dozen
    (hD : intrinsicDozen referenceCouple=referenceCoordinateDozen) (p : Point) :
    canonicalBase (coordinateRowFrame p)=coordinateFrame := by
  apply Set.Subset.antisymm _ (coordinateFrame_subset_row_canonicalBase p)
  rintro x ⟨c,hc,hp,hx⟩
  obtain ⟨g,hg⟩ := referenceCouple_same_row_set_transport p c hc hp
  rw [←hg,←intrinsicDozen_gaussianImage,hD] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  change codeGaussianHom g • y∈coordinateFrame
  rw [codeGaussianHom_cross]
  exact coordinateFrame_code_stable g y (referenceCoordinateDozen_subset hy)

end Atlas.Rudvalis
