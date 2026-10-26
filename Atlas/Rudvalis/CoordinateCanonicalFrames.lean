import Atlas.Rudvalis.CoordinateRowDozens
import Atlas.Rudvalis.ReferenceQuartetExhaustion

namespace Atlas.Rudvalis

/-- Every coordinate row determines the entire coordinate frame intrinsically. -/
theorem coordinateRow_canonicalBase_eq (p : Point) :
    canonicalBase (coordinateRowFrame p)=coordinateFrame :=
  coordinateRow_canonicalBase_eq_of_reference_dozen reference_intrinsicDozen_eq p

theorem coordinateFrame_isCanonicalBase : coordinateFrame∈canonicalBases :=
  ⟨coordinateRowFrame (rowLabel 0),coordinateRowFrame_isQuartet _,coordinateRow_canonicalBase_eq _⟩

/-- The dozen of either complementary couple in a row slice is exactly the associated three-row plane. -/
theorem coordinatePlaneSlice_dozen_eq (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) :
    intrinsicDozen (coordinatePlaneSlice p a δ)=coordinatePlaneDozen a :=
  coordinatePlaneSlice_dozen_eq_of_reference reference_intrinsicDozen_eq p a hap δ

theorem rowCoupleDozens_eq_planes (p : Point) :
    rowCoupleDozens p=Set.range (rowPlaneDozen p) :=
  rowCoupleDozens_eq_planes_of_reference reference_intrinsicDozen_eq p

/-- The couples in a coordinate row determine precisely three distinct intrinsic dozens. -/
theorem rowCoupleDozens_card (p : Point) : Nat.card (rowCoupleDozens p)=3 :=
  rowCoupleDozens_card_of_reference reference_intrinsicDozen_eq p

theorem coordinateRow_three_dozen_geometry (p : Point) :
    Nat.card (rowCoupleDozens p)=3 ∧
    (∀D∈rowCoupleDozens p,Nat.card D=12) ∧
    (∀D∈rowCoupleDozens p,∀D'∈rowCoupleDozens p,D≠D' → D∩D'=coordinateRowFrame p) ∧
    {c | ∃D∈rowCoupleDozens p,c∈D}=coordinateFrame := by
  refine ⟨rowCoupleDozens_card p,?_,?_,?_⟩
  · intro D hD
    rw [rowCoupleDozens_eq_planes] at hD
    obtain ⟨a,rfl⟩ := hD
    exact coordinatePlaneDozen_card a.val
  · intro D hD D' hD' hne
    rw [rowCoupleDozens_eq_planes] at hD hD'
    obtain ⟨a,rfl⟩ := hD
    obtain ⟨b,rfl⟩ := hD'
    exact rowPlaneDozen_intersection p a b (fun h=>hne (congrArg (rowPlaneDozen p) h))
  · rw [rowCoupleDozens_eq_planes]
    have he : {c | ∃D∈Set.range (rowPlaneDozen p),c∈D}=
        {c | ∃a : {a : Point // dot a.val p.val=0},c∈rowPlaneDozen p a} := by
      ext c
      constructor
      · rintro ⟨D,⟨a,rfl⟩,hc⟩; exact ⟨a,hc⟩
      · rintro ⟨a,hc⟩; exact ⟨_,⟨a,rfl⟩,hc⟩
    rw [he,rowPlaneDozens_union]

end Atlas.Rudvalis
