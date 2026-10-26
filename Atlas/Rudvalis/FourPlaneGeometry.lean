import Atlas.Rudvalis.TorsionMinimum

/-! Four-point plane moments and the unique relation of the four active row labels. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def fourPlanePoint (r : Bit) (i : Fin 4) : E :=
  ![r,![0,1,0,1] i,![0,0,1,1] i]

def fourActivePoint (i : Fin 4) : Point :=
  ⟨fourPlanePoint 1 i,by intro h; have := congrFun h 0; simp [fourPlanePoint] at this⟩

def squareIndex (b c : Bit) : Fin 4 := if c=0 then (if b=0 then 0 else 1) else (if b=0 then 2 else 3)

theorem fourPlanePoint_inverse (x : E) : fourPlanePoint (x 0) (squareIndex (x 1) (x 2))=x := by
  decide +kernel +revert

theorem fourPlanePoint_injective (r : Bit) : Function.Injective (fourPlanePoint r) := by
  decide +kernel +revert

theorem fourActivePoint_injective : Function.Injective fourActivePoint := by
  intro i j h
  exact fourPlanePoint_injective 1 (congrArg Subtype.val h)

/-- The only binary relation among the four active labels is their total sum. -/
theorem fourActivePoint_relation (v : Fin 4 → Bit) :
    (∀ j : Fin 3,(∑ i : Fin 4,(fourActivePoint i).val j * v i)=0) ↔
      ∀ i,v i=v 0 := by
  decide +kernel +revert

/-- An even subset of a four-point plane is affine in its two free coordinates. -/
theorem four_plane_even_affine (v : Fin 4 → Bit) :
    (∑ i,v i)=0 ↔ ∀ i,v i=v 0+(v 1+v 0)*fourPlanePoint 0 i 1+
      (v 2+v 0)*fourPlanePoint 0 i 2 := by
  decide +kernel +revert

def fourPlanePattern (δ b c : Bit) (i : Fin 4) : Bit :=
  δ+b*fourPlanePoint 0 i 1+c*fourPlanePoint 0 i 2

theorem fourPlanePattern_moments (r δ b c : Bit) :
    (∑ i,fourPlanePattern δ b c i)=0 ∧
    (∑ i,fourPlanePattern δ b c i • fourPlanePoint r i)=![0,c,b] := by
  decide +kernel +revert

/-- For any permitted moment, the two even subsets differ by the whole plane. -/
theorem four_plane_even_moment_classification (r : Bit) (v : Fin 4 → Bit)
    (he : (∑ i,v i)=0) :
    ∃! δ : Bit,∀ i,v i=fourPlanePattern δ
      ((∑ j,v j • fourPlanePoint r j) 2) ((∑ j,v j • fourPlanePoint r j) 1) i := by
  have hh : ∀ r : Bit,∀ v : Fin 4 → Bit,(∑ i,v i)=0 → ∀ i,
      v i=fourPlanePattern (v 0) ((∑ j,v j • fourPlanePoint r j) 2)
        ((∑ j,v j • fourPlanePoint r j) 1) i := by decide +kernel
  refine ⟨v 0,hh r v he,?_⟩
  intro δ hδ
  simpa [fourPlanePattern,fourPlanePoint] using (hδ 0).symm

end Atlas.Rudvalis

