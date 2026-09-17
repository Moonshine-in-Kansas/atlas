import Atlas.Fischer.ResidueCentralizerGeneration
import Atlas.Fischer.ResidueOrder

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def residuePointCentralizer (S : Finset Omega) (x : ResiduePoint S) : residueCentralizer S :=
  ⟨x.val,by
    rintro y ⟨i,hi,rfl⟩
    exact (x.property.2.2 i hi).eq⟩

/-- The actual quotient image of an original residue involution. -/
def residueDistinguishedElement (S : Finset Omega) (x : ResiduePoint S) : ResidueGroup S :=
  QuotientGroup.mk' (residueCentralElementary S) (residuePointCentralizer S x)

/-- Killing the marked elementary subgroup leaves exactly the images of the
original residual involutions as generators. -/
theorem residueDistinguishedElement_generates (S : Finset Omega) (hS : S.card ≤ 2) :
    Subgroup.closure (Set.range (residueDistinguishedElement S))=⊤ := by
  let U := residueBasicSet S ∪ Set.range (fun x : ResiduePoint S => x.val)
  have hC : residueCentralizer S=Subgroup.closure U :=
    (residueGenerated_eq_centralizer S hS).symm
  have hgen : Subgroup.closure ((residueCentralizer S).subtype ⁻¹' U)=⊤ := by
    rw [hC]
    exact Subgroup.closure_preimage_eq_top U
  let q := QuotientGroup.mk' (residueCentralElementary S)
  have hm := congrArg (fun H : Subgroup (residueCentralizer S) => H.map q) hgen
  rw [MonoidHom.map_closure,Subgroup.map_top_of_surjective q
    (QuotientGroup.mk'_surjective _)] at hm
  apply top_unique
  rw [← hm]
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨x,hx,rfl⟩
  rcases hx with hx | ⟨y,hy⟩
  · have hx0 : q x=1 := (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.subset_closure hx)
    rw [hx0]
    exact Subgroup.one_mem _
  · apply Subgroup.subset_closure
    refine ⟨y,?_⟩
    apply congrArg q
    exact Subtype.ext hy

end Atlas.Fischer
