import Atlas.Fischer.FischerDoubleCoverExact
import Atlas.Fischer.ResiduePerfectness

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def doubleCoverResidualElement (i j : Omega) (x : ResiduePoint {i,j}) : FischerDoubleCover i j :=
  QuotientGroup.mk' (doubleCentralizerFirstKernel i j) (residuePointCentralizer {i,j} x)

theorem doubleCoverResidualElement_basic (i j k : Omega) (hk : k∉({i,j}:Finset Omega)) :
    doubleCoverResidualElement i j (residueBasicPoint {i,j} k hk)=doubleCoverMarkedElement i j k := by
  apply congrArg (QuotientGroup.mk' (doubleCentralizerFirstKernel i j))
  apply Subtype.ext
  exact (generatedCocodeRayHom_coordinate k).symm

theorem doubleCoverResidualElement_square (i j : Omega) (x : ResiduePoint {i,j}) :
    doubleCoverResidualElement i j x ^ 2=1 := by
  rw [doubleCoverResidualElement,← map_pow]
  have hx : (residuePointCentralizer {i,j} x)^2=1 := by
    apply Subtype.ext
    obtain ⟨t,ht⟩ := x.prop.1
    change x.val^2=1
    rw [← ht,← distinguishedRootElement_order t]
    exact pow_orderOf_eq_one _
  rw [hx,map_one]

theorem doubleCoverResidualElement_conjugate (i j : Omega)
    (x y : ResiduePoint {i,j}) :
    ∃ g : FischerDoubleCover i j,
      g*doubleCoverResidualElement i j x*g⁻¹=doubleCoverResidualElement i j y := by
  haveI := residuePoint_transitive ({i,j}:Finset Omega) (by have h := Finset.card_insert_le i ({j}:Finset Omega); simpa using h.trans (by decide : 1+1≤4))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (residueCentralizer {i,j}) x y
  let q := QuotientGroup.mk' (doubleCentralizerFirstKernel i j)
  refine ⟨q g,?_⟩
  change q g*q (residuePointCentralizer {i,j} x)*(q g)⁻¹=q (residuePointCentralizer {i,j} y)
  rw [← map_inv,← map_mul,← map_mul]
  apply congrArg q
  apply Subtype.ext
  exact (residuePoint_smul_val {i,j} g x).symm.trans (congrArg Subtype.val hg)

/-- The double cover retains the second marked involution as one additional generator. -/
theorem doubleCover_generators (i j : Omega) :
    Subgroup.closure (insert (doubleCoverMarkedElement i j j)
      (Set.range (doubleCoverResidualElement i j)))=⊤ := by
  let S : Finset Omega := {i,j}
  let U := residueBasicSet S ∪ Set.range (fun x : ResiduePoint S => x.val)
  have hC : residueCentralizer S=Subgroup.closure U :=
    (residueGenerated_eq_centralizer S (by have h := Finset.card_insert_le i ({j}:Finset Omega); simpa [S] using h)).symm
  have hgen : Subgroup.closure ((residueCentralizer S).subtype ⁻¹' U)=⊤ := by
    rw [hC]
    exact Subgroup.closure_preimage_eq_top U
  let q := QuotientGroup.mk' (doubleCentralizerFirstKernel i j)
  have hm := congrArg (fun H : Subgroup (residueCentralizer S) => H.map q) hgen
  rw [MonoidHom.map_closure,Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hm
  apply top_unique
  rw [← hm]
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨a,ha,rfl⟩
  rcases ha with ⟨k,hk,hka⟩ | ⟨x,hx⟩
  · have he : q a=doubleCoverMarkedElement i j k := by
      apply congrArg q
      apply Subtype.ext
      exact hka.symm.trans (generatedCocodeRayHom_coordinate k).symm
    rw [he]
    rcases Finset.mem_insert.mp hk with rfl | hk
    · rw [doubleCoverMarkedElement_first]
      exact Subgroup.one_mem _
    · have hk := Finset.mem_singleton.mp hk
      rw [hk]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
  · apply Subgroup.subset_closure
    apply Set.mem_insert_of_mem
    refine ⟨x,?_⟩
    apply congrArg q
    exact Subtype.ext hx

end Atlas.Fischer
