import Atlas.Fischer.RootMapSubspaces

namespace Atlas.Fischer

def HermitianOrthogonalSubspaces (S T : Submodule Scalar Coordinates) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, hermitian x y=0

theorem hermitianOrthogonal_span (s t : Set Coordinates)
    (h : ∀ x ∈ s, ∀ y ∈ t, hermitian x y=0) :
    HermitianOrthogonalSubspaces (Submodule.span Scalar s) (Submodule.span Scalar t) := by
  have hx (x : Coordinates) (hx : x ∈ s) : ∀ y ∈ Submodule.span Scalar t, hermitian x y=0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y z hy hz ihy ihz => rw [hermitian_add_right,ihy,ihz,add_zero]
    | smul a y hy ih => rw [hermitian_smul_right,ih,mul_zero]
  intro x hxx
  induction hxx using Submodule.span_induction with
  | mem x hxx => exact hx x hxx
  | zero => intro y _; simp
  | add x z hx hz ihx ihz =>
      intro y hy
      rw [hermitian_add_left,ihx y hy,ihz y hy,add_zero]
  | smul a x hx ih => intro y hy; rw [hermitian_smul_left,ih y hy,mul_zero]

theorem HermitianOrthogonalSubspaces.symm {S T : Submodule Scalar Coordinates}
    (h : HermitianOrthogonalSubspaces S T) : HermitianOrthogonalSubspaces T S := by
  intro y hy x hx
  rw [← hermitian_star,h x hx y hy,star_zero]

theorem HermitianOrthogonalSubspaces.disjoint {S T : Submodule Scalar Coordinates}
    (h : HermitianOrthogonalSubspaces S T) : Disjoint S T := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  exact (hermitian_self_eq_zero x).mp (h x hx x hy)

/-- Antiunitarity assembles on invariant orthogonal actual subspaces. -/
theorem rootMap_antiunitary_sup (r : Coordinates) (S T : Submodule Scalar Coordinates)
    (hS : Set.MapsTo (rootMap r) S S) (hT : Set.MapsTo (rootMap r) T T)
    (aS : RootMapAntiunitaryOn r S) (aT : RootMapAntiunitaryOn r T)
    (hST : HermitianOrthogonalSubspaces S T) : RootMapAntiunitaryOn r (S ⊔ T) := by
  intro x hx y hy
  obtain ⟨s,hs,t,ht,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hy
  simp only [rootMap_add,hermitian_add_left,hermitian_add_right,star_add,
    aS s hs u hu,aT t ht v hv,hST s hs v hv,hST.symm t ht u hu,
    hST _ (hS hs) _ (hT hv),hST.symm _ (hT ht) _ (hS hu),star_zero,add_zero,zero_add]

theorem rootMap_invariant_sup (r : Coordinates) (S T : Submodule Scalar Coordinates)
    (hS : Set.MapsTo (rootMap r) S S) (hT : Set.MapsTo (rootMap r) T T) :
    Set.MapsTo (rootMap r) (S ⊔ T : Submodule Scalar Coordinates) (S ⊔ T : Submodule Scalar Coordinates) := by
  intro x hx
  obtain ⟨s,hs,t,ht,rfl⟩ := Submodule.mem_sup.mp hx
  rw [rootMap_add]
  exact Submodule.mem_sup.mpr ⟨_,hS hs,_,hT ht,rfl⟩

end Atlas.Fischer
