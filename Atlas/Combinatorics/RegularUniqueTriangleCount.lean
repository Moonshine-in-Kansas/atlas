import Atlas.Combinatorics.UniqueTriangleFrames

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def relationEdgeFiberEquiv {X : Type*} (R : X → X → Prop) :
    RelationEdge R ≃ (x : X) × {y : X // R x y} where
  toFun p := ⟨p.val.1,p.val.2,p.property⟩
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem relationEdge_card {X : Type*} [Fintype X] (R : X → X → Prop) (d : ℕ)
    (hd : ∀ x,Nat.card {y : X // R x y}=d) :
    Nat.card (RelationEdge R)=Nat.card X*d := by
  rw [Nat.card_congr (relationEdgeFiberEquiv R),Nat.card_sigma]
  simp_rw [hd]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card]
  simp [nsmul_eq_mul]

/-- Double count ordered triangle incidences. Every adjacent ordered pair
has one completion, while every unordered triangle has six ordered edges. -/
theorem regular_unique_triangle_count {X : Type*} [Fintype X]
    (R : X → X → Prop) (hsym : Symmetric R) (hirr : Irreflexive R)
    (hu : ∀ x y,R x y → ∃! z,R x z ∧ R y z)
    (d : ℕ) (hd : ∀ x,Nat.card {y : X // R x y}=d) :
    Nat.card (RelationTriangle R)*6=Nat.card X*d := by
  classical
  letI : Fintype (RelationTriangle R) := Fintype.ofFinite _
  have hf (F : RelationTriangle R) : Nat.card {p : X × X // p∈F.val.offDiag}=6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.offDiag_card,F.property.1]
  have h := Nat.card_congr (triangleEdgeEquiv R hsym hirr hu)
  rw [Nat.card_sigma,relationEdge_card R d hd] at h
  change (∑ F : RelationTriangle R,Nat.card {p : X × X // p∈F.val.offDiag})=Nat.card X*d at h
  simp_rw [hf] at h
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card] at h
  simpa [nsmul_eq_mul] using h

/-- The315-point, degree-ten specialization uses only finite incidence axioms. -/
theorem regular_unique_triangle_count_315_10 {X : Type*} [Fintype X]
    (R : X → X → Prop) (hsym : Symmetric R) (hirr : Irreflexive R)
    (hu : ∀ x y,R x y → ∃! z,R x z ∧ R y z)
    (hx : Nat.card X=315) (hd : ∀ x,Nat.card {y : X // R x y}=10) :
    Nat.card (RelationTriangle R)=525 := by
  have h := regular_unique_triangle_count R hsym hirr hu 10 hd
  rw [hx] at h
  omega

end Atlas.Combinatorics
