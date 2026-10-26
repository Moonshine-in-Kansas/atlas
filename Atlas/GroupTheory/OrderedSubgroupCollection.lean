import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Uniform collection infrastructure. No finiteness, cardinality, or
root-system recognition enters these purely group-theoretic lemmas. -/
namespace Atlas.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

def orderedSubgroupProduct : List (Subgroup G) → Set G
  | [] => {1}
  | H :: L => (H : Set G) * orderedSubgroupProduct L

def subgroupListJoin : List (Subgroup G) → Subgroup G
  | [] => ⊥
  | H :: L => H ⊔ subgroupListJoin L

theorem subgroupListJoin_le_iff (L : List (Subgroup G)) (K : Subgroup G) :
    subgroupListJoin L ≤ K ↔ ∀ H ∈ L, H ≤ K := by
  induction L with
  | nil => simp [subgroupListJoin]
  | cons H L ih => simp [subgroupListJoin, sup_le_iff, ih]

theorem orderedSubgroupProduct_subset_join (L : List (Subgroup G)) :
    orderedSubgroupProduct L ⊆ (subgroupListJoin L : Set G) := by
  induction L with
  | nil => simp [orderedSubgroupProduct, subgroupListJoin]
  | cons H L ih =>
    rintro g ⟨x,hx,y,hy,rfl⟩
    exact (H ⊔ subgroupListJoin L).mul_mem
      ((show H ≤ H ⊔ subgroupListJoin L from le_sup_left) hx)
      ((show subgroupListJoin L ≤ H ⊔ subgroupListJoin L from le_sup_right) (ih hy))

/-- Move one later generator past an arbitrary element of the head subgroup.
The replacement is allowed anywhere in the ordered tail product. -/
def CollectsBefore (H : Subgroup G) (L : List (Subgroup G)) : Prop :=
  ∀ x ∈ H, ∀ J ∈ L, ∀ y ∈ J,
    ∃ z ∈ orderedSubgroupProduct L, y*x = x*z

/-- Every suffix has the requisite head-versus-tail collection law. -/
def HasOrderedCollection : List (Subgroup G) → Prop
  | [] => True
  | H :: L => CollectsBefore H L ∧ HasOrderedCollection L

theorem collectsBefore_le_normalizer {H : Subgroup G} {L : List (Subgroup G)}
    (hcollect : CollectsBefore H L) : H ≤ Subgroup.normalizer (subgroupListJoin L) := by
  let K := subgroupListJoin L
  have hconj (x : G) (hx : x ∈ H) :
      ∀ y ∈ K, x⁻¹*y*x ∈ K := by
    have hle : K ≤ K.comap (MulAut.conj x⁻¹).toMonoidHom := by
      apply (subgroupListJoin_le_iff L _).mpr
      intro J hJ y hy
      obtain ⟨z,hz,hrel⟩ := hcollect x hx J hJ y hy
      change x⁻¹*y*(x⁻¹)⁻¹ ∈ K
      rw [inv_inv]
      have heq : x⁻¹*y*x = z := by
        calc
          x⁻¹*y*x = x⁻¹*(y*x) := by simp only [mul_assoc]
          _ = x⁻¹*(x*z) := by rw [hrel]
          _ = z := by simp
      rw [heq]
      exact orderedSubgroupProduct_subset_join L hz
    intro y hy
    have hh := hle hy
    change x⁻¹*y*(x⁻¹)⁻¹ ∈ K at hh
    simpa only [inv_inv] using hh
  intro x hx
  apply Subgroup.mem_normalizer_iff''.mpr
  intro y
  constructor
  · exact hconj x hx y
  · intro hy
    have h := hconj x⁻¹ (H.inv_mem hx) (x⁻¹*y*x) hy
    simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using h

/-- Collection implies that the ordered product is exactly a subgroup carrier. -/
theorem orderedSubgroupProduct_eq_join (L : List (Subgroup G))
    (hcollect : HasOrderedCollection L) :
    orderedSubgroupProduct L = (subgroupListJoin L : Set G) := by
  induction L with
  | nil => ext g; simp [orderedSubgroupProduct, subgroupListJoin]
  | cons H L ih =>
    change (H : Set G) * orderedSubgroupProduct L = ((H ⊔ subgroupListJoin L : Subgroup G) : Set G)
    rw [ih hcollect.2]
    exact (Subgroup.coe_mul_of_left_le_normalizer_right H (subgroupListJoin L)
      (collectsBefore_le_normalizer hcollect.1)).symm

/-- In particular both multiplication and inversion stay in the ordered image. -/
theorem orderedSubgroupProduct_mul_mem {L : List (Subgroup G)}
    (hcollect : HasOrderedCollection L) {x y : G}
    (hx : x ∈ orderedSubgroupProduct L) (hy : y ∈ orderedSubgroupProduct L) :
    x*y ∈ orderedSubgroupProduct L := by
  rw [orderedSubgroupProduct_eq_join L hcollect] at hx hy ⊢
  exact (subgroupListJoin L).mul_mem hx hy

theorem orderedSubgroupProduct_inv_mem {L : List (Subgroup G)}
    (hcollect : HasOrderedCollection L) {x : G}
    (hx : x ∈ orderedSubgroupProduct L) : x⁻¹ ∈ orderedSubgroupProduct L := by
  rw [orderedSubgroupProduct_eq_join L hcollect] at hx ⊢
  exact (subgroupListJoin L).inv_mem hx

end Atlas.GroupTheory
