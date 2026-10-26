import Atlas.LinearGroups.SuzukiFamily.GlobalPointAction
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Double transitivity of the concrete ovoid action, independently of the order. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem pointLeft_inv_cancel (g : Atlas.Symplectic.Sp 2 F) (p : Projective F) :
    pointLeft g⁻¹ (pointLeft g p)=p := by
  have hh := congrFun (pointLeft_mul g⁻¹ g) p
  simpa [pointLeft_one] using hh.symm

theorem root_origin (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    pointLeft (rootElement m a b) (affinePoint m 0 0)=affinePoint m a b := by
  simpa using root_affine m hcard a b 0 0

theorem move_point_to_infinity (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    {p : Projective F} (hp : p ∈ pointSet m) :
    ∃ g : Group F m, pointLeft g.val p=infinityPoint := by
  obtain ⟨op,rfl⟩ := hp
  cases op with
  | none => exact ⟨1,congrFun pointLeft_one infinityPoint⟩
  | some p =>
    rcases p with ⟨a,b⟩
    refine ⟨⟨weylElement * (rootElement m a b)⁻¹,
      (generated m).mul_mem (weylElement_mem m)
        ((generated m).inv_mem (rootElement_mem m a b))⟩,?_⟩
    change pointLeft (weylElement * (rootElement m a b)⁻¹) (affinePoint m a b)=_
    rw [pointLeft_mul]
    change pointLeft weylElement (pointLeft (rootElement m a b)⁻¹ (affinePoint m a b))=_
    rw [← root_origin m hcard a b,pointLeft_inv_cancel,weyl_origin]

theorem move_pair_to_base (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    {p q : Projective F} (hp : p ∈ pointSet m) (hq : q ∈ pointSet m) (hpq : p≠q) :
    ∃ g : Group F m, pointLeft g.val p=infinityPoint ∧ pointLeft g.val q=affinePoint m 0 0 := by
  obtain ⟨t,ht⟩ := move_point_to_infinity m hcard hp
  obtain ⟨op,hop⟩ := generated_preserves_pointSet m hcard t.property hq
  cases op with
  | none => exact False.elim (hpq (pointLeft_injective t.val (ht.trans hop)))
  | some r =>
    rcases r with ⟨a,b⟩
    change affinePoint m a b=pointLeft t.val q at hop
    refine ⟨⟨(rootElement m a b)⁻¹*t.val,
      (generated m).mul_mem ((generated m).inv_mem (rootElement_mem m a b)) t.property⟩,?_,?_⟩
    · change pointLeft ((rootElement m a b)⁻¹*t.val) p=_
      rw [pointLeft_mul]
      change pointLeft (rootElement m a b)⁻¹ (pointLeft t.val p)=_
      rw [ht,← root_infinity m a b,pointLeft_inv_cancel]
      exact (root_infinity m a b).symm
    · change pointLeft ((rootElement m a b)⁻¹*t.val) q=_
      rw [pointLeft_mul]
      change pointLeft (rootElement m a b)⁻¹ (pointLeft t.val q)=_
      rw [← hop,← root_origin m hcard a b,pointLeft_inv_cancel]

theorem pointAction_two_pretransitive (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    letI := pointAction m hcard
    MulAction.IsMultiplyPretransitive (Group F m) (pointSet (F := F) m) 2 := by
  letI := pointAction m hcard
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨s,hs1,hs2⟩ := move_pair_to_base m hcard a.property b.property
    (fun he => hab (Subtype.ext he))
  obtain ⟨t,ht1,ht2⟩ := move_pair_to_base m hcard c.property d.property
    (fun he => hcd (Subtype.ext he))
  refine ⟨t⁻¹*s,?_,?_⟩
  · apply Subtype.ext
    change pointLeft (t.val⁻¹*s.val) a.val=c.val
    rw [pointLeft_mul]
    change pointLeft t.val⁻¹ (pointLeft s.val a.val)=c.val
    rw [hs1,← ht1,pointLeft_inv_cancel]
  · apply Subtype.ext
    change pointLeft (t.val⁻¹*s.val) b.val=d.val
    rw [pointLeft_mul]
    change pointLeft t.val⁻¹ (pointLeft s.val b.val)=d.val
    rw [hs2,← ht2,pointLeft_inv_cancel]

theorem pointAction_preprimitive (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    letI := pointAction m hcard
    MulAction.IsPreprimitive (Group F m) (pointSet (F := F) m) := by
  letI := pointAction m hcard
  exact MulAction.isPreprimitive_of_is_two_pretransitive (pointAction_two_pretransitive m hcard)
end Atlas.SuzukiFamily
