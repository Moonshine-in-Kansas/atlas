import Atlas.LinearGroups.Orthogonal.EvenBSingularTransport
import Atlas.LinearGroups.Symplectic.Primitivity

/-! # Actual singular points of even B and symplectic projective points -/
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

theorem evenSingularLift_ne_zero (u : VectorD n F) (hu : u ≠ 0) : evenSingularLift u ≠ 0 :=
  fun h => hu (congrArg Prod.fst h)

theorem evenSingularLift_smul (c : F) (u : VectorD n F) :
    evenSingularLift (c • u) = c • evenSingularLift u := by
  apply evenB_singular_eq_of_first_eq _ _ (evenSingularLift_singular _)
  · rw [(formB n F).map_smul,evenSingularLift_singular,smul_zero]
  · rfl

def evenSingularPointOfVector (u : VectorD n F) (hu : u ≠ 0) : SingularPoints (formB n F) :=
  singularPointMk _ (evenSingularLift u) (evenSingularLift_ne_zero u hu) (evenSingularLift_singular u)

def evenSingularPointLift : Atlas.Symplectic.Points n F → SingularPoints (formB n F) :=
  Projectivization.lift (fun u => evenSingularPointOfVector u.val u.prop) (by
    intro u v c hc
    apply Subtype.ext
    change Projectivization.mk F (evenSingularLift u.val) _ = Projectivization.mk F (evenSingularLift v.val) _
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨c,by rw [← evenSingularLift_smul,← hc]⟩)

@[simp] theorem evenSingularPointLift_mk (u : VectorD n F) (hu : u ≠ 0) :
    evenSingularPointLift (Projectivization.mk F u hu) = evenSingularPointOfVector u hu := rfl

theorem evenSingularPointLift_surjective : Function.Surjective (evenSingularPointLift (n := n) (F := F)) := by
  intro p
  let u := p.val.rep
  have hu : u.1 ≠ 0 := evenB_singular_first_ne_zero u p.val.rep_nonzero p.prop
  refine ⟨Projectivization.mk F u.1 hu,?_⟩
  have he : evenSingularLift u.1 = u :=
    evenB_singular_eq_of_first_eq _ _ (evenSingularLift_singular _) p.prop rfl
  apply Subtype.ext
  change Projectivization.mk F (evenSingularLift u.1) _ = p.val
  rw [← Projectivization.mk_rep p.val,Projectivization.mk_eq_mk_iff']
  exact ⟨1,by simpa using he.symm⟩

theorem evenSingularPointLift_injective : Function.Injective (evenSingularPointLift (n := n) (F := F)) := by
  intro p q hpq
  rw [← Projectivization.mk_rep p,← Projectivization.mk_rep q] at hpq ⊢
  have h := congrArg Subtype.val hpq
  change Projectivization.mk F (evenSingularLift p.rep) _ = Projectivization.mk F (evenSingularLift q.rep) _ at h
  rw [Projectivization.mk_eq_mk_iff'] at h ⊢
  obtain ⟨c,hc⟩ := h
  exact ⟨c,congrArg Prod.fst hc⟩

def evenSingularPointEquiv : Atlas.Symplectic.Points n F ≃ SingularPoints (formB n F) :=
  Equiv.ofBijective evenSingularPointLift ⟨evenSingularPointLift_injective,evenSingularPointLift_surjective⟩

theorem evenSingularLift_equivariant (g : O_B n F) (u : VectorD n F) :
    g.val (evenSingularLift u) = evenSingularLift (evenProjection g • u) := by
  apply evenB_singular_eq_of_first_eq _ _ ((g.prop _).trans (evenSingularLift_singular _))
    (evenSingularLift_singular _)
  rw [even_first]
  exact (evenProjection_apply g u).symm

theorem evenSingularPointLift_smul (g : O_B n F) (p : Atlas.Symplectic.Points n F) :
    evenSingularPointLift (evenProjection g • p) = g • evenSingularPointLift p := by
  rw [← Projectivization.mk_rep p,Projectivization.smul_mk]
  apply Subtype.ext
  change Projectivization.mk F (evenSingularLift (evenProjection g • p.rep)) _ =
    g.val • Projectivization.mk F (evenSingularLift p.rep) _
  rw [Projectivization.smul_mk,Projectivization.mk_eq_mk_iff']
  exact ⟨1,by simpa only [one_smul,LinearEquiv.smul_def] using evenSingularLift_equivariant g p.rep⟩



/-- The square-root lift is equivariant for the actual full B/C comparison. -/
def evenSingularPointActionHom : Atlas.Symplectic.Points n F →ₑ[
    (evenFullEquivSp (n := n) (F := F)).symm.toMonoidHom] SingularPoints (formB n F) where
  toFun := evenSingularPointLift
  map_smul' a p := by
    have h := evenSingularPointLift_smul ((evenFullEquivSp (n := n) (F := F)).symm a) p
    have he : evenProjection ((evenFullEquivSp (n := n) (F := F)).symm a) = a :=
      (evenFullEquivSp (n := n) (F := F)).apply_symm_apply a
    rw [he] at h
    exact h

theorem evenB_full_faithful (hn : 1 ≤ n) :
    FaithfulSMul (O_B n F) (SingularPoints (formB n F)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hs : ∀ p : Atlas.Symplectic.Points n F, evenProjection g • p = p := by
    intro p
    apply evenSingularPointLift_injective
    rw [evenSingularPointLift_smul,hg]
  have hc := (Atlas.Symplectic.fixes_points_iff_central (evenProjection g)).mp hs
  rw [even_symplectic_center (by omega),Subgroup.mem_bot] at hc
  apply evenProjection_injective
  exact hc.trans evenProjection.map_one.symm

theorem evenB_projective_faithful (hn : 1 ≤ n) :
    FaithfulSMul (B n F) (SingularPoints (formB n F)) := by
  letI := evenB_full_faithful (F := F) hn
  apply faithfulSMul_iff.mpr
  intro g hg
  obtain ⟨a,rfl⟩ := projectiveElementaryMap_surjective (formB n F) g
  have ha : a.val = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := SingularPoints (formB n F))
    intro p
    exact (hg p).trans (one_smul _ _).symm
  have ha' : a = 1 := Subtype.ext ha
  rw [ha',map_one]

variable [Finite F]

theorem evenB_full_primitive (hn : 2 ≤ n) :
    MulAction.IsPreprimitive (O_B n F) (SingularPoints (formB n F)) := by
  let f : Atlas.Symplectic.Points n F →ₑ[
      (Atlas.Symplectic.projection : Atlas.Symplectic.Sp n F →* Atlas.Symplectic.PSp n F)]
      Atlas.Symplectic.Points n F := {
    toFun := id
    map_smul' := fun g p => (Atlas.Symplectic.projection_smul g p).symm }
  letI : MulAction.IsPreprimitive (Atlas.Symplectic.Sp n F) (Atlas.Symplectic.Points n F) :=
    (MulAction.isPreprimitive_congr (f := f) Atlas.Symplectic.projection_surjective
      Function.bijective_id).mpr (Atlas.Symplectic.projective_preprimitive hn)
  exact MulAction.IsPreprimitive.of_surjective (f := evenSingularPointActionHom)
    evenSingularPointLift_surjective

theorem evenB_elementary_primitive (hn : 2 ≤ n) :
    MulAction.IsPreprimitive (elementarySubgroup (formB n F)) (SingularPoints (formB n F)) := by
  letI := evenB_full_primitive (F := F) hn
  let f : SingularPoints (formB n F) →ₑ[
      (evenElementaryBEquivFull (n := n) (F := F)).symm.toMonoidHom]
      SingularPoints (formB n F) := { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem evenB_projective_primitive (hn : 2 ≤ n) :
    MulAction.IsPreprimitive (B n F) (SingularPoints (formB n F)) := by
  letI := evenB_elementary_primitive (F := F) hn
  let f : SingularPoints (formB n F) →ₑ[projectiveElementaryMap (formB n F)]
      SingularPoints (formB n F) := { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id
end Atlas.Orthogonal
