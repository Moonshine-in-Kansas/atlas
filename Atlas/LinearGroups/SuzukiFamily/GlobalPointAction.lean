import Atlas.LinearGroups.SuzukiFamily.RootPointAction
import Atlas.LinearGroups.SuzukiFamily.TorusPointAction
import Atlas.LinearGroups.SuzukiFamily.WeylPointAction

/-! Restriction of the actual projective action to the finite Suzuki ovoid. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def pointSetStabilizer (m : ℕ) : Subgroup (Atlas.Symplectic.Sp 2 F) where
  carrier := {g | Set.MapsTo (pointLeft g) (pointSet m) (pointSet m)}
  one_mem' := by simp [pointLeft_one,Set.mapsTo_id]
  mul_mem' := by
    intro g h hg hh p hp
    rw [pointLeft_mul]
    exact hg (hh hp)
  inv_mem' := by
    intro g hg p hp
    letI : Finite (pointSet (F := F) m) := Finite.of_equiv (Option (F × F)) (pointEquiv m)
    have hb := ((pointSet (F := F) m).toFinite.injOn_iff_bijOn_of_mapsTo hg).mp
      (pointLeft_injective g).injOn
    obtain ⟨x,hx,hxp⟩ := hb.surjOn hp
    have he : pointLeft g⁻¹ (pointLeft g x)=x := by
      have hh := congrFun (pointLeft_mul g⁻¹ g) x
      simpa [pointLeft_one] using hh.symm
    rw [← hxp,he]
    exact hx

theorem generated_preserves_pointSet (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    generated (F := F) m ≤ pointSetStabilizer m := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ((⟨⟨a,b⟩,rfl⟩ | ⟨t,rfl⟩) | hw)
  · rintro p ⟨v,rfl⟩
    cases v with
    | none => exact ⟨none, (root_infinity m a b).symm⟩
    | some v => exact ⟨some (a+v.1,b+v.2+a*theta F m v.1),
        (root_affine m hcard a b v.1 v.2).symm⟩
  · rintro p ⟨v,rfl⟩
    cases v with
    | none => exact ⟨none, (torus_infinity m t).symm⟩
    | some v => exact ⟨some (theta F m ((t⁻¹:Fˣ):F)*v.1,
        ((t⁻¹:Fˣ):F)^2*theta F m ((t⁻¹:Fˣ):F)*v.2),
        (torus_affine m hcard t v.1 v.2).symm⟩
  · have he : g=weylElement := Set.mem_singleton_iff.mp hw
    subst g
    rintro p ⟨v,rfl⟩
    cases v with
    | none => exact ⟨some (0,0),(weyl_infinity m).symm⟩
    | some v =>
      by_cases hn : norm m v.1 v.2=0
      · obtain ⟨ha,hb⟩ := (norm_eq_zero_iff m hcard v.1 v.2).mp hn
        exact ⟨none,by simpa [pointParam,ha,hb] using (weyl_origin (F := F) m).symm⟩
      · exact ⟨some (inverseFirst m v.1 v.2,inverseSecond m v.1 v.2),
          (weyl_affine m hcard v.1 v.2 hn).symm⟩

def pointAction (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    MulAction (Group F m) (pointSet (F := F) m) where
  smul g p := ⟨pointLeft g.val p.val,generated_preserves_pointSet m hcard g.property p.property⟩
  one_smul p := by apply Subtype.ext; exact congrFun pointLeft_one p.val
  mul_smul g h p := by
    apply Subtype.ext
    exact congrFun (pointLeft_mul g.val h.val) p.val
end Atlas.SuzukiFamily
