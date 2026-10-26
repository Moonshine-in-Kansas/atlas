import Atlas.LinearGroups.F4.PairScalarKernel

/-! The scalar torus normalizes the actual fifteen-parameter radical.
The proof uses its affine cell action, not a full Levi order or normality input. -/
set_option maxRecDepth 4096
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def scalarRadicalParameters (a : Fˣ) (p : RadicalParameters F) : RadicalParameters F where
  point := (a:F) • p.point
  central := (a:F)^2 • p.central

theorem scalarParabolic_lower (a : Fˣ) (x : OppositeCell F) :
    oppositeLowerCoordinates (scalarParabolic a • x).val=
      (a:F) • oppositeLowerCoordinates x.val := by
  rw [oppositeCellParabolicAction_val,scalarParabolic_character]
  change oppositeLowerCoordinates ((a^2).val • (scalarTorus a).val x.val)=_
  rw [scalarTorus_apply]
  ext i; fin_cases i <;>
    simp [oppositeLowerCoordinates,scalarTorusApply,pow_two,mul_assoc,mul_comm,mul_left_comm]

theorem scalarParabolic_central (a : Fˣ) (x : OppositeCell F) :
    centralSevenCoordinates (scalarParabolic a • x).val=
      (a:F)^2 • centralSevenCoordinates x.val := by
  rw [oppositeCellParabolicAction_val,scalarParabolic_character]
  change centralSevenCoordinates ((a^2).val • (scalarTorus a).val x.val)=_
  rw [scalarTorus_apply]
  ext i; fin_cases i <;> simp [centralSevenCoordinates,scalarTorusApply]

theorem radicalCocycle_smul_smul (a : F) (u v : Fin 8 → F) :
    radicalCocycle (a • u) (a • v)=a^2 • radicalCocycle u v := by
  simp only [radicalCocycle_apply,←halfWordBilinearMap_apply,map_smul,
    LinearMap.smul_apply,smul_smul,pow_two]

theorem scalarParabolic_radicalOpposite (a : Fˣ) (p : RadicalParameters F) (x : OppositeCell F) :
    scalarParabolic a • radicalOpposite p x=
      radicalOpposite (scalarRadicalParameters a p) (scalarParabolic a • x) := by
  apply oppositeCell_coordinate_ext
  · rw [scalarParabolic_lower,radicalOpposite_lower,radicalOpposite_lower,scalarParabolic_lower]
    exact smul_add _ _ _
  · rw [scalarParabolic_central,radicalOpposite_central,radicalOpposite_central,
      scalarParabolic_central,scalarParabolic_lower]
    change (a:F)^2 • (_+radicalCocycle p.point (oppositeLowerCoordinates x.val)+p.central)=
      (a:F)^2 • _+radicalCocycle ((a:F) • p.point) ((a:F) • oppositeLowerCoordinates x.val)+
        (a:F)^2 • p.central
    rw [radicalCocycle_smul_smul,smul_add,smul_add]

attribute [local irreducible] radicalElement scalarTorus

theorem scalarTorus_radical_commutation (a : Fˣ) (p : RadicalParameters F) :
    scalarTorus a*radicalElement p=radicalElement (scalarRadicalParameters a p)*scalarTorus a := by
  apply oppositeCell_action_ext
  intro x
  have h := congrArg Subtype.val (scalarParabolic_radicalOpposite a p x)
  rw [oppositeCellParabolicAction_val,scalarParabolic_character,radicalOpposite_val,
    radicalOpposite_val,oppositeCellParabolicAction_val,scalarParabolic_character] at h
  change (a^2).val • (scalarTorus a).val ((radicalElement p).val x.val)=
    (radicalElement (scalarRadicalParameters a p)).val ((a^2).val • (scalarTorus a).val x.val) at h
  rw [map_smul] at h
  have hh := congrArg (fun v : Carrier F=>((a^2)⁻¹).val • v) h
  change (scalarTorus a).val ((radicalElement p).val x.val)=
    (radicalElement (scalarRadicalParameters a p)).val ((scalarTorus a).val x.val)
  simpa only [smul_smul,Units.inv_mul,one_smul] using hh

theorem scalarTorus_radical_conjugation (a : Fˣ) (p : RadicalParameters F) :
    scalarTorus a*radicalElement p*(scalarTorus a)⁻¹=
      radicalElement (scalarRadicalParameters a p) := by
  rw [scalarTorus_radical_commutation,mul_assoc,mul_inv_cancel,mul_one]

theorem scalarTorus_normalizes_radical (a : Fˣ) :
    scalarTorus a∈Subgroup.normalizer (radicalSubgroup (F:=F) : Set (Model F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨scalarRadicalParameters a p, (scalarTorus_radical_conjugation a p).symm⟩
  · intro hg
    have hginv : scalarTorus a⁻¹=(scalarTorus a)⁻¹ := by
      apply mul_left_cancel (a:=scalarTorus a)
      rw [←scalarTorus_mul,mul_inv_cancel,scalarTorus_one,mul_inv_cancel]
    obtain ⟨p,hp⟩ := hg
    change radicalElement p=scalarTorus a*g*(scalarTorus a)⁻¹ at hp
    have he := scalarTorus_radical_conjugation a⁻¹ p
    rw [hginv,hp] at he
    have hh : g=radicalElement (scalarRadicalParameters a⁻¹ p) := by
      simpa [mul_assoc] using he
    exact ⟨scalarRadicalParameters a⁻¹ p,hh.symm⟩

end Atlas.F4
