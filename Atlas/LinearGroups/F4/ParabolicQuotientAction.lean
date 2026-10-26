import Atlas.LinearGroups.F4.PointQuotientIsometry
import Atlas.LinearGroups.F4.ParabolicMarkedPoint

/-! The actual marked-point stabilizer acts by isometries on the seven-dimensional
quadratic quotient. No surjectivity or identification of its image is asserted. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def parabolicRestricted (g : parabolicPointStabilizer (F:=F)) :
    parabolicCrossTrace (F:=F) ≃ₗ[F] parabolicCrossTrace (F:=F) where
  toFun x := ⟨g.val.val x.val,by
    refine ⟨(parabolicPointStabilizer_preserves_kernel g x.val).mpr x.prop.1,?_⟩
    change trace (g.val.val x.val)=0
    rw [stabilizer_trace]
    exact x.prop.2⟩
  invFun x := ⟨(g⁻¹).val.val x.val,by
    refine ⟨(parabolicPointStabilizer_preserves_kernel g⁻¹ x.val).mpr x.prop.1,?_⟩
    change trace ((g⁻¹).val.val x.val)=0
    rw [stabilizer_trace]
    exact x.prop.2⟩
  left_inv x := by apply Subtype.ext; exact g.val.val.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact g.val.val.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact g.val.val.map_add x.val y.val
  map_smul' s x := by apply Subtype.ext; exact g.val.val.map_smul s x.val

theorem parabolicRestricted_middle (g : parabolicPointStabilizer (F:=F)) :
    parabolicMiddleSubspace (F:=F) ≤
      (parabolicMiddleSubspace (F:=F)).comap (parabolicRestricted g).toLinearMap := by
  intro x hx
  exact parabolicPointStabilizer_preserves_imageZero g hx

def parabolicQuotientMap (g : parabolicPointStabilizer (F:=F)) :
    ((parabolicCrossTrace (F:=F)) ⧸ (parabolicMiddleSubspace (F:=F))) →ₗ[F]
      ((parabolicCrossTrace (F:=F)) ⧸ (parabolicMiddleSubspace (F:=F))) :=
  (parabolicMiddleSubspace (F:=F)).mapQ _ (parabolicRestricted g).toLinearMap
    (parabolicRestricted_middle g)

@[simp] theorem parabolicQuotientMap_mk (g : parabolicPointStabilizer (F:=F))
    (x : parabolicCrossTrace (F:=F)) :
    parabolicQuotientMap g (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (parabolicRestricted g x) := rfl

def parabolicQuotientEquiv (g : parabolicPointStabilizer (F:=F)) :
    ((parabolicCrossTrace (F:=F)) ⧸ (parabolicMiddleSubspace (F:=F))) ≃ₗ[F]
      ((parabolicCrossTrace (F:=F)) ⧸ (parabolicMiddleSubspace (F:=F))) where
  toLinearMap := parabolicQuotientMap g
  invFun := parabolicQuotientMap g⁻¹
  left_inv x := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    change Submodule.Quotient.mk (parabolicRestricted g⁻¹ (parabolicRestricted g v)) =
      Submodule.Quotient.mk v
    congr 1
    apply Subtype.ext
    exact g.val.val.symm_apply_apply v.val
  right_inv x := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    change Submodule.Quotient.mk (parabolicRestricted g (parabolicRestricted g⁻¹ v)) =
      Submodule.Quotient.mk v
    congr 1
    apply Subtype.ext
    exact g.val.val.apply_symm_apply v.val

def parabolicSevenEquiv (g : parabolicPointStabilizer (F:=F)) :
    Atlas.Orthogonal.VectorB 3 F ≃ₗ[F] Atlas.Orthogonal.VectorB 3 F :=
  (parabolicMiddleQuotientEquiv (F:=F)).symm.trans
    ((parabolicQuotientEquiv g).trans (parabolicMiddleQuotientEquiv (F:=F)))

theorem parabolicSevenEquiv_apply (g : parabolicPointStabilizer (F:=F))
    (x : parabolicCrossTrace (F:=F)) :
    parabolicSevenEquiv g (parabolicSevenMap x)=parabolicSevenMap (parabolicRestricted g x) := by
  change parabolicMiddleQuotientEquiv (F:=F)
    (parabolicQuotientMap g ((parabolicMiddleQuotientEquiv (F:=F)).symm (parabolicSevenMap x)))=_
  rw [←parabolicMiddleQuotientEquiv_mk x,LinearEquiv.symm_apply_apply,
    parabolicQuotientMap_mk,parabolicMiddleQuotientEquiv_mk]

theorem parabolicSevenEquiv_isometry (g : parabolicPointStabilizer (F:=F))
    (v : Atlas.Orthogonal.VectorB 3 F) :
    Atlas.Orthogonal.formB 3 F (parabolicSevenEquiv g v)=Atlas.Orthogonal.formB 3 F v := by
  obtain ⟨x,rfl⟩ := parabolicSevenMap_surjective v
  rw [parabolicSevenEquiv_apply,parabolicSevenMap_form,parabolicSevenMap_form]
  change -quadraticTrace (g.val.val x.val) = -quadraticTrace x.val
  rw [stabilizer_quadraticTrace]

def parabolicOrthogonalHom : parabolicPointStabilizer (F:=F) →*
    Atlas.Orthogonal.isometrySubgroup (Atlas.Orthogonal.formB 3 F) where
  toFun g := ⟨parabolicSevenEquiv g,parabolicSevenEquiv_isometry g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := parabolicSevenMap_surjective v
    rw [parabolicSevenEquiv_apply]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := parabolicSevenMap_surjective v
    change parabolicSevenEquiv (g*h) (parabolicSevenMap x)=
      parabolicSevenEquiv g (parabolicSevenEquiv h (parabolicSevenMap x))
    rw [parabolicSevenEquiv_apply,parabolicSevenEquiv_apply,parabolicSevenEquiv_apply]
    rfl

end Atlas.F4
