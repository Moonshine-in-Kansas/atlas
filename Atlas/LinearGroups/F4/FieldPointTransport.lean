import Atlas.LinearGroups.F4.FieldTransport
import Atlas.LinearGroups.F4.ParabolicMarkedPoint

/-! Coefficientwise field transport of the actual white projective points and
of their marked stabilizers. The map is semilinear over the given field equivalence. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K]

def coefficientSemilinear (f : F ≃+* K) : Carrier F →ₛₗ[f.toRingHom] Carrier K where
  toFun := Atlas.Albert.map f.toRingHom
  map_add' := Atlas.Albert.map_add f.toRingHom
  map_smul' a x := by
    apply Prod.ext
    · ext i; exact f.map_mul a (x.1 i)
    · ext i j; exact f.map_mul a (x.2 i j)

theorem coefficientSemilinear_injective (f : F ≃+* K) :
    Function.Injective (coefficientSemilinear f) := by
  intro x y h
  have he := congrArg (Atlas.Albert.map f.symm.toRingHom) h
  exact (coefficient_inverse f x).symm.trans (he.trans (coefficient_inverse f y))

def fieldPointMap (f : F ≃+* K) (p : WhiteZeroPoints F) : WhiteZeroPoints K :=
  ⟨Projectivization.map (coefficientSemilinear f) (coefficientSemilinear_injective f) p.val,by
    rw [←Projectivization.mk_rep p.val,Projectivization.map_mk]
    apply (Atlas.LinearAlgebra.cone_mk_iff
      (fun x : Carrier K => trace x=0 ∧ adjoint x=0) (whiteZero_smul_iff K) _ _).mpr
    change trace (Atlas.Albert.map f.toRingHom p.val.rep)=0 ∧
      adjoint (Atlas.Albert.map f.toRingHom p.val.rep)=0
    constructor
    · rw [trace_map,p.prop.1,map_zero]
    · rw [adjoint_map,p.prop.2]
      exact (coefficientSemilinear f).map_zero⟩

theorem fieldPointMap_inverse (f : F ≃+* K) (p : WhiteZeroPoints F) :
    fieldPointMap f.symm (fieldPointMap f p)=p := by
  apply Subtype.ext
  change Projectivization.map (coefficientSemilinear f.symm) (coefficientSemilinear_injective f.symm)
    (Projectivization.map (coefficientSemilinear f) (coefficientSemilinear_injective f) p.val)=p.val
  rw [←Projectivization.mk_rep p.val,Projectivization.map_mk,Projectivization.map_mk]
  change Projectivization.mk F
    (Atlas.Albert.map f.symm.toRingHom (Atlas.Albert.map f.toRingHom p.val.rep)) _ = _
  apply (Projectivization.mk_eq_mk_iff _ _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul] using (coefficient_inverse f p.val.rep).symm⟩

def fieldPointTransport (f : F ≃+* K) : WhiteZeroPoints F ≃ WhiteZeroPoints K where
  toFun := fieldPointMap f
  invFun := fieldPointMap f.symm
  left_inv := fieldPointMap_inverse f
  right_inv := fieldPointMap_inverse f.symm

theorem fieldPointTransport_equivariant (f : F ≃+* K) (g : Model F)
    (p : WhiteZeroPoints F) :
    fieldPointTransport f (g • p)=fieldTransport f g • fieldPointTransport f p := by
  apply Subtype.ext
  change Projectivization.map (coefficientSemilinear f) (coefficientSemilinear_injective f) (g.val • p.val)=
    (fieldTransport f g).val • Projectivization.map (coefficientSemilinear f) (coefficientSemilinear_injective f) p.val
  rw [←Projectivization.mk_rep p.val]
  simp only [Projectivization.smul_mk,Projectivization.map_mk,LinearEquiv.smul_def]
  change Projectivization.mk K (Atlas.Albert.map f.toRingHom (g.val p.val.rep)) _ =
    Projectivization.mk K ((fieldTransport f g).val (Atlas.Albert.map f.toRingHom p.val.rep)) _
  apply (Projectivization.mk_eq_mk_iff _ _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul] using fieldTransport_apply f g p.val.rep⟩

theorem coefficient_parabolicVector (f : F ≃+* K) :
    Atlas.Albert.map f.toRingHom (parabolicVector (F:=F))=parabolicVector (F:=K) := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [Atlas.Albert.map,parabolicVector]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Atlas.Albert.map,parabolicVector]

theorem fieldPointTransport_parabolicPoint (f : F ≃+* K) :
    fieldPointTransport f (parabolicPoint (F:=F))=parabolicPoint (F:=K) := by
  apply Subtype.ext
  change Projectivization.map (coefficientSemilinear f) (coefficientSemilinear_injective f)
    (Projectivization.mk F parabolicVector _)=Projectivization.mk K parabolicVector _
  rw [Projectivization.map_mk]
  change Projectivization.mk K (Atlas.Albert.map f.toRingHom parabolicVector) _=_
  apply (Projectivization.mk_eq_mk_iff _ _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul] using (coefficient_parabolicVector f).symm⟩

theorem fieldTransport_mem_parabolic_iff (f : F ≃+* K) (g : Model F) :
    fieldTransport f g∈parabolicPointStabilizer (F:=K) ↔
      g∈parabolicPointStabilizer (F:=F) := by
  change fieldTransport f g • parabolicPoint=parabolicPoint ↔
    g • parabolicPoint=parabolicPoint
  rw [←fieldPointTransport_parabolicPoint f,←fieldPointTransport_equivariant]
  exact (fieldPointTransport f).injective.eq_iff

/-- Field transport restricts to the actual marked-point stabilizers. -/
def fieldParabolicTransport (f : F ≃+* K) :
    parabolicPointStabilizer (F:=F) ≃* parabolicPointStabilizer (F:=K) where
  toFun g := ⟨fieldTransport f g.val,(fieldTransport_mem_parabolic_iff f g.val).mpr g.prop⟩
  invFun g := ⟨fieldTransport f.symm g.val,(fieldTransport_mem_parabolic_iff f.symm g.val).mpr g.prop⟩
  left_inv g := Subtype.ext (fieldEmbedding_inverse f g.val)
  right_inv g := Subtype.ext (fieldEmbedding_inverse f.symm g.val)
  map_mul' g h := Subtype.ext ((fieldTransport f).map_mul g.val h.val)

end Atlas.F4
