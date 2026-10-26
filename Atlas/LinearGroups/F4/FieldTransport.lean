import Atlas.LinearGroups.F4.Basic
import Atlas.Algebra.Albert.ScalarExtensionEquiv

/-! Field transport of the actual full Albert polynomial stabilizer. -/
noncomputable section
namespace Atlas.F4
variable {F K : Type*} [Field F] [Field K]

def fieldEmbedding (f : F →+* K) : Model F →* Model K :=
  Atlas.Albert.extendStabilizer f

theorem fieldEmbedding_apply (f : F →+* K) (g : Model F) (x : Atlas.Albert.Carrier F) :
    (fieldEmbedding f g).val (Atlas.Albert.map f x) = Atlas.Albert.map f (g.val x) :=
  Atlas.Albert.extendStabilizer_map f g x

theorem fieldEmbedding_injective (f : F →+* K) : Function.Injective (fieldEmbedding f) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun k : Model K => k.val (Atlas.Albert.map f x)) he
  rw [fieldEmbedding_apply,fieldEmbedding_apply] at hx
  apply Prod.ext
  · funext i
    apply f.injective
    exact congrArg (fun z : Atlas.Albert.Carrier K => z.1 i) hx
  · funext i j
    apply f.injective
    exact congrArg (fun z : Atlas.Albert.Carrier K => z.2 i j) hx

theorem coefficient_inverse (f : F ≃+* K) (x : Atlas.Albert.Carrier F) :
    Atlas.Albert.map f.symm.toRingHom (Atlas.Albert.map f.toRingHom x) = x := by
  apply Prod.ext
  · funext i; exact f.symm_apply_apply _
  · funext i j; exact f.symm_apply_apply _

theorem fieldEmbedding_inverse (f : F ≃+* K) (g : Model F) :
    fieldEmbedding f.symm.toRingHom (fieldEmbedding f.toRingHom g) = g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h := fieldEmbedding_apply f.symm.toRingHom (fieldEmbedding f.toRingHom g)
    (Atlas.Albert.map f.toRingHom x)
  rw [fieldEmbedding_apply f.toRingHom g x,coefficient_inverse,coefficient_inverse] at h
  exact h

def fieldTransport (f : F ≃+* K) : Model F ≃* Model K where
  toFun := fieldEmbedding f.toRingHom
  invFun := fieldEmbedding f.symm.toRingHom
  left_inv := fieldEmbedding_inverse f
  right_inv := fieldEmbedding_inverse f.symm
  map_mul' := (fieldEmbedding f.toRingHom).map_mul

theorem fieldTransport_apply (f : F ≃+* K) (g : Model F) (x : Atlas.Albert.Carrier F) :
    (fieldTransport f g).val (Atlas.Albert.map f.toRingHom x) =
      Atlas.Albert.map f.toRingHom (g.val x) := fieldEmbedding_apply f.toRingHom g x

end Atlas.F4
