import Atlas.GroupTheory.Amalgam.UniversalCompletion
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! A terminal vertex recovers the group at that vertex; this is only a
regression theorem for universal completion, not a Curtis–Tits theorem. -/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Atlas.GroupTheory.Amalgam

variable {J : Type u} [Category.{v} J] (A : J ⥤ GrpCat.{u})
  {t : J} (ht : IsTerminal t)

/-- The terminal vertex supplies the canonical compatible family. -/
def terminalMaps : CompatibleMaps A (A.obj t) where
  map j := (A.map (ht.from j)).hom
  compatible f x := by
    change (A.map f ≫ A.map (ht.from _)) x = _
    rw [← A.map_comp, ht.comp_from]

/-- With a terminal object, the completion is the corresponding vertex group. -/
def terminalEquiv : Completion A ≃* A.obj t where
  toFun := lift (terminalMaps A ht)
  invFun := inclusion A t
  map_mul' := (lift (terminalMaps A ht)).map_mul
  left_inv := by
    intro x
    have h : (inclusion A t).comp (lift (terminalMaps A ht)) =
        MonoidHom.id (Completion A) := by
      apply hom_ext
      intro j y
      simp only [MonoidHom.comp_apply, lift_inclusion, MonoidHom.id_apply]
      exact inclusion_compatible A (ht.from j) y
    exact DFunLike.congr_fun h x
  right_inv x := by
    rw [lift_inclusion]
    change A.map (ht.from t) x = x
    rw [ht.from_self, A.map_id]
    rfl

end Atlas.GroupTheory.Amalgam
