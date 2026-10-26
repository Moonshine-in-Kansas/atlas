import Atlas.LinearGroups.ReeF4.SpecialVectors
import Atlas.LinearAlgebra.ProjectiveConeCount
import Mathlib.LinearAlgebra.Projectivization.Action

/-! Actual projective special points and their intrinsic Ree action. The special
condition is imposed on projective representatives using the proved scalar
invariance, rather than identifying these with all Albert rank-one points.
No transitivity, faithfulness, incidence or cardinality is asserted here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The projective lines represented by intrinsic special vectors. -/
abbrev SpecialPoints (m : ℕ) :=
  Atlas.LinearAlgebra.ConePoints (F := F) (IsSpecialVector (F := F) m)

/-- A special vector determines its actual projective point. -/
def specialPointMk (m : ℕ) (u : TraceZero F) (hu : IsSpecialVector m u) :
    SpecialPoints (F := F) m :=
  Atlas.LinearAlgebra.conePointMk (IsSpecialVector m)
    (isSpecialVector_units_smul_iff m) ⟨u,hu.ne_zero,hu⟩

theorem specialPointMk_rep (m : ℕ) (p : SpecialPoints (F := F) m) :
    specialPointMk m p.val.rep p.property = p :=
  Subtype.ext (Projectivization.mk_rep p.val)

theorem specialPointMk_eq_iff (m : ℕ) (u v : TraceZero F)
    (hu : IsSpecialVector m u) (hv : IsSpecialVector m v) :
    specialPointMk m u hu = specialPointMk m v hv ↔ ∃ a : Fˣ, a • v = u := by
  constructor
  · intro h
    exact (Projectivization.mk_eq_mk_iff F u v hu.ne_zero hv.ne_zero).mp
      (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (Projectivization.mk_eq_mk_iff F u v hu.ne_zero hv.ne_zero).mpr h

theorem specialPointMk_units_smul (m : ℕ) (u : TraceZero F)
    (hu : IsSpecialVector m u) (a : Fˣ) :
    specialPointMk m (a • u) ((isSpecialVector_units_smul_iff m a u).mpr hu) =
      specialPointMk m u hu :=
  (specialPointMk_eq_iff m _ _ _ _).mpr ⟨a,rfl⟩

/-- The full intrinsic stabilizer acts on the actual special projective points. -/
instance specialPointsAction (m : ℕ) : MulAction (Model F m) (SpecialPoints (F := F) m) where
  smul g p := ⟨g.val • p.val, by
    rw [← Projectivization.mk_rep p.val,Projectivization.smul_mk]
    apply (Atlas.LinearAlgebra.cone_mk_iff (IsSpecialVector m)
      (isSpecialVector_units_smul_iff m) _ _).mpr
    simpa only [LinearEquiv.smul_def] using p.property.map_model g⟩
  one_smul p := Subtype.ext (one_smul _ _)
  mul_smul g h p := Subtype.ext (mul_smul g.val h.val p.val)

theorem specialPointMk_smul (m : ℕ) (g : Model F m) (u : TraceZero F)
    (hu : IsSpecialVector m u) :
    g • specialPointMk m u hu = specialPointMk m (g.val u) (hu.map_model g) := rfl

/-- A structural representative decomposition, independent of any point count. -/
def specialVectorEquivPointsUnits (m : ℕ) :
    {u : TraceZero F // IsSpecialVector m u} ≃ SpecialPoints (F := F) m × Fˣ :=
  (show {u : TraceZero F // IsSpecialVector m u} ≃
      Atlas.LinearAlgebra.NonzeroCone (IsSpecialVector (F := F) m) from
    { toFun := fun u => ⟨u.val,u.property.ne_zero,u.property⟩
      invFun := fun u => ⟨u.val,u.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (Atlas.LinearAlgebra.nonzeroConeEquivPointsUnits (IsSpecialVector m)
      (isSpecialVector_units_smul_iff m))

end Atlas.ReeF4
