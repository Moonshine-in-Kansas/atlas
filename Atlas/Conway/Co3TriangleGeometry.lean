import Atlas.Conway.Co3TriangleStabilizer
import Atlas.Conway.Co3HeptadDot

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem leech_sub_norm (x y : leech) :
    integerDot (x-y).val (x-y).val = integerDot x.val x.val+integerDot y.val y.val-
      2*integerDot x.val y.val := by
  change (∑ i, (x.val i-y.val i)*(x.val i-y.val i)) = _
  simp only [integerDot,Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- Intrinsic oriented 2-3-4 triangles with fixed norm-six side. -/
def Co3Triangles (a : Omega) := {u : leech // integerDot u.val u.val = 32 ∧
  integerDot (normSixVector a-u).val (normSixVector a-u).val = 64}

theorem co3_triangle_iff (a : Omega) (u : leech) :
    (integerDot u.val u.val = 32 ∧ integerDot (normSixVector a-u).val (normSixVector a-u).val = 64) ↔
      integerDot u.val u.val = 32 ∧ integerDot (normSixVector a).val u.val = 8 := by
  rw [leech_sub_norm,normSixVector_norm]
  omega

instance co3Triangles_finite (a : Omega) : Finite (Co3Triangles a) := by
  let f : Co3Triangles a → LeechShell 4 := fun u => ⟨u.val,u.prop.1⟩
  exact Finite.of_injective f (fun _ _ h => Subtype.ext (congrArg (fun v : LeechShell 4 => v.val) h))

def co3BaseTriangle (a : Omega) : Co3Triangles a :=
  ⟨oddMinimumVector a 0,co3_base_triangle_norms a⟩

instance co3TrianglesAction (a : Omega) : MulAction (fullVectorStabilizer (normSixVector a)) (Co3Triangles a) where
  smul g u := ⟨g.val.val u.val,(g.val.prop _ _).trans u.prop.1,by
    have he : normSixVector a-g.val.val u.val = g.val.val (normSixVector a-u.val) := by
      rw [map_sub,show g.val.val (normSixVector a) = _ from g.prop]
    rw [he]; exact (g.val.prop _ _).trans u.prop.2⟩
  one_smul u := Subtype.ext rfl
  mul_smul g h u := Subtype.ext rfl

theorem co3_triangle_stabilizer_eq (a : Omega) :
    MulAction.stabilizer (fullVectorStabilizer (normSixVector a)) (co3BaseTriangle a) =
      Co3TriangleStabilizer a := by
  ext g
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

end Atlas.Conway
