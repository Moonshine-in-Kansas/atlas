import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralOperatorData
import Atlas.LinearGroups.G2.WeylMaps
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Group.Units.Hom

/-! The four literal old octonion root matrices, over every
field. The integral tables are data; their identification below is a separate
coordinate proof. No finite-field, order, center or simplicity result is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.G2
open scoped Matrix
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

variable (K : Type*) [Field K]

/-- The faithful matrix representation in the existing eight octonion coordinates. -/
def faithfulMatrixHom8 : Atlas.G2.Model K →* Matrix (Fin 8) (Fin 8) K :=
  (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin 8)).toMonoidHom.comp
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := K) (M := Atlas.SplitOctonion.Carrier K)).comp (Atlas.G2.representation K))

theorem faithfulMatrixHom8_apply (g : Atlas.G2.Model K) (r c : Fin 8) :
    faithfulMatrixHom8 K g r c = g.val (Pi.single c 1) r := by
  change LinearMap.toMatrixAlgEquiv' g.val.toLinearMap r c = _
  exact LinearMap.toMatrixAlgEquiv'_apply _ r c

theorem faithfulMatrixHom8_injective : Function.Injective (faithfulMatrixHom8 K) := by
  intro g h he
  apply Atlas.G2.representation_injective K
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin 8)).injective
  exact he

/-- The same literal representation with its canonical matrix-unit codomain. -/
def faithfulMatrixUnitsHom8 : Atlas.G2.Model K →* (Matrix (Fin 8) (Fin 8) K)ˣ :=
  (faithfulMatrixHom8 K).toHomUnits

@[simp] theorem faithfulMatrixUnitsHom8_val (g : Atlas.G2.Model K) :
    (faithfulMatrixUnitsHom8 K g : Matrix (Fin 8) (Fin 8) K) =
      faithfulMatrixHom8 K g := rfl

theorem faithfulMatrixUnitsHom8_injective :
    Function.Injective (faithfulMatrixUnitsHom8 K) := by
  intro g h he
  apply faithfulMatrixHom8_injective K
  exact congrArg (fun u : (Matrix (Fin 8) (Fin 8) K)ˣ => u.val) he

/-- Ordered E0,E1,F0,F1. Both negative-root parameters have positive sign. -/
def octonionSimpleRoot (i : Fin 4) (t : K) : Atlas.G2.Model K :=
  ![Atlas.G2.rootE t, Atlas.G2.rootF t,
    Atlas.G2.weylR * Atlas.G2.rootE t * Atlas.G2.weylR,
    Atlas.G2.weylS * Atlas.G2.rootF t * Atlas.G2.weylS] i

/-- Literal integral quadratic polynomial, without division by two or three. -/
def quadraticSimpleMatrix8 (i : Fin 4) (t : K) : Matrix (Fin 8) (Fin 8) K :=
  1 + t • (simpleMatrix i).map (Int.castRingHom K) +
    t ^ 2 • (simpleSecondMatrix i).map (Int.castRingHom K)

private theorem rootE_row_0 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 0 =
      quadraticSimpleMatrix8 K 0 t 0 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_1 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 1 =
      quadraticSimpleMatrix8 K 0 t 1 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_2 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 2 =
      quadraticSimpleMatrix8 K 0 t 2 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_3 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 3 =
      quadraticSimpleMatrix8 K 0 t 3 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_4 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 4 =
      quadraticSimpleMatrix8 K 0 t 4 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_5 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 5 =
      quadraticSimpleMatrix8 K 0 t 5 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_6 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 6 =
      quadraticSimpleMatrix8 K 0 t 6 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootE_row_7 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) 7 =
      quadraticSimpleMatrix8 K 0 t 7 c := by
  dsimp only [Atlas.G2.Explicit.rootEApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

theorem faithfulMatrixHom8_rootE (t : K) :
    faithfulMatrixHom8 K (Atlas.G2.rootE t) = quadraticSimpleMatrix8 K 0 t := by
  ext r c
  rw [faithfulMatrixHom8_apply]
  change (Atlas.G2.Explicit.rootEApply t (Pi.single c 1)) r = _
  fin_cases r
  · exact rootE_row_0 K t c
  · exact rootE_row_1 K t c
  · exact rootE_row_2 K t c
  · exact rootE_row_3 K t c
  · exact rootE_row_4 K t c
  · exact rootE_row_5 K t c
  · exact rootE_row_6 K t c
  · exact rootE_row_7 K t c

private theorem rootF_row_0 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 0 =
      quadraticSimpleMatrix8 K 1 t 0 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_1 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 1 =
      quadraticSimpleMatrix8 K 1 t 1 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_2 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 2 =
      quadraticSimpleMatrix8 K 1 t 2 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_3 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 3 =
      quadraticSimpleMatrix8 K 1 t 3 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_4 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 4 =
      quadraticSimpleMatrix8 K 1 t 4 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_5 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 5 =
      quadraticSimpleMatrix8 K 1 t 5 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_6 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 6 =
      quadraticSimpleMatrix8 K 1 t 6 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem rootF_row_7 (t : K) (c : Fin 8) :
    (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) 7 =
      quadraticSimpleMatrix8 K 1 t 7 c := by
  dsimp only [Atlas.G2.Explicit.rootFApply]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

theorem faithfulMatrixHom8_rootF (t : K) :
    faithfulMatrixHom8 K (Atlas.G2.rootF t) = quadraticSimpleMatrix8 K 1 t := by
  ext r c
  rw [faithfulMatrixHom8_apply]
  change (Atlas.G2.Explicit.rootFApply t (Pi.single c 1)) r = _
  fin_cases r
  · exact rootF_row_0 K t c
  · exact rootF_row_1 K t c
  · exact rootF_row_2 K t c
  · exact rootF_row_3 K t c
  · exact rootF_row_4 K t c
  · exact rootF_row_5 K t c
  · exact rootF_row_6 K t c
  · exact rootF_row_7 K t c

private theorem negativeE_row_0 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 0 =
      quadraticSimpleMatrix8 K 2 t 0 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_1 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 1 =
      quadraticSimpleMatrix8 K 2 t 1 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_2 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 2 =
      quadraticSimpleMatrix8 K 2 t 2 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_3 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 3 =
      quadraticSimpleMatrix8 K 2 t 3 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_4 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 4 =
      quadraticSimpleMatrix8 K 2 t 4 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_5 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 5 =
      quadraticSimpleMatrix8 K 2 t 5 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_6 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 6 =
      quadraticSimpleMatrix8 K 2 t 6 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeE_row_7 (t : K) (c : Fin 8) :
    (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) 7 =
      quadraticSimpleMatrix8 K 2 t 7 c := by
  dsimp only [Atlas.G2.weylRApply, Atlas.G2.Explicit.rootEApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

theorem faithfulMatrixHom8_negativeE (t : K) :
    faithfulMatrixHom8 K (Atlas.G2.weylR * Atlas.G2.rootE t * Atlas.G2.weylR) =
      quadraticSimpleMatrix8 K 2 t := by
  ext r c
  rw [faithfulMatrixHom8_apply]
  change (Atlas.G2.weylRApply (Atlas.G2.Explicit.rootEApply t (Atlas.G2.weylRApply (Pi.single c 1)))) r = _
  fin_cases r
  · exact negativeE_row_0 K t c
  · exact negativeE_row_1 K t c
  · exact negativeE_row_2 K t c
  · exact negativeE_row_3 K t c
  · exact negativeE_row_4 K t c
  · exact negativeE_row_5 K t c
  · exact negativeE_row_6 K t c
  · exact negativeE_row_7 K t c

private theorem negativeF_row_0 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 0 =
      quadraticSimpleMatrix8 K 3 t 0 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_1 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 1 =
      quadraticSimpleMatrix8 K 3 t 1 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_2 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 2 =
      quadraticSimpleMatrix8 K 3 t 2 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_3 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 3 =
      quadraticSimpleMatrix8 K 3 t 3 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_4 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 4 =
      quadraticSimpleMatrix8 K 3 t 4 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_5 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 5 =
      quadraticSimpleMatrix8 K 3 t 5 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_6 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 6 =
      quadraticSimpleMatrix8 K 3 t 6 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

private theorem negativeF_row_7 (t : K) (c : Fin 8) :
    (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) 7 =
      quadraticSimpleMatrix8 K 3 t 7 c := by
  dsimp only [Atlas.G2.weylSApply, Atlas.G2.Explicit.rootFApply, Matrix.cons_val]
  fin_cases c <;>
    norm_num [quadraticSimpleMatrix8, simpleMatrix, simpleSecondMatrix,
      simpleTable, simpleSecondTable, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, Pi.single_apply, Fin.ext_iff] <;>
    first | rfl | ring

theorem faithfulMatrixHom8_negativeF (t : K) :
    faithfulMatrixHom8 K (Atlas.G2.weylS * Atlas.G2.rootF t * Atlas.G2.weylS) =
      quadraticSimpleMatrix8 K 3 t := by
  ext r c
  rw [faithfulMatrixHom8_apply]
  change (Atlas.G2.weylSApply (Atlas.G2.Explicit.rootFApply t (Atlas.G2.weylSApply (Pi.single c 1)))) r = _
  fin_cases r
  · exact negativeF_row_0 K t c
  · exact negativeF_row_1 K t c
  · exact negativeF_row_2 K t c
  · exact negativeF_row_3 K t c
  · exact negativeF_row_4 K t c
  · exact negativeF_row_5 K t c
  · exact negativeF_row_6 K t c
  · exact negativeF_row_7 K t c

theorem faithfulMatrixHom8_simpleRoot (i : Fin 4) (t : K) :
    faithfulMatrixHom8 K (octonionSimpleRoot K i t) =
      quadraticSimpleMatrix8 K i t := by
  fin_cases i
  · exact faithfulMatrixHom8_rootE K t
  · exact faithfulMatrixHom8_rootF K t
  · exact faithfulMatrixHom8_negativeE K t
  · exact faithfulMatrixHom8_negativeF K t

private theorem conjugated_add {G : Type*} [Group G] (w : G) (hw : w * w = 1)
    (f : K → G) (hf : ∀ s t, f s * f t = f (s + t)) (s t : K) :
    (w * f s * w) * (w * f t * w) = w * f (s + t) * w := by
  calc
    _ = w * (f s * (w * w) * f t) * w := by simp only [mul_assoc]
    _ = w * (f s * f t) * w := by rw [hw]; simp only [mul_one]
    _ = _ := by rw [hf]

theorem octonionSimpleRoot_add (i : Fin 4) (s t : K) :
    octonionSimpleRoot K i s * octonionSimpleRoot K i t =
      octonionSimpleRoot K i (s + t) := by
  fin_cases i
  · exact Atlas.G2.rootE_add s t
  · exact Atlas.G2.rootF_add s t
  · exact conjugated_add K Atlas.G2.weylR
      (by simpa only [pow_two] using Atlas.G2.weylR_sq (K := K))
      Atlas.G2.rootE Atlas.G2.rootE_add s t
  · exact conjugated_add K Atlas.G2.weylS
      (by simpa only [pow_two] using Atlas.G2.weylS_sq (K := K))
      Atlas.G2.rootF Atlas.G2.rootF_add s t

@[simp] theorem octonionSimpleRoot_zero (i : Fin 4) :
    octonionSimpleRoot K i 0 = 1 := by
  apply mul_left_cancel (a := octonionSimpleRoot K i 0)
  simpa only [zero_add, mul_one] using octonionSimpleRoot_add K i 0 0

theorem octonionSimpleRoot_neg (i : Fin 4) (t : K) :
    octonionSimpleRoot K i (-t) = (octonionSimpleRoot K i t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [octonionSimpleRoot_add, neg_add_cancel, octonionSimpleRoot_zero]

theorem faithfulMatrixHom8_simpleRoot_inverse (i : Fin 4) (t : K) :
    faithfulMatrixHom8 K ((octonionSimpleRoot K i t)⁻¹) =
      quadraticSimpleMatrix8 K i (-t) := by
  rw [← octonionSimpleRoot_neg, faithfulMatrixHom8_simpleRoot]

theorem quadraticSimpleMatrix8_add (i : Fin 4) (s t : K) :
    quadraticSimpleMatrix8 K i s * quadraticSimpleMatrix8 K i t =
      quadraticSimpleMatrix8 K i (s + t) := by
  simpa only [map_mul, faithfulMatrixHom8_simpleRoot] using
    congrArg (faithfulMatrixHom8 K) (octonionSimpleRoot_add K i s t)

theorem quadraticSimpleMatrix8_zero (i : Fin 4) :
    quadraticSimpleMatrix8 K i 0 = 1 := by
  rw [← faithfulMatrixHom8_simpleRoot, octonionSimpleRoot_zero, map_one]

theorem quadraticSimpleMatrix8_mul_neg (i : Fin 4) (t : K) :
    quadraticSimpleMatrix8 K i t * quadraticSimpleMatrix8 K i (-t) = 1 := by
  rw [quadraticSimpleMatrix8_add, add_neg_cancel, quadraticSimpleMatrix8_zero]

theorem quadraticSimpleMatrix8_neg_mul (i : Fin 4) (t : K) :
    quadraticSimpleMatrix8 K i (-t) * quadraticSimpleMatrix8 K i t = 1 := by
  rw [quadraticSimpleMatrix8_add, neg_add_cancel, quadraticSimpleMatrix8_zero]

end Atlas.Chevalley.Comparison.G2
