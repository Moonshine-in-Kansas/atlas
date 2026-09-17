import Atlas.LinearGroups.ReeG2.CrossProductGroup
import Atlas.LinearGroups.G2.Basic

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The preserved symmetric pairing in the actual matrix basis. -/
def bilinear (v w : Vector F) : F := dotProduct v (formMatrix *ᵥ w)

theorem generated_preserves_bilinear (m : ℕ) (g : Ambient F)
    (hg : g ∈ generated F m) (v w : Vector F) :
    bilinear (rowEquiv g v) (rowEquiv g w) = bilinear v w := by
  have he := generated_le_formStabilizer m hg
  change g.val * formMatrix * g.val.transpose = formMatrix at he
  unfold bilinear
  rw [rowEquiv_apply,rowEquiv_apply,Matrix.mulVec_vecMul,
    ← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,← Matrix.mul_assoc,he]

/-- Scalar plus imaginary coordinates in the existing Wilson split-octonion algebra. -/
def octonionCoordinates : (F × Vector F) ≃ₗ[F] Atlas.SplitOctonion.Carrier F where
  toFun p := ![p.2 0,p.2 1,p.2 2,p.1-p.2 3,p.1+p.2 3,-p.2 4,-p.2 5,-p.2 6]
  invFun x := (-(x 3+x 4), ![x 0,x 1,x 2,x 3-x 4,-x 5,-x 6,-x 7])
  left_inv p := by
    apply Prod.ext
    · dsimp
      apply sub_eq_zero.mp
      ring_nf
      reduce_mod_char!
    · ext i
      fin_cases i <;> simp <;> apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!
  right_inv x := by
    ext i
    fin_cases i <;> simp <;> apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r p := by
    ext i
    fin_cases i <;> simp <;> ring

set_option maxHeartbeats 1600000 in
-- Direct verification of the eight multiplication coordinates in characteristic three.
theorem octonionCoordinates_mul (s t : F) (v w : Vector F) :
    octonionCoordinates (s*t-bilinear v w, s • w + t • v + crossProduct v w) =
      Atlas.SplitOctonion.mul (octonionCoordinates (s,v)) (octonionCoordinates (t,w)) := by
  ext i
  fin_cases i <;>
    simp [octonionCoordinates,Atlas.SplitOctonion.mul,bilinear,formMatrix,Matrix.vecHead,Matrix.vecTail,
      crossProduct,wedgeCoordinate,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

end Atlas.ReeG2
