import Atlas.LinearGroups.Unitary.Hermitian
import Atlas.FieldTheory.FiniteQuadraticCounts

/-! # The actual unitary determinant exact sequence

The determinant maps the retained full unitary matrix group onto the norm-one
units in positive dimension. Its kernel is the retained special unitary carrier.
No group order, generation or simplicity theorem enters this argument.
-/
noncomputable section
namespace Atlas.Unitary
open Matrix
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The usual matrix determinant, retaining its unit value. -/
def determinantUnits (hdeg : Module.finrank F K = 2) : U F K n hdeg →* Kˣ := by
  let := conjugationStarRing F K hdeg
  exact (Units.map Matrix.detMonoidHom).comp Unitary.toUnits

@[simp] theorem determinantUnits_val (hdeg : Module.finrank F K = 2)
    (g : U F K n hdeg) : (determinantUnits hdeg g : K) = g.val.det := rfl

theorem determinantUnits_normOne (hdeg : Module.finrank F K = 2)
    (g : U F K n hdeg) : determinantUnits hdeg g ∈ normOne F K := by
  rw [normOne_mem_iff hdeg, determinantUnits_val]
  let := conjugationStarRing F K hdeg
  exact (Matrix.det_of_mem_unitary g.prop).2

/-- The determinant with its exact norm-one codomain. -/
def determinant (hdeg : Module.finrank F K = 2) : U F K n hdeg →* normOne F K :=
  (determinantUnits hdeg).codRestrict _ (determinantUnits_normOne hdeg)

@[simp] theorem determinant_val (hdeg : Module.finrank F K = 2)
    (g : U F K n hdeg) : ((determinant hdeg g).val : K) = g.val.det := rfl

/-- An arbitrary diagonal of norm-one scalars is in the full unitary group. -/
def diagonalUnitary (hdeg : Module.finrank F K = 2) (d : Fin n → normOne F K) :
    U F K n hdeg :=
  ⟨Matrix.diagonal (fun i => ((d i).val : K)), by
    apply (mem_u_iff_preserves_hermitian hdeg _).mpr
    intro v w
    simp only [hermitian, Matrix.mulVec_diagonal, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hi := (normOne_mem_iff hdeg (d i).val).mp (d i).prop
    calc
      ((d i).val : K) * v i * (conjugation F K ((d i).val : K) * conjugation F K (w i)) =
          (((d i).val : K) * conjugation F K ((d i).val : K)) *
            (v i * conjugation F K (w i)) := by ring
      _ = v i * conjugation F K (w i) := by rw [hi, one_mul]⟩

/-- A diagonal matrix with just one prescribed determinant. -/
def diagonalAt (hdeg : Module.finrank F K = 2) (i : Fin n) (a : normOne F K) :
    U F K n hdeg := by
  classical
  exact diagonalUnitary hdeg (fun j => if j = i then a else 1)

@[simp] theorem determinant_diagonalAt (hdeg : Module.finrank F K = 2)
    (i : Fin n) (a : normOne F K) : determinant hdeg (diagonalAt hdeg i a) = a := by
  apply Subtype.ext
  apply Units.ext
  change (Matrix.diagonal (fun j : Fin n =>
    (((if j = i then a else 1) : normOne F K).val : K))).det = (a.val : K)
  classical
  simp only [Matrix.det_diagonal]
  simp_rw [apply_ite (fun x : normOne F K => (x.val : K)), show (((1 : normOne F K).val : K)) = 1 from rfl]
  simpa using Finset.prod_ite_eq' Finset.univ i (fun _ => (a.val : K))

theorem determinant_surjective (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Function.Surjective (determinant (n := n) hdeg) := by
  intro a
  exact ⟨diagonalAt hdeg ⟨0, hn⟩ a, determinant_diagonalAt hdeg _ a⟩

/-- Inclusion of the retained special carrier into the full unitary group. -/
def specialInclusion (hdeg : Module.finrank F K = 2) : SU F K n hdeg →* U F K n hdeg where
  toFun g := ⟨g.val, g.prop.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem specialInclusion_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (specialInclusion (n := n) hdeg) := by
  intro g h he
  apply Subtype.ext
  exact congrArg (fun x : U F K n hdeg => x.val) he

/-- Actual multiplicative equivalence onto the determinant kernel. -/
def specialEquivDetKernel (hdeg : Module.finrank F K = 2) :
    SU F K n hdeg ≃* (determinant (n := n) hdeg).ker where
  toFun g := ⟨specialInclusion hdeg g, by
    apply Subtype.ext
    apply Units.ext
    exact g.prop.2⟩
  invFun g := ⟨g.val.val, g.val.prop, by
    have he : determinant hdeg g.val = 1 := g.prop
    exact congrArg (fun a : normOne F K => (a.val : K)) he⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Division-free order relation, independent of the as-yet-unproved U order. -/
theorem card_su_mul_normOne (hdeg : Module.finrank F K = 2) (hn : 0 < n) :
    Nat.card (SU F K n hdeg) * (Nat.card F + 1) = Nat.card (U F K n hdeg) := by
  have he := Nat.card_congr (specialEquivDetKernel (n := n) hdeg).toEquiv
  have h := (determinant (n := n) hdeg).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (determinant_surjective hdeg hn),
    Subgroup.card_top, normOne_card hdeg, ← he] at h
  exact h
end Atlas.Unitary
