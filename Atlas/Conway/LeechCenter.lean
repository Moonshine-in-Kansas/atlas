import Atlas.Conway.GolayCoordinateSeparation
import Atlas.Lattices.LeechVisibleSymmetries
import Atlas.Mathieu.SextetTransitivity
import Mathlib.GroupTheory.Subgroup.Center

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators

theorem sign_coordinateEight (c : golay) (a : Omega) :
    (signIsometry c).val (coordinateEight a) =
      if c.val a = 0 then coordinateEight a else -coordinateEight a := by
  apply Subtype.ext
  ext i
  by_cases hi : i = a
  · subst i
    split_ifs <;> simp_all [signIsometry,signChange,coordinateEight,coordinateVector]
  · split_ifs <;> simp_all [signIsometry,signChange,coordinateEight,coordinateVector,Pi.single_apply]

theorem central_axis_offDiagonal (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) (a i : Omega) (hi : i ≠ a) :
    (g.val (coordinateEight a)).val i = 0 := by
  obtain ⟨c,hc⟩ := golay_coordinate_separates i a hi
  have he := congrArg (fun z : LeechIsometryGroup => (z.val (coordinateEight a)).val)
    ((Subgroup.mem_center_iff.mp hg) (signIsometry c))
  change signChange c.val (g.val (coordinateEight a)).val =
    (g.val ((signIsometry c).val (coordinateEight a))).val at he
  rw [sign_coordinateEight] at he
  have hh := congrFun he i
  rcases bit_cases (c.val i) with hci | hci <;>
    rcases bit_cases (c.val a) with hca | hca
  all_goals simp [hci,hca] at hc
  all_goals simp [signChange,hci,hca,map_neg] at hh
  all_goals omega

def centralAxisValue (g : LeechIsometryGroup) (a : Omega) : ℤ :=
  (g.val (coordinateEight a)).val a

theorem central_axis_shape (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) (a : Omega) :
    (g.val (coordinateEight a)).val = coordinateVector a (centralAxisValue g a) := by
  ext i
  by_cases hi : i = a
  · subst i; simp [coordinateVector,centralAxisValue]
  · rw [central_axis_offDiagonal g hg a i hi]
    simp [coordinateVector,Pi.single_apply,hi]

theorem central_axis_value (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) (a : Omega) :
    centralAxisValue g a = 8 ∨ centralAxisValue g a = -8 := by
  have hh := g.prop (coordinateEight a) (coordinateEight a)
  rw [central_axis_shape g hg a] at hh
  change integerDot (coordinateVector a _) (coordinateVector a _) =
    integerDot (coordinateVector a 8) (coordinateVector a 8) at hh
  rw [integerDot_coordinateVector,integerDot_coordinateVector] at hh
  simp only [coordinateVector,Pi.single_eq_same] at hh
  rcases le_total 0 (centralAxisValue g a) with hp | hp
  · left; nlinarith
  · right; nlinarith

theorem central_coordinate (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) (x : leech) (a : Omega) :
    (g.val x).val a * centralAxisValue g a = x.val a * 8 := by
  have hh := g.prop x (coordinateEight a)
  rw [central_axis_shape g hg a] at hh
  change integerDot _ (coordinateVector a _) = integerDot _ (coordinateVector a 8) at hh
  rwa [integerDot_coordinateVector,integerDot_coordinateVector] at hh

theorem permutation_coordinateEight (σ : Mathieu24CodeModel) (a : Omega) :
    (permutationIsometry σ).val (coordinateEight a) = coordinateEight (σ.val a) := by
  apply Subtype.ext
  ext i
  change coordinateVector a 8 (σ.val.symm i) = coordinateVector (σ.val a) 8 i
  simp only [coordinateVector,Pi.single_apply,Equiv.symm_apply_eq]

theorem central_axis_constant (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) (a b : Omega) :
    centralAxisValue g a = centralAxisValue g b := by
  obtain ⟨σ,hσ⟩ := golay_coordinate_transitive a b
  have he := congrArg (fun z : LeechIsometryGroup => (z.val (coordinateEight a)).val b)
    ((Subgroup.mem_center_iff.mp hg) (permutationIsometry σ))
  change (g.val (coordinateEight a)).val (σ.val.symm b) =
    (g.val ((permutationIsometry σ).val (coordinateEight a))).val b at he
  rw [permutation_coordinateEight,hσ] at he
  have ha : σ.val.symm b = a := by rw [← hσ,Equiv.symm_apply_apply]
  rwa [ha] at he

theorem central_eq_one_or_negation (g : LeechIsometryGroup)
    (hg : g ∈ Subgroup.center LeechIsometryGroup) : g = 1 ∨ g = negationIsometry := by
  let a : Omega := ((0,0),0)
  rcases central_axis_value g hg a with hp | hn
  · left
    apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext; ext i
    have hi := central_coordinate g hg x i
    rw [central_axis_constant g hg i a,hp] at hi
    change (g.val x).val i = x.val i
    omega
  · right
    apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext; ext i
    have hi := central_coordinate g hg x i
    rw [central_axis_constant g hg i a,hn] at hi
    rw [negationIsometry_apply]
    change (g.val x).val i = -x.val i
    omega

theorem negation_mem_center : negationIsometry ∈ Subgroup.center LeechIsometryGroup := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  change g.val (negationIsometry.val x) = negationIsometry.val (g.val x)
  rw [negationIsometry_apply,negationIsometry_apply,map_neg]

theorem leech_center_iff (g : LeechIsometryGroup) :
    g ∈ Subgroup.center LeechIsometryGroup ↔ g = 1 ∨ g = negationIsometry := by
  constructor
  · exact central_eq_one_or_negation g
  · rintro (rfl | rfl)
    · exact (Subgroup.center LeechIsometryGroup).one_mem
    · exact negation_mem_center

end Atlas.Conway
