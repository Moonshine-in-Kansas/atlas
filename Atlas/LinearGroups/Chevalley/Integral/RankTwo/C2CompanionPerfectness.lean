import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2CompanionRootRelations
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2LoweringConjugation
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectness
import Atlas.LinearGroups.Chevalley.WeightCompanionCrossTorus

/-! Perfectness of the actual selected C2 companion.
This uses its actual simultaneous representation, not an assumed simply connected group
or a lift along an injective adjoint projection. The only missing same-root
Weyl identity required here is checked on both actual blocks. No old Sp4 result,
full projection-kernel theorem, group-order statement or simplicity is assumed.
-/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open Group ClassicalData
local instance c2CompanionPerfectRootDecidableEq : DecidableEq (BRoot 2) :=
  Classical.decEq _
local instance c2CompanionPerfectBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
open scoped commutatorElement
local instance c2CompanionPerfectRankNeZero : NeZero C2.rank := ⟨by decide⟩
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The long-root lowering bridge is an integral four-coordinate identity. -/
theorem nb_eb_nbInv_lowering : nb * eb * nbInv = -fb := by decide

variable {R : Type*} [CommRing R]

theorem matrix_long_conjugate_X (t : R) :
    (Int.castRingHom R).mapMatrix nb * XB t *
      (Int.castRingHom R).mapMatrix nbInv = YB (-t) := by
  let c := (Int.castRingHom R).mapMatrix (m := Fin 4)
  have h0 : c nb * c nbInv = 1 := by rw [← map_mul, nb_inverse, map_one]
  have h1 : c nb * c eb * c nbInv = -c fb := by
    rw [← map_mul, ← map_mul, nb_eb_nbInv_lowering, map_neg]
  change c nb * (1 + t • c eb) * c nbInv = 1 + (-t) • c fb
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
  rw [h0, h1]
  simp only [smul_neg, neg_smul]

/-- This is equality in the actual simultaneous adjoint/weight subgroup. -/
theorem companion_weyl_long_conjugate_X (t : R) :
    weyl 1 * selectedWeightCompanionX C2 R 1 t * (weyl 1)⁻¹ =
      selectedWeightCompanionY C2 R 1 (-t) := by
  apply ext R
  · simp only [map_mul, map_inv, rho_weyl, rho_X, rho_Y]
    exact c2_weyl_long_conjugate_X t
  · rw [map_mul, map_mul, matrix_weyl_long, matrix_xlong,
      matrix_weyl_long_inv, matrix_ylong]
    exact matrix_long_conjugate_X t

private theorem short_cartan_odd :
    Odd ((rootDatum C2).base.cartanMatrix ((rootDatum C2).indexEquiv 0)
      ((rootDatum C2).indexEquiv 1)) := by
  change Odd ((baseC 1).cartanMatrix (baseCIndexEquiv 1 0) (baseCIndexEquiv 1 1))
  rw [baseC_cartan]
  decide

variable (K : Type*) [Field K]

theorem companion_Xshort_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionX C2 K 0 t ∈ commutator (Companion K) :=
  weightCompanionX_mem_commutator_of_odd_cartan (rootDatum C2).pairing
    (rootDatum C2).base (selectedWeightOrbits C2) (selectedWeightOrbits_closed C2)
    (selectedWeightOrbits_minuscule C2) K hchar
    ((rootDatum C2).indexEquiv 0) ((rootDatum C2).indexEquiv 1) short_cartan_odd t

theorem companion_Yshort_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionY C2 K 0 t ∈ commutator (Companion K) :=
  weightCompanionY_mem_commutator_of_odd_cartan (rootDatum C2).pairing
    (rootDatum C2).base (selectedWeightOrbits C2) (selectedWeightOrbits_closed C2)
    (selectedWeightOrbits_minuscule C2) K hchar
    ((rootDatum C2).indexEquiv 0) ((rootDatum C2).indexEquiv 1) short_cartan_odd t

/-- Division by two occurs only in this odd-characteristic group argument. -/
theorem companion_W_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    rootW t ∈ commutator (Companion K) := by
  have htwo : (2 : K) ≠ 0 := by
    intro h
    apply hchar
    linear_combination -h
  have hp : (-2 : K) * 1 * (-t / 2) = t := by
    field_simp [htwo] <;> ring
  rw [← hp, ← companion_short_short_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem unconjugate_mem_normal {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal] (n x : G) (h : n * x * n⁻¹ ∈ H) : x ∈ H := by
  have hc := (inferInstance : H.Normal).conj_mem' _ h n
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc

theorem companion_Xlong_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionX C2 K 1 t ∈ commutator (Companion K) :=
  unconjugate_mem_normal (commutator (Companion K)) (weyl 0)
    (selectedWeightCompanionX C2 K 1 t) (companion_W_mem_commutator K hchar t)

theorem companion_Ylong_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionY C2 K 1 t ∈ commutator (Companion K) := by
  let H := commutator (Companion K)
  have h := (inferInstance : H.Normal).conj_mem _
    (companion_Xlong_mem_commutator K hchar (-t)) (weyl 1)
  simpa only [companion_weyl_long_conjugate_X, neg_neg] using h

/-- Perfectness before any assertion identifying the full central kernel. -/
theorem companion_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (Companion K) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply weightCompanion_induction (rootDatum C2).pairing (rootDatum C2).base
    (selectedWeightOrbits C2) (selectedWeightOrbits_closed C2)
    (selectedWeightOrbits_minuscule C2) K ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨k,rfl⟩ := (rootDatum C2).indexEquiv.surjective i
    fin_cases k
    · exact companion_Xshort_mem_commutator K hchar t
    · exact companion_Xlong_mem_commutator K hchar t
  · intro i t
    obtain ⟨k,rfl⟩ := (rootDatum C2).indexEquiv.surjective i
    fin_cases k
    · exact companion_Yshort_mem_commutator K hchar t
    · exact companion_Ylong_mem_commutator K hchar t

theorem companion_isPerfect_of_card_three [Fintype K] (hq : Fintype.card K = 3) :
    IsPerfect (Companion K) :=
  companion_isPerfect_of_neg_one_ne_one K (neg_one_ne_one_of_card_three K hq)

/-- The already proved torus argument covers q>3, including characteristic two.
Only the ternary field needs the additional rank-two commutator argument. -/
theorem companion_isPerfect_of_card_gt_two [Fintype K] (hq : 2 < Fintype.card K) :
    IsPerfect (Companion K) := by
  by_cases hlarge : 3 < Fintype.card K
  · exact selectedWeightCompanion_isPerfect_of_card_gt_three C2 K hlarge
  · exact companion_isPerfect_of_card_three K (by omega)

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule

namespace Atlas.Chevalley
open Group
variable (K : Type*) [Field K]

theorem selectedWeightCompanion_C2_isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion (.C 2 (by decide)) K) :=
  Integral.RankTwo.C2Minuscule.companion_isPerfect_of_neg_one_ne_one K hchar

theorem selectedWeightCompanion_C2_isPerfect_of_card_gt_two [Fintype K]
    (hq : 2 < Fintype.card K) : IsPerfect (SelectedWeightCompanion (.C 2 (by decide)) K) :=
  Integral.RankTwo.C2Minuscule.companion_isPerfect_of_card_gt_two K hq

end Atlas.Chevalley
