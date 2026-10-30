import Atlas.Comparisons.Exceptional.G2Binary.UnitaryMarking
import Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity
import Atlas.LinearGroups.Unitary.IsotropicCount
import Atlas.LinearGroups.Unitary.PointNormalClosure
import Atlas.LinearGroups.Unitary.GenerationThreeComplete
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
Source-only continuation for ISO-6048, 27 October 2026. NOT BUILT OR AUDITED.

The new mathematical checkpoint is generation of the actual SU3(F9/F3), and
then its actual full-center quotient, by the 28 marked line transvections.
The saved coordinate table is connected to the faithful quotient action.
The original long-root normal closure is also represented faithfully on Fin 28.

No equality or conjugacy of the two permutation images is asserted. In
particular, numbering both point sets does not prove equivariance. The binary
full-group extension and the unitary field involution remain separate targets.

This file deliberately does not import or modify the preserved
UnitaryLinesDraft.lean; the overlapping setup below has a separate namespace.
No new group enumeration or permutation certificate is introduced.
-/

noncomputable section
namespace Atlas.Comparisons.G2Binary.Source6048
open Matrix Atlas.Unitary Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization

abbrev Special := Atlas.Unitary.SU BaseThree FieldNine 3 fieldNine_degree
abbrev Projective := Atlas.Unitary.PSU BaseThree FieldNine 3 fieldNine_degree
abbrev Lines := Atlas.Unitary.IsotropicPoints BaseThree FieldNine 3

theorem markedVector_ne_zero (i : Fin 28) : unitaryVector i ≠ 0 :=
  (unitary_marking_geometry.1 i).1

theorem markedVector_isotropic (i : Fin 28) :
    hermitian BaseThree FieldNine (unitaryVector i) (unitaryVector i) = 0 :=
  (explicitHermitian_eq _ _).symm.trans (unitary_marking_geometry.1 i).2

def markedLine (i : Fin 28) : Lines :=
  isotropicPoint (unitaryVector i) (markedVector_ne_zero i) (markedVector_isotropic i)

theorem markedLine_injective : Function.Injective markedLine := by
  intro i j h
  have hp := congrArg Subtype.val h
  change Projectivization.mk FieldNine (unitaryVector i) _ =
    Projectivization.mk FieldNine (unitaryVector j) _ at hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff FieldNine _ _ _ _).mp hp
  apply unitary_marking_geometry.2.1 i j (a : FieldNine) a.ne_zero
  simpa only [Units.smul_def] using ha.symm

theorem card_lines : Nat.card Lines = 28 := by
  rw [card_isotropicPoints_dim_three fieldNine_degree]
  norm_num [BaseThree, Nat.card_zmod]

instance : Finite Lines := Nat.finite_of_card_ne_zero (by rw [card_lines]; decide)

def unitaryMarking : Fin 28 ≃ Lines :=
  Equiv.ofBijective markedLine
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨markedLine_injective, by simp [card_lines]⟩)

theorem imaginary_trace_zero :
    imaginaryUnit + conjugation BaseThree FieldNine imaginaryUnit = 0 := by
  rw [fieldNine_conjugation]
  decide

/-- An element of the original full special unitary matrix carrier. -/
def specialRoot (i : Fin 28) : Special :=
  transvection fieldNine_degree (unitaryVector i) imaginaryUnit
    (markedVector_isotropic i) imaginary_trace_zero

theorem specialRoot_apply (i : Fin 28) (x : UVector) :
    (specialRoot i).val *ᵥ x = unitaryRootAction i x := by
  change transvectionMatrix (F := BaseThree) (unitaryVector i) imaginaryUnit *ᵥ x = _
  rw [transvectionMatrix_apply]
  simp only [unitaryRootAction, explicitHermitian_eq]

theorem specialRoot_on_lines (i j : Fin 28) :
    specialRoot i • markedLine j = markedLine (unitaryRootImage i j) := by
  obtain ⟨a, _ha, he⟩ := unitary_root_action_checked i j
  apply Subtype.ext
  change specialRoot i • Projectivization.mk FieldNine (unitaryVector j) _ =
    Projectivization.mk FieldNine (unitaryVector (unitaryRootImage i j)) _
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨a, ?_⟩
  change a • unitaryVector (unitaryRootImage i j) =
    (specialRoot i).val *ᵥ unitaryVector j
  rw [specialRoot_apply]
  exact he.symm

/-- Every element of the actual marked line group is a power of its one
chosen transvection: the only trace-zero parameters are 0, i and -i. -/
theorem markedLineGroup_eq_zpowers (i : Fin 28) :
    lineTransvections fieldNine_degree (unitaryVector i) (markedVector_isotropic i) =
      Subgroup.zpowers (specialRoot i) := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    have ht : a.toAdd.val + a.toAdd.val ^ 3 = 0 := by
      rw [← fieldNine_conjugation]
      exact (trace_zero_iff fieldNine_degree _).mp a.toAdd.prop
    rcases unitary_marking_geometry.2.2 a.toAdd.val ht with ha | ha | ha
    · have he : lineTransvectionHom fieldNine_degree (unitaryVector i)
          (markedVector_isotropic i) a = 1 := by
        apply Subtype.ext
        change transvectionMatrix (F := BaseThree) (unitaryVector i) a.toAdd.val = 1
        rw [ha, transvectionMatrix_zero]
      rw [he]
      exact (Subgroup.zpowers (specialRoot i)).one_mem
    · have he : lineTransvectionHom fieldNine_degree (unitaryVector i)
          (markedVector_isotropic i) a = specialRoot i := by
        apply Subtype.ext
        change transvectionMatrix (F := BaseThree) (unitaryVector i) a.toAdd.val =
          transvectionMatrix (F := BaseThree) (unitaryVector i) imaginaryUnit
        rw [ha]
      rw [he]
      exact Subgroup.mem_zpowers (specialRoot i)
    · have he : lineTransvectionHom fieldNine_degree (unitaryVector i)
          (markedVector_isotropic i) a = (specialRoot i)⁻¹ := by
        apply mul_left_cancel (a := specialRoot i)
        rw [mul_inv_cancel]
        apply Subtype.ext
        change transvectionMatrix (F := BaseThree) (unitaryVector i) imaginaryUnit *
          transvectionMatrix (F := BaseThree) (unitaryVector i) a.toAdd.val = 1
        rw [ha]
        exact transvectionMatrix_inverse (unitaryVector i)
          (markedVector_isotropic i) imaginaryUnit
      rw [he]
      exact (Subgroup.zpowers (specialRoot i)).inv_mem (Subgroup.mem_zpowers _)
  · apply Subgroup.zpowers_le.mpr
    refine ⟨Multiplicative.ofAdd
      ⟨imaginaryUnit, (trace_zero_iff fieldNine_degree _).mpr imaginary_trace_zero⟩, ?_⟩
    rfl

theorem markedPointGroup_eq_zpowers (i : Fin 28) :
    pointTransvections fieldNine_degree (markedLine i) =
      Subgroup.zpowers (specialRoot i) := by
  calc
    _ = lineTransvections fieldNine_degree (unitaryVector i)
        (markedVector_isotropic i) := by
      apply lineTransvections_eq_of_projective_eq fieldNine_degree _ _ _ _
        (markedLine i).val.rep_nonzero (markedVector_ne_zero i)
      exact Projectivization.mk_rep (markedLine i).val
    _ = _ := markedLineGroup_eq_zpowers i

/-- Genuine generation of the full retained SU, with the q>2 hypothesis discharged. -/
theorem specialRoots_generate : Subgroup.closure (Set.range specialRoot) = ⊤ := by
  apply top_unique
  rw [← transvectionGenerated_three_eq_top fieldNine_degree
    (by norm_num [BaseThree, Nat.card_zmod]), transvectionGenerated_eq_iSup_points]
  apply iSup_le
  intro p
  obtain ⟨i, rfl⟩ := unitaryMarking.surjective p
  change pointTransvections fieldNine_degree (markedLine i) ≤ _
  rw [markedPointGroup_eq_zpowers]
  exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨i, rfl⟩)

/-- The quotient is by the actual full center, without replacing its carrier. -/
def projectiveRoot (i : Fin 28) : Projective :=
  projection BaseThree FieldNine 3 fieldNine_degree (specialRoot i)

theorem projectiveRoots_generate :
    Subgroup.closure (Set.range projectiveRoot) = ⊤ := by
  let L : Subgroup Projective := Subgroup.closure (Set.range projectiveRoot)
  have hle : Subgroup.closure (Set.range specialRoot) ≤
      L.comap (projection BaseThree FieldNine 3 fieldNine_degree) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  rw [specialRoots_generate] at hle
  apply top_unique
  intro g _
  obtain ⟨u, rfl⟩ := projection_surjective BaseThree FieldNine 3 fieldNine_degree g
  exact hle (Subgroup.mem_top u)

/-- Faithful action of the actual PSU quotient in the saved unitary numbering. -/
def unitaryRepresentation : Projective →* Equiv.Perm (Fin 28) :=
  unitaryMarking.symm.permCongrHom.toMonoidHom.comp
    (projectiveIsotropicPerm fieldNine_degree (by decide : 0 < 3))

theorem unitaryRepresentation_injective : Function.Injective unitaryRepresentation := by
  have hp : Function.Injective
      (projectiveIsotropicPerm fieldNine_degree (by decide : 0 < 3)) :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr
      (isotropicPerm_kernel fieldNine_degree (by decide : 0 < 3)).symm
  exact unitaryMarking.symm.permCongrHom.injective.comp hp

theorem unitaryRepresentation_apply (g : Projective) (j : Fin 28) :
    unitaryMarking (unitaryRepresentation g j) =
      projectiveIsotropicPerm fieldNine_degree (by decide : 0 < 3) g
        (unitaryMarking j) := by
  change unitaryMarking (unitaryMarking.symm _) = _
  exact unitaryMarking.apply_symm_apply _

def rootPermutation (i : Fin 28) : Equiv.Perm (Fin 28) :=
  unitaryRepresentation (projectiveRoot i)

/-- The table is the action of actual projected matrices, not a replacement group. -/
theorem rootPermutation_apply (i j : Fin 28) :
    rootPermutation i j = unitaryRootImage i j := by
  apply unitaryMarking.injective
  rw [rootPermutation, unitaryRepresentation_apply]
  change specialRoot i • markedLine j = markedLine (unitaryRootImage i j)
  exact specialRoot_on_lines i j

/-- The whole permutation image is generated by the displayed 28 rows. -/
theorem unitaryImage_generated :
    Subgroup.closure (Set.range rootPermutation) = unitaryRepresentation.range := by
  have hi : unitaryRepresentation '' Set.range projectiveRoot =
      Set.range rootPermutation := by
    ext g
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨projectiveRoot i, ⟨i, rfl⟩, rfl⟩
  rw [← hi, ← MonoidHom.map_closure, projectiveRoots_generate,
    ← MonoidHom.range_eq_map]

/-- The preserved binary marking, using the actual trace/norm-one root pairs. -/
def binaryPoint (i : Fin 28) : QuadraticPoint :=
  ⟨markedVector i, marking_complete.1 i⟩

theorem binaryPoint_surjective : Function.Surjective binaryPoint := by
  intro p
  obtain ⟨i, hi⟩ := marking_complete.2.1 p.val p.property
  exact ⟨i, Subtype.ext hi⟩

def binaryMarking : Fin 28 ≃ QuadraticPoint :=
  Equiv.ofBijective binaryPoint
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨binaryPoint_surjective, by simp [Nat.card_eq_fintype_card, card_quadraticPoint]⟩)

/-- Restriction of the original octonion action to the actual long-root closure. -/
def binaryRepresentation : Atlas.G2.BinaryException.H →* Equiv.Perm (Fin 28) :=
  binaryMarking.symm.permCongrHom.toMonoidHom.comp
    (quadraticPointRepresentation.comp Atlas.G2.BinaryException.H.subtype)

theorem binaryRepresentation_injective : Function.Injective binaryRepresentation := by
  have hq : Function.Injective quadraticPointRepresentation := MulAction.toPerm_injective
  exact binaryMarking.symm.permCongrHom.injective.comp (hq.comp Subtype.val_injective)

theorem binaryRepresentation_apply (g : Atlas.G2.BinaryException.H) (j : Fin 28) :
    binaryMarking (binaryRepresentation g j) = g.val • binaryMarking j := by
  change binaryMarking (binaryMarking.symm _) = _
  exact binaryMarking.apply_symm_apply _

end Atlas.Comparisons.G2Binary.Source6048
