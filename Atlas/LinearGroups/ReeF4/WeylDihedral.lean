import Atlas.LinearGroups.ReeF4.WeylRootTransport
import Atlas.LinearGroups.ReeF4.WeylOrder
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Sixteen concrete Weyl operators, with faithful dihedral multiplication.
The local checks concern only the sixteen Weyl elements, not elements of the
ambient finite-field stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F]

def weylDihedralLift : DihedralGroup 8 → (TraceZero F ≃ₗ[F] TraceZero F)
  | .r i => (weylRho * weylSigma) ^ i.val
  | .sr i => weylRho * (weylRho * weylSigma) ^ i.val

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
-- Only sixteen coordinate-transport identities are checked in the actual representation.
theorem weylDihedralLift_coordinates (d : DihedralGroup 8) (w : TraceZero F)
    (i : Fin 3) (j : Fin 9) :
    wilsonCoordinatesEquiv (weylDihedralLift d w : Carrier F) i j =
      wilsonCoordinatesEquiv (w : Carrier F)
        ((weylDihedralPermutation d).symm (i,j)).1
        ((weylDihedralPermutation d).symm (i,j)).2 := by
  cases d with
  | r k =>
    exact weylCoordinateCompatible_pow
      (weylCoordinateCompatible_mul weylRho_coordinateCompatible
        weylSigma_coordinateCompatible) k.val w (i,j)
  | sr k =>
    exact weylCoordinateCompatible_mul weylRho_coordinateCompatible
      (weylCoordinateCompatible_pow
        (weylCoordinateCompatible_mul weylRho_coordinateCompatible
          weylSigma_coordinateCompatible) k.val) w (i,j)

def weylDihedralMap : DihedralGroup 8 →* (TraceZero F ≃ₗ[F] TraceZero F) where
  toFun := weylDihedralLift
  map_one' := rfl
  map_mul' a b := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    apply (wilsonCoordinatesEquiv (F := F)).injective
    funext i j
    change wilsonCoordinatesEquiv (weylDihedralLift (a*b) w : Carrier F) i j =
      wilsonCoordinatesEquiv (weylDihedralLift a (weylDihedralLift b w) : Carrier F) i j
    simp only [weylDihedralLift_coordinates, weylDihedralPermutation_mul]
    rfl

/-- Two marked root images distinguish all sixteen actual operators. -/
def weylDihedralSignature : DihedralGroup 8 → ShortRootLabel × ShortRootLabel
  | .r i => (![((0,0),(0,2)), ((2,1),(2,0)), ((0,5),(0,0)), ((2,7),(2,1)),
      ((0,7),(0,5)), ((2,6),(2,7)), ((0,2),(0,7)), ((2,0),(2,6))]) ⟨i.val, ZMod.val_lt i⟩
  | .sr i => (![((0,0),(0,5)), ((2,0),(2,1)), ((0,2),(0,0)), ((2,6),(2,0)),
      ((0,7),(0,2)), ((2,7),(2,6)), ((0,5),(0,7)), ((2,1),(2,7))]) ⟨i.val, ZMod.val_lt i⟩

theorem weylDihedralSignature_injective : Function.Injective weylDihedralSignature := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 500000 in
theorem weylDihedralSignature_permutation : ∀ d : DihedralGroup 8,
    (weylDihedralPermutation d (weylRootMark (0,0)),
      weylDihedralPermutation d (weylRootMark (0,2))) =
    (weylRootMark (weylDihedralSignature d).1,
      weylRootMark (weylDihedralSignature d).2) := by
  intro d
  fin_cases d <;> decide

theorem weylDihedral_signature_images (d : DihedralGroup 8) :
    (weylDihedralMap (F := F) d (rootVector (0,0)),
      weylDihedralMap (F := F) d (rootVector (0,2))) =
    (rootVector (weylDihedralSignature d).1,
      rootVector (weylDihedralSignature d).2) := by
  have hc : WeylCoordinateCompatible (weylDihedralMap (F := F) d)
      (weylDihedralPermutation d) :=
    fun w c => weylDihedralLift_coordinates d w c.1 c.2
  exact Prod.ext
    (weylCoordinateCompatible_root hc _ _
      (congrArg Prod.fst (weylDihedralSignature_permutation d)))
    (weylCoordinateCompatible_root hc _ _
      (congrArg Prod.snd (weylDihedralSignature_permutation d)))

variable [Nontrivial F]

private theorem weyl_rootVector_injective : Function.Injective (rootVector (F := F)) := by
  intro r s h
  have hv := congrArg (fun x : TraceZero F => x.val.2 r.1 r.2) h
  apply Prod.ext
  · by_contra hn
    simpa [rootVector, Pi.single_apply, hn] using hv
  · by_contra hn
    by_cases hb : r.1 = s.1
    · simpa [rootVector, Pi.single_apply, hb, hn] using hv
    · simpa [rootVector, Pi.single_apply, hb] using hv


theorem weylDihedralMap_injective : Function.Injective (weylDihedralMap (F := F)) := by
  intro d e h
  apply weylDihedralSignature_injective
  have hp := congrArg
    (fun g : TraceZero F ≃ₗ[F] TraceZero F => (g (rootVector (0,0)), g (rootVector (0,2)))) h
  rw [weylDihedral_signature_images, weylDihedral_signature_images] at hp
  exact Prod.ext (weyl_rootVector_injective (congrArg Prod.fst hp))
    (weyl_rootVector_injective (congrArg Prod.snd hp))

def weylSubgroup : Subgroup (TraceZero F ≃ₗ[F] TraceZero F) :=
  (weylDihedralMap (F := F)).range

def weylDihedralEquiv : DihedralGroup 8 ≃* weylSubgroup (F := F) :=
  MonoidHom.ofInjective weylDihedralMap_injective

theorem card_weylSubgroup : Nat.card (weylSubgroup (F := F)) = 16 := by
  rw [← Nat.card_congr (weylDihedralEquiv (F := F)).toEquiv, DihedralGroup.nat_card]

theorem weylRho_mem_weylSubgroup : weylRho (F := F) ∈ weylSubgroup := by
  refine ⟨DihedralGroup.sr 0, ?_⟩
  apply LinearEquiv.ext
  intro w
  rfl

theorem weylSigma_mem_weylSubgroup : weylSigma (F := F) ∈ weylSubgroup := by
  refine ⟨DihedralGroup.sr 1, ?_⟩
  change weylRho * (weylRho * weylSigma) ^ (1 : ZMod 8).val = weylSigma
  change weylRho * (weylRho * weylSigma) ^ 1 = weylSigma
  rw [pow_one, ← mul_assoc, ← pow_two, weylRho_square, one_mul]

theorem weylSubgroup_eq_closure : weylSubgroup (F := F) =
    Subgroup.closure {weylRho, weylSigma} := by
  apply le_antisymm
  · let C : Subgroup (TraceZero F ≃ₗ[F] TraceZero F) :=
      Subgroup.closure {weylRho, weylSigma}
    have hr : weylRho ∈ C := Subgroup.subset_closure (by simp)
    have hs : weylSigma ∈ C := Subgroup.subset_closure (by simp)
    rintro _ ⟨d, rfl⟩
    cases d with
    | r i => exact C.pow_mem (C.mul_mem hr hs) i.val
    | sr i => exact C.mul_mem hr (C.pow_mem (C.mul_mem hr hs) i.val)
  · apply (Subgroup.closure_le weylSubgroup).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact weylRho_mem_weylSubgroup
    · exact weylSigma_mem_weylSubgroup

end Atlas.ReeF4

