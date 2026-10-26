import Atlas.LinearGroups.Triality.UnipotentSolvable

/-! The two simple-root coordinate homomorphisms of U. Their kernels are
concrete candidates for the two parabolic radicals; parabolic normality is
proved separately, not included in their definitions. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def unipotentParameters (g : unipotent F K hdeg) : PositiveParameters F K :=
  (unipotentCoordinates F K hdeg).symm g

theorem unipotentParameters_recover (g : unipotent F K hdeg) :
    positiveMatrix F K (unipotentParameters F K hdeg g) = g.val :=
  congrArg Subtype.val ((unipotentCoordinates F K hdeg).apply_symm_apply g)

theorem unipotentParameters_one :
    unipotentParameters F K hdeg 1 = ⟨0,0,0,0,0,0⟩ := by
  apply positiveMatrix_injective F K
  rw [unipotentParameters_recover, positiveMatrix_zero]
  rfl

theorem unipotentParameters_mul (g h : unipotent F K hdeg) :
    unipotentParameters F K hdeg (g*h) =
      positiveCollect F K (unipotentParameters F K hdeg g) (unipotentParameters F K hdeg h) := by
  apply positiveMatrix_injective F K
  rw [← positiveMatrix_mul F K hdeg, unipotentParameters_recover,
    unipotentParameters_recover, unipotentParameters_recover]
  rfl

def shortCoordinate : unipotent F K hdeg →* Multiplicative K where
  toFun g := Multiplicative.ofAdd (unipotentParameters F K hdeg g).a
  map_one' := by rw [unipotentParameters_one]; rfl
  map_mul' g h := by rw [unipotentParameters_mul]; rfl

def longCoordinate : unipotent F K hdeg →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (unipotentParameters F K hdeg g).b
  map_one' := by rw [unipotentParameters_one]; rfl
  map_mul' g h := by rw [unipotentParameters_mul]; rfl

def shortRadicalKernel : Subgroup (unipotent F K hdeg) := (shortCoordinate F K hdeg).ker
def longRadicalKernel : Subgroup (unipotent F K hdeg) := (longCoordinate F K hdeg).ker

instance shortRadicalKernel_normal : (shortRadicalKernel F K hdeg).Normal := inferInstanceAs
  (shortCoordinate F K hdeg).ker.Normal
instance longRadicalKernel_normal : (longRadicalKernel F K hdeg).Normal := inferInstanceAs
  (longCoordinate F K hdeg).ker.Normal

theorem shortCoordinate_surjective : Function.Surjective (shortCoordinate F K hdeg) := by
  intro a
  refine ⟨unipotentCoordinates F K hdeg ⟨a.toAdd,0,0,0,0,0⟩, ?_⟩
  simp [shortCoordinate, unipotentParameters]

theorem longCoordinate_surjective : Function.Surjective (longCoordinate F K hdeg) := by
  intro b
  refine ⟨unipotentCoordinates F K hdeg ⟨0,b.toAdd,0,0,0,0⟩, ?_⟩
  simp [longCoordinate, unipotentParameters]

theorem shortRadicalKernel_solvable : Group.IsSolvable (shortRadicalKernel F K hdeg) := by
  letI := unipotent_solvable F K hdeg
  infer_instance

theorem longRadicalKernel_solvable : Group.IsSolvable (longRadicalKernel F K hdeg) := by
  letI := unipotent_solvable F K hdeg
  infer_instance

theorem card_shortRadicalKernel :
    Nat.card (shortRadicalKernel F K hdeg) = Nat.card F ^ 9 := by
  have hh := (shortCoordinate F K hdeg).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (shortCoordinate_surjective F K hdeg),
    Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K),
    card_unipotent F K hdeg, FiniteCubic.card_extension hdeg] at hh
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F ^ 3 by exact pow_pos Nat.card_pos _)
  change Nat.card (shortCoordinate F K hdeg).ker * _ = _
  calc
    _ = Nat.card F ^ 12 := by simpa using hh
    _ = _ := by ring

theorem card_longRadicalKernel :
    Nat.card (longRadicalKernel F K hdeg) = Nat.card F ^ 11 := by
  have hh := (longCoordinate F K hdeg).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (longCoordinate_surjective F K hdeg),
    Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F),
    card_unipotent F K hdeg] at hh
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F ^ 1 by exact pow_pos Nat.card_pos _)
  change Nat.card (longCoordinate F K hdeg).ker * _ = _
  calc
    _ = Nat.card F ^ 12 := by simpa using hh
    _ = _ := by ring

end Atlas.Triality
