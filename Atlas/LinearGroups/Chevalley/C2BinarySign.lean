import Atlas.LinearGroups.Chevalley.C2BinarySixForms

/-! The sign character of the genuine six-form action of the selected
C2 companion over F2. The displayed long-root element acts as a transposition. -/
noncomputable section
namespace Atlas.Chevalley.C2Binary
open Classical Integral.RankTwo.C2Minuscule
open scoped Matrix
local instance : NeZero C2.rank := ⟨by decide⟩

def label (g : G) (i : Fin 6) : Fin 6 := (preserves_weight g i).choose

theorem label_spec (g : G) (i : Fin 6) :
    (fun v => form i (weightMatrixHom K g *ᵥ v)) = form (label g i) :=
  (preserves_weight g i).choose_spec

theorem label_one (i : Fin 6) : label 1 i = i := by
  apply form_injective
  funext v
  rw [← congrFun (label_spec 1 i) v, map_one, Matrix.one_mulVec]

theorem label_mul (g h : G) (i : Fin 6) : label (g * h) i = label h (label g i) := by
  apply form_injective
  funext v
  rw [← congrFun (label_spec (g * h) i) v, map_mul, ← Matrix.mulVec_mulVec,
    congrFun (label_spec g i) (weightMatrixHom K h *ᵥ v),
    congrFun (label_spec h (label g i)) v]

def permutation (g : G) : Equiv.Perm (Fin 6) where
  toFun := label g⁻¹
  invFun := label g
  left_inv i := by rw [← label_mul, inv_mul_cancel, label_one]
  right_inv i := by rw [← label_mul, mul_inv_cancel, label_one]

def permutationHom : G →* Equiv.Perm (Fin 6) where
  toFun := permutation
  map_one' := by
    apply Equiv.ext
    intro i
    change label (1 : G)⁻¹ i = i
    rw [inv_one, label_one]
  map_mul' g h := by
    apply Equiv.ext
    intro i
    change label (g * h)⁻¹ i = label g⁻¹ (label h⁻¹ i)
    rw [mul_inv_rev, label_mul]

theorem long_root_inv :
    (selectedWeightCompanionX C2 K 1 1)⁻¹ = selectedWeightCompanionX C2 K 1 1 := by
  let f := weightCompanionXHom (rootDatum C2).pairing (rootDatum C2).base
    (selectedWeightOrbits C2) (selectedWeightOrbits_closed C2)
    (selectedWeightOrbits_minuscule C2) K ((rootDatum C2).indexEquiv 1)
  have h := map_inv f (Multiplicative.ofAdd (1 : K))
  change selectedWeightCompanionX C2 K 1 (-1) =
    (selectedWeightCompanionX C2 K 1 1)⁻¹ at h
  rw [show (-1 : K) = 1 by decide] at h
  exact h.symm

theorem permutationHom_long_root :
    permutationHom (selectedWeightCompanionX C2 K 1 1) = Equiv.swap 0 1 := by
  apply Equiv.ext
  intro i
  change label (selectedWeightCompanionX C2 K 1 1)⁻¹ i = Equiv.swap 0 1 i
  rw [long_root_inv]
  apply form_injective
  rw [← label_spec, matrix_xlong]
  exact long_root_swaps i

def oddSign : G →* ℤˣ := Equiv.Perm.sign.comp permutationHom

theorem oddSign_long_root : oddSign (selectedWeightCompanionX C2 K 1 1) = -1 := by
  change Equiv.Perm.sign (permutationHom (selectedWeightCompanionX C2 K 1 1)) = -1
  rw [permutationHom_long_root, Equiv.Perm.sign_swap (by decide : (0 : Fin 6) ≠ 1)]

end Atlas.Chevalley.C2Binary
