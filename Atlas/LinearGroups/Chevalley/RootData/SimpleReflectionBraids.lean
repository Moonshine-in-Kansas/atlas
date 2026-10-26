import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords
import Atlas.LinearGroups.Chevalley.RootData.DihedralRootWords

/-! Literal rank-two braids and longest-word involutions in the actual
root-permutation Weyl image. No Coxeter presentation is assumed. -/

noncomputable section
namespace Atlas.Chevalley.RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The bundled actual word agrees with the unbundled reflection word. -/
theorem rootWeylWord_val_eq_reflectionWord (l : List b.support) :
    (rootWeylWord P b l).val = reflectionWord P (l.map Subtype.val) := by
  rw [rootWeylWord_val]
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [simpleReflectionWord_cons, List.map_cons, reflectionWord, ih]

/-- The length-2 braid in the actual root-permutation Weyl image. -/
theorem rootWeylWord_braid_two (i j : b.support)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0) :
    rootWeylWord P b [i, j] = rootWeylWord P b [j, i] := by
  apply Subtype.ext
  have hbij : P.pairingIn ℤ i.val j.val = 0 := hij
  have hbji : P.pairingIn ℤ j.val i.val = 0 := hji
  have hpij : P.pairing i.val j.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, hbij]
    simp
  have hpji : P.pairing j.val i.val = 0 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, hbji]
    simp
  simp only [rootWeylWord_val_eq_reflectionWord, List.map_cons, List.map_nil]
  ext k
  apply P.root.injective
  simp only [reflectionWord, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
    P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
  module

/-- The length-3 braid in the actual root-permutation Weyl image. -/
theorem rootWeylWord_braid_three (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    rootWeylWord P b [i, j, i] = rootWeylWord P b [j, i, j] := by
  apply Subtype.ext
  have hbij : P.pairingIn ℤ i.val j.val = -1 := hij
  have hbji : P.pairingIn ℤ j.val i.val = -1 := hji
  have hpij : P.pairing i.val j.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ i.val j.val, hbij]
    simp
  have hpji : P.pairing j.val i.val = -1 := by
    rw [← P.algebraMap_pairingIn ℤ j.val i.val, hbji]
    simp
  simp only [rootWeylWord_val_eq_reflectionWord, List.map_cons, List.map_nil]
  ext k
  apply P.root.injective
  simp only [reflectionWord, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    P.root_reflectionPerm, P.reflection_apply, map_sub, map_smul,
    P.root_coroot'_eq_pairing, P.pairing_same, hpij, hpji]
  module

/-- The length-4 braid in the actual root-permutation Weyl image. -/
theorem rootWeylWord_braid_four (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) :
    rootWeylWord P b [i, j, i, j] = rootWeylWord P b [j, i, j, i] := by
  apply Subtype.ext
  simpa only [rootWeylWord_val_eq_reflectionWord, List.map_cons, List.map_nil]
    using reflectionWord_four P i.val j.val hij hji

/-- The length-6 braid in the actual root-permutation Weyl image. -/
theorem rootWeylWord_braid_six (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) :
    rootWeylWord P b [i, j, i, j, i, j] = rootWeylWord P b [j, i, j, i, j, i] := by
  apply Subtype.ext
  simpa only [rootWeylWord_val_eq_reflectionWord, List.map_cons, List.map_nil]
    using reflectionWord_six P i.val j.val hij hji

private theorem rootWeylWord_mul_self_of_reverse (l : List b.support)
    (h : rootWeylWord P b l.reverse = rootWeylWord P b l) :
    rootWeylWord P b l * rootWeylWord P b l = 1 := by
  have hinv : (rootWeylWord P b l)⁻¹ = rootWeylWord P b l :=
    (rootWeylWord_reverse P b l).symm.trans h
  calc
    rootWeylWord P b l * rootWeylWord P b l =
        rootWeylWord P b l * (rootWeylWord P b l)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel _

/-- The length-2 alternating longest word is an involution. -/
theorem rootWeylWord_two_mul_self (i j : b.support)
    (hij : b.cartanMatrix i j = 0) (hji : b.cartanMatrix j i = 0)
    : rootWeylWord P b [i, j] * rootWeylWord P b [i, j] = 1 := by
  apply rootWeylWord_mul_self_of_reverse P b
  simpa only [List.reverse_cons, List.reverse_nil, List.cons_append,
    List.nil_append] using (rootWeylWord_braid_two P b i j hij hji).symm

/-- The length-3 alternating longest word is an involution. -/
theorem rootWeylWord_three_mul_self (i j : b.support)
    : rootWeylWord P b [i, j, i] * rootWeylWord P b [i, j, i] = 1 := by
  apply rootWeylWord_mul_self_of_reverse P b
  rfl

/-- The length-4 alternating longest word is an involution. -/
theorem rootWeylWord_four_mul_self (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2)
    : rootWeylWord P b [i, j, i, j] * rootWeylWord P b [i, j, i, j] = 1 := by
  apply rootWeylWord_mul_self_of_reverse P b
  simpa only [List.reverse_cons, List.reverse_nil, List.cons_append,
    List.nil_append] using (rootWeylWord_braid_four P b i j hij hji).symm

/-- The length-6 alternating longest word is an involution. -/
theorem rootWeylWord_six_mul_self (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3)
    : rootWeylWord P b [i, j, i, j, i, j] * rootWeylWord P b [i, j, i, j, i, j] = 1 := by
  apply rootWeylWord_mul_self_of_reverse P b
  simpa only [List.reverse_cons, List.reverse_nil, List.cons_append,
    List.nil_append] using (rootWeylWord_braid_six P b i j hij hji).symm

end Atlas.Chevalley.RootData
