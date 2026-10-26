import Atlas.LinearGroups.Chevalley.RootData.DihedralRootWords
import Atlas.LinearGroups.Chevalley.WeylRootActionComplete

/-! Source candidate: exact signed action of every actual simple Weyl word
on root basis vectors, and the length-four/six braid on those columns. These
theorems alone do not identify the action on Cartan or companion blocks. -/

noncomputable section
open scoped Matrix
namespace Atlas.Chevalley
open Integral RootData
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

def adjointWeylWord : List b.support → Adjoint P b R
  | [] => 1
  | i :: l => adjointWeyl P b R i 1 * adjointWeylWord l

theorem adjointWeylWord_root (l : List b.support) (k : ι) :
    (adjointWeylWord P b R l).val.val *ᵥ rootVector P b R k =
      (-1 : R) ^ ((inversionRoots P (l.map Subtype.val)).map
        (fun j => P.chainBotCoeff j k)).sum •
        rootVector P b R (reflectionWord P (l.map Subtype.val) k) := by
  induction l with
  | nil => simp [adjointWeylWord, reflectionWord, inversionRoots]
  | cons i l ih =>
    calc
      _ = ((-1 : R) ^ ((inversionRoots P (l.map Subtype.val)).map
          (fun j => P.chainBotCoeff j k)).sum *
          (-1 : R) ^ P.chainBotCoeff i (reflectionWord P (l.map Subtype.val) k)) •
          rootVector P b R (P.reflectionPerm i (reflectionWord P (l.map Subtype.val) k)) := by
        change ((adjointWeyl P b R i 1).val.val *
          (adjointWeylWord P b R l).val.val) *ᵥ rootVector P b R k = _
        rw [← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
          adjointWeyl_one_root_signed, smul_smul]
      _ = _ := by
        rw [chainBotCoeff_reflectionWord_right]
        simp only [List.map_cons, inversionRoots, reflectionWord,
          List.sum_cons, Equiv.Perm.mul_apply, pow_add, mul_comm]

/-- Exact scalar and label data suffice on root columns. This does not infer
whole-matrix equality from the root columns. -/
theorem adjointWeylWord_root_eq_of_inversionPerm (l r : List b.support)
    (hperm : reflectionWord P (l.map Subtype.val) = reflectionWord P (r.map Subtype.val))
    (hroots : (inversionRoots P (l.map Subtype.val)).Perm
      (inversionRoots P (r.map Subtype.val))) (k : ι) :
    (adjointWeylWord P b R l).val.val *ᵥ rootVector P b R k =
      (adjointWeylWord P b R r).val.val *ᵥ rootVector P b R k := by
  have hsum := (hroots.map (fun j => P.chainBotCoeff j k)).sum_eq
  rw [adjointWeylWord_root, adjointWeylWord_root, hperm, hsum]

theorem adjointWeylWord_four_root (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -2) (k : ι) :
    (adjointWeylWord P b R [i, j, i, j]).val.val *ᵥ rootVector P b R k =
      (adjointWeylWord P b R [j, i, j, i]).val.val *ᵥ rootVector P b R k := by
  apply adjointWeylWord_root_eq_of_inversionPerm
  · exact reflectionWord_four P i.val j.val hij hji
  · change (inversionRoots P [i.val, j.val, i.val, j.val]).Perm
      (inversionRoots P [j.val, i.val, j.val, i.val])
    rw [inversionRoots_four_reverse P i.val j.val hij hji]
    exact List.reverse_perm _

theorem adjointWeylWord_six_root (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (k : ι) :
    (adjointWeylWord P b R [i, j, i, j, i, j]).val.val *ᵥ rootVector P b R k =
      (adjointWeylWord P b R [j, i, j, i, j, i]).val.val *ᵥ rootVector P b R k := by
  apply adjointWeylWord_root_eq_of_inversionPerm
  · exact reflectionWord_six P i.val j.val hij hji
  · change (inversionRoots P [i.val, j.val, i.val, j.val, i.val, j.val]).Perm
      (inversionRoots P [j.val, i.val, j.val, i.val, j.val, i.val])
    rw [inversionRoots_six_reverse P i.val j.val hij hji]
    exact List.reverse_perm _

end Atlas.Chevalley
