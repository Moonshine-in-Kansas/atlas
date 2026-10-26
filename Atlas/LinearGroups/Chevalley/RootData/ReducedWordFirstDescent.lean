import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! A first letter of a reduced actual root word is a left descent. Only the
already proved sign-controlled length formula for actual root permutations is
used; there is no abstract Coxeter or group-realization hypothesis. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rootWeylWord_inverse_first_negative (i : b.support) (l : List b.support)
    (hred : IsReducedRootWord P b (i :: l)) :
    ¬ b.IsPos (((rootWeylWord P b (i :: l))⁻¹).val i.val) := by
  apply (rootWeylLength_mul_simple_lt_iff P b
    (rootWeylWord P b (i :: l))⁻¹ i).mp
  have he : (rootWeylWord P b (i :: l))⁻¹ * simpleWeylReflection P b i =
      (rootWeylWord P b l)⁻¹ := by
    change (simpleWeylReflection P b i * rootWeylWord P b l)⁻¹ *
      simpleWeylReflection P b i = (rootWeylWord P b l)⁻¹
    group
  rw [he, rootWeylLength_inv, rootWeylLength_inv]
  have hle := rootWeylWord_length_le P b l
  have hlen : rootWeylLength P b (rootWeylWord P b (i :: l)) = l.length + 1 := hred
  omega

end Atlas.Chevalley.RootData
