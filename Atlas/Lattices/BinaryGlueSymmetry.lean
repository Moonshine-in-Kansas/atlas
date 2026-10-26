import Atlas.Lattices.BinaryGlueSpan

/-! Signed permutations preserve binary half-frame glue modulo the integer frame. -/
namespace Atlas.Lattices
open scoped BigOperators
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

theorem binaryHalfLift_permute (b : ι→V) (p : Equiv.Perm ι) (w : ι→ZMod 2) :
    binaryHalfLift b (w ∘ p.symm)=∑i,(((w i).val : ℚ)/2) • b (p i) := by
  unfold binaryHalfLift
  rw [←Equiv.sum_comp p]
  simp

/-- The sign discrepancy is an explicit integer sum of frame vectors. -/
theorem binaryHalfLift_signed_permutation (b : ι→V) (p : Equiv.Perm ι)
    (s : ι→ZMod 2) (f : V →ₗ[ℚ] V)
    (hf : ∀i,f (b i)=if s i=0 then b (p i) else -b (p i)) (w : ι→ZMod 2) :
    f (binaryHalfLift b w)=binaryHalfLift b (w ∘ p.symm)-
      ∑i,if s i=1 ∧ w i=1 then b (p i) else 0 := by
  rw [binaryHalfLift_permute]
  simp only [binaryHalfLift,map_sum,map_smul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf]
  have hb : ∀a : ZMod 2,a=0 ∨ a=1 := by decide +kernel
  rcases hb (s i) with hs|hs <;> rcases hb (w i) with hw|hw <;>
    (simp [hs,hw,ZMod.val_one_eq_one_mod]; try module)

/-- Lattice-preserving signed frame permutations preserve liftability of the binary word. -/
theorem binaryHalfLift_permute_mem (L : Submodule ℤ V) (b : ι→V)
    (hb : ∀i,b i∈L) (p : Equiv.Perm ι) (s : ι→ZMod 2) (f : V →ₗ[ℚ] V)
    (hf : ∀i,f (b i)=if s i=0 then b (p i) else -b (p i))
    (hL : ∀v,v∈L → f v∈L) (w : ι→ZMod 2) (hw : binaryHalfLift b w∈L) :
    binaryHalfLift b (w ∘ p.symm)∈L := by
  have he := binaryHalfLift_signed_permutation b p s f hf w
  have hd : (∑i,if s i=1 ∧ w i=1 then b (p i) else 0)∈L := by
    apply L.sum_mem
    intro i _
    split_ifs
    · exact hb (p i)
    · exact L.zero_mem
  rw [eq_sub_iff_add_eq] at he
  rw [←he]
  exact L.add_mem (hL _ hw) hd

theorem liftableBinaryCode_permute_mem (L : Submodule ℤ V) (b : ι→V)
    (hb : ∀i,b i∈L) (p : Equiv.Perm ι) (s : ι→ZMod 2) (f : V →ₗ[ℚ] V)
    (hf : ∀i,f (b i)=if s i=0 then b (p i) else -b (p i))
    (hL : ∀v,v∈L → f v∈L) (w : ι→ZMod 2) (hw : w∈liftableBinaryCode L b hb) :
    w ∘ p.symm∈liftableBinaryCode L b hb :=
  binaryHalfLift_permute_mem L b hb p s f hf hL w hw

end Atlas.Lattices
