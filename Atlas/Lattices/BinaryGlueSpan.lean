import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Choose
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Module

namespace Atlas.Lattices
open scoped BigOperators
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

def binaryHalfLift (b : ι→V) (w : ι→ZMod 2) : V :=
  ∑ i,(((w i).val : ℚ)/2) • b i

theorem binaryHalfLift_zero (b : ι→V) : binaryHalfLift b 0=0 := by
  simp [binaryHalfLift]

theorem binaryHalfLift_add (b : ι→V) (v w : ι→ZMod 2) :
    binaryHalfLift b (v+w)=binaryHalfLift b v+binaryHalfLift b w-
      ∑i,if v i=1 ∧ w i=1 then b i else 0 := by
  have hc : ∀a c : ZMod 2,((a+c).val : ℚ)/2=
      (a.val : ℚ)/2+(c.val : ℚ)/2-(if a=1 ∧ c=1 then 1 else 0) := by decide +kernel
  simp only [binaryHalfLift,Pi.add_apply,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc]
  split_ifs <;> simp [add_smul,sub_smul]

/-- Binary glue words whose half-frame sums belong to an integral module form a code. -/
noncomputable def liftableBinaryCode (L : Submodule ℤ V) (b : ι→V) (hb : ∀i,b i∈L) :
    Submodule (ZMod 2) (ι→ZMod 2) where
  carrier := {w | binaryHalfLift b w∈L}
  zero_mem' := by change binaryHalfLift b 0∈L; rw [binaryHalfLift_zero]; exact L.zero_mem
  add_mem' := by
    intro v w hv hw
    change binaryHalfLift b (v+w)∈L
    rw [binaryHalfLift_add]
    apply L.sub_mem (L.add_mem hv hw)
    apply L.sum_mem
    intro i _
    split_ifs
    · exact hb i
    · exact L.zero_mem
  smul_mem' := by
    intro a w hw
    change binaryHalfLift b (a • w)∈L
    have h : ∀a : ZMod 2,a=0 ∨ a=1 := by decide +kernel
    rcases h a with rfl|rfl
    · simp only [zero_smul,binaryHalfLift_zero]; exact L.zero_mem
    · simpa using hw

theorem binaryHalfLift_mem_of_span (L : Submodule ℤ V) (b : ι→V) (hb : ∀i,b i∈L)
    (s : Set (ι→ZMod 2)) (hs : ∀w∈s,binaryHalfLift b w∈L)
    (w : ι→ZMod 2) (hw : w∈Submodule.span (ZMod 2) s) : binaryHalfLift b w∈L := by
  have he : Submodule.span (ZMod 2) s≤liftableBinaryCode L b hb :=
    Submodule.span_le.mpr hs
  exact he hw

theorem integerHalfLift_mem (L : Submodule ℤ V) (b : ι→V) (hb : ∀i,b i∈L)
    (z : ι→ℤ) (hz : binaryHalfLift b (fun i => (z i : ZMod 2))∈L) :
    (∑i,((z i : ℚ)/2) • b i)∈L := by
  classical
  have hd (i : ι) : ∃k : ℤ,z i=((z i : ZMod 2).val : ℤ)+2*k := by
    have hc : ((z i-((z i : ZMod 2).val : ℤ) : ℤ) : ZMod 2)=0 := by simp
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hc
    change z i-((z i : ZMod 2).val : ℤ)=2*k at hk
    exact ⟨k,by linarith⟩
  choose k hk using hd
  have he : (∑i,((z i : ℚ)/2) • b i)=binaryHalfLift b (fun i => (z i : ZMod 2))+
      ∑i,k i • b i := by
    simp only [binaryHalfLift,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Int.cast_smul_eq_zsmul ℚ,←add_smul]
    congr 1
    have hc := congrArg (fun n : ℤ => (n : ℚ)) (hk i)
    push_cast at hc
    linarith
  rw [he]
  exact L.add_mem hz (L.sum_mem (fun i _ => L.smul_mem (k i) (hb i)))

end Atlas.Lattices

