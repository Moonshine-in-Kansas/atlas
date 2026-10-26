import Atlas.Codes.QuaternaryLayers
import Mathlib.Algebra.Module.ZMod
import Mathlib.InformationTheory.Hamming

namespace Atlas.Codes.Quaternary
open scoped BigOperators

def twiceFour : Quat →+ ZMod 8 where
  toFun a := 2*(a.val : ZMod 8)
  map_zero' := by decide +kernel
  map_add' := by decide +kernel

def squareModEight (a : Quat) : ZMod 8 := (a.val : ZMod 8)^2

theorem squareModEight_add (a b : Quat) :
    squareModEight (a+b)=squareModEight a+squareModEight b+twiceFour (a*b) := by
  decide +kernel +revert

theorem squareModEight_neg (a : Quat) : squareModEight (-a)=squareModEight a := by
  decide +kernel +revert

theorem squareModEight_intCast (n : ℤ) : squareModEight (n : Quat)=(n : ZMod 8)^2 := by
  let f : ZMod 8 →+* Quat := ZMod.castHom (by decide : 4 ∣ 8) Quat
  have h : ∀ a : ZMod 8, squareModEight (f a)=a^2 := by decide +kernel
  simpa using h (n : ZMod 8)

variable {ι : Type*} [Fintype ι]

def normModEight (w : ι → Quat) : ZMod 8 := ∑ i, squareModEight (w i)

theorem normModEight_zero : normModEight (0 : ι → Quat)=0 := by
  simp [normModEight,squareModEight]

theorem normModEight_add (v w : ι → Quat) :
    normModEight (v+w)=normModEight v+normModEight w+twiceFour (quaternaryForm v w) := by
  simp only [normModEight,Pi.add_apply,squareModEight_add,Finset.sum_add_distrib]
  change _ = _ + _ + twiceFour (∑ i,v i*w i)
  rw [map_sum]

theorem normModEight_neg (w : ι → Quat) : normModEight (-w)=normModEight w := by
  simp [normModEight,squareModEight_neg]

def evenPart (Q : Submodule Quat (ι → Quat)) (hQ : Q≤quaternaryForm.orthogonal Q) :
    Submodule Quat (ι → Quat) := AddSubgroup.toZModSubmodule 4
  {carrier := {w | w∈Q ∧ normModEight w=0}
   zero_mem' := ⟨Q.zero_mem,normModEight_zero⟩
   add_mem' := by
     intro v w hv hw
     refine ⟨Q.add_mem hv.1 hw.1,?_⟩
     rw [normModEight_add,hv.2,hw.2,(hQ hw.1) v hv.1,map_zero,add_zero,add_zero]
   neg_mem' := by
     intro v hv
     exact ⟨Q.neg_mem hv.1,by rw [normModEight_neg,hv.2]⟩}

theorem normModEight_intCast (v : ι → ℤ) :
    normModEight (fun i => (v i : Quat)) = (∑ i, v i^2 : ℤ) := by
  simp [normModEight,squareModEight_intCast]

theorem normModEight_double (b : ι → Binary) :
    normModEight (double b)=4*(hammingNorm b : ZMod 8) := by
  classical
  have h (a : Binary) : squareModEight (doubleScalar a)=
      (if a=0 then 0 else 4) := by decide +kernel +revert
  simp only [normModEight,double,AddMonoidHom.coe_mk,ZeroHom.coe_mk,h]
  simp [hammingNorm,Finset.card_filter,Finset.mul_sum,mul_ite]

def euclideanSymbolWeight (a : Quat) : ℕ := if a=0 then 0 else if a=2 then 4 else 1

def euclideanWeight (w : ι → Quat) : ℕ := ∑ i,euclideanSymbolWeight (w i)

theorem euclideanWeight_modEight (w : ι → Quat) :
    (euclideanWeight w : ZMod 8)=normModEight w := by
  have h (a : Quat) : (euclideanSymbolWeight a : ZMod 8)=squareModEight a := by
    decide +kernel +revert
  simp [euclideanWeight,normModEight,h]

theorem euclideanWeight_even_iff (w : ι → Quat) :
    8 ∣ euclideanWeight w ↔ normModEight w=0 := by
  rw [← euclideanWeight_modEight,ZMod.natCast_eq_zero_iff]

end Atlas.Codes.Quaternary


