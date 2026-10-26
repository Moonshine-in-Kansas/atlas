import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic

/-! Rational pairing duality for integral binary Construction-A glue.
No sporadic construction enters the definitions or proofs. -/
namespace Atlas.Lattices.BinaryGlue
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

abbrev Binary := ZMod 2
abbrev Code := Submodule Binary (ι → Binary)

def residue (z : ι → ℤ) : ι → Binary := fun i => z i

def integerCast (z : ι → ℤ) : ι → ℚ := fun i => z i

def half (z : ι → ℤ) : ι → ℚ := fun i => (z i : ℚ)/2

def dualCode (C : Code (ι:=ι)) : Code (ι:=ι) :=
  C.orthogonalBilin (dotProductBilin Binary Binary)

/-- The integer preimage of the given binary code, as exact rational vectors. -/
def MemGlue (C : Code (ι:=ι)) (y : ι → ℚ) : Prop :=
  ∃z : ι → ℤ,residue z∈C ∧ integerCast z=y

/-- Integral pairing against every integer lift in the binary glue. -/
def MemDual (C : Code (ι:=ι)) (y : ι → ℚ) : Prop :=
  ∀z : ι → ℤ,residue z∈C → ∃k : ℤ,(∑i,y i*(z i : ℚ))=k

theorem dual_half_coordinates (C : Code (ι:=ι)) (y : ι → ℚ) (hy : MemDual C y) :
    ∃z : ι → ℤ,half z=y := by
  classical
  have h (i : ι) : ∃k : ℤ,2*y i=k := by
    have hz : residue (Pi.single i 2)=0 := by
      ext j
      by_cases hj : j=i <;> simp [residue,hj]
      decide
    obtain ⟨k,hk⟩ := hy (Pi.single i 2) (hz ▸ C.zero_mem)
    exact ⟨k,by simpa [Pi.single_apply,mul_comm] using hk⟩
  choose z hz using h
  refine ⟨z,?_⟩
  ext i
  change (z i : ℚ)/2=y i
  rw [←hz i]
  ring

theorem half_pairing (z w : ι → ℤ) :
    (∑i,half z i*(w i : ℚ))=((∑i,z i*w i : ℤ) : ℚ)/2 := by
  simp only [half,Int.cast_sum,Int.cast_mul,div_eq_mul_inv]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem half_mem_dual_iff (C : Code (ι:=ι)) (z : ι → ℤ) :
    MemDual C (half z) ↔ residue z∈dualCode C := by
  classical
  constructor
  · intro hz c hc
    let w : ι → ℤ := fun i => (c i).val
    have hw : residue w=c := by ext i; simp [residue,w]
    obtain ⟨k,hk⟩ := hz w (hw ▸ hc)
    rw [half_pairing] at hk
    have he : (∑i,z i*w i)=2*k := by
      have he' : ((∑i,z i*w i : ℤ) : ℚ)=2*(k : ℚ) := by linarith
      exact_mod_cast he'
    have hm : ((∑i,z i*w i : ℤ) : Binary)=0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ⟨k,he⟩
    change (∑i,c i*residue z i)=0
    rw [←hw]
    simpa [residue,Int.cast_sum,Int.cast_mul,mul_comm] using hm
  · intro hz w hw
    have he := hz (residue w) hw
    have hm : ((∑i,z i*w i : ℤ) : Binary)=0 := by
      simpa [dotProductBilin,dotProduct,residue,Int.cast_sum,Int.cast_mul,mul_comm] using he
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hm
    refine ⟨k,?_⟩
    rw [half_pairing,hk]
    push_cast
    ring

/-- The dual of K(C) is one half of K(C-perp). -/
theorem mem_dual_iff_half_dualCode (C : Code (ι:=ι)) (y : ι → ℚ) :
    MemDual C y ↔ ∃z : ι → ℤ,residue z∈dualCode C ∧ half z=y := by
  constructor
  · intro hy
    obtain ⟨z,rfl⟩ := dual_half_coordinates C y hy
    exact ⟨z,(half_mem_dual_iff C z).mp hy,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact (half_mem_dual_iff C z).mpr hz

theorem mem_dual_iff_twice_mem (C : Code (ι:=ι)) (y : ι → ℚ) :
    MemDual C y ↔ MemGlue (dualCode C) (fun i => 2*y i) := by
  rw [mem_dual_iff_half_dualCode]
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨z,hz,?_⟩
    ext i
    change (z i : ℚ)=2*((z i : ℚ)/2)
    ring
  · rintro ⟨z,hz,he⟩
    refine ⟨z,hz,?_⟩
    ext i
    have hi := congrFun he i
    change (z i : ℚ)=2*y i at hi
    change (z i : ℚ)/2=y i
    linarith

/-- For a self-dual binary code, K(C)*=(1/2)K(C). -/
theorem selfDual_mem_dual_iff_twice_mem (C : Code (ι:=ι)) (hC : dualCode C=C)
    (y : ι → ℚ) : MemDual C y ↔ MemGlue C (fun i => 2*y i) := by
  rw [mem_dual_iff_twice_mem,hC]

end Atlas.Lattices.BinaryGlue
