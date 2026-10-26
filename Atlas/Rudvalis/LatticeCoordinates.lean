import Atlas.Rudvalis.QuaternaryMinimum
import Mathlib.Data.Rat.Cast.Order

/-! Version 33 Construction A in exact rational coordinates: L={z/2 : z mod4∈C}. -/
namespace Atlas.Rudvalis
open scoped BigOperators

abbrev IntegerCoordinates := Coordinate→ℤ
abbrev RationalSpace := Coordinate→ℚ

def reduceModFour : IntegerCoordinates →ₗ[ℤ] QuaternaryWord where
  toFun z i := (z i : ZMod 4)
  map_add' z w := by ext i; simp
  map_smul' a z := by ext i; simp

noncomputable def doubledLattice : Submodule ℤ IntegerCoordinates :=
  (quaternaryCode.restrictScalars ℤ).comap reduceModFour

def halfCoordinates : IntegerCoordinates →ₗ[ℤ] RationalSpace where
  toFun z i := (z i : ℚ)/2
  map_add' z w := by ext i; simp [add_div]
  map_smul' a z := by ext i; simp [mul_div_assoc]

noncomputable def rudvalisLattice : Submodule ℤ RationalSpace := doubledLattice.map halfCoordinates

theorem doubledLattice_mem (z : IntegerCoordinates) :
    z∈doubledLattice ↔ reduceModFour z∈quaternaryCode := Iff.rfl

theorem rudvalisLattice_mem (v : RationalSpace) : v∈rudvalisLattice ↔
    ∃ z : IntegerCoordinates, reduceModFour z∈quaternaryCode ∧ halfCoordinates z=v := Iff.rfl

theorem halfCoordinates_injective : Function.Injective halfCoordinates := by
  intro z w h
  funext i
  have he := congrFun h i
  change (z i : ℚ)/2=(w i : ℚ)/2 at he
  have hh : (z i : ℚ)=(w i : ℚ) := by linarith
  exact_mod_cast hh

theorem halfCoordinates_mem (z : IntegerCoordinates) :
    halfCoordinates z∈rudvalisLattice ↔ reduceModFour z∈quaternaryCode := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hz : w=z := halfCoordinates_injective he
    exact hz ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem twice_integer_mem (z : IntegerCoordinates) :
    (fun i => 2*(z i : ℚ))∈rudvalisLattice := by
  refine ⟨(fun i => 4*z i),?_,?_⟩
  · change reduceModFour (fun i => 4*z i)∈quaternaryCode
    have h : reduceModFour (fun i => 4*z i)=0 := by
      ext i
      change ((4*z i : ℤ) : ZMod 4)=0
      rw [Int.cast_mul]
      exact (congrArg (fun a : ZMod 4 => a*(z i : ZMod 4)) (by decide : (4 : ZMod 4)=0)).trans (zero_mul _)
    rw [h]
    exact quaternaryCode.zero_mem
  · ext i
    change ((4*z i : ℤ) : ℚ)/2=2*(z i : ℚ)
    push_cast
    ring

def rationalDot (v w : RationalSpace) : ℚ := ∑ i,v i*w i
def integerDot (z w : IntegerCoordinates) : ℤ := ∑ i,z i*w i

theorem rationalDot_half (z w : IntegerCoordinates) :
    rationalDot (halfCoordinates z) (halfCoordinates w)=(integerDot z w : ℚ)/4 := by
  simp only [rationalDot,halfCoordinates,LinearMap.coe_mk,AddHom.coe_mk,integerDot,
    Int.cast_sum,Int.cast_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

def coordinateMinimum (i : Coordinate) : RationalSpace := Pi.single i 2

theorem coordinateMinimum_mem (i : Coordinate) : coordinateMinimum i∈rudvalisLattice := by
  have h := twice_integer_mem (Pi.single i 1)
  convert h using 1
  funext j
  simp [coordinateMinimum,Pi.single_apply]

theorem coordinateMinimum_norm (i : Coordinate) : rationalDot (coordinateMinimum i) (coordinateMinimum i)=4 := by
  classical
  simp [rationalDot,coordinateMinimum,Pi.single_apply]
  norm_num

theorem doubledLattice_pairing_divisible (z w : IntegerCoordinates)
    (hz : z∈doubledLattice) (hw : w∈doubledLattice) : 4∣integerDot z w := by
  have h := quaternaryCode_self_orthogonal hw (reduceModFour z) hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  simpa [integerDot,Atlas.Codes.Quaternary.quaternaryForm,reduceModFour,dotProduct] using h

theorem rudvalisLattice_integral (v w : RationalSpace)
    (hv : v∈rudvalisLattice) (hw : w∈rudvalisLattice) : ∃ k : ℤ,rationalDot v w=k := by
  obtain ⟨z,hz,rfl⟩ := hv
  obtain ⟨y,hy,rfl⟩ := hw
  obtain ⟨k,hk⟩ := doubledLattice_pairing_divisible z y hz hy
  refine ⟨k,?_⟩
  rw [rationalDot_half,hk]
  push_cast
  ring

theorem rudvalisLattice_even (v : RationalSpace) (hv : v∈rudvalisLattice) :
    ∃ k : ℤ,rationalDot v v=2*(k : ℚ) := by
  obtain ⟨z,hz,rfl⟩ := hv
  obtain ⟨k,hk⟩ := quaternaryCode_integer_norm z hz
  refine ⟨k,?_⟩
  have he : integerDot z z=∑i,z i^2 := by simp [integerDot,pow_two]
  rw [rationalDot_half,he,hk]
  push_cast
  ring

theorem rationalDot_self_nonneg (v : RationalSpace) : 0≤rationalDot v v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

theorem rationalDot_self_eq_zero (v : RationalSpace) : rationalDot v v=0 ↔ v=0 := by
  constructor
  · intro h
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈(Finset.univ : Finset Coordinate)) => mul_self_nonneg (v i))).mp h
    funext i
    exact mul_self_eq_zero.mp (he i (Finset.mem_univ i))
  · rintro rfl
    simp [rationalDot]

end Atlas.Rudvalis
