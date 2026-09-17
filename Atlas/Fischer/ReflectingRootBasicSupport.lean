import Atlas.Fischer.DuadicPointRays
import Atlas.Fischer.AxisSums
import Atlas.Fischer.ProductMaps

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem hermitian_basicAxis_coordinates (i : Omega) (x : Coordinates) :
    hermitian (basicAxis i) x = star (rootAxisSum x) / 8 - star (x (.inl i)) := by
  rw [basicAxis_eq, hermitian_sub_left, hermitian_smul_left]
  simp only [axisSum, hermitian_sum_left, u, hermitian_coordinateVector_left,
    coordinateWeight, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [← Finset.mul_sum]
  simp only [rootAxisSum, star_sum]
  ring

theorem hermitian_basicAxis_basicAxis (i j : Omega) :
    hermitian (basicAxis i) (basicAxis j) = if i=j then 9 else 1 := by
  rw [hermitian_basicAxis_coordinates, rootAxisSum_basic]
  by_cases h : i=j <;> norm_num [basicAxis,h]

theorem hermitian_basicAxis_octadic (i : Omega) {O : Octad}
    (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    hermitian (basicAxis i) (octadicRoot Q χ) = if i ∈ O.val then 1 else 0 := by
  rw [hermitian_basicAxis_coordinates,rootAxisSum_octadic,octadicRoot_axis_coefficient]
  split_ifs <;> norm_num

theorem hermitian_basicAxis_duadic (i : Omega) (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    hermitian (basicAxis i) (chosenDuadicRoot p ξ) = if i ∈ p.val then 1 else 0 := by
  rw [hermitian_basicAxis_coordinates,chosenDuadicRoot_axisSum,chosenDuadicRoot_axis_coefficient]
  split_ifs <;> norm_num

theorem basic_octadic_support {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) :
    {i : Omega | hermitian (basicAxis i) (octadicRoot Q χ) ≠ 0} = O.val := by
  ext i
  simp [hermitian_basicAxis_octadic]

theorem basic_duadic_support (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    {i : Omega | hermitian (basicAxis i) (chosenDuadicRoot p ξ) ≠ 0} = p.val := by
  ext i
  simp [hermitian_basicAxis_duadic]

end Atlas.Fischer
