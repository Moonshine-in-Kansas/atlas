import Atlas.Fischer.ReflectingRayFamily

noncomputable section
namespace Atlas.Fischer

/-- Actual images in normalized ray space, not merely parameter sets. -/
def BasicReflectingRay := Set.range (fun i => rootRay (basicAxis i))
def OctadicReflectingRay := Set.range (fun t : OctadicRootParameter =>
  rootRay (octadicRoot (chosenOctadCalibration t.1) t.2))
def DuadicReflectingRay := Set.range (fun t : DuadicRootParameter =>
  rootRay (chosenDuadicRoot t.1 t.2))

theorem basicReflectingRay_card : Nat.card BasicReflectingRay = 24 := by
  rw [BasicReflectingRay, ← Nat.card_congr
    (Equiv.ofInjective (fun i => rootRay (basicAxis i)) basicAxis_ray_injective)]
  exact basicRootParameter_card

theorem octadicReflectingRay_card : Nat.card OctadicReflectingRay = 24288 := by
  rw [OctadicReflectingRay, ← Nat.card_congr
    (Equiv.ofInjective (fun t : OctadicRootParameter =>
      rootRay (octadicRoot (chosenOctadCalibration t.1) t.2)) octadicParameter_ray_injective)]
  exact octadicRootParameter_card

theorem duadicReflectingRay_card : Nat.card DuadicReflectingRay = 282624 := by
  rw [DuadicReflectingRay, ← Nat.card_congr
    (Equiv.ofInjective (fun t : DuadicRootParameter => rootRay (chosenDuadicRoot t.1 t.2))
      (duadicParameter_ray_injective chosenDuadicRoot_injective))]
  exact duadicRootParameter_card

theorem basic_octadic_ray_images_disjoint : Disjoint BasicReflectingRay OctadicReflectingRay := by
  apply Set.disjoint_left.mpr
  rintro x ⟨i, rfl⟩ ⟨t, ht⟩
  exact basic_octadic_rays_ne i (chosenOctadCalibration t.1) t.2 ht.symm

theorem basic_duadic_ray_images_disjoint : Disjoint BasicReflectingRay DuadicReflectingRay := by
  apply Set.disjoint_left.mpr
  rintro x ⟨i, rfl⟩ ⟨t, ht⟩
  exact basic_chosenDuadic_rays_ne i t.1 t.2 ht.symm

theorem octadic_duadic_ray_images_disjoint : Disjoint OctadicReflectingRay DuadicReflectingRay := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s, rfl⟩ ⟨t, ht⟩
  exact octadic_chosenDuadic_rays_ne (chosenOctadCalibration s.1) s.2 t.1 t.2 ht.symm

end Atlas.Fischer
