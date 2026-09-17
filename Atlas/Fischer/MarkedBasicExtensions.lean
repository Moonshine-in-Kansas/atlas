import Atlas.Fischer.ReflectingFamilyMoments
import Atlas.Fischer.ReflectingRootBasicSupport
import Mathlib.Logic.Equiv.Sum

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual rays different from each marked basic ray and having nonzero pairing
with every marked basic representative. No tuple homogeneity is assumed. -/
def IsMarkedBasicExtension (S : Finset Omega) (t : ReflectingRootParameter) : Prop :=
  ∀ i ∈ S, reflectingRootParameterRay t ≠ rootRay (basicAxis i) ∧
    hermitian (basicAxis i) (reflectingRootParameterVector t) ≠ 0

abbrev MarkedBasicExtension (S : Finset Omega) :=
  {t : ReflectingRootParameter // IsMarkedBasicExtension S t}

theorem markedBasicExtension_basic (S : Finset Omega) (j : Omega) :
    IsMarkedBasicExtension S (.inl j) ↔ j ∉ S := by
  classical
  constructor
  · intro h hj
    exact (h j hj).1 rfl
  · intro hj i hi
    refine ⟨?_, ?_⟩
    · intro h
      exact hj ((basicAxis_ray_injective h) ▸ hi)
    · change hermitian (basicAxis i) (basicAxis j) ≠ 0
      rw [hermitian_basicAxis_basicAxis]
      split_ifs <;> norm_num

theorem markedBasicExtension_octadic (S : Finset Omega) (t : OctadicRootParameter) :
    IsMarkedBasicExtension S (.inr (.inl t)) ↔ S ⊆ t.1.val := by
  classical
  constructor
  · intro h i hi
    have hh := (h i hi).2
    change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration t.1) t.2) ≠ 0 at hh
    simpa only [hermitian_basicAxis_octadic, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] using hh
  · intro h i hi
    exact ⟨(basic_octadic_rays_ne i _ _).symm,
      by change hermitian (basicAxis i) (octadicRoot (chosenOctadCalibration t.1) t.2) ≠ 0
         rw [hermitian_basicAxis_octadic, if_pos (h hi)]; norm_num⟩

theorem markedBasicExtension_duadic (S : Finset Omega) (t : DuadicRootParameter) :
    IsMarkedBasicExtension S (.inr (.inr t)) ↔ S ⊆ t.1.val := by
  classical
  constructor
  · intro h i hi
    have hh := (h i hi).2
    change hermitian (basicAxis i) (chosenDuadicRoot t.1 t.2) ≠ 0 at hh
    by_contra hn
    rw [hermitian_basicAxis_duadic, if_neg hn] at hh
    exact hh rfl
  · intro h i hi
    exact ⟨(basic_chosenDuadic_rays_ne i _ _).symm,
      by change hermitian (basicAxis i) (chosenDuadicRoot t.1 t.2) ≠ 0
         rw [hermitian_basicAxis_duadic, if_pos (h hi)]; norm_num⟩

/-- Exact decomposition into the three actual geometric parameter families. -/
def markedBasicExtensionEquiv (S : Finset Omega) : MarkedBasicExtension S ≃
    {i : Omega // i ∉ S} ⊕
      ((Σ O : {O : Octad // S ⊆ O.val}, OctadicCharacter O.val) ⊕
        (Σ p : {p : RootDuad // S ⊆ p.val}, Module.Dual Bit (duadShortenedCode p.val.val))) :=
  Equiv.subtypeSum.trans (Equiv.sumCongr
    (Equiv.subtypeEquivRight (markedBasicExtension_basic S))
    (Equiv.subtypeSum.trans (Equiv.sumCongr
      ((Equiv.subtypeEquivRight (markedBasicExtension_octadic S)).trans
        (Equiv.subtypeSigmaEquiv (fun O : Octad => OctadicCharacter O) (fun O => S ⊆ O.val)))
      ((Equiv.subtypeEquivRight (markedBasicExtension_duadic S)).trans
        (Equiv.subtypeSigmaEquiv (fun p : RootDuad => Module.Dual Bit (duadShortenedCode p.val))
          (fun p => S ⊆ p.val))))))

end Atlas.Fischer
