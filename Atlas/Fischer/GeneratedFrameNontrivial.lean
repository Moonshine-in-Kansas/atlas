import Atlas.Fischer.OctadicGeneratedFrameTranslation
import Atlas.Fischer.BasicOctadicRays

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual four-dimensional affine direction space has a nonzero direction. -/
theorem octadTranslationSpace_exists_ne_zero (O : Octad) :
    ∃ t : OctadTranslationSpace O, t ≠ 0 := by
  let v : Fin 4 → Bit := fun _ => 1
  refine ⟨(octadDirectionCoordinates O).symm v,?_⟩
  intro h
  have he := congrArg (octadDirectionCoordinates O) h
  rw [LinearEquiv.apply_symm_apply,map_zero] at he
  have hh := congrFun he 0
  exact one_ne_zero hh

/-- A nontrivial actual generated symmetry of the standard frame is supplied
by two octadic reflections, independently of any group-order or H-generation proof. -/
theorem rootGenerated_basicFrame_nontrivial (O : Octad) :
    ∃ e : SemilinearAlgebraAutomorphism, e ∈ rootGeneratedAlgebraGroup ∧
      e ∈ basicFrameStabilizer ∧ ∃ i : Omega,
      rootRay (e.val (basicAxis i)) ≠ rootRay (basicAxis i) := by
  classical
  obtain ⟨t,ht⟩ := octadTranslationSpace_exists_ne_zero O
  have hp : (0 : OctadicCharacter O) (octadShortenedOne O)=t.val (octadShortenedOne O) := by
    exact t.property.symm
  have hd : octadicPhaseDifference O 0 t.val hp=t := by
    apply Subtype.ext
    exact zero_add _
  let σ := octadicFrameTranslation O t
  have hσ : σ ≠ 1 := octadicFrameTranslation_nontrivial O t ht
  have hmove : ∃ i, σ i ≠ i := by
    by_contra hn
    push_neg at hn
    apply hσ
    exact Equiv.ext hn
  obtain ⟨i,hi⟩ := hmove
  refine ⟨octadicGeneratedPhasePair O 0 t.val,octadicGeneratedPhasePair_mem _ _ _,
    octadicGeneratedPhasePair_frame _ _ _ hp,i,?_⟩
  rw [octadicGeneratedPhasePair_basic O 0 t.val hp,hd]
  intro h
  exact hi (basicAxis_ray_injective h)

end Atlas.Fischer
