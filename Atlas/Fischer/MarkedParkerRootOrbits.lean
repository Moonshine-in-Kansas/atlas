import Atlas.Fischer.MarkedOctadSupportOrbits
import Atlas.Fischer.MarkedDuadSupportOrbits
import Atlas.Fischer.ParkerRootFibreTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual Parker subgroup fixing a marked coordinate subset pointwise. -/
def parkerMarkedSubset (T : Finset Omega) : Subgroup ParkerStandardGroup :=
  (fixingSubgroup Mathieu24CodeModel (T : Set Omega)).comap parkerStandardProjection

theorem mem_parkerMarkedSubset_iff (T : Finset Omega) (e : ParkerStandardGroup) :
    e∈parkerMarkedSubset T ↔ ∀ i∈T,(parkerStandardProjection e).val i=i :=
  mem_fixingSubgroup_iff Mathieu24CodeModel

/-- All actual octadic roots with S inside and x outside form one orbit under
the actual Parker subgroup fixing S and x pointwise. -/
theorem markedParker_octadicRoot_transitive (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (O P : Octad) (hSO : S ⊆ O.val) (hSP : S ⊆ P.val)
    (hxO : x∉O.val) (hxP : x∉P.val) (Q : OctadCalibration O) (R : OctadCalibration P)
    (χ : OctadicCharacter O) (ψ : OctadicCharacter P) :
    ∃ e : parkerMarkedSubset (insert x S),
      parkerCoordinateAction e.val (octadicRoot Q χ)=octadicRoot R ψ := by
  obtain ⟨g,hg,hfix,hx⟩ := mathieu_marked_octad_transitive S hS x O P hSO hSP hxO hxP
  obtain ⟨e,he⟩ := parkerStandardProjection_surjective g
  have hOP : parkerOctadAction e O=P := by
    apply Subtype.ext
    change permuteBlock (parkerStandardProjection e).val O.val=P.val
    rw [he]
    exact congrArg Subtype.val hg
  obtain ⟨f,hf,hroot⟩ := octadicRoot_parker_transport_with_projection e Q R hOP χ ψ
  refine ⟨⟨f,?_⟩,hroot⟩
  rw [mem_parkerMarkedSubset_iff,hf,he]
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact hx
  · exact hfix i hi

/-- All actual chosen duadic roots with S inside and x outside form one orbit
under this same marked Parker subgroup, retaining the actual product model. -/
theorem markedParker_duadicRoot_transitive (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (p q : RootDuad) (hSp : S ⊆ p.val) (hSq : S ⊆ q.val)
    (hxp : x∉p.val) (hxq : x∉q.val)
    (ξ : Module.Dual Bit (duadShortenedCode p.val))
    (η : Module.Dual Bit (duadShortenedCode q.val)) :
    ∃ e : parkerMarkedSubset (insert x S),
      parkerCoordinateAction e.val (chosenDuadicRoot p ξ)=chosenDuadicRoot q η := by
  obtain ⟨g,hg,hfix,hx⟩ := mathieu_marked_duad_transitive S hS x p q hSp hSq hxp hxq
  obtain ⟨e,he⟩ := parkerStandardProjection_surjective g
  obtain ⟨f,hf,hroot⟩ := chosenDuadicRoot_parker_transport_with_projection e p q (by rw [he];exact hg) ξ η
  refine ⟨⟨f,?_⟩,hroot⟩
  rw [mem_parkerMarkedSubset_iff,hf,he]
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact hx
  · exact hfix i hi

end Atlas.Fischer
