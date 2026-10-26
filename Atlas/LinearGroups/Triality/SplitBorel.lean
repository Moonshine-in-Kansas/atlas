import Atlas.LinearGroups.Triality.BorelStructure

/-! The split exact sequence U → B → Kˣ×Fˣ for the actual Borel. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def borelTorusCoordinate (b : borel F K hdeg) : Kˣ × Fˣ := ((borelCoordinates F K hdeg).symm b).2

theorem borelTorusCoordinate_word (p : PositiveParameters F K) (h : Kˣ × Fˣ) :
    borelTorusCoordinate F K hdeg (borelCoordinates F K hdeg (p,h))=h := by
  simp [borelTorusCoordinate]

def borelProjection : borel F K hdeg →* Kˣ × Fˣ where
  toFun := borelTorusCoordinate F K hdeg
  map_one' := by
    have he : (1 : borel F K hdeg)=borelCoordinates F K hdeg (⟨0,0,0,0,0,0⟩,1) := by
      apply Subtype.ext
      simp [borelCoordinates,borelWord,positiveMatrix_zero]
    rw [he,borelTorusCoordinate_word]
  map_mul' b c := by
    obtain ⟨⟨p,h⟩,rfl⟩ := (borelCoordinates F K hdeg).surjective b
    obtain ⟨⟨r,k⟩,rfl⟩ := (borelCoordinates F K hdeg).surjective c
    have he : borelCoordinates F K hdeg (p,h)*borelCoordinates F K hdeg (r,k)=
        borelCoordinates F K hdeg (positiveCollect F K p (torusScale F K h r),h*k) := by
      apply Subtype.ext
      exact borelWord_mul F K hdeg p r h k
    rw [he,borelTorusCoordinate_word,borelTorusCoordinate_word,borelTorusCoordinate_word]

def borelSection : (Kˣ × Fˣ) →* borel F K hdeg where
  toFun h := ⟨torusMap F K h,torus_le_borel F K hdeg ⟨h,rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' h k := Subtype.ext (map_mul _ _ _)

theorem borelProjection_section : Function.LeftInverse (borelProjection F K hdeg) (borelSection F K hdeg) := by
  intro h
  have he : borelSection F K hdeg h=borelCoordinates F K hdeg (⟨0,0,0,0,0,0⟩,h) := by
    apply Subtype.ext
    simp [borelSection,borelCoordinates,borelWord,positiveMatrix_zero]
  rw [he]
  exact borelTorusCoordinate_word F K hdeg _ h

theorem borelProjection_kernel : (borelProjection F K hdeg).ker=
    (unipotent F K hdeg).subgroupOf (borel F K hdeg) := by
  ext b
  obtain ⟨⟨p,h⟩,rfl⟩ := (borelCoordinates F K hdeg).surjective b
  change borelTorusCoordinate F K hdeg (borelCoordinates F K hdeg (p,h))=1 ↔
    borelWord F K p h ∈ unipotent F K hdeg
  rw [borelTorusCoordinate_word]
  constructor
  · rintro rfl
    exact ⟨p,by simp [borelWord]⟩
  · rintro ⟨r,hr⟩
    have he : borelWord F K r 1=borelWord F K p h := by simpa [borelWord] using hr
    have hh : (r,(1 : Kˣ × Fˣ))=(p,h) := by apply borelWord_injective F K; exact he
    exact (congrArg (fun x : PositiveParameters F K × (Kˣ × Fˣ) => x.2) hh).symm

end Atlas.Triality
