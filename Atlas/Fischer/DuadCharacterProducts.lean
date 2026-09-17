import Atlas.Fischer.DuadProductCocodeAction
import Atlas.Fischer.ReflectingRoots

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Reparametrize the actual product family by the full dual of C_p. This
introduces no coordinate formula, injectivity, or additional root model. -/
def duadCharacterProduct (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (ξ : Module.Dual Bit (duadShortenedCode p)) : Coordinates :=
  let v := (duadCharacterEquiv p hp F G hFG).symm ξ
  duadOctadicProduct Q R v.1 v.2

@[simp] theorem duadCharacterProduct_equiv (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) :
    duadCharacterProduct p hp F G hFG Q R (duadCharacterEquiv p hp F G hFG (χ,ψ))=
      duadOctadicProduct Q R χ ψ := by
  simp [duadCharacterProduct]

/-- The restriction translation on characters agrees with actual cocode action
on the product vectors, before any distinctness theorem is used. -/
theorem duadCharacterProduct_cocode (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (d : Cocode) (ξ : Module.Dual Bit (duadShortenedCode p)) :
    parkerCoordinateAction (parkerCocodeStandard d) (duadCharacterProduct p hp F G hFG Q R ξ)=
      duadCharacterProduct p hp F G hFG Q R (duadCocodeCharacterAction p d ξ) := by
  have he : (duadCharacterEquiv p hp F G hFG).symm (duadCocodeRestriction p d)=
      (octadCocodeRestriction F d,octadCocodeRestriction G d) := by
    rw [← duadCharacterEquiv_cocode p hp F G hFG d,LinearEquiv.symm_apply_apply]
  simp only [duadCharacterProduct,duadCocodeCharacterAction,map_add,he,
    Prod.fst_add,Prod.snd_add,parkerCocodeAction_duadOctadicProduct]

/-- Every actual product vector is reflecting. -/
theorem duadCharacterProduct_isReflectingRoot (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    IsReflectingRoot (duadCharacterProduct p hp F G hFG Q R ξ) :=
  duadOctadicProduct_algebra_package (hFG ▸ hp) Q R _ _

/-- The actual cocode acts transitively on the image of the parameterized product
family; this does not assert that its parameters are distinct. -/
theorem duadCharacterProduct_transitive (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (ξ μ : Module.Dual Bit (duadShortenedCode p)) :
    ∃ d : Cocode, parkerCoordinateAction (parkerCocodeStandard d)
      (duadCharacterProduct p hp F G hFG Q R ξ)=duadCharacterProduct p hp F G hFG Q R μ := by
  obtain ⟨d,hd⟩ := duadCocodeCharacterAction_transitive p ξ μ
  exact ⟨d,by rw [duadCharacterProduct_cocode,hd]⟩

/-- The annihilator fixes every actual product vector. The converse is deliberately
not part of this theorem and requires the separate coefficient/distinctness proof. -/
theorem duadCharacterProduct_annihilator_fixed (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (d : Cocode) (hd : d ∈ duadCocodeAnnihilator p)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    parkerCoordinateAction (parkerCocodeStandard d)
      (duadCharacterProduct p hp F G hFG Q R ξ)=duadCharacterProduct p hp F G hFG Q R ξ := by
  rw [duadCharacterProduct_cocode,(duadCocodeCharacterAction_kernel p d).mpr hd ξ]

/-- The dual reparametrization has exactly the original pair-product image. -/
theorem duadCharacterProduct_range (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    Set.range (duadCharacterProduct p hp F G hFG Q R)=
      Set.range (fun v : OctadicCharacter F × OctadicCharacter G =>
        duadOctadicProduct Q R v.1 v.2) := by
  ext x
  constructor
  · rintro ⟨ξ,rfl⟩
    exact ⟨(duadCharacterEquiv p hp F G hFG).symm ξ,rfl⟩
  · rintro ⟨⟨χ,ψ⟩,rfl⟩
    exact ⟨duadCharacterEquiv p hp F G hFG (χ,ψ),duadCharacterProduct_equiv p hp F G hFG Q R χ ψ⟩

/-- Transitivity stated on the actual vector image, without injectivity. -/
theorem duadCharacterProduct_range_transitive (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    {x y : Coordinates} (hx : x ∈ Set.range (duadCharacterProduct p hp F G hFG Q R))
    (hy : y ∈ Set.range (duadCharacterProduct p hp F G hFG Q R)) :
    ∃ d : Cocode, parkerCoordinateAction (parkerCocodeStandard d) x=y := by
  obtain ⟨ξ,rfl⟩ := hx
  obtain ⟨μ,rfl⟩ := hy
  exact duadCharacterProduct_transitive p hp F G hFG Q R ξ μ

end Atlas.Fischer
