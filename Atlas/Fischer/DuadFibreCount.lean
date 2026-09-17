import Atlas.Fischer.DuadProductInjectivity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual vector image of the chosen-pair product construction. -/
def DuadProductFibre (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :=
  Set.range (duadCharacterProduct p hp F G hFG Q R)

/-- Exact fibre size from the proved character injection, independently of
any absolute bound or global reflecting-ray classification. -/
theorem duadProductFibre_card (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    Nat.card (DuadProductFibre p hp F G hFG Q R)=1024 := by
  have h := Nat.card_congr (Equiv.ofInjective (duadCharacterProduct p hp F G hFG Q R)
    (duadCharacterProduct_injective p hp F G hFG Q R))
  exact h.symm.trans (duadCharacters_card p hp)

/-- The actual cocode action has exactly the shortened-duad annihilator as
its kernel on the vector fibre. -/
theorem duadProductFibre_cocode_kernel (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G) (d : Cocode) :
    (∀ ξ, parkerCoordinateAction (parkerCocodeStandard d)
      (duadCharacterProduct p hp F G hFG Q R ξ)=duadCharacterProduct p hp F G hFG Q R ξ) ↔
    d ∈ duadCocodeAnnihilator p := by
  constructor
  · intro h
    apply (duadCocodeCharacterAction_kernel p d).mp
    intro ξ
    apply duadCharacterProduct_injective p hp F G hFG Q R
    rw [← duadCharacterProduct_cocode]
    exact h ξ
  · intro h ξ
    exact duadCharacterProduct_annihilator_fixed p hp F G hFG Q R d h ξ

/-- Every point stabilizer for the transitive cocode action is this same
four-element annihilator; equality is proved on actual product vectors. -/
theorem duadProductFibre_cocode_stabilizer (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G) (d : Cocode)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    parkerCoordinateAction (parkerCocodeStandard d) (duadCharacterProduct p hp F G hFG Q R ξ)=
      duadCharacterProduct p hp F G hFG Q R ξ ↔ d ∈ duadCocodeAnnihilator p := by
  rw [duadCharacterProduct_cocode]
  constructor
  · intro h
    have he := duadCharacterProduct_injective p hp F G hFG Q R h
    have hz : duadCocodeRestriction p d=0 := by
      simpa [duadCocodeCharacterAction] using he
    exact hz
  · intro h
    have he := (duadCocodeCharacterAction_kernel p d).mpr h ξ
    rw [he]

theorem duadProductFibre_cocode_kernel_card (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    Nat.card {d : Cocode // ∀ ξ, parkerCoordinateAction (parkerCocodeStandard d)
      (duadCharacterProduct p hp F G hFG Q R ξ)=duadCharacterProduct p hp F G hFG Q R ξ}=4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun d =>
    duadProductFibre_cocode_kernel p hp F G hFG Q R d))]
  exact duadCocodeAnnihilator_card p hp

theorem duadProductFibre_cocode_stabilizer_card (p : Finset Omega) (hp : p.card=2)
    (F G : Octad) (hFG : F.val ∩ G.val=p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    Nat.card {d : Cocode // parkerCoordinateAction (parkerCocodeStandard d)
      (duadCharacterProduct p hp F G hFG Q R ξ)=duadCharacterProduct p hp F G hFG Q R ξ}=4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun d =>
    duadProductFibre_cocode_stabilizer p hp F G hFG Q R d ξ))]
  exact duadCocodeAnnihilator_card p hp

end Atlas.Fischer

