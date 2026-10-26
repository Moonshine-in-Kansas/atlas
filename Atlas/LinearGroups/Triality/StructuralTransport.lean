import Atlas.LinearGroups.Triality.CubicFieldTransport
import Atlas.LinearGroups.Triality.ParabolicAction

/-! Transport of positive coordinates, torus, Borel and parabolics. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {F E K L : Type*} [Field F] [Field E] [Field K] [Field L]
  [Finite F] [Finite E] [Finite K] [Finite L] [Algebra F K] [Algebra E L]
variable (eF : F ≃+* E) (eK : K ≃+* L)
  (hcompat : ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t))

include eF hcompat

theorem fieldEquiv_nextShortRoot (t : K) :
    fieldEquivFullD eK (nextShortRoot F K t)=nextShortRoot E L (eK t) := by
  simp [nextShortRoot,map_mul,fieldEquiv_differenceRoot,fieldEquiv_sumRoot,
    fieldEquiv_sigma eK (Nat.card_congr eF.toEquiv),hcompat]

theorem fieldEquiv_middleRoot (t : K) :
    fieldEquivFullD eK (middleRoot F K t)=middleRoot E L (eK t) := by
  simp [middleRoot,map_mul,fieldEquiv_differenceRoot,fieldEquiv_sumRoot,
    fieldEquiv_sigma eK (Nat.card_congr eF.toEquiv),hcompat]

theorem fieldEquiv_highLongRoot (t : F) :
    fieldEquivFullD eK (highLongRoot F K t)=highLongRoot E L (eF t) := by
  simp [highLongRoot,map_mul,fieldEquiv_differenceRoot,fieldEquiv_sumRoot,
    fieldEquiv_sigma eK (Nat.card_congr eF.toEquiv),hcompat]

theorem fieldEquiv_highestRoot (t : F) :
    fieldEquivFullD eK (highestRoot F K t)=highestRoot E L (eF t) := by
  simp [highestRoot,map_mul,fieldEquiv_differenceRoot,fieldEquiv_sumRoot,
    fieldEquiv_sigma eK (Nat.card_congr eF.toEquiv),hcompat]

def transportParameters (p : PositiveParameters F K) : PositiveParameters E L :=
  ⟨eK p.a,eF p.b,eK p.c,eK p.d,eF p.u,eF p.v⟩

theorem fieldEquiv_positiveMatrix (p : PositiveParameters F K) :
    fieldEquivFullD eK (positiveMatrix F K p)=positiveMatrix E L (transportParameters eF eK p) := by
  simp only [positiveMatrix,positiveWord,map_mul,fieldEquiv_shortRoot eK (Nat.card_congr eF.toEquiv),
    fieldEquiv_longRoot eF eK hcompat,fieldEquiv_nextShortRoot eF eK hcompat,
    fieldEquiv_middleRoot eF eK hcompat,fieldEquiv_highLongRoot eF eK hcompat,
    fieldEquiv_highestRoot eF eK hcompat,transportParameters]

def transportTorus (h : Kˣ × Fˣ) : Lˣ × Eˣ :=
  (Units.mapEquiv eK.toMulEquiv h.1,Units.mapEquiv eF.toMulEquiv h.2)

theorem fieldEquiv_torusMap (h : Kˣ × Fˣ) :
    fieldEquivFullD eK (torusMap F K h)=torusMap E L (transportTorus eF eK h) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  change eK ((torusMap F K h).val (fun k => eK.symm (x k)) i)=
    (torusMap E L (transportTorus eF eK h)).val x i
  rcases i with i|i <;> fin_cases i <;>
    simp [torusMap,torusWeights,diagonalEmbedding,diagonalLinear,transportTorus,
      sigmaUnit,baseUnit,fieldEquiv_sigma eK (Nat.card_congr eF.toEquiv),hcompat]

theorem fieldEquiv_borelWord (p : PositiveParameters F K) (h : Kˣ × Fˣ) :
    fieldEquivFullD eK (borelWord F K p h)=
      borelWord E L (transportParameters eF eK p) (transportTorus eF eK h) := by
  simp only [borelWord,map_mul,fieldEquiv_positiveMatrix eF eK hcompat,fieldEquiv_torusMap eF eK hcompat]

theorem fieldEquiv_borel (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) :
    (borel F K hK).map (fieldEquivFullD eK).toMonoidHom=borel E L hL := by
  ext g
  constructor
  · rintro ⟨b,⟨⟨p,h⟩,rfl⟩,rfl⟩
    exact ⟨(transportParameters eF eK p,transportTorus eF eK h),
      (fieldEquiv_borelWord eF eK hcompat p h).symm⟩
  · rintro ⟨⟨p,h⟩,rfl⟩
    let p' := transportParameters eF.symm eK.symm p
    let h' := transportTorus eF.symm eK.symm h
    refine ⟨borelWord F K p' h',⟨(p',h'),rfl⟩,?_⟩
    change fieldEquivFullD eK (borelWord F K p' h')=_
    rw [fieldEquiv_borelWord eF eK hcompat]
    have hp : transportParameters eF eK p'=p := by cases p; simp [p',transportParameters]
    have hh : transportTorus eF eK h'=h := by
      ext <;> simp [h',transportTorus]
    rw [hp,hh]

theorem fieldEquiv_shortWeyl : fieldEquivFullD eK (shortWeyl F K)=shortWeyl E L := by
  simp [shortWeyl,fieldEquiv_shortRoot eK (Nat.card_congr eF.toEquiv),
    fieldEquiv_shortNegativeRoot eK (Nat.card_congr eF.toEquiv)]

theorem fieldEquiv_longWeyl : fieldEquivFullD eK (longWeyl F K)=longWeyl E L := by
  simp [longWeyl,fieldEquiv_longRoot eF eK hcompat,fieldEquiv_longNegativeRoot eF eK hcompat]

theorem fieldEquiv_shortParabolic (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) :
    (shortParabolic F K hK).map (fieldEquivFullD eK).toMonoidHom=shortParabolic E L hL := by
  rw [shortParabolic,Subgroup.map_sup,fieldEquiv_borel eF eK hcompat hK hL,
    MonoidHom.map_closure]
  simp only [Set.image_singleton,MulEquiv.coe_toMonoidHom,fieldEquiv_shortWeyl eF eK hcompat]
  rfl

theorem fieldEquiv_longParabolic (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) :
    (longParabolic F K hK).map (fieldEquivFullD eK).toMonoidHom=longParabolic E L hL := by
  rw [longParabolic,Subgroup.map_sup,fieldEquiv_borel eF eK hcompat hK hL,
    MonoidHom.map_closure]
  simp only [Set.image_singleton,MulEquiv.coe_toMonoidHom,fieldEquiv_longWeyl eF eK hcompat]
  rfl

end Atlas.Triality
