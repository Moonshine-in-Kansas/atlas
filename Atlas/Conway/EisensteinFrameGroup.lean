import Atlas.Conway.EisensteinFrameOrder
import Atlas.Mathieu.TernaryPhaseAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.TypeTags

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- The full coordinate M11 acts on the six-dimensional code, before the scalar quotient. -/
def eisensteinCodeAction (g : TernaryPureAutomorphism) : MulAut (Multiplicative ternaryGolay) :=
  AddEquiv.toMultiplicative
    (LinearEquiv.ofLinearMap (ternaryPureCodeEnd g) (ternaryPureCodeEnd g⁻¹)
      (by change ternaryPureCodeEnd g * ternaryPureCodeEnd g⁻¹ = 1
          rw [← map_mul,mul_inv_cancel,map_one])
      (by change ternaryPureCodeEnd g⁻¹ * ternaryPureCodeEnd g = 1
          rw [← map_mul,inv_mul_cancel,map_one])).toAddEquiv

def eisensteinCodeActionHom : TernaryPureAutomorphism →* MulAut (Multiplicative ternaryGolay) where
  toFun := eisensteinCodeAction
  map_one' := by
    apply MulEquiv.ext; intro t
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun s : Module.End (ZMod 3) ternaryGolay => s t.toAdd) (map_one ternaryPureCodeEnd))
  map_mul' g h := by
    apply MulEquiv.ext; intro t
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun s : Module.End (ZMod 3) ternaryGolay => s t.toAdd) (map_mul ternaryPureCodeEnd g h))

abbrev EisensteinCodeSemidirect :=
  Multiplicative ternaryGolay ⋊[eisensteinCodeActionHom] TernaryPureAutomorphism

theorem eisensteinCoordinate_phase_conjugation (g : TernaryPureAutomorphism) :
    eisensteinPhaseIsometries.comp (eisensteinCodeActionHom g).toMonoidHom =
      (MulAut.conj (eisensteinCoordinateIsometries g)).toMonoidHom.comp eisensteinPhaseIsometries := by
  apply MonoidHom.ext
  intro t
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  funext i
  change eisensteinToRational (eisensteinPhase (t.toAdd.val (g.val.symm i)))*z i =
    eisensteinToRational (eisensteinPhase (t.toAdd.val (g.val.symm i)))*z (g.val (g.val.symm i))
  rw [Equiv.apply_symm_apply]

def eisensteinCodeSemidirectIsometries : EisensteinCodeSemidirect →* eisensteinHermitianGroup :=
  SemidirectProduct.lift eisensteinPhaseIsometries eisensteinCoordinateIsometries
    eisensteinCoordinate_phase_conjugation

def eisensteinSignCharacter (a : ZMod 2) : ℤ := if a=0 then 1 else -1

theorem eisensteinSignCharacter_add : ∀ a b : ZMod 2,
    eisensteinSignCharacter (a+b) = eisensteinSignCharacter a * eisensteinSignCharacter b := by decide

def eisensteinSignHom : Multiplicative (ZMod 2) →* eisensteinHermitianGroup where
  toFun a := if a.toAdd=0 then 1 else eisensteinSignIsometry
  map_one' := rfl
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    have h : ∀ a b : ZMod 2,
        (if a+b=0 then z else -z) =
          if a=0 then (if b=0 then z else -z) else -(if b=0 then z else -z) := by
      intro a b
      have ha : a=0 ∨ a=1 := by revert a; decide
      have hb : b=0 ∨ b=1 := by revert b; decide
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · simp
      · simp
      · simp
      · rw [show (1 : ZMod 2)+1=0 by decide]
        simp
    have hfun (c : Multiplicative (ZMod 2)) (w : EisensteinRationalCoordinates) :
        (if c.toAdd=0 then (1 : eisensteinHermitianGroup) else eisensteinSignIsometry).val w =
          if c.toAdd=0 then w else -w := by split_ifs <;> rfl
    change (if (a*b).toAdd=0 then (1 : eisensteinHermitianGroup) else eisensteinSignIsometry).val z =
      (if a.toAdd=0 then (1 : eisensteinHermitianGroup) else eisensteinSignIsometry).val
        ((if b.toAdd=0 then (1 : eisensteinHermitianGroup) else eisensteinSignIsometry).val z)
    rw [hfun,hfun,hfun]
    exact h a.toAdd b.toAdd

theorem eisensteinSignHom_commutes (a : Multiplicative (ZMod 2)) (f : eisensteinHermitianGroup) :
    eisensteinSignHom a * f = f * eisensteinSignHom a := by
  by_cases ha : a.toAdd=0
  · have ha' : a=1 := ha
    simp [eisensteinSignHom,ha']
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change (if a.toAdd=0 then 1 else eisensteinSignIsometry).val (f.val z) =
      f.val ((if a.toAdd=0 then 1 else eisensteinSignIsometry).val z)
    simp [ha,eisensteinSignIsometry]

abbrev EisensteinFrameAbstractGroup := Multiplicative (ZMod 2) × EisensteinCodeSemidirect

def eisensteinFrameAbstractHom : EisensteinFrameAbstractGroup →* eisensteinHermitianGroup where
  toFun p := eisensteinSignHom p.1 * eisensteinCodeSemidirectIsometries p.2
  map_one' := by simp
  map_mul' p q := by
    change eisensteinSignHom (p.1*q.1) * eisensteinCodeSemidirectIsometries (p.2*q.2) = _
    rw [map_mul,map_mul]
    calc
      _ = eisensteinSignHom p.1 *
        (eisensteinSignHom q.1 * eisensteinCodeSemidirectIsometries p.2) *
          eisensteinCodeSemidirectIsometries q.2 := by group
      _ = eisensteinSignHom p.1 *
        (eisensteinCodeSemidirectIsometries p.2 * eisensteinSignHom q.1) *
          eisensteinCodeSemidirectIsometries q.2 := by rw [eisensteinSignHom_commutes q.1 (eisensteinCodeSemidirectIsometries p.2)]
      _ = _ := by group

def eisensteinAbstractParameters (p : EisensteinFrameAbstractGroup) : EisensteinMonomialParameters :=
  (decide (p.1.toAdd ≠ 0),p.2.left.toAdd,p.2.right)

theorem eisensteinAbstractParameters_injective : Function.Injective eisensteinAbstractParameters := by
  intro p q he
  have hsign : p.1 = q.1 := by
    change p.1.toAdd = q.1.toAdd
    have hi : Function.Injective (fun a : ZMod 2 => decide (a≠0)) := by decide
    exact hi (congrArg (fun x : EisensteinMonomialParameters => x.1) he)
  have hl : p.2.left = q.2.left :=
    congrArg (fun x : EisensteinMonomialParameters => Multiplicative.ofAdd x.2.1) he
  have hr : p.2.right = q.2.right := congrArg (fun x : EisensteinMonomialParameters => x.2.2) he
  exact Prod.ext hsign (SemidirectProduct.ext hl hr)

theorem eisensteinAbstractParameters_surjective : Function.Surjective eisensteinAbstractParameters := by
  rintro ⟨b,t,g⟩
  refine ⟨(Multiplicative.ofAdd (if b then 1 else 0),⟨Multiplicative.ofAdd t,g⟩),?_⟩
  cases b <;> rfl

theorem eisensteinFrameAbstractHom_parameters (p : EisensteinFrameAbstractGroup) :
    eisensteinFrameAbstractHom p = eisensteinMonomialParameterIsometry (eisensteinAbstractParameters p) := by
  by_cases hp : p.1.toAdd=0
  · have hp' : p.1=1 := hp
    simp [eisensteinFrameAbstractHom,eisensteinAbstractParameters,eisensteinMonomialParameterIsometry,
      eisensteinSignHom,hp,hp',eisensteinCodeSemidirectIsometries,SemidirectProduct.lift,mul_assoc]
  · have hp' : p.1≠1 := hp
    simp [eisensteinFrameAbstractHom,eisensteinAbstractParameters,eisensteinMonomialParameterIsometry,
      eisensteinSignHom,hp,hp',eisensteinCodeSemidirectIsometries,SemidirectProduct.lift,mul_assoc]

def eisensteinFrameGroupHom : EisensteinFrameAbstractGroup →* eisensteinCoordinateFrameStabilizer where
  toFun p := ⟨eisensteinFrameAbstractHom p,by
    rw [eisensteinFrameAbstractHom_parameters]
    exact (eisensteinFrameFromParameters (eisensteinAbstractParameters p)).prop⟩
  map_one' := Subtype.ext (map_one eisensteinFrameAbstractHom)
  map_mul' p q := Subtype.ext (map_mul eisensteinFrameAbstractHom p q)

theorem eisensteinFrameGroupHom_bijective : Function.Bijective eisensteinFrameGroupHom := by
  have he : eisensteinFrameGroupHom = fun p =>
      eisensteinFrameFromParameters (eisensteinAbstractParameters p) := by
    funext p
    exact Subtype.ext (eisensteinFrameAbstractHom_parameters p)
  rw [he]
  exact (show Function.Bijective eisensteinFrameFromParameters from
    ⟨eisensteinFrameFromParameters_injective,eisensteinFrameFromParameters_surjective⟩).comp
      ⟨eisensteinAbstractParameters_injective,eisensteinAbstractParameters_surjective⟩

/-- The full frame stabilizer has exact group structure C2 × (T ⋊ M11),
with the actual ternary code and its full coordinate action. -/
def eisensteinFullFrameGroupEquiv : EisensteinFrameAbstractGroup ≃* eisensteinCoordinateFrameStabilizer :=
  MulEquiv.ofBijective eisensteinFrameGroupHom eisensteinFrameGroupHom_bijective

end Atlas.Conway
