import Atlas.Fischer.ParkerSections
import Mathlib.FieldTheory.Finite.Basic

namespace Atlas.Fischer
open Atlas.Codes
namespace ParkerSection
variable {K : ParkerElementarySubcode}

noncomputable instance : Fintype K.code := Fintype.ofFinite K.code
noncomputable instance : Fintype (Module.Dual Bit K.code) := Fintype.ofInjective (fun l : Module.Dual Bit K.code => (l : K.code → Bit)) DFunLike.coe_injective
noncomputable instance : Fintype (ParkerSection K) :=
  Fintype.ofEquiv (Module.Dual Bit K.code) (chosen K).characterEquiv

theorem card : Nat.card (ParkerSection K) = Nat.card K.code := by
  rw [← Nat.card_congr (chosen K).characterEquiv]
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := Bit) (V := Module.Dual Bit K.code),
    Module.card_eq_pow_finrank (K := Bit) (V := K.code), Subspace.dual_finrank_eq]

def Calibrated (a : K.code) (s : Bit) := {q : ParkerSection K // q.sign a = s}

/-- Each of the two sign fibers has exactly half the sections. This explicit
bijection retains the calibration rather than merely counting complements. -/
noncomputable def calibrationEquiv (a : K.code) (s : Bit)
    (l : Module.Dual Bit K.code) (hl : l a = 1) :
    Calibrated a s × Bit ≃ ParkerSection K where
  toFun p := p.1.val.translate (p.2 • l)
  invFun q := (⟨q.translate ((q.sign a+s) • l), by
    change q.sign a+(q.sign a+s)*l a=s
    rw [hl,mul_one,← add_assoc,CharTwo.add_self_eq_zero,zero_add]⟩,q.sign a+s)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply ParkerSection.ext
      funext b
      change (p.1.val.sign b+p.2*l b)+
        ((p.1.val.sign a+p.2*l a+s)*l b) = p.1.val.sign b
      rw [hl,mul_one,p.1.property]
      have he : s+p.2+s=p.2 := by
        calc
          _ = p.2+(s+s) := by abel
          _ = p.2 := by rw [CharTwo.add_self_eq_zero,add_zero]
      rw [he,add_assoc,CharTwo.add_self_eq_zero,add_zero]
    · change p.1.val.sign a+p.2*l a+s=p.2
      rw [hl,mul_one,p.1.property]
      calc
        _ = p.2+(s+s) := by abel
        _ = p.2 := by rw [CharTwo.add_self_eq_zero,add_zero]
  right_inv q := by
    apply ParkerSection.ext
    funext b
    change (q.sign b+(q.sign a+s)*l b)+(q.sign a+s)*l b=q.sign b
    rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]

theorem calibrated_card_mul_two (a : K.code) (ha : a ≠ 0) (s : Bit) :
    Nat.card (Calibrated a s) * 2 = Nat.card K.code := by
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one Bit ha
  have he := Nat.card_congr (calibrationEquiv a s l hl)
  rw [Nat.card_prod,card] at he
  simpa [Nat.card_eq_fintype_card,Bit,ZMod.card] using he

theorem calibrated_card (a : K.code) (ha : a ≠ 0) (s : Bit) :
    Nat.card (Calibrated a s) = Nat.card K.code / 2 := by
  have h := calibrated_card_mul_two a ha s
  omega

end ParkerSection
end Atlas.Fischer
