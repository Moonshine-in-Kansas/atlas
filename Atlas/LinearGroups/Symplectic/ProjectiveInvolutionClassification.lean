import Atlas.LinearGroups.Symplectic.InvolutionRepresentativeDimensions

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]
open Atlas.LinearInvolution

theorem negative_mul_square_one (g : Sp n F) (hg : g^2=1) :
    (negativeIdentity*g)^2=1 := by
  apply ext_action
  intro x
  have hx := congrArg (fun z : Sp n F => z • x) hg
  simpa [pow_two,mul_smul] using hx

theorem negative_minus_eq_plus (g : Sp n F) :
    minus (toLinear (negativeIdentity*g)).toLinearMap = plus (toLinear g).toLinearMap := by
  ext x
  simp only [mem_minus,mem_plus,LinearEquiv.coe_coe,toLinear_apply,mul_smul,
    negativeIdentity_apply,neg_inj]

theorem minusDimension_neg_add (g : Sp n F) (hg : g^2=1) (h2 : (2:F) ≠ 0) :
    minusDimension (negativeIdentity*g) + minusDimension g = 2*n := by
  have ht : Function.Involutive (toLinear g).toLinearMap := by
    intro x
    change g • (g • x) = x
    rw [←mul_smul,←pow_two,hg,one_smul]
  unfold minusDimension
  rw [negative_minus_eq_plus,finrank_plus_add_minus _ ht h2]
  simp [Vector,Index,Module.finrank_pi,Fintype.card_sum,two_mul]

theorem projection_square_one_isConj_iff (hn : 0<n) (g h : Sp n F)
    (hg : g^2=1) (hh : h^2=1) (h2 : (2:F) ≠ 0) :
    IsConj (projection g) (projection h) ↔
      minusDimension g = minusDimension h ∨ minusDimension g + minusDimension h = 2*n := by
  rw [projection_isConj_iff_signed hn,
    square_one_isConj_iff_minusDimension_eq g h hg hh h2,
    square_one_isConj_iff_minusDimension_eq g (negativeIdentity*h) hg
      (negative_mul_square_one h hh) h2]
  have hd := minusDimension_neg_add h hh h2
  omega

end Atlas.Symplectic

namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

@[simp] theorem signRepresentative_empty : (signRepresentative ∅ : Sp n F)=1 := by
  apply ext_action
  intro x
  funext i
  simp

theorem minusDimension_one (h2 : (2:F) ≠ 0) : minusDimension (1 : Sp n F)=0 := by
  simpa using signRepresentative_minusDimension (n := n) (F := F) ∅ h2

theorem square_one_minusDimension_eq_zero_iff (g : Sp n F) (hg : g^2=1) (h2 : (2:F) ≠ 0) :
    minusDimension g = 0 ↔ g=1 := by
  rw [←minusDimension_one (n := n) h2,
    ←square_one_isConj_iff_minusDimension_eq g 1 hg (one_pow 2) h2]
  simp

theorem square_one_minusDimension_bounds (g : Sp n F) (hg : g^2=1)
    (h2 : (2:F) ≠ 0) (hcentral : g ∉ Subgroup.center (Sp n F)) :
    0 < minusDimension g ∧ minusDimension g < 2*n := by
  have hn : g ≠ 1 := fun he => hcentral (he ▸ (Subgroup.center _).one_mem)
  have hn' : negativeIdentity*g ≠ (1 : Sp n F) := by
    intro he
    have hc : g = negativeIdentity := by
      have hh := congrArg (fun z : Sp n F => negativeIdentity*z) he
      simpa [←mul_assoc,←pow_two] using hh
    exact hcentral (hc ▸ negativeIdentity_central)
  have hd := minusDimension_neg_add g hg h2
  have hp := (square_one_minusDimension_eq_zero_iff g hg h2).not.mpr hn
  have hp' := (square_one_minusDimension_eq_zero_iff (negativeIdentity*g)
    (negative_mul_square_one g hg) h2).not.mpr hn'
  omega

def rankSignRepresentative (r : ℕ) : Sp n F := signRepresentative (Finset.univ.filter (fun i : Fin n => i.val < r))

theorem rankSignRepresentative_square (r : ℕ) : (rankSignRepresentative r : Sp n F)^2=1 :=
  signRepresentative_square _

theorem rankSignRepresentative_minusDimension (r : ℕ) (hr : r ≤ n) (h2 : (2:F) ≠ 0) :
    minusDimension (rankSignRepresentative r : Sp n F)=2*r := by
  rw [rankSignRepresentative,signRepresentative_minusDimension _ h2,Fin.card_filter_val_lt,min_eq_right hr]

end Atlas.Symplectic
