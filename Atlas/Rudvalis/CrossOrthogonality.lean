import Atlas.Rudvalis.GaussianCrossAction

/-! Intrinsic Hermitian orthogonality on actual Gaussian minimal crosses. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def HermitianOrthogonal (v w : RationalSpace) : Prop :=
  rationalDot v w=0 ∧ rationalDot (rationalI v) w=0

theorem rationalDot_comm (v w : RationalSpace) : rationalDot v w=rationalDot w v := by
  simp [rationalDot,mul_comm]

theorem rationalDot_neg_left (v w : RationalSpace) : rationalDot (-v) w= -rationalDot v w := by
  simp [rationalDot]

theorem rationalI_skew (v w : RationalSpace) :
    rationalDot (rationalI v) w= -rationalDot v (rationalI w) := by
  have h := rationalI_pairing v (rationalI w)
  rw [rationalI_square] at h
  have he : rationalDot (rationalI v) (-w)= -rationalDot (rationalI v) w := by simp [rationalDot]
  rw [he] at h
  linarith

theorem hermitianOrthogonal_symm (v w : RationalSpace) :
    HermitianOrthogonal v w ↔ HermitianOrthogonal w v := by
  have step (a b : RationalSpace) (h : HermitianOrthogonal a b) : HermitianOrthogonal b a := by
    refine ⟨(rationalDot_comm b a).trans h.1,?_⟩
    rw [rationalI_skew,rationalDot_comm b (rationalI a),h.2,neg_zero]
  exact ⟨step v w,step w v⟩

theorem hermitianOrthogonal_I_left (v w : RationalSpace) :
    HermitianOrthogonal (rationalI v) w ↔ HermitianOrthogonal v w := by
  simp only [HermitianOrthogonal,rationalI_square,rationalDot_neg_left,neg_eq_zero,and_comm]

theorem hermitianOrthogonal_gaussian (g : gaussianLatticeGroup) (v w : RationalSpace) :
    HermitianOrthogonal (g.val v) (g.val w) ↔ HermitianOrthogonal v w := by
  rw [HermitianOrthogonal,←g.prop.2.2,g.prop.1,g.prop.1]
  rfl

theorem hermitianOrthogonal_I_pow (n : ℕ) (v w : RationalSpace) :
    HermitianOrthogonal (rationalMonomialHom (codeI.val^n) v) w ↔ HermitianOrthogonal v w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',map_mul]
    change HermitianOrthogonal (rationalI (rationalMonomialHom (codeI.val^n) v)) w ↔ _
    exact (hermitianOrthogonal_I_left _ _).trans ih

theorem hermitianOrthogonal_units_left (u : GaussianUnits) (v w : MinimalShell) :
    HermitianOrthogonal (u • v).val.val w.val.val ↔ HermitianOrthogonal v.val.val w.val.val := by
  classical
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp u.prop)
  change HermitianOrthogonal (rationalMonomialHom u.val.val v.val.val) w.val.val ↔ _
  rw [←he]
  exact hermitianOrthogonal_I_pow n v.val.val w.val.val

theorem hermitianOrthogonal_units_right (u : GaussianUnits) (v w : MinimalShell) :
    HermitianOrthogonal v.val.val (u • w).val.val ↔ HermitianOrthogonal v.val.val w.val.val := by
  rw [hermitianOrthogonal_symm,hermitianOrthogonal_units_left,hermitianOrthogonal_symm]

def CrossOrthogonal (x y : MinimalCross) : Prop :=
  ∃ v w : MinimalShell,minimalCross v=x ∧ minimalCross w=y ∧ HermitianOrthogonal v.val.val w.val.val

theorem crossOrthogonal_mk (v w : MinimalShell) :
    CrossOrthogonal (minimalCross v) (minimalCross w) ↔ HermitianOrthogonal v.val.val w.val.val := by
  constructor
  · rintro ⟨a,b,ha,hb,h⟩
    obtain ⟨u,hu⟩ := (minimalCross_eq_iff a v).mp ha
    obtain ⟨t,ht⟩ := (minimalCross_eq_iff b w).mp hb
    rw [←hu,←ht] at h
    exact (hermitianOrthogonal_units_right t v w).mp ((hermitianOrthogonal_units_left u v (t • w)).mp h)
  · intro h
    exact ⟨v,w,rfl,rfl,h⟩

theorem crossOrthogonal_symm (x y : MinimalCross) : CrossOrthogonal x y ↔ CrossOrthogonal y x := by
  induction x using Quotient.inductionOn with | h v =>
    induction y using Quotient.inductionOn with | h w =>
      change CrossOrthogonal (minimalCross v) (minimalCross w) ↔ CrossOrthogonal (minimalCross w) (minimalCross v)
      rw [crossOrthogonal_mk,crossOrthogonal_mk,hermitianOrthogonal_symm]

theorem crossOrthogonal_irrefl (x : MinimalCross) : ¬CrossOrthogonal x x := by
  induction x using Quotient.inductionOn with | h v =>
    change ¬CrossOrthogonal (minimalCross v) (minimalCross v)
    rw [crossOrthogonal_mk]
    intro h
    have hv := v.prop
    have hz := h.1
    linarith

theorem minimalCross_ne_of_hermitian_orthogonal (v w : MinimalShell)
    (h : HermitianOrthogonal v.val.val w.val.val) : minimalCross v≠minimalCross w := by
  intro he
  have hh := (crossOrthogonal_mk v w).mpr h
  rw [he] at hh
  exact crossOrthogonal_irrefl _ hh

theorem minimalCross_ne_of_orthogonal (v w : MinimalShell)
    (h : rationalDot v.val.val w.val.val=0)
    (hi : rationalDot v.val.val (rationalI w.val.val)=0) : minimalCross v≠minimalCross w := by
  apply minimalCross_ne_of_hermitian_orthogonal v w
  exact ⟨h,by rw [rationalI_skew,hi,neg_zero]⟩

theorem crossOrthogonal_gaussian (g : gaussianLatticeGroup) (x y : MinimalCross) :
    CrossOrthogonal (g • x) (g • y) ↔ CrossOrthogonal x y := by
  induction x using Quotient.inductionOn with | h v =>
    induction y using Quotient.inductionOn with | h w =>
      change CrossOrthogonal (g • minimalCross v) (g • minimalCross w) ↔ CrossOrthogonal (minimalCross v) (minimalCross w)
      rw [←gaussian_minimalCross_smul,←gaussian_minimalCross_smul,crossOrthogonal_mk,crossOrthogonal_mk]
      exact hermitianOrthogonal_gaussian g v.val.val w.val.val

end Atlas.Rudvalis
