import Atlas.GroupTheory.PrimitivePointChains

/-! Equivariance of finite point-stabilizer move certificates.
The stabilizer move at x is transported by actual group conjugation. -/
namespace Atlas.GroupTheory
open MulAction
variable {G X : Type*} [Group G] [MulAction G X]

theorem stabilizerMoveChain_smul (g : G) {a b c : X}
    (hc : StabilizerMoveChain G a b c) :
    StabilizerMoveChain G (g • a) (g • b) (g • c) := by
  induction hc with
  | left => exact .left
  | right => exact .right
  | move x y hx hy h ihx ihy =>
      have hk : g*h.val*g⁻¹∈stabilizer G (g • x) := by
        change (g*h.val*g⁻¹) • (g • x)=g • x
        rw [mul_smul,mul_smul,inv_smul_smul]
        have hh : h.val • x=x := h.prop
        rw [hh]
      have hm := StabilizerMoveChain.move (g • x) (g • y) ihx ihy
        (⟨g*h.val*g⁻¹,hk⟩ : stabilizer G (g • x))
      change StabilizerMoveChain G (g • a) (g • b)
        ((g*h.val*g⁻¹) • (g • y)) at hm
      change StabilizerMoveChain G (g • a) (g • b) (g • (h.val • y))
      simpa only [mul_smul,inv_smul_smul] using hm

theorem stabilizerMoveChain_smul_iff (g : G) (a b c : X) :
    StabilizerMoveChain G (g • a) (g • b) (g • c) ↔ StabilizerMoveChain G a b c := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using stabilizerMoveChain_smul g⁻¹ h
  · exact stabilizerMoveChain_smul g

theorem stabilizerMoveClosure_image (g : G) (a b : X) :
    (fun x : X=>g • x) '' stabilizerMoveClosure G a b=
      stabilizerMoveClosure G (g • a) (g • b) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact stabilizerMoveChain_smul g hy
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul g x⟩
    change StabilizerMoveChain G a b (g⁻¹ • x)
    simpa only [inv_smul_smul] using stabilizerMoveChain_smul g⁻¹ hx

/-- Transport an explicit escape certificate through an invariant relation. -/
theorem stabilizerMoveChain_escape_smul (g : G) (R : X → X → Prop)
    (hR : ∀ x y, R (g • x) (g • y) ↔ R x y) {a b : X}
    (h : ∃ c, StabilizerMoveChain G a b c ∧ ¬R a c) :
    ∃ c, StabilizerMoveChain G (g • a) (g • b) c ∧ ¬R (g • a) c := by
  obtain ⟨c,hc,he⟩ := h
  exact ⟨g • c,stabilizerMoveChain_smul g hc,fun hr => he ((hR a c).mp hr)⟩

end Atlas.GroupTheory
