import Atlas.LinearGroups.Triality.StructuralTransport

/-! Equivariant transport of the actual parabolic coset geometry. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {F E K L : Type*} [Field F] [Field E] [Field K] [Field L]
  [Finite F] [Finite E] [Finite K] [Finite L] [Algebra F K] [Algebra E L]
variable (eF : F ≃+* E) (eK : K ≃+* L)
  (hcompat : ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t))
  (hK : Module.finrank F K=3) (hL : Module.finrank E L=3)

theorem fieldEquiv_val (g : Group F K) :
    (fieldEquiv eF eK hcompat g).val=fieldEquivFullD eK g.val := rfl

theorem fieldEquiv_mem_parabolic (g : Group F K) :
    fieldEquiv eF eK hcompat g ∈ parabolic E L hL ↔ g ∈ parabolic F K hK := by
  change fieldEquivFullD eK g.val ∈ longParabolic E L hL ↔ g.val ∈ longParabolic F K hK
  rw [← fieldEquiv_longParabolic eF eK hcompat hK hL]
  constructor
  · rintro ⟨a,ha,he⟩
    have hh : a=g.val := (fieldEquivFullD eK).injective he
    exact hh ▸ ha
  · intro hg
    exact ⟨g.val,hg,rfl⟩

def parabolicPointsEquiv : ParabolicPoints F K hK ≃ ParabolicPoints E L hL :=
  Quotient.congr (fieldEquiv eF eK hcompat).toEquiv (fun a b => by
    simp only [QuotientGroup.leftRel_apply]
    change a⁻¹*b ∈ parabolic F K hK ↔
      (fieldEquiv eF eK hcompat a)⁻¹*(fieldEquiv eF eK hcompat b) ∈ parabolic E L hL
    rw [← map_inv,← map_mul]
    exact (fieldEquiv_mem_parabolic eF eK hcompat hK hL _).symm)

theorem parabolicPointsEquiv_smul (g : Group F K) (x : ParabolicPoints F K hK) :
    parabolicPointsEquiv eF eK hcompat hK hL (g • x)=
      fieldEquiv eF eK hcompat g • parabolicPointsEquiv eF eK hcompat hK hL x := by
  refine QuotientGroup.induction_on x ?_
  intro a
  change QuotientGroup.mk (fieldEquiv eF eK hcompat (g*a))=
    QuotientGroup.mk (fieldEquiv eF eK hcompat g*fieldEquiv eF eK hcompat a)
  rw [map_mul]

end Atlas.Triality
