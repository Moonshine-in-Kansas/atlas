import Atlas.LinearGroups.Chevalley.TwistedE6.TorusTupleAction
import Atlas.LinearGroups.Chevalley.TwistedE6.TorusUnitParameters

/-! The actual fixed torus in the simply connected E6 graph–field fixed group.
Its multiplicative parameters are two base-field units and two quadratic-field
units. All membership and exhaustion arguments concern the literal T∩H. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def fixedTorusTupleHom :
    TorusUnitParameters.fixedUnitTuples F K →* companionFixedTorus F K where
  toFun t := ⟨e6PublicTorusParameters K t.val,
    (e6PublicTorusParameters_mem_companionFixedTorus_iff F K t.val).mpr t.property⟩
  map_one' := Subtype.ext (map_one (e6PublicTorusParameters K))
  map_mul' s t := Subtype.ext (map_mul (e6PublicTorusParameters K) s.val t.val)

@[simp] theorem fixedTorusTupleHom_val (t : TorusUnitParameters.fixedUnitTuples F K) :
    (fixedTorusTupleHom F K t).val = e6PublicTorusParameters K t.val := rfl

theorem fixedTorusTupleHom_injective : Function.Injective (fixedTorusTupleHom F K) := by
  intro s t h
  apply Subtype.ext
  apply e6PublicTorusParameters_injective K
  exact congrArg (fun g : companionFixedTorus F K => g.val) h

theorem fixedTorusTupleHom_surjective : Function.Surjective (fixedTorusTupleHom F K) := by
  intro g
  obtain ⟨t, ht⟩ := (e6PublicTorusParametersEquiv K).surjective ⟨g.val, g.property.1⟩
  have hval : e6PublicTorusParameters K t = g.val :=
    congrArg (fun u : selectedWeightCompanionTorusSubgroup .E6 K => u.val) ht
  have hfixed : e6PublicTorusParameters K t ∈ companionFixedSubgroup F K := by
    rw [hval]
    exact g.property.2
  have htuple : t ∈ TorusUnitParameters.fixedUnitTuples F K :=
    (e6PublicTorusParameters_mem_companionFixedSubgroup_iff F K t).mp hfixed
  exact ⟨⟨t, htuple⟩, Subtype.ext hval⟩

def fixedTorusTupleEquiv :
    TorusUnitParameters.fixedUnitTuples F K ≃* companionFixedTorus F K :=
  MulEquiv.ofBijective (fixedTorusTupleHom F K)
    ⟨fixedTorusTupleHom_injective F K, fixedTorusTupleHom_surjective F K⟩

/-- Two fixed-node units and two free exchanged-pair units, in the public marking. -/
def companionFixedTorusParametersEquiv (hdeg : Module.finrank F K = 2) :
    TorusUnitParameters.Parameters F K ≃* companionFixedTorus F K :=
  (TorusUnitParameters.parametersEquiv F K hdeg).trans (fixedTorusTupleEquiv F K)

@[simp] theorem companionFixedTorusParametersEquiv_val (hdeg : Module.finrank F K = 2)
    (p : TorusUnitParameters.Parameters F K) :
    (companionFixedTorusParametersEquiv F K hdeg p).val =
      e6PublicTorusParameters K (TorusUnitParameters.expand F K p) := rfl

/-- Uniform fixed torus order, including characteristics 2,3 and q=2. -/
theorem companionFixedTorus_card (hdeg : Module.finrank F K = 2) :
    Nat.card (companionFixedTorus F K) = (Nat.card F - 1)^2 * (Nat.card F^2 - 1)^2 := by
  calc
    _ = Nat.card (TorusUnitParameters.fixedUnitTuples F K) :=
      (Nat.card_congr (fixedTorusTupleEquiv F K).toEquiv).symm
    _ = (Nat.card F - 1)^2 * (Nat.card F^2 - 1)^2 :=
      TorusUnitParameters.fixedUnitTuples_card F K hdeg

end Atlas.Chevalley.TwistedE6
