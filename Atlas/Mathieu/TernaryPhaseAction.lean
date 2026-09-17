import Atlas.Mathieu.TernaryMathieu11Full
import Atlas.Codes.TernaryGolayCyclicFixed

noncomputable section
namespace Atlas.Codes

/-- The action of the full coordinate group on the actual code. -/
def ternaryPureCodeEnd : TernaryPureAutomorphism →* Module.End (ZMod 3) ternaryGolay where
  toFun g :=
    { toFun := fun w => ⟨fun i => w.val (g.val.symm i), g.prop _ w.prop⟩
      map_add' _ _ := Subtype.ext rfl
      map_smul' _ _ := Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro w
    apply Subtype.ext; rfl
  map_mul' _ _ := by
    apply LinearMap.ext; intro w
    apply Subtype.ext; rfl

theorem ternaryPureCodeEnd_constants (g : TernaryPureAutomorphism) :
    ternaryConstants ≤ ternaryConstants.comap (ternaryPureCodeEnd g) := by
  intro w hw
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
  rw [← hc]
  change ternaryPureCodeEnd g (c • ternaryOne) ∈ ternaryConstants
  rw [map_smul]
  have he : ternaryPureCodeEnd g ternaryOne = ternaryOne := Subtype.ext rfl
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

def ternaryPurePhaseEnd (g : TernaryPureAutomorphism) : Module.End (ZMod 3) TernaryPhaseModule :=
  ternaryConstants.mapQ ternaryConstants (ternaryPureCodeEnd g) (ternaryPureCodeEnd_constants g)

theorem ternaryPurePhaseEnd_pow (g : TernaryPureAutomorphism) (hg : g ^ 11 = 1) :
    ternaryPurePhaseEnd g ^ 11 = 1 := by
  have he : ternaryPureCodeEnd g ^ 11 = 1 := by rw [← map_pow,hg,map_one]
  rw [ternaryPurePhaseEnd, ← Submodule.mapQ_pow]
  simp [he, Module.End.one_eq_id, Submodule.mapQ_id]

/-- Cauchy's theorem and the twelve-coordinate faithful realization supply an
actual eleven-cycle with one fixed point. -/
theorem ternaryPure_exists_eleven_cycle : ∃ g : TernaryPureAutomorphism,
    g ^ 11 = 1 ∧ ∃ a : Fin 12,
      ∀ i, i ≠ a → ∀ j, j ≠ a → ∃ k : ℕ, (g.val.symm ^ k) i = j := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := TernaryPureAutomorphism) 11
    (by rw [ternaryPureAutomorphism_order]; decide)
  have hgpow : g ^ 11 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have ho : orderOf g.val.symm = 11 := by
    change orderOf g.val⁻¹ = 11
    rw [orderOf_inv]
    exact (orderOf_injective ternaryPureAutomorphism.subtype
      ternaryPureAutomorphism.subtype_injective g).trans hg
  have hcycle : Equiv.Perm.IsCycle g.val.symm := Equiv.Perm.isCycle_of_prime_order'
    (by rw [ho]; decide) (by rw [ho]; norm_num)
  have hsupport : (Equiv.Perm.support g.val.symm).card = 11 := hcycle.orderOf.symm.trans ho
  have hcompl : (Equiv.Perm.support g.val.symm)ᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hsupport]
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcompl
  have hn (i : Fin 12) (hi : i ≠ a) : g.val.symm i ≠ i := by
    intro he
    have hm : i ∈ (Equiv.Perm.support g.val.symm)ᶜ := by simpa using he
    rw [ha,Finset.mem_singleton] at hm
    exact hi hm
  refine ⟨g,hgpow,a,?_⟩
  intro i hi j hj
  exact (hcycle.sameCycle (hn i hi) (hn j hj)).exists_nat_pow_eq

theorem ternaryPhase_exists_fixed_free_operator :
    ∃ g : TernaryPureAutomorphism, ternaryPurePhaseEnd g ^ 11 = 1 ∧
      ∀ v, ternaryPurePhaseEnd g v = v → v = 0 := by
  obtain ⟨g,hg,a,ha⟩ := ternaryPure_exists_eleven_cycle
  refine ⟨g,ternaryPurePhaseEnd_pow g hg,?_⟩
  intro v hv
  apply ternaryPhase_fixed_eq_zero g.val.symm a ha (ternaryPureCodeEnd g)
    (fun _ _ => rfl) ?_ (ternaryPureCodeEnd_constants g) v hv
  rw [← map_pow,hg,map_one]

/-- The actual five-dimensional phase module is irreducible for the full
coordinate group, identified above with the existing M11. -/
theorem ternaryPhase_invariant_eq_bot_or_top (W : Submodule (ZMod 3) TernaryPhaseModule)
    (hW : ∀ g : TernaryPureAutomorphism, ∀ v ∈ W, ternaryPurePhaseEnd g v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨g,hg,hfix⟩ := ternaryPhase_exists_fixed_free_operator
  exact Atlas.RepresentationTheory.ternary_finrank_five_invariant_eq_bot_or_top
    ternaryPhaseModule_finrank (ternaryPurePhaseEnd g) hg hfix W (hW g)

theorem ternaryPhase_action_difference_surjective :
    ∃ g : TernaryPureAutomorphism,
      Function.Surjective (fun v => ternaryPurePhaseEnd g v - v) := by
  obtain ⟨g,_,hfix⟩ := ternaryPhase_exists_fixed_free_operator
  exact ⟨g,Atlas.RepresentationTheory.difference_surjective_of_fixed_eq_zero _ hfix⟩

end Atlas.Codes
