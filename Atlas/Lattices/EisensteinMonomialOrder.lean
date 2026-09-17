import Atlas.Lattices.EisensteinMonomialCriterion

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

def eisensteinPhaseUnit (a : ZMod 3) : Eisensteinˣ where
  val := eisensteinPhase a
  inv := eisensteinPhase (-a)
  val_inv := by rw [← eisensteinPhase_add,add_neg_cancel,eisensteinPhase_zero]
  inv_val := eisensteinPhase_neg_mul a

def eisensteinSignedPhase (b : Bool) (a : ZMod 3) : Eisenstein :=
  if b then -eisensteinPhase a else eisensteinPhase a

theorem eisensteinSignedPhase_injective :
    Function.Injective (fun p : Bool × ZMod 3 => eisensteinSignedPhase p.1 p.2) := by
  decide +kernel

def eisensteinSignedPhaseUnit (b : Bool) (a : ZMod 3) : Eisensteinˣ :=
  if b then -eisensteinPhaseUnit a else eisensteinPhaseUnit a

theorem eisensteinSignedPhaseUnit_val (b : Bool) (a : ZMod 3) :
    (eisensteinSignedPhaseUnit b a : Eisenstein) = eisensteinSignedPhase b a := by
  cases b <;> rfl

/-- All integral unit-monomial data that preserve the actual congruence lattice. -/
abbrev EisensteinMonomialDatum := {p : (Fin 12 → Eisensteinˣ) × Equiv.Perm (Fin 12) //
  ∀ z ∈ eisensteinLeechModule, eisensteinUnitMonomial p.1 p.2 z ∈ eisensteinLeechModule}

abbrev EisensteinMonomialParameters := Bool × ternaryGolay × TernaryPureAutomorphism

def eisensteinMonomialFromParameters (p : EisensteinMonomialParameters) : EisensteinMonomialDatum :=
  ⟨(fun i => eisensteinSignedPhaseUnit p.1 (p.2.1.val i),p.2.2.val),by
    apply (eisensteinUnitMonomial_lattice_iff _ _).mpr
    cases hb : p.1
    · exact ⟨1,Or.inl rfl,p.2.1,fun i => by simp [eisensteinSignedPhaseUnit,eisensteinPhaseUnit],p.2.2.prop⟩
    · exact ⟨-1,Or.inr rfl,p.2.1,fun i => by simp [eisensteinSignedPhaseUnit,eisensteinPhaseUnit],p.2.2.prop⟩⟩

theorem eisensteinMonomialFromParameters_injective :
    Function.Injective eisensteinMonomialFromParameters := by
  intro p q he
  have hg : p.2.2 = q.2.2 := Subtype.ext (congrArg (fun d : EisensteinMonomialDatum => d.val.2) he)
  have hh (i : Fin 12) : (p.1,p.2.1.val i) = (q.1,q.2.1.val i) := by
    apply eisensteinSignedPhase_injective
    have hc := congrArg (fun d : EisensteinMonomialDatum => (d.val.1 i : Eisenstein)) he
    simpa only [eisensteinMonomialFromParameters,eisensteinSignedPhaseUnit_val] using hc
  have hb : p.1 = q.1 := congrArg (fun x : Bool × ZMod 3 => x.1) (hh 0)
  have ht : p.2.1 = q.2.1 := Subtype.ext (funext (fun i => congrArg (fun x : Bool × ZMod 3 => x.2) (hh i)))
  exact Prod.ext hb (Prod.ext ht hg)

theorem eisensteinMonomialFromParameters_surjective :
    Function.Surjective eisensteinMonomialFromParameters := by
  rintro ⟨⟨u,σ⟩,h⟩
  obtain ⟨ε,hε,t,hu,hσ⟩ := (eisensteinUnitMonomial_lattice_iff u σ).mp h
  rcases hε with rfl | rfl
  · refine ⟨(false,t,⟨σ,hσ⟩),?_⟩
    apply Subtype.ext
    change ((fun i => eisensteinSignedPhaseUnit false (t.val i)),σ) = (u,σ)
    refine Prod.ext ?_ (show σ = σ from rfl)
    funext i
    apply Units.ext
    change eisensteinPhase (t.val i) = (u i : Eisenstein)
    simpa using (hu i).symm
  · refine ⟨(true,t,⟨σ,hσ⟩),?_⟩
    apply Subtype.ext
    change ((fun i => eisensteinSignedPhaseUnit true (t.val i)),σ) = (u,σ)
    refine Prod.ext ?_ (show σ = σ from rfl)
    funext i
    apply Units.ext
    change -eisensteinPhase (t.val i) = (u i : Eisenstein)
    simpa using (hu i).symm

def eisensteinMonomialParameterEquiv : EisensteinMonomialParameters ≃ EisensteinMonomialDatum :=
  Equiv.ofBijective eisensteinMonomialFromParameters
    ⟨eisensteinMonomialFromParameters_injective,eisensteinMonomialFromParameters_surjective⟩

theorem eisensteinMonomialDatum_card : Nat.card EisensteinMonomialDatum = 11547360 := by
  rw [← Nat.card_congr eisensteinMonomialParameterEquiv]
  change Nat.card (Bool × ternaryGolay × TernaryPureAutomorphism) = _
  rw [Nat.card_prod,Nat.card_prod,ternaryGolay_card,ternaryPureAutomorphism_order]
  norm_num [Nat.card_eq_fintype_card]

theorem eisensteinUnitMonomial_injective : Function.Injective
    (fun p : (Fin 12 → Eisensteinˣ) × Equiv.Perm (Fin 12) => eisensteinUnitMonomial p.1 p.2) := by
  rintro ⟨u,σ⟩ ⟨v,τ⟩ h
  have hu : u=v := by
    funext i
    apply Units.ext
    have he := congrFun (congrFun h (fun _ => 1)) i
    simpa [eisensteinUnitMonomial] using he
  have hi (i : Fin 12) : σ.symm i = τ.symm i := by
    by_contra he
    have hh := congrFun (congrFun h (Pi.single (σ.symm i) 1)) i
    have hz : (u i : Eisenstein) = 0 := by
      simpa [eisensteinUnitMonomial,Pi.single_apply,he,Ne.symm he] using hh
    exact (u i).ne_zero hz
  have hs : σ=τ := by
    have hh : σ.symm=τ.symm := Equiv.ext hi
    have he := congrArg Equiv.symm hh
    simpa using he
  exact Prod.ext hu hs

end Atlas.Lattices
