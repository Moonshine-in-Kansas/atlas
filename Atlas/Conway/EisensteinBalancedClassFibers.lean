import Atlas.Conway.EisensteinBalancedClassEquality

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

def eisensteinBalancedConstantPhase (c : TernaryBalancedWords) (r : ZMod 3) :
    EisensteinBalancedPhase c :=
  ⟨fun _ => r,by
    apply ternaryHexadRestriction_le (ternaryBalancedSixWord c)
    refine ⟨r • ternaryOne,?_⟩
    funext i
    simp [ternaryRestriction,ternaryOne]⟩

theorem eisensteinBalanced_sign_positions_card (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) :
    Nat.card {k : ternarySupport c.val.val // c.val.val k.val=c.val.val j.val}=3 := by
  classical
  have hn := (Finset.mem_filter.mp j.prop).2
  let e : {k : ternarySupport c.val.val // c.val.val k.val=c.val.val j.val} ≃
      {i : Fin 12 // c.val.val i=c.val.val j.val} :=
    { toFun := fun k => ⟨k.val.val,k.prop⟩
      invFun := fun i => ⟨⟨i.val,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun hz => hn (i.prop.symm.trans hz)⟩⟩,i.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hc : c.val.val j.val=1 ∨ c.val.val j.val=2 := by
    have h : ∀ x : ZMod 3,x≠0 → x=1 ∨ x=2 := by decide
    exact h _ hn
  rcases hc with hc | hc
  · rw [hc]; exact c.prop.1
  · rw [hc]; exact c.prop.2

def eisensteinBalancedFixedFiber (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :=
  {q : (ternarySupport c.val.val) × EisensteinBalancedPhase c //
    eisensteinClass (eisensteinBalancedPhasedLatticeVector c j a)=
      eisensteinClass (eisensteinBalancedPhasedLatticeVector c q.1 q.2)}

def eisensteinBalancedFixedFiberMap (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    {k : ternarySupport c.val.val // c.val.val k.val=c.val.val j.val} × ZMod 3 →
      eisensteinBalancedFixedFiber c j a := fun p =>
  ⟨(p.1.val,a+eisensteinBalancedConstantPhase c p.2),
    (eisensteinBalancedClass_eq_iff _ _ _ _ _).mpr
      ⟨p.1.prop.symm,p.2,fun _ => rfl⟩⟩

theorem eisensteinBalancedFixedFiberMap_bijective (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    Function.Bijective (eisensteinBalancedFixedFiberMap c j a) := by
  constructor
  · rintro ⟨k,r⟩ ⟨l,s⟩ he
    have hp := congrArg Subtype.val he
    have hk : k=l := Subtype.ext (congrArg Prod.fst hp)
    subst l
    have hh := congrArg (fun p : (ternarySupport c.val.val) × EisensteinBalancedPhase c =>
      p.2.val j) hp
    change a.val j+r=a.val j+s at hh
    have hrs := add_left_cancel hh
    subst s
    rfl
  · rintro ⟨⟨k,b⟩,hb⟩
    obtain ⟨hj,r,hr⟩ := (eisensteinBalancedClass_eq_iff _ _ _ _ _).mp hb
    refine ⟨(⟨k,hj.symm⟩,r),?_⟩
    apply Subtype.ext
    change (k,a+eisensteinBalancedConstantPhase c r)=(k,b)
    apply Prod.ext
    · rfl
    apply Subtype.ext
    funext i
    exact (hr i).symm

theorem eisensteinBalancedFixedFiber_card (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (a : EisensteinBalancedPhase c) :
    Nat.card (eisensteinBalancedFixedFiber c j a)=9 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (eisensteinBalancedFixedFiberMap_bijective c j a)),
    Nat.card_prod,eisensteinBalanced_sign_positions_card]
  norm_num

def eisensteinBalancedParameterClass (p : EisensteinBalancedParameters) : EisensteinClasses :=
  eisensteinClass (eisensteinBalancedPhasedLatticeVector p.1 p.2.1 p.2.2)

def eisensteinBalancedFullFiberMap (p : EisensteinBalancedParameters) :
    eisensteinBalancedFixedFiber p.1 p.2.1 p.2.2 →
      {q : EisensteinBalancedParameters // eisensteinBalancedParameterClass p=eisensteinBalancedParameterClass q} :=
  fun q => ⟨⟨p.1,q.val⟩,q.prop⟩

theorem eisensteinBalancedFullFiberMap_bijective (p : EisensteinBalancedParameters) :
    Function.Bijective (eisensteinBalancedFullFiberMap p) := by
  constructor
  · intro q r he
    apply Subtype.ext
    have h := congrArg Subtype.val he
    exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  · rintro ⟨⟨d,k,b⟩,h⟩
    have hd := eisensteinBalancedClass_code p.1 d p.2.1 k p.2.2 b h
    subst d
    exact ⟨⟨(k,b),h⟩,rfl⟩

theorem eisensteinBalancedParameterClass_fiber_card (p : EisensteinBalancedParameters) :
    Nat.card {q : EisensteinBalancedParameters //
      eisensteinBalancedParameterClass q=eisensteinBalancedParameterClass p}=9 := by
  let e : {q : EisensteinBalancedParameters //
      eisensteinBalancedParameterClass q=eisensteinBalancedParameterClass p} ≃
      {q : EisensteinBalancedParameters //
      eisensteinBalancedParameterClass p=eisensteinBalancedParameterClass q} :=
    Equiv.subtypeEquivRight (fun _ => eq_comm)
  rw [Nat.card_congr e,
    ← Nat.card_congr (Equiv.ofBijective _ (eisensteinBalancedFullFiberMap_bijective p)),
    eisensteinBalancedFixedFiber_card]

end Atlas.Conway
