import Atlas.LinearGroups.F4.PairScalarKernel

/-! Unique factors in the actual seven-dimensional quotient-action kernel.
This reduction uses no order theorem for F₄ or its orthogonal quotient. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def parabolicKernelFactor (x : RadicalParameters F × Fˣ) :
    (parabolicOrthogonalHom (F:=F)).ker :=
  ⟨radicalParabolicHom x.1*(scalarPair x.2).val,by
    change parabolicOrthogonalHom (radicalParabolicHom x.1*(scalarPair x.2).val)=1
    rw [map_mul,radicalParabolic_orthogonal,one_mul]
    exact scalarPair_orthogonal x.2⟩

theorem parabolicKernelFactor_bijective : Function.Bijective (parabolicKernelFactor (F:=F)) := by
  constructor
  · rintro ⟨p,a⟩ ⟨q,b⟩ h
    have he : parabolicDecompositionMap (p,scalarPair a)=parabolicDecompositionMap (q,scalarPair b) :=
      congrArg Subtype.val h
    have hh := parabolicDecompositionMap_bijective.1 he
    have hp := congrArg Prod.fst hh
    have ha := congrArg Prod.snd hh
    have hab : a=b := scalarPairHom_injective ha
    exact Prod.ext hp hab
  · intro g
    obtain ⟨p,l,he⟩ := parabolic_factorization g.val
    have hl : pairOrthogonalHom l=1 := by
      have hg : parabolicOrthogonalHom g.val=1 := g.prop
      rw [he,map_mul,radicalParabolic_orthogonal,one_mul] at hg
      exact hg
    have hr : l∈(scalarPairHom (F:=F)).range := by
      rw [scalarPairHom_range]
      exact hl
    obtain ⟨a,ha⟩ := hr
    refine ⟨(p,a),Subtype.ext ?_⟩
    change radicalParabolicHom p*(scalarPair a).val=g.val
    rw [show scalarPair a=l from ha]
    exact he.symm

def parabolicKernelFactorEquiv : RadicalParameters F × Fˣ ≃
    (parabolicOrthogonalHom (F:=F)).ker :=
  Equiv.ofBijective parabolicKernelFactor parabolicKernelFactor_bijective

theorem card_parabolicOrthogonalHom_kernel [Finite F] :
    Nat.card (parabolicOrthogonalHom (F:=F)).ker=Nat.card F^15*(Nat.card F-1) := by
  rw [←Nat.card_congr parabolicKernelFactorEquiv,Nat.card_prod,Nat.card_units]
  change Nat.card (Atlas.GroupTheory.BilinearExtension (radicalCocycle (F:=F)))*_=_
  rw [Atlas.GroupTheory.BilinearExtension.card]
  simp only [Nat.card_fun,Nat.card_fin]
  ring

end Atlas.F4
