import Atlas.Rudvalis.LatticeFrameStabilizer

namespace Atlas.Rudvalis

/-- Full rational Gaussian isometry group of the actual Version 33 lattice. -/
def gaussianLatticeGroup : Subgroup (RationalSpace ≃ₗ[ℚ] RationalSpace) where
  carrier := {f | (∀v w,rationalDot (f v) (f w)=rationalDot v w) ∧
    (∀v,v∈rudvalisLattice ↔ f v∈rudvalisLattice) ∧
    (∀v,f (rationalI v)=rationalI (f v))}
  one_mem' := by exact ⟨fun _ _ => rfl,fun _ => Iff.rfl,fun _ => rfl⟩
  mul_mem' := by
    intro f g hf hg
    refine ⟨?_,?_,?_⟩
    · intro v w; exact (hf.1 _ _).trans (hg.1 _ _)
    · intro v; exact (hg.2.1 v).trans (hf.2.1 (g v))
    · intro v; change f (g (rationalI v))=rationalI (f (g v)); rw [hg.2.2,hf.2.2]
  inv_mem' := by
    intro f hf
    refine ⟨?_,?_,?_⟩
    · intro v w
      simpa using (hf.1 (f.symm v) (f.symm w)).symm
    · intro v
      simpa using (hf.2.1 (f.symm v)).symm
    · intro v
      apply f.injective
      simpa using (hf.2.2 (f.symm v)).symm

noncomputable def codeGaussianHom : codeGroup →* gaussianLatticeGroup :=
  { toFun := fun g => ⟨rationalMonomialHom g.val,
      rationalMonomial_pairing g.val,codeGroup_lattice_iff g,codeGroup_rational_gaussian_linear g⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun g h => Subtype.ext (map_mul _ g.val h.val) }

theorem codeGaussianHom_injective : Function.Injective codeGaussianHom := by
  intro g h he
  exact Subtype.ext (rationalMonomialHom_injective (congrArg Subtype.val he))

/-- The full Gaussian lattice group has exactly the verified code group on the coordinate frame. -/
theorem gaussian_coordinate_stabilizer (f : gaussianLatticeGroup) :
    (∀i,coordinateShell (f.val (coordinateMinimum i))) ↔
    ∃g : codeGroup,codeGaussianHom g=f := by
  constructor
  · intro h
    obtain ⟨g,hg⟩ := coordinateFrame_full_stabilizer f.val f.prop.1 f.prop.2.1 h
    exact ⟨g,Subtype.ext hg⟩
  · rintro ⟨g,rfl⟩ i
    refine ⟨g.val.right i,?_⟩
    have h : rationalMonomialHom g.val (coordinateMinimum i)=
        if g.val.left.toAdd (g.val.right i)=0 then coordinateMinimum (g.val.right i)
        else -coordinateMinimum (g.val.right i) := by
      funext j
      change liftedSign (g.val.left.toAdd j) (coordinateMinimum i (g.val.right.symm j))=_
      have he : g.val.right.symm j=i ↔ j=g.val.right i := g.val.right.symm_apply_eq
      by_cases hj : j=g.val.right i
      · subst j
        simp [coordinateMinimum,liftedSign]
        split <;> simp_all
      · have hi := mt he.mp hj
        simp [coordinateMinimum,liftedSign,Pi.single_apply,hj,hi]
        split <;> simp_all [Pi.single_apply]
    change rationalMonomialHom g.val (coordinateMinimum i)=_ ∨ _
    by_cases hb : g.val.left.toAdd (g.val.right i)=0
    · exact Or.inl (by simpa [hb,codeGaussianHom] using h)
    · exact Or.inr (by simpa [hb,codeGaussianHom] using h)

end Atlas.Rudvalis
