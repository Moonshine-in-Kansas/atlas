import Atlas.GroupTheory.CenterSimpleQuotient

/-!
# Uniqueness of a nonabelian simple quotient of a central extension

No finiteness or perfectness assumption is placed on the covering group.
The intermediate statement only requires the second quotient to be nontrivial
and centerless; its simplicity is a consequence rather than a premise.
-/

namespace Atlas.GroupTheory

variable {U S T : Type*} [Group U] [Group S] [Group T]

/-- A surjection onto a centerless group kills every central subgroup. -/
theorem central_kernel_le_kernel (f : U →* S)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) :
    f.ker ≤ g.ker := by
  intro x hx
  have h := Subgroup.map_center_le_center hg
    (show g x ∈ (Subgroup.center U).map g from ⟨x, hc hx, rfl⟩)
  rw [hT, Subgroup.mem_bot] at h
  exact h

/-- The factor homomorphism through a given central quotient. -/
noncomputable def centralQuotientFactor (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) : S →* T :=
  f.liftOfSurjective hf ⟨g, central_kernel_le_kernel f hc g hg hT⟩

@[simp] theorem centralQuotientFactor_apply (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) (x : U) :
    centralQuotientFactor f hf hc g hg hT (f x) = g x :=
  f.liftOfRightInverse_comp_apply _ _ _ x

theorem centralQuotientFactor_surjective (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) :
    Function.Surjective (centralQuotientFactor f hf hc g hg hT) := by
  intro t
  obtain ⟨x, rfl⟩ := hg t
  exact ⟨f x, centralQuotientFactor_apply f hf hc g hg hT x⟩

/-- A nontrivial centerless quotient of a central extension of a simple group
is the same simple group. -/
theorem centralQuotientFactor_injective [IsSimpleGroup S] [Nontrivial T]
    (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) :
    Function.Injective (centralQuotientFactor f hf hc g hg hT) := by
  let φ := centralQuotientFactor f hf hc g hg hT
  have hφ := centralQuotientFactor_surjective f hf hc g hg hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with hb | ht
  · exact (MonoidHom.ker_eq_bot_iff φ).mp hb
  · obtain ⟨t, htne⟩ := exists_ne (1 : T)
    obtain ⟨s, hs⟩ := hφ t
    have h : s ∈ φ.ker := by rw [ht]; trivial
    exact False.elim (htne (hs.symm.trans h))

/-- The canonical identification of any nontrivial centerless quotient with
the given simple central quotient. -/
noncomputable def centralSimpleQuotientEquiv [IsSimpleGroup S] [Nontrivial T]
    (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) : S ≃* T :=
  MulEquiv.ofBijective (centralQuotientFactor f hf hc g hg hT)
    ⟨centralQuotientFactor_injective f hf hc g hg hT,
      centralQuotientFactor_surjective f hf hc g hg hT⟩

@[simp] theorem centralSimpleQuotientEquiv_apply [IsSimpleGroup S] [Nontrivial T]
    (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hT : Subgroup.center T = ⊥) (x : U) :
    centralSimpleQuotientEquiv f hf hc g hg hT (f x) = g x :=
  centralQuotientFactor_apply f hf hc g hg hT x

/-- In particular, every nonabelian simple quotient of the covering group is
isomorphic to its given simple central quotient. -/
noncomputable def nonabelianSimpleQuotientEquiv [IsSimpleGroup S] [IsSimpleGroup T]
    (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hn : ¬ IsMulCommutative T) : S ≃* T :=
  centralSimpleQuotientEquiv f hf hc g hg (center_eq_bot_of_simple_nonabelian T hn)

@[simp] theorem nonabelianSimpleQuotientEquiv_apply [IsSimpleGroup S] [IsSimpleGroup T]
    (f : U →* S) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center U) (g : U →* T)
    (hg : Function.Surjective g) (hn : ¬ IsMulCommutative T) (x : U) :
    nonabelianSimpleQuotientEquiv f hf hc g hg hn (f x) = g x :=
  centralSimpleQuotientEquiv_apply f hf hc g hg _ x

end Atlas.GroupTheory
