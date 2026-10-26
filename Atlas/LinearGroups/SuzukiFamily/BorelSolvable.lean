import Atlas.LinearGroups.SuzukiFamily.Borel

/-! Exact root kernel of the full stabilizer's torus quotient and solvability. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

@[simp] theorem borelParameters_symm_short (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (t : Fˣ) :
    (borelParameters m hcard).symm (shortInBorel m hcard a b t)=(a,b,t) :=
  (borelParameters m hcard).symm_apply_apply (a,b,t)

@[simp] theorem shortInBorel_zero_one (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    shortInBorel (F := F) m hcard 0 0 1=1 := by
  apply Subtype.ext
  apply Subtype.ext
  simp [shortInBorel,shortForm,rootElement_zero]

def borelProjection (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) : borel m hcard →* Fˣ where
  toFun g := ((borelParameters m hcard).symm g).2.2
  map_one' := by rw [← shortInBorel_zero_one m hcard,borelParameters_symm_short]
  map_mul' := by
    intro g k
    obtain ⟨⟨a,b,s⟩,rfl⟩ := (shortInBorel_bijective m hcard).surjective g
    obtain ⟨⟨c,d,t⟩,rfl⟩ := (shortInBorel_bijective m hcard).surjective k
    rw [shortInBorel_mul m hcard]
    simp only [borelParameters_symm_short]

@[simp] theorem borelProjection_short (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (t : Fˣ) : borelProjection m hcard (shortInBorel m hcard a b t)=t := by
  exact congrArg (fun p : F × F × Fˣ => p.2.2) (borelParameters_symm_short m hcard a b t)

def rootIntoBorel (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    rootSubgroup m hcard →* borel m hcard where
  toFun g := ⟨⟨g.val,rootSubgroup_le_generated m hcard g.property⟩,
    (mem_borel m hcard _).mpr (by
      obtain ⟨⟨a,b⟩,he⟩ := g.property
      rw [← he]
      exact root_infinity m a b)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem borelProjection_ker_eq_root (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    (borelProjection m hcard).ker=(rootIntoBorel m hcard).range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨a,b,t⟩,rfl⟩ := (shortInBorel_bijective m hcard).surjective g
    have ht : t=1 := by simpa using (borelProjection m hcard).mem_ker.mp hg
    subst t
    refine ⟨⟨rootElement m a b,⟨(a,b),rfl⟩⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp [rootIntoBorel,shortInBorel,shortForm]
  · rintro g ⟨u,rfl⟩
    obtain ⟨⟨a,b⟩,he⟩ := u.property
    have hu : rootIntoBorel m hcard u=shortInBorel m hcard a b 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [rootIntoBorel,shortInBorel,shortForm] using he.symm
    rw [hu]
    exact (borelProjection m hcard).mem_ker.mpr (borelProjection_short m hcard a b 1)

theorem borelProjection_surjective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Surjective (borelProjection m hcard) := fun t =>
  ⟨shortInBorel m hcard 0 0 t,borelProjection_short m hcard 0 0 t⟩

theorem borel_solvable (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    _root_.Group.IsSolvable (borel m hcard) := by
  letI := rootSubgroup_solvable m hcard
  exact _root_.Group.isSolvable_of_ker_le_range (rootIntoBorel m hcard)
    (borelProjection m hcard) (borelProjection_ker_eq_root m hcard).le
end Atlas.SuzukiFamily
