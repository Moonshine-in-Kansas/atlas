import Atlas.LinearGroups.SuzukiFamily.Bruhat

/-! Exact one- and two-point stabilizers, derived from the matrix normal forms. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem fixes_infinity_iff_short (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.Symplectic.Sp 2 F) (hg : g ∈ generated m) :
    pointLeft g infinityPoint=infinityPoint ↔ ∃ a b t, g=shortForm m a b t := by
  constructor
  · intro hp
    rcases generated_hasForm m hcard hg with hs | ⟨a,b,t,c,d,rfl⟩
    · exact hs
    · rw [longForm_infinity m hcard] at hp
      exact False.elim (infinity_ne_affine m a b hp.symm)
  · rintro ⟨a,b,t,rfl⟩
    exact shortForm_infinity m a b t

theorem shortForm_origin (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (t : Fˣ) :
    pointLeft (shortForm m a b t) (affinePoint m 0 0)=affinePoint m a b := by
  simp only [shortForm,pointLeft_mul,Function.comp_apply,torus_affine m hcard,
    mul_zero,root_affine m hcard,map_zero,add_zero]

theorem fixes_two_iff_torus (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (g : Atlas.Symplectic.Sp 2 F) (hg : g ∈ generated m) :
    (pointLeft g infinityPoint=infinityPoint ∧
      pointLeft g (affinePoint m 0 0)=affinePoint m 0 0) ↔ ∃ t, g=torusElement m t := by
  constructor
  · rintro ⟨hi,ho⟩
    obtain ⟨a,b,t,rfl⟩ := (fixes_infinity_iff_short m hcard g hg).mp hi
    rw [shortForm_origin m hcard] at ho
    have he : (a,b)=(0,0) := affinePoint_injective m ho
    have ha : a=0 := congrArg Prod.fst he
    have hb : b=0 := congrArg Prod.snd he
    exact ⟨t,by simp [shortForm,ha,hb,rootElement_zero]⟩
  · rintro ⟨t,rfl⟩
    exact ⟨torus_infinity m t,by simpa using torus_affine m hcard t 0 0⟩

theorem pointAction_faithful (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    letI := pointAction m hcard
    FaithfulSMul (Group F m) (pointSet (F := F) m) := by
  letI := pointAction m hcard
  apply faithfulSMul_iff.mpr
  intro g hg
  have hf : ∀ p ∈ pointSet m, pointLeft g.val p=p := by
    intro p hp
    exact congrArg Subtype.val (hg ⟨p,hp⟩)
  obtain ⟨t,ht⟩ := (fixes_two_iff_torus m hcard g.val g.property).mp
    ⟨hf _ ⟨none,rfl⟩,hf _ ⟨some (0,0),rfl⟩⟩
  have h1 := hf _ ⟨some (1,0),rfl⟩
  change pointLeft g.val (affinePoint m 1 0)=affinePoint m 1 0 at h1
  rw [ht,torus_affine m hcard] at h1
  have he : (theta F m ((t⁻¹:Fˣ):F)*1,((t⁻¹:Fˣ):F)^2*theta F m ((t⁻¹:Fˣ):F)*0)=(1,0) :=
    affinePoint_injective m h1
  have hv : ((t⁻¹:Fˣ):F)=1 := (theta F m).injective (by simpa using congrArg Prod.fst he)
  have hu : t=1 := inv_eq_one.mp (Units.ext hv)
  apply Subtype.ext
  simpa [hu] using ht
end Atlas.SuzukiFamily
