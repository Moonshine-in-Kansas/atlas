import Atlas.LinearGroups.SuzukiFamily.NormalForms
import Atlas.LinearGroups.SuzukiFamily.Commutation

/-! Stability of the two explicit cells under generators. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def HasForm (m : ℕ) (g : Atlas.Symplectic.Sp 2 F) : Prop :=
  (∃ a b t, g=shortForm m a b t) ∨ (∃ a b t c d, g=longForm m a b t c d)

theorem hasForm_one (m : ℕ) : HasForm m (1 : Atlas.Symplectic.Sp 2 F) := by
  exact Or.inl ⟨0,0,1,by simp [shortForm,rootElement_zero]⟩

theorem hasForm_root_left (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) {g : Atlas.Symplectic.Sp 2 F} (hg : HasForm m g) :
    HasForm m (rootElement m a b * g) := by
  rcases hg with ⟨c,d,t,rfl⟩ | ⟨c,d,t,e,f,rfl⟩
  · exact Or.inl ⟨a+c,b+d+a*theta F m c,t,by
      simp only [shortForm,← mul_assoc,rootElement_mul m hcard]⟩
  · exact Or.inr ⟨a+c,b+d+a*theta F m c,t,e,f,by
      simp only [longForm,← mul_assoc,rootElement_mul m hcard]⟩

theorem hasForm_torus_left (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (s : Fˣ) {g : Atlas.Symplectic.Sp 2 F} (hg : HasForm m g) :
    HasForm m (torusElement m s * g) := by
  rcases hg with ⟨a,b,t,rfl⟩ | ⟨a,b,t,c,d,rfl⟩
  · refine Or.inl ⟨theta F m ((s⁻¹:Fˣ):F)*a,
      ((s⁻¹:Fˣ):F)^2*theta F m ((s⁻¹:Fˣ):F)*b,s*t,?_⟩
    simp only [shortForm,← mul_assoc]
    rw [torus_root_swap m hcard,mul_assoc,← torusElement_mul]
  · refine Or.inr ⟨theta F m ((s⁻¹:Fˣ):F)*a,
      ((s⁻¹:Fˣ):F)^2*theta F m ((s⁻¹:Fˣ):F)*b,s⁻¹*t,c,d,?_⟩
    simp only [longForm,← mul_assoc]
    rw [torus_root_swap m hcard]
    simp only [mul_assoc]
    rw [← mul_assoc (torusElement m s) weylElement,torus_weyl_swap]
    simp only [torusElement_mul,mul_assoc]

theorem hasForm_weyl_left (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    {g : Atlas.Symplectic.Sp 2 F} (hg : HasForm m g) :
    HasForm m (weylElement * g) := by
  rcases hg with ⟨a,b,t,rfl⟩ | ⟨a,b,t,c,d,rfl⟩
  · refine Or.inr ⟨0,0,t,theta F m (t:F)*a,(t:F)^2*theta F m (t:F)*b,?_⟩
    simp only [shortForm,longForm,rootElement_zero,one_mul,mul_assoc]
    rw [root_torus_swap m hcard]
    simp only [mul_assoc]
  · by_cases hn : norm m a b=0
    · obtain ⟨ha,hb⟩ := (norm_eq_zero_iff m hcard a b).mp hn
      subst a; subst b
      have he : weylElement * longForm m 0 0 t c d=torusElement m t * rootElement m c d := by
        simp [longForm,rootElement_zero,← mul_assoc]
      rw [he]
      exact hasForm_torus_left m hcard t (Or.inl ⟨c,d,1,by simp [shortForm]⟩)
    · let s := bruhatTorus m a b hn
      let e := theta F m (t:F)*(b/norm m a b)
      let f := (t:F)^2*theta F m (t:F)*(a/norm m a b)
      refine Or.inr ⟨inverseFirst m a b,inverseSecond m a b,s*t,
        e+c,f+d+e*theta F m c,?_⟩
      change weylElement * (rootElement m a b * weylElement * torusElement m t *
        rootElement m c d) = _
      rw [← mul_assoc,← mul_assoc,← mul_assoc,weyl_root_rewrite m hcard a b hn]
      simp only [mul_assoc]
      rw [← mul_assoc (rootElement m (b/norm m a b) (a/norm m a b)),
        root_torus_swap m hcard]
      simp only [mul_assoc,rootElement_mul m hcard,longForm,torusElement_mul,s,e,f]
end Atlas.SuzukiFamily
