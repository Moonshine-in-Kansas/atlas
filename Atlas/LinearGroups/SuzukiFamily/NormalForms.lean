import Atlas.LinearGroups.SuzukiFamily.GlobalPointAction
import Atlas.LinearGroups.SuzukiFamily.GroupRelations

/-! The two candidate Bruhat cells, with disjointness and unique parameters. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def shortForm (m : ℕ) (a b : F) (t : Fˣ) : Atlas.Symplectic.Sp 2 F :=
  rootElement m a b * torusElement m t

def longForm (m : ℕ) (a b : F) (t : Fˣ) (c d : F) : Atlas.Symplectic.Sp 2 F :=
  rootElement m a b * weylElement * torusElement m t * rootElement m c d

theorem shortForm_infinity (m : ℕ) (a b : F) (t : Fˣ) :
    pointLeft (shortForm m a b t) infinityPoint=infinityPoint := by
  simp only [shortForm,pointLeft_mul,Function.comp_apply,torus_infinity,root_infinity]

theorem longForm_infinity (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (t : Fˣ) (c d : F) :
    pointLeft (longForm m a b t c d) infinityPoint=affinePoint m a b := by
  simp only [longForm,pointLeft_mul,Function.comp_apply,root_infinity,torus_infinity,
    weyl_infinity m,root_affine m hcard,map_zero,mul_zero,add_zero]

theorem short_ne_long (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b c d e f : F) (s t : Fˣ) : shortForm m a b s ≠ longForm m c d t e f := by
  intro he
  have hp := congrArg (fun g => pointLeft g infinityPoint) he
  rw [shortForm_infinity,longForm_infinity m hcard] at hp
  exact infinity_ne_affine m c d hp

theorem torus_root_injective (m : ℕ) :
    Function.Injective (fun p : Fˣ × F × F =>
      torusElement m p.1 * rootElement m p.2.1 p.2.2) := by
  rintro ⟨s,a,b⟩ ⟨t,c,d⟩ he
  have hst : s=t := by
    apply Units.ext
    have hh := congrArg (fun g => matrix g 1 1) he
    simpa [matrix_mul,matrix_torus,matrix_root,h,u,Matrix.mul_apply,
      Matrix.diagonal_apply,Fin.sum_univ_succ,-theta_apply] using hh
  subst t
  have hab := rootElement_injective m (a₁ := (a,b)) (a₂ := (c,d)) (mul_left_cancel he)
  cases hab
  rfl

theorem shortForm_injective (m : ℕ) :
    Function.Injective (fun p : F × F × Fˣ => shortForm m p.1 p.2.1 p.2.2) := by
  rintro ⟨a,b,s⟩ ⟨c,d,t⟩ he
  have hst : s=t := by
    apply Units.ext
    have hh := congrArg (fun g => matrix g 1 1) he
    simpa [shortForm,matrix_mul,matrix_torus,matrix_root,h,u,Matrix.mul_apply,
      Matrix.diagonal_apply,Fin.sum_univ_succ,-theta_apply] using hh
  subst t
  have hab := rootElement_injective m (a₁ := (a,b)) (a₂ := (c,d)) (mul_right_cancel he)
  cases hab
  rfl

theorem longForm_injective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Injective (fun p : (F × F) × (Fˣ × F × F) =>
      longForm m p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  rintro ⟨⟨a,b⟩,⟨s,c,d⟩⟩ ⟨⟨e,f⟩,⟨t,k,l⟩⟩ he
  have hp := congrArg (fun g => pointLeft g infinityPoint) he
  simp only [longForm_infinity m hcard] at hp
  have hef := affinePoint_injective m (a₁ := (a,b)) (a₂ := (e,f)) hp
  cases hef
  have ht : torusElement m s * rootElement m c d = torusElement m t * rootElement m k l := by
    apply mul_left_cancel (a := rootElement m a b * weylElement)
    simpa only [longForm,mul_assoc] using he
  have hk := torus_root_injective m (a₁ := (s,c,d)) (a₂ := (t,k,l)) ht
  cases hk
  rfl
end Atlas.SuzukiFamily
