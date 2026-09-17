import Atlas.LinearAlgebra.SymplecticBasis
import Mathlib.Tactic

/-! # Actual isometries between alternating spaces of equal finite dimension -/
noncomputable section
namespace Atlas.AlternatingForm
universe u v w
variable {F : Type u} [Field F]

/-- Nondegenerate alternating forms of equal finite dimension admit an actual linear isometry. -/
theorem isometry_exists_of_finrank_eq
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate)
    (C : LinearMap.BilinForm F W) (hCalt : C.IsAlt) (hC : C.Nondegenerate)
    (hdim : Module.finrank F V = Module.finrank F W) :
    ∃ e : V ≃ₗ[F] W, ∀ y z, C (e y) (e z) = B y z := by
  generalize hn : Module.finrank F V = n
  induction n using Nat.strong_induction_on generalizing V W with
  | h n ih =>
    by_cases hn0 : n = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
      haveI : Subsingleton W := Module.finrank_zero_iff.mp (hdim.symm.trans (hn.trans hn0))
      refine ⟨LinearEquiv.ofSubsingleton V W,?_⟩
      intro y z
      have hy : y = 0 := Subsingleton.elim _ _
      have hz : z = 0 := Subsingleton.elim _ _
      simp [hy,hz]
    · haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
      haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (M := W) (by omega)
      obtain ⟨a,ha⟩ := exists_ne (0 : V)
      obtain ⟨b,hb⟩ := exists_ne (0 : W)
      obtain ⟨f,haf⟩ := exists_partner B hB ha
      obtain ⟨g,hbg⟩ := exists_partner C hC hb
      let P := complement B a f
      let R := complement C b g
      let BP := B.restrict P
      let CR := C.restrict R
      have hPdim := finrank_complement B hA a f haf
      have hRdim := finrank_complement C hCalt b g hbg
      have hlt : Module.finrank F P < n := by dsimp only [P]; omega
      have heq : Module.finrank F P = Module.finrank F R := by dsimp only [P,R]; omega
      obtain ⟨i,hi⟩ := ih (Module.finrank F P) hlt
        BP (complement_alternating B hA a f haf) (complement_nondegenerate B hA a f haf hB)
        CR (complement_alternating C hCalt b g hbg) (complement_nondegenerate C hCalt b g hbg hC)
        heq rfl
      let L := split B hA a f haf
      let M := split C hCalt b g hbg
      let E : V ≃ₗ[F] W := L.trans (((LinearEquiv.refl F (F×F)).prodCongr i).trans M.symm)
      have hE (z : (F × F) × P) : E (L.symm z) = M.symm (z.1,i z.2) := by
        change M.symm (((LinearEquiv.refl F (F×F)).prodCongr i) (L (L.symm z))) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      refine ⟨E,?_⟩
      intro y z
      obtain ⟨y,rfl⟩ := L.symm.surjective y
      obtain ⟨z,rfl⟩ := L.symm.surjective z
      rw [hE,hE]
      rw [split_form C hCalt b g hbg,split_form B hA a f haf]
      have hh := hi y.2 z.2
      change C (i y.2).val (i z.2).val = B y.2.val z.2.val at hh
      rw [hh]

end Atlas.AlternatingForm
