import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-! Finite abelian groups killed by four split into cyclic factors of order four and two. -/
namespace Atlas.LinearAlgebra

noncomputable def splitPiAddEquiv {ι : Type*} (p : ι → Prop) [DecidablePred p]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] :
    (∀ i, M i) ≃+ ((∀ i : {i // p i}, M i.val) × (∀ i : {i // ¬p i}, M i.val)) where
  toEquiv := Equiv.piEquivPiSubtypeProd p M
  map_add' _ _ := rfl

noncomputable def piFinAddEquiv {ι : Type*} [Fintype ι] (M : Type*) [AddCommGroup M] :
    (ι → M) ≃+ (Fin (Fintype.card ι) → M) where
  toEquiv := Equiv.piCongrLeft' (fun _ => M) (Fintype.equivFin ι)
  map_add' _ _ := rfl

theorem exponent_four_decomposition (G : Type*) [AddCommGroup G] [Finite G]
    (hfour : ∀ g : G, (4 : ℕ) • g=0) :
    ∃ m n : ℕ, Nonempty (G ≃+ ((Fin m → ZMod 4) × (Fin n → ZMod 2))) := by
  classical
  obtain ⟨ι,hι,k,hk,⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let f : G ≃+ (∀ i, ZMod (k i)) := e.trans (DirectSum.addEquivProd _)
  have hdiv (i : ι) : k i ∣ 4 := by
    have h := congrFun (congrArg f (hfour (f.symm (Pi.single i 1)))) i
    simp only [map_nsmul,map_zero,f.apply_symm_apply] at h
    have he : (4 : ℕ) • (1 : ZMod (k i))=0 := by simpa using h
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr he
    simpa only [ZMod.addOrderOf_one] using hd
  have hcases (i : ι) : k i=4 ∨ k i=2 := by
    have hi := hk i
    have hd := hdiv i
    have hle : k i≤4 := Nat.le_of_dvd (by decide) hd
    interval_cases hki : k i <;> simp_all
  let I := {i : ι // k i=4}
  let J := {i : ι // ¬k i=4}
  let eI : (∀ i : I,ZMod (k i.val)) ≃+ (I → ZMod 4) :=
    AddEquiv.piCongrRight (fun i => (ZMod.ringEquivCongr i.prop).toAddEquiv)
  let eJ : (∀ i : J,ZMod (k i.val)) ≃+ (J → ZMod 2) :=
    AddEquiv.piCongrRight (fun i =>
      (ZMod.ringEquivCongr ((hcases i.val).resolve_left i.prop)).toAddEquiv)
  exact ⟨Fintype.card I,Fintype.card J,⟨f.trans
    ((splitPiAddEquiv (fun i => k i=4) (fun i => ZMod (k i))).trans
      ((eI.prodCongr eJ).trans ((piFinAddEquiv (ι := I) (ZMod 4)).prodCongr
        (piFinAddEquiv (ι := J) (ZMod 2)))))⟩⟩

end Atlas.LinearAlgebra
