import Atlas.Lattices.EisensteinGenerators
import Atlas.Mathieu.TernaryMathieu11Full

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

def eisensteinPermutation (σ : Equiv.Perm (Fin 12)) (z : EisensteinCoordinates) :
    EisensteinCoordinates := fun i => z (σ.symm i)

theorem eisensteinPermutation_mem (g : TernaryPureAutomorphism)
    (z : EisensteinCoordinates) (hz : z ∈ eisensteinLeechModule) :
    eisensteinPermutation g.val z ∈ eisensteinLeechModule := by
  obtain ⟨m,u,hu,hc,hd⟩ := hz
  refine ⟨m,eisensteinPermutation g.val u,fun i => hu (g.val.symm i),?_,?_⟩
  · exact g.prop (eisensteinWordResidue u) hc
  · change 3*eisensteinTheta ∣ (∑ i, z (g.val.symm i))+3*m
    rw [Equiv.sum_comp]; exact hd

theorem eisensteinPermutation_lattice_iff (g : TernaryPureAutomorphism)
    (z : EisensteinCoordinates) :
    eisensteinPermutation g.val z ∈ eisensteinLeechModule ↔ z ∈ eisensteinLeechModule := by
  constructor
  · intro h
    have hh := eisensteinPermutation_mem g⁻¹ _ h
    have he : eisensteinPermutation (g⁻¹).val (eisensteinPermutation g.val z) = z := by
      funext i
      change z (g.val.symm (g.val i)) = z i
      rw [Equiv.symm_apply_apply]
    rw [he] at hh; exact hh
  · exact eisensteinPermutation_mem g z

def eisensteinRationalPermutation (σ : Equiv.Perm (Fin 12))
    (z : EisensteinRationalCoordinates) : EisensteinRationalCoordinates := fun i => z (σ.symm i)

theorem eisensteinPermutation_hermitian (σ : Equiv.Perm (Fin 12))
    (z w : EisensteinRationalCoordinates) :
    eisensteinHermitian (eisensteinRationalPermutation σ z) (eisensteinRationalPermutation σ w) =
      eisensteinHermitian z w := by
  unfold eisensteinHermitian eisensteinRationalPermutation
  congr 1
  exact σ.symm.sum_comp (fun i => star (z i) * w i)

theorem eisenstein_theta_cancel {a b : Eisenstein}
    (h : eisensteinTheta*a = eisensteinTheta*b) : a=b := by
  apply eisenstein_three_cancel
  have hh := congrArg (fun x => -eisensteinTheta*x) h
  have hs := eisensteinTheta_sq
  linear_combination hh + (a-b)*hs

theorem eisensteinCongruence_residue (z : EisensteinCoordinates) (m : Eisenstein)
    (hz : EisensteinCongruence z m) (i : Fin 12) :
    eisensteinResidue (z i) = eisensteinResidue m := by
  obtain ⟨u,hu,_,_⟩ := hz
  rw [hu i]
  simp [show eisensteinResidue eisensteinTheta = 0 by decide +kernel]

/-- The code is recovered from lattice vectors divisible coordinatewise by theta. -/
theorem eisensteinLeechModule_theta_code (u : EisensteinCoordinates)
    (hu : eisensteinTheta • u ∈ eisensteinLeechModule) :
    eisensteinWordResidue u ∈ ternaryGolay := by
  obtain ⟨m,hm⟩ := hu
  have hres := eisensteinCongruence_residue _ m hm 0
  have hz : eisensteinResidue m = 0 := by
    simpa [Pi.smul_apply,smul_eq_mul,
      show eisensteinResidue eisensteinTheta = 0 by decide +kernel] using hres.symm
  obtain ⟨a,ha⟩ := (eisensteinResidue_eq_zero m).mp hz
  have hm0 : EisensteinCongruence (eisensteinTheta • u) 0 := by
    apply (eisensteinCongruence_lift_independent _ 0 a).mp
    simpa [ha] using hm
  obtain ⟨v,hv,hc,_⟩ := hm0
  have he : u = v := by
    funext i
    apply eisenstein_theta_cancel
    simpa using hv i
  rw [he]; exact hc

/-- Pure coordinate permutations preserving the lattice necessarily preserve its code. -/
theorem eisensteinPermutation_code_necessary (σ : Equiv.Perm (Fin 12))
    (hp : ∀ z ∈ eisensteinLeechModule, eisensteinPermutation σ z ∈ eisensteinLeechModule) :
    TernaryCoordinatePreserves σ := by
  rintro w ⟨p,rfl⟩
  let q : Fin 6 → Eisenstein := fun j => (p j).val
  have hq : (fun j => eisensteinResidue (q j)) = p := by
    funext j; simp [q,eisensteinResidue]
  have he := eisensteinEncoder_residue q
  rw [hq] at he
  have hl := hp _ (eisensteinEncoder_lattice q)
  have hf : eisensteinPermutation σ (eisensteinTheta • eisensteinEncoder q) =
      eisensteinTheta • eisensteinPermutation σ (eisensteinEncoder q) := rfl
  rw [hf] at hl
  have hc := eisensteinLeechModule_theta_code _ hl
  have hs : eisensteinWordResidue (eisensteinPermutation σ (eisensteinEncoder q)) =
      fun i => ternaryEncoder p (σ.symm i) := by
    funext i
    exact congrFun he (σ.symm i)
  rw [hs] at hc; exact hc

theorem eisensteinGlue_residue (i : Fin 12) : eisensteinResidue (eisensteinGlue i) = 1 := by
  by_cases hi : i=0
  · subst i; decide +kernel
  · simp [eisensteinGlue,hi]

def eisensteinUnitMonomial (u : Fin 12 → Eisensteinˣ) (σ : Equiv.Perm (Fin 12))
    (z : EisensteinCoordinates) : EisensteinCoordinates := fun i => (u i : Eisenstein)*z (σ.symm i)

/-- The glue vector forces one common sign residue for every monomial lattice symmetry. -/
theorem eisensteinUnitMonomial_common_residue (u : Fin 12 → Eisensteinˣ)
    (σ : Equiv.Perm (Fin 12))
    (hp : ∀ z ∈ eisensteinLeechModule, eisensteinUnitMonomial u σ z ∈ eisensteinLeechModule) :
    (∀ i, eisensteinResidue (u i : Eisenstein) = 1) ∨
      (∀ i, eisensteinResidue (u i : Eisenstein) = -1) := by
  obtain ⟨m,hm⟩ := hp eisensteinGlue eisensteinGlue_mem
  have hi (i : Fin 12) : eisensteinResidue (u i : Eisenstein) = eisensteinResidue m := by
    have h := eisensteinCongruence_residue _ m hm i
    simpa [eisensteinUnitMonomial,eisensteinGlue_residue] using h
  have hn : eisensteinResidue m ≠ 0 := by
    rw [← hi 0]
    exact ((u 0).isUnit.map eisensteinResidue).ne_zero
  have hc : ∀ a : ZMod 3, a ≠ 0 → a=1 ∨ a = -1 := by decide
  rcases hc _ hn with h | h
  · left; intro i; exact (hi i).trans h
  · right; intro i; exact (hi i).trans h

/-- Any common theta-residue can be used as the congruence lift. -/
theorem eisensteinLeechModule_common_lift (z : EisensteinCoordinates)
    (hz : z ∈ eisensteinLeechModule) (m : Eisenstein)
    (hm : ∀ i, eisensteinResidue (z i) = eisensteinResidue m) :
    EisensteinCongruence z m := by
  obtain ⟨n,hn⟩ := hz
  have he : eisensteinResidue (n-m) = 0 := by
    have hi := eisensteinCongruence_residue z n hn 0
    rw [map_sub,← hi,hm 0,sub_self]
  obtain ⟨a,ha⟩ := (eisensteinResidue_eq_zero _).mp he
  have hna : n = m + eisensteinTheta*a := by linear_combination ha
  rw [hna] at hn
  exact (eisensteinCongruence_lift_independent z m a).mp hn

/-- The ternary residue code is necessary for any explicit common-lift witness. -/
theorem eisensteinLeechModule_code_of_witness (z : EisensteinCoordinates)
    (hz : z ∈ eisensteinLeechModule) (m : Eisenstein) (u : EisensteinCoordinates)
    (hu : ∀ i, z i = m + eisensteinTheta*u i) :
    eisensteinWordResidue u ∈ ternaryGolay := by
  have hm := eisensteinLeechModule_common_lift z hz m (fun i => by
    rw [hu i]
    simp [show eisensteinResidue eisensteinTheta = 0 by decide +kernel])
  obtain ⟨v,hv,hc,_⟩ := hm
  have he : u = v := by
    funext i
    apply eisenstein_theta_cancel
    exact add_left_cancel ((hu i).symm.trans (hv i))
  rw [he]; exact hc

end Atlas.Lattices
