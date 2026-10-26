import Atlas.LinearGroups.SuzukiFamily.RootDerived
import Mathlib.Algebra.CharP.Reduced

/-! Perfectness, completing root commutators with an explicit Weyl word and torus squares. -/
noncomputable section
namespace Atlas.SuzukiFamily
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem weyl_root_word (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    (rootElement m 1 1)⁻¹ * (weylElement * rootElement m 0 1 * weylElement) *
      (rootElement m 1 0)⁻¹ = (weylElement : Atlas.Symplectic.Sp 2 F) := by
  have hn : norm m (0:F) 1≠0 := by simp [norm]
  have he := weyl_root_rewrite m hcard 0 1 hn
  have ht : bruhatTorus m (0:F) 1 hn=1 := by
    apply Units.ext
    simp [bruhatTorus,norm]
  simp only [ht,torusElement_one,mul_one] at he
  have hi : inverseFirst m (0:F) 1=1 := by simp [inverseFirst,norm]
  have hj : inverseSecond m (0:F) 1=1 := by simp [inverseSecond,hi,norm]
  simp only [hi,hj] at he
  have hn1 : norm m (0:F) 1=1 := by simp [norm]
  rw [hn1,div_one,zero_div] at he
  rw [he]
  group

theorem weyl_mem_derivedAmbient (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (hm : 1≤m) :
    (weylElement : Atlas.Symplectic.Sp 2 F) ∈ derivedAmbient m := by
  have hc := conjugate_mem_derivedAmbient m (weylElement_mem m)
    (root_mem_derivedAmbient m hcard hm 0 1)
  rw [weylElement_inv] at hc
  rw [← weyl_root_word m hcard]
  exact (derivedAmbient m).mul_mem
    ((derivedAmbient m).mul_mem ((derivedAmbient m).inv_mem (root_mem_derivedAmbient m hcard hm 1 1)) hc)
    ((derivedAmbient m).inv_mem (root_mem_derivedAmbient m hcard hm 1 0))

theorem torus_square_mem_derivedAmbient (m : ℕ) (t : Fˣ) :
    torusElement m (t^2) ∈ derivedAmbient m := by
  have he : ⁅(weylElement : Atlas.Symplectic.Sp 2 F),torusElement m t⁻¹⁆ = torusElement m (t^2) := by
    rw [commutatorElement_def,weylElement_inv,weyl_torus_weyl,inv_inv]
    rw [← torusElement_inv,inv_inv,← torusElement_mul,pow_two]
  rw [← he]
  exact commutator_mem_derivedAmbient m (weylElement_mem m) (torusElement_mem m t⁻¹)

theorem torus_mem_derivedAmbient (m : ℕ) (t : Fˣ) :
    torusElement m t ∈ derivedAmbient m := by
  obtain ⟨s,hs⟩ := isSquare_of_charTwo' (t:F)
  have hs0 : s≠0 := by intro he; subst s; simpa using hs
  let v : Fˣ := Units.mk0 s hs0
  have hv : v^2=t := by apply Units.ext; simpa [v,pow_two] using hs.symm
  rw [← hv]
  exact torus_square_mem_derivedAmbient m v

theorem perfect_of_large (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (hm : 1≤m) :
    _root_.Group.IsPerfect (Group F m) := by
  have hle : generated (F := F) m ≤ derivedAmbient m := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ((⟨⟨a,b⟩,rfl⟩ | ⟨t,rfl⟩) | hw)
    · exact root_mem_derivedAmbient m hcard hm a b
    · exact torus_mem_derivedAmbient m t
    · have he : g=weylElement := Set.mem_singleton_iff.mp hw
      subst g
      exact weyl_mem_derivedAmbient m hcard hm
  constructor
  apply top_unique
  intro x hx
  obtain ⟨y,hy,he⟩ := hle x.property
  have hh : y=x := Subtype.ext he
  simpa [hh] using hy
end Atlas.SuzukiFamily
