import Atlas.LinearGroups.ReeG2.RootDerived
import Atlas.LinearGroups.ReeG2.ConstantWords
import Atlas.LinearGroups.ReeG2.PointTransitivity
import Atlas.FieldTheory.ReeScalarSquares

noncomputable section
namespace Atlas.ReeG2
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem upsilon_mem_derivedAmbient (m : ℕ) (hp : Parameters F m) :
    (upsilon : Ambient F) ∈ derivedAmbient m := by
  have hb := beta_mem_derivedAmbient m hp 1
  have hc := conjugate_mem_derivedAmbient m (upsilon_mem_generated m) hb
  rw [upsilon_inv] at hc
  rw [← beta_weyl_word m]
  exact (derivedAmbient m).mul_mem ((derivedAmbient m).mul_mem hb hc) hb

theorem torus_minus_one_mem_derivedAmbient (m : ℕ) (hp : Parameters F m) :
    torus m (-1 : Fˣ) ∈ derivedAmbient m := by
  have ha := alpha_mem_derivedAmbient m hp 1
  have hb := beta_mem_derivedAmbient m hp 1
  have hc := gamma_mem_derivedAmbient m hp.cardinality 1
  have hca := conjugate_mem_derivedAmbient m (upsilon_mem_generated m) ha
  have hcc := conjugate_mem_derivedAmbient m (upsilon_mem_generated m) hc
  rw [upsilon_inv] at hca hcc
  rw [← minus_one_torus_word m hp.cardinality]
  exact (derivedAmbient m).mul_mem ((derivedAmbient m).mul_mem
    ((derivedAmbient m).mul_mem ((derivedAmbient m).mul_mem ha
      ((derivedAmbient m).inv_mem hca)) hb) hcc) ha

theorem torus_square_mem_derivedAmbient (m : ℕ) (l : Fˣ) :
    torus m (l^2) ∈ derivedAmbient m := by
  have he : ⁅(upsilon : Ambient F), torus m l⁻¹⁆ = torus m (l^2) := by
    rw [commutatorElement_def,upsilon_torus,inv_inv]
    have hi : (torus m l⁻¹)⁻¹ = torus m l := by
      change ((torusHom m) l⁻¹)⁻¹ = (torusHom m) l
      simp
    rw [hi,← torus_mul,pow_two]
  rw [← he]
  exact commutator_mem_derivedAmbient m (upsilon_mem_generated m) (torus_mem_generated m _)

theorem torus_mem_derivedAmbient (m : ℕ) (hp : Parameters F m) (l : Fˣ) :
    torus m l ∈ derivedAmbient m := by
  rcases unit_eq_square_or_negative_square m hp.cardinality l with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · exact torus_square_mem_derivedAmbient m k
  · rw [show -(k^2) = (-1)*(k^2) by simp,torus_mul]
    exact (derivedAmbient m).mul_mem (torus_minus_one_mem_derivedAmbient m hp)
      (torus_square_mem_derivedAmbient m k)

/-- Perfectness of the actual generated Ree matrix group in the public range. -/
theorem perfect (m : ℕ) (hp : Parameters F m) : Group.IsPerfect (Model F m) := by
  have hle : generated F m ≤ derivedAmbient m := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (((⟨a,rfl⟩ | ⟨b,rfl⟩) | ⟨c,rfl⟩) | ⟨l,rfl⟩) | hw
    · exact alpha_mem_derivedAmbient m hp a
    · exact beta_mem_derivedAmbient m hp b
    · exact gamma_mem_derivedAmbient m hp.cardinality c
    · exact torus_mem_derivedAmbient m hp l
    · have : g = upsilon := Set.mem_singleton_iff.mp hw
      subst g
      exact upsilon_mem_derivedAmbient m hp
  constructor
  apply top_unique
  intro x hx
  obtain ⟨y,hy,he⟩ := hle x.property
  have hh : y = x := Subtype.ext he
  simpa [hh] using hy

end Atlas.ReeG2
