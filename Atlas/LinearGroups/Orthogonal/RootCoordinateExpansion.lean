import Atlas.LinearGroups.Orthogonal.RootBasisGeneration

noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic Module
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype ι]

theorem coordinate_siegel_mem_of_coefficient_vanishing
    (Q : QuadraticForm F V) (b : Basis ι F V) (i : ι) (hu : Q (b i)=0)
    (v : V) (huv : Q.polarBilin (b i) v=0)
    (hv : ∀j, Q.polarBilin (b i) (b j) ≠ 0 → b.repr v j=0) :
    siegelElement Q (b i) v hu huv ∈ coordinateRootSubgroup Q b := by
  have hj (j : ι) : Q.polarBilin (b i) (b.repr v j • b j)=0 := by
    by_cases hh : Q.polarBilin (b i) (b j)=0
    · rw [map_smul,hh,smul_zero]
    · rw [hv j hh,zero_smul,map_zero]
  let w (j : ι) : rootParameterSpace Q (b i) := ⟨b.repr v j • b j,hj j⟩
  have hs (s : Finset ι) : rootParameterHom Q (b i) hu (Multiplicative.ofAdd (∑j∈s,w j)) ∈
      coordinateRootSubgroup Q b := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (coordinateRootSubgroup Q b).one_mem
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      change rootParameterHom Q (b i) hu
        (Multiplicative.ofAdd (w j) * Multiplicative.ofAdd (∑k∈s,w k)) ∈ _
      rw [map_mul]
      exact (coordinateRootSubgroup Q b).mul_mem (coordinateRoot_mem Q b i j _ hu _) ih
  have he : (∑j,w j) = (⟨v,huv⟩ : rootParameterSpace Q (b i)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,w]
    exact b.sum_repr v
  have hh := hs Finset.univ
  rw [he] at hh
  exact hh

theorem coordinate_root_le_of_coefficient_vanishing
    (Q : QuadraticForm F V) (b : Basis ι F V) (i : ι) (u : V)
    (hu : Q u=0) (hbi : b i=u)
    (hv : ∀v, Q.polarBilin u v=0 → ∀j, Q.polarBilin u (b j) ≠ 0 → b.repr v j=0) :
    rootSubgroup Q u hu ≤ coordinateRootSubgroup Q b := by
  subst u
  rintro g ⟨v,rfl⟩
  exact coordinate_siegel_mem_of_coefficient_vanishing Q b i hu v.toAdd.val v.toAdd.prop
    (hv v.toAdd.val v.toAdd.prop)

end Atlas.Orthogonal
