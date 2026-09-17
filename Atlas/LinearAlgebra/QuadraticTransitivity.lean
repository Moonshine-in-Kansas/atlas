import Atlas.LinearAlgebra.QuadraticReflection
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-! # Full quadratic isometry transitivity on nonzero singular vectors -/
noncomputable section
namespace Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem singular_not_polar_radical (hQ : Q.radical=⊥) (u : V) (hu : u≠0)
    (hqu : Q u=0) : ¬ ∀ w, Q.polarBilin u w=0 := by
  intro h
  have hm : u ∈ Q.radical := ⟨hqu,LinearMap.ext h⟩
  rw [hQ,Submodule.mem_bot] at hm
  exact hu hm

/-- Two nonzero linear pairings admit a common nonzero value, even over F₂. -/
theorem exists_pairing_both (u v : V)
    (hu : ¬ ∀ w, Q.polarBilin u w=0) (hv : ¬ ∀ w, Q.polarBilin v w=0) :
    ∃ w, Q.polarBilin u w≠0 ∧ Q.polarBilin v w≠0 := by
  obtain ⟨a,ha⟩ := exists_normalized_partner Q u hu
  obtain ⟨b,hb⟩ := exists_normalized_partner Q v hv
  by_cases hva : Q.polarBilin v a=0
  · by_cases hub : Q.polarBilin u b=0
    · refine ⟨a+b,?_,?_⟩ <;> simp only [map_add,ha,hb,hva,hub,zero_add,add_zero,ne_eq,one_ne_zero,not_false_eq_true]
    · exact ⟨b,hub,hb ▸ one_ne_zero⟩
  · exact ⟨a,ha ▸ one_ne_zero,hva⟩

/-- Orthogonal singular vectors have a singular connector pairing nontrivially with both. -/
theorem exists_singular_connector (u v : V) (hqu : Q u=0)
    (huv : Q.polarBilin u v=0)
    (hu : ¬ ∀ w, Q.polarBilin u w=0) (hv : ¬ ∀ w, Q.polarBilin v w=0) :
    ∃ w, Q w=0 ∧ Q.polarBilin u w≠0 ∧ Q.polarBilin v w≠0 := by
  obtain ⟨w,huw,hvw⟩ := exists_pairing_both Q u v hu hv
  have hvu : Q.polarBilin v u=0 := (polar_swap Q v u).trans huv
  have huu : Q.polarBilin u u=0 := by rw [polar_self,hqu,mul_zero]
  refine ⟨w-(Q w / Q.polarBilin u w) • u, ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg,← neg_smul,add_smul,hqu,polar_swap Q w u]
    field_simp
    ring
  · simpa only [map_sub,map_smul,huu,smul_zero,sub_zero] using huw
  · simpa only [map_sub,map_smul,hvu,smul_zero,sub_zero] using hvw

/-- Transitivity is proved by one or two actual quadratic reflections. -/
theorem exists_isometry_singular (hQ : Q.radical=⊥) (u v : V)
    (hu : u≠0) (hv : v≠0) (hqu : Q u=0) (hqv : Q v=0) :
    ∃ g : Q.IsometryEquiv Q, g u=v := by
  by_cases huv : Q.polarBilin u v=0
  · obtain ⟨w,hqw,huw,hvw⟩ := exists_singular_connector Q u v hqu huv
      (singular_not_polar_radical Q hQ u hu hqu) (singular_not_polar_radical Q hQ v hv hqv)
    obtain ⟨g,hg⟩ := reflection_transports Q u w hqu hqw huw
    have hwv : Q.polarBilin w v≠0 := by rwa [polar_swap Q w v]
    obtain ⟨k,hk⟩ := reflection_transports Q w v hqw hqv hwv
    refine ⟨g.trans k,?_⟩
    change k (g u)=v
    rw [hg,hk]
  · exact reflection_transports Q u v hqu hqv huv

end Atlas.Quadratic
