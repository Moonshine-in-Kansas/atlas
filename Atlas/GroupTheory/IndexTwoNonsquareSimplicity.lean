import Atlas.GroupTheory.IndexTwoInvariantNormals
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Lean.Elab.Tactic.Omega

namespace Atlas.GroupTheory

/-- The two cosets of an index-two subgroup, without a splitting assumption. -/
theorem index_two_normal_form {J : Type*} [Group J]
    (K : Subgroup J) (hi : K.index = 2) (d : J) (hd : d ∉ K)
    (g : J) : ∃ k : K, g = k.val ∨ g = k.val * d := by
  by_cases hg : g ∈ K
  · exact ⟨⟨g,hg⟩, Or.inl rfl⟩
  · have hdi : d⁻¹ ∉ K := by simpa using hd
    have hgd : g * d⁻¹ ∈ K :=
      (K.mul_mem_iff_of_index_two hi).mpr (by simp [hg,hdi])
    exact ⟨⟨g * d⁻¹,hgd⟩, Or.inr (by simp [mul_assoc])⟩

/-- Stability under one outside conjugation promotes normality to the full group.
The outside element need not be an involution. -/
theorem normal_map_of_index_two_conjugation_invariant {J : Type*} [Group J]
    (K : Subgroup J) [K.Normal] (hi : K.index = 2) (d : J) (hd : d ∉ K)
    (H : Subgroup K) [H.Normal]
    (hstable : H.map (MulAut.conjNormal d).toMonoidHom = H) :
    (H.map K.subtype).Normal := by
  constructor
  intro n hn g
  obtain ⟨n,hn,rfl⟩ := hn
  obtain ⟨k,hk | hk⟩ := index_two_normal_form K hi d hd g
  · subst g
    exact ⟨k*n*k⁻¹, (inferInstance : H.Normal).conj_mem n hn k, rfl⟩
  · subst g
    have han : MulAut.conjNormal d n ∈ H := by
      rw [← hstable]
      exact ⟨n,hn,rfl⟩
    refine ⟨k*(MulAut.conjNormal d n)*k⁻¹,
      (inferInstance : H.Normal).conj_mem _ han k, ?_⟩
    change k.val * (d*n.val*d⁻¹) * k.val⁻¹ = (k.val*d)*n.val*(k.val*d)⁻¹
    simp only [mul_inv_rev,mul_assoc]

/-- Conjugation by an outside element is involutive on normal subgroups of an
index-two subgroup, even when it is not involutive on elements. -/
theorem index_two_normal_subgroup_double_conjugation {J : Type*} [Group J]
    (K : Subgroup J) [K.Normal] (hi : K.index = 2) (d : J)
    (H : Subgroup K) [H.Normal] :
    (H.map (MulAut.conjNormal d).toMonoidHom).map
      (MulAut.conjNormal d).toMonoidHom = H := by
  have hdd : d*d ∈ K := (K.mul_mem_iff_of_index_two hi).mpr Iff.rfl
  let k : K := ⟨d*d,hdd⟩
  have he : (MulAut.conjNormal d).toMonoidHom.comp
      (MulAut.conjNormal d).toMonoidHom = (MulAut.conj k).toMonoidHom := by
    ext x
    change d * (d * x.val * d⁻¹) * d⁻¹ = (d*d)*x.val*(d*d)⁻¹
    simp only [mul_inv_rev,mul_assoc]
  rw [Subgroup.map_map, he]
  exact Subgroup.Normal.map_conj_eq H k

/-- An index-two minimal normal subgroup of nonsquare order is simple. This
argument requires no involutory complement and no action hypotheses. -/
theorem simple_of_index_two_minimal_normal_nonsquare {J : Type*}
    [Group J] [Finite J] (K : Subgroup J) [K.Normal] [Nontrivial K]
    (hi : K.index = 2)
    (hmin : ∀ L : Subgroup J, L.Normal → L = ⊥ ∨ K ≤ L)
    (hns : ∀ n : ℕ, Nat.card K ≠ n ^ 2) : IsSimpleGroup K := by
  have hproper : K ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hi
    exact (by decide : (1 : ℕ) ≠ 2) hi
  obtain ⟨d,hd⟩ : ∃ d : J, d ∉ K := by
    by_contra h
    apply hproper
    apply top_unique
    intro g _
    exact Classical.not_not.mp (fun hg => h ⟨g,hg⟩)
  let a : K ≃* K := MulAut.conjNormal d
  have hminimal (H : Subgroup K) (hH : H.Normal)
      (hstable : H.map a.toMonoidHom = H) : H = ⊥ ∨ H = ⊤ := by
    letI := hH
    have hL := normal_map_of_index_two_conjugation_invariant K hi d hd H hstable
    rcases hmin (H.map K.subtype) hL with h | h
    · left
      apply bot_unique
      intro n hn
      have he : n.val = 1 := by
        have hm : n.val ∈ H.map K.subtype := ⟨n,hn,rfl⟩
        simpa [h] using hm
      exact Subtype.ext he
    · right
      apply top_unique
      intro n _
      obtain ⟨m,hm,he⟩ := h n.prop
      have : m = n := Subtype.ext he
      simpa [this] using hm
  constructor
  intro N hN
  letI := hN
  by_cases hb : N = ⊥
  · exact Or.inl hb
  by_cases ht : N = ⊤
  · exact Or.inr ht
  exfalso
  let M := N.map a.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  have hdouble : M.map a.toMonoidHom = N :=
    index_two_normal_subgroup_double_conjugation K hi d N
  have hinv : (N ⊓ M).map a.toMonoidHom = N ⊓ M := by
    rw [Subgroup.map_inf N M a.toMonoidHom a.injective, hdouble]
    exact inf_comm _ _
  have hsinv : (N ⊔ M).map a.toMonoidHom = N ⊔ M := by
    rw [Subgroup.map_sup, hdouble]
    exact sup_comm _ _
  have hiNM : N ⊓ M = ⊥ := by
    rcases hminimal _ inferInstance hinv with h | h
    · exact h
    · exact False.elim (ht (top_unique (h ▸ inf_le_left)))
  have hsNM : N ⊔ M = ⊤ := by
    rcases hminimal _ inferInstance hsinv with h | h
    · exact False.elim (hb (bot_unique (h ▸ le_sup_left)))
    · exact h
  have hdis : Disjoint N M := disjoint_iff.mpr hiNM
  have hc : N.IsComplement' M := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdis, ?_⟩
    intro k
    have hk : k ∈ N ⊔ M := hsNM.symm ▸ Subgroup.mem_top k
    obtain ⟨n,hn,m,hm,he⟩ := Subgroup.mem_sup_of_normal_right.mp hk
    exact ⟨(⟨n,hn⟩,⟨m,hm⟩),he⟩
  have hmcard : Nat.card M = Nat.card N :=
    (Nat.card_congr (a.subgroupMap N).toEquiv).symm
  apply hns (Nat.card N)
  calc
    Nat.card K = Nat.card (N × M) := Nat.card_congr hc.equiv
    _ = Nat.card N ^ 2 := by rw [Nat.card_prod, hmcard, pow_two]

/-- An ambient normal subgroup of index at most two contains the commutator:
its quotient is trivial or cyclic of order two. -/
theorem commutator_le_of_normal_index_le_two {J : Type*} [Group J] [Finite J]
    (N : Subgroup J) [N.Normal] (hi : N.index ≤ 2) : commutator J ≤ N := by
  by_cases ht : N = ⊤
  · rw [ht]
    exact le_top
  have hlo := N.one_lt_index_of_ne_top ht
  have he : N.index = 2 := by omega
  have hcard : Nat.card (J ⧸ N) = 2 := N.index_eq_card.symm.trans he
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic (J ⧸ N) := isCyclic_of_prime_card hcard
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

/-- The normal-index bound gives exactly the ambient minimality hypothesis
needed by the nonsquare simplicity argument for the derived subgroup. -/
theorem commutator_normal_dichotomy_of_index_bound {J : Type*}
    [Group J] [Finite J]
    (hbound : ∀ N : Subgroup J, N.Normal → N ≠ ⊥ → N.index ≤ 2)
    (N : Subgroup J) (hN : N.Normal) : N = ⊥ ∨ commutator J ≤ N := by
  by_cases hb : N = ⊥
  · exact Or.inl hb
  · letI := hN
    exact Or.inr (commutator_le_of_normal_index_le_two N (hbound N hN hb))

end Atlas.GroupTheory

