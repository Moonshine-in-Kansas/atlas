import Atlas.GroupTheory.InvariantOrbitDivisibility
import Mathlib.GroupTheory.GroupAction.Primitive

namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

/-- One distinguished suborbit and divisible remaining orbits obstruct nontrivial blocks. -/
theorem primitive_of_one_suborbit_divisible_rest
    {G K X : Type*} [Group G] [Group K] [MulAction G X] [MulAction K X]
    [Finite X] [IsPretransitive G X]
    (x : X) (φ : K →* G) (hact : ∀k : K,∀y : X,φ k • y=k • y)
    (hfix : ∀k : K,k • x=x) (O : Set X) (hxO : x∉O)
    (hOstable : ∀k : K,∀y : X,k • y∈O ↔ y∈O)
    (hOtrans : ∀a∈O,∀b∈O,∃g : G,g • x=x ∧ g • a=b)
    (n : ℕ) (hdiv : ∀y : X,y≠x → y∉O → n∣Nat.card (orbit K y))
    (harith : ∀d m : ℕ,∀e : Bool,d=1+(if e then Nat.card O else 0)+n*m →
      d∣Nat.card X → d=1 ∨ d=Nat.card X) : IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base x
  intro B hx hB
  have hb (k : K) (y : X) (hy : y∈B) : k • y∈B := by
    have hkg : φ k∈stabilizer G x := by change φ k • x=x; rw [hact,hfix]
    have he := hB.stabilizer_le hx hkg
    rw [←hact,←he,Set.smul_mem_smul_set_iff]
    exact hy
  let T : Set X := {y | y∈B ∧ y≠x ∧ y∉O}
  have ht : n∣Nat.card T := invariant_card_dvd_of_orbits T (Set.toFinite _) (by
    intro k y hy
    refine ⟨hb k y hy.1,?_,?_⟩
    · intro he
      have h := congrArg (fun z : X=>k⁻¹ • z) he
      rw [inv_smul_smul,hfix] at h
      exact hy.2.1 h
    · exact fun he=>hy.2.2 ((hOstable k y).mp he)) n (fun y hy=>hdiv y hy.2.1 hy.2.2)
  obtain ⟨m,hm⟩ := ht
  have hpart : B=({x}∪(B∩O))∪T := by
    ext y
    constructor
    · intro hy
      by_cases he : y=x
      · exact Or.inl (Or.inl he)
      by_cases ho : y∈O
      · exact Or.inl (Or.inr ⟨hy,ho⟩)
      · exact Or.inr ⟨hy,he,ho⟩
    · rintro ((he|hy)|hy)
      · exact (show y=x from he).symm ▸ hx
      · exact hy.1
      · exact hy.1
  have hd1 : Disjoint ({x} : Set X) (B∩O) := by
    rw [Set.disjoint_left]; intro y hy hz; have he : y=x := hy; subst y; exact hxO hz.2
  have hd2 : Disjoint ({x}∪(B∩O)) T := by
    rw [Set.disjoint_left]
    intro y hy hz
    rcases hy with hy|hy
    · exact hz.2.1 hy
    · exact hz.2.2 hy.2
  have hc : Nat.card B=1+Nat.card ↥(B∩O)+n*m := by
    change B.ncard=1+(B∩O).ncard+n*m
    conv_lhs => rw [hpart,Set.ncard_union_eq hd2,Set.ncard_union_eq hd1,Set.ncard_singleton]
    change 1+Nat.card ↥(B∩O)+Nat.card T=_
    rw [hm]
    rfl
  have hO : B∩O=∅ ∨ B∩O=O := by
    by_cases he : B∩O=∅
    · exact Or.inl he
    right
    obtain ⟨a,ha⟩ := Set.nonempty_iff_ne_empty.mpr he
    apply Set.Subset.antisymm Set.inter_subset_right
    intro b hbO
    obtain ⟨g,hgx,hga⟩ := hOtrans a ha.2 b hbO
    refine ⟨?_,hbO⟩
    have heq := hB.stabilizer_le hx hgx
    rw [←hga,←heq,Set.smul_mem_smul_set_iff]
    exact ha.1
  have hc' : Nat.card B=1 ∨ Nat.card B=Nat.card X := by
    rcases hO with he|he
    · simp only [he,Nat.card_eq_fintype_card (α := ↥(∅ : Set X)),Fintype.card_ofIsEmpty,add_zero] at hc
      exact harith _ m false (by simpa using hc) (hB.ncard_dvd_card ⟨x,hx⟩)
    · rw [he] at hc
      exact harith _ m true hc (hB.ncard_dvd_card ⟨x,hx⟩)
  rcases hc' with he|he
  · exact Or.inl (B.ncard_le_one_iff_subsingleton.mp (by change Nat.card B≤1; omega))
  · exact Or.inr (B.eq_univ_iff_ncard.mpr he)

end Atlas.GroupTheory
