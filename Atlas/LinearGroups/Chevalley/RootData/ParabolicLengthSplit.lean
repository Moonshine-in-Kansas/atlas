import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! Greedy parabolic descent in the actual root-permutation Weyl image.
This gives a length-additive factorization with a reduced word in selected
simple reflections. Uniqueness and a coset generating polynomial are separate. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Every actual Weyl element has a length-additive right factor represented
by a reduced word using J, leaving a factor positive on every simple root in J.
No uniqueness of this factorization is asserted here. -/
theorem exists_rootWeyl_parabolic_length_split (J : Set b.support)
    (w : P.weylGroupToPerm.range) :
    ∃ x : P.weylGroupToPerm.range, ∃ l : List b.support,
      (∀ i ∈ l, i ∈ J) ∧
      (∀ i : b.support, i ∈ J → b.IsPos (x.val i.val)) ∧
      w = x * rootWeylWord P b l ∧
      rootWeylLength P b w = rootWeylLength P b x + l.length ∧
      IsReducedRootWord P b l := by
  let Q (v : P.weylGroupToPerm.range) : Prop :=
    ∃ x : P.weylGroupToPerm.range, ∃ l : List b.support,
      (∀ i ∈ l, i ∈ J) ∧
      (∀ i : b.support, i ∈ J → b.IsPos (x.val i.val)) ∧
      v = x * rootWeylWord P b l ∧
      rootWeylLength P b v = rootWeylLength P b x + l.length ∧
      IsReducedRootWord P b l
  change Q w
  have haux : ∀ n : ℕ, ∀ v : P.weylGroupToPerm.range,
      rootWeylLength P b v = n → Q v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hvn
      by_cases hp : ∀ i : b.support, i ∈ J → b.IsPos (v.val i.val)
      · refine ⟨v, [], ?_, hp, ?_, ?_, ?_⟩
        · simp
        · simp only [rootWeylWord, List.map_nil, List.prod_nil, mul_one]
        · simp
        · dsimp only [IsReducedRootWord]
          exact Nat.eq_zero_of_le_zero (rootWeylWord_length_le P b [])
      · have hex : ∃ i : b.support, i ∈ J ∧ ¬ b.IsPos (v.val i.val) := by
          by_contra h
          apply hp
          intro i hi
          by_contra hn
          exact h ⟨i, hi, hn⟩
        obtain ⟨i, hi, hneg⟩ := hex
        have hstep := rootWeylLength_mul_simple_of_negative P b v i hneg
        have hlt : rootWeylLength P b (v * simpleWeylReflection P b i) < n := by
          omega
        obtain ⟨x, l, hl, hx, hfactor, hlen, _hred⟩ :=
          ih _ hlt _ rfl
        have happ : rootWeylWord P b (l ++ [i]) =
            rootWeylWord P b l * simpleWeylReflection P b i := by
          rw [rootWeylWord_append]
          simp only [rootWeylWord, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one]
        have hfactor' : v = x * rootWeylWord P b (l ++ [i]) := by
          calc
            v = (v * simpleWeylReflection P b i) * simpleWeylReflection P b i := by
              rw [mul_assoc, simpleWeylReflection_mul_self, mul_one]
            _ = (x * rootWeylWord P b l) * simpleWeylReflection P b i := by rw [hfactor]
            _ = x * rootWeylWord P b (l ++ [i]) := by rw [happ, mul_assoc]
        have hlen' : rootWeylLength P b v =
            rootWeylLength P b x + (l ++ [i]).length := by
          rw [List.length_append, List.length_singleton]
          omega
        refine ⟨x, l ++ [i], ?_, hx, hfactor', hlen', ?_⟩
        · intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact hl k hk
          · have hki : k = i := List.mem_singleton.mp hk
            simpa only [hki] using hi
        · have hlow := rootWeylLength_mul_le P b x (rootWeylWord P b (l ++ [i]))
          rw [← hfactor'] at hlow
          have hupp := rootWeylWord_length_le P b (l ++ [i])
          dsimp only [IsReducedRootWord]
          omega
  exact haux _ w rfl

end Atlas.Chevalley.RootData
