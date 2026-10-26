import Atlas.LinearGroups.Chevalley.RootData.ParabolicWordReduction

/-! An actual injective Weyl homomorphism identifying the simple generators
with a chosen ambient subset identifies the full standard parabolic and its
word length. Existence and injectivity of that homomorphism are explicit
hypotheses, never consequences of a matching group order. -/
noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

private theorem word_lift {α β : Type*} (k : α → β) (J : Finset β)
    (hk : ∀ j, j ∈ J ↔ ∃ i, k i = j)
    (l : List β) (hl : ∀ j ∈ l, j ∈ J) :
    ∃ r : List α, r.map k = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons j l ih =>
    obtain ⟨i, rfl⟩ := (hk j).mp (hl j List.mem_cons_self)
    obtain ⟨r, hr⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    exact ⟨i :: r, by simp only [List.map_cons, hr]⟩

variable {ι M N ι' M' N' : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)
  (Q : RootPairing ι' ℤ M' N') [Q.IsCrystallographic] [Q.IsReduced]
  (c : Q.Base)
  (f : P.weylGroupToPerm.range →* Q.weylGroupToPerm.range)
  (k : b.support → c.support)
  (hs : ∀ i, f (simpleWeylReflection P b i) = simpleWeylReflection Q c (k i))

include hs

theorem rootWeylHom_word (l : List b.support) :
    f (rootWeylWord P b l) = rootWeylWord Q c (l.map k) := by
  induction l with
  | nil => exact f.map_one
  | cons i l ih =>
    change f (simpleWeylReflection P b i * rootWeylWord P b l) =
      simpleWeylReflection Q c (k i) * rootWeylWord Q c (l.map k)
    rw [map_mul, hs, ih]


theorem rootWeylHom_range_eq_parabolic (J : Finset c.support)
    (hk : ∀ j, j ∈ J ↔ ∃ i, k i = j) :
    f.range = rootParabolicSubgroup Q c J := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨l, _, hl⟩ := rootWeylLength_spec P b v
    have he : rootWeylWord P b l = v := by
      apply Subtype.ext
      simpa only [rootWeylWord_val] using hl
    rw [← he, rootWeylHom_word P b Q c f k hs]
    apply rootWeylWord_mem_parabolic
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    exact (hk (k i)).mpr ⟨i, rfl⟩
  · intro hw
    obtain ⟨l, hl, he⟩ := (rootParabolic_mem_iff_word Q c J w).mp hw
    obtain ⟨r, hr⟩ := word_lift k J hk l hl
    refine ⟨rootWeylWord P b r, ?_⟩
    rw [rootWeylHom_word P b Q c f k hs, hr, he]

theorem rootWeylHom_length (hf : Function.Injective f)
    (J : Finset c.support) (hk : ∀ j, j ∈ J ↔ ∃ i, k i = j)
    (w : P.weylGroupToPerm.range) :
    rootWeylLength Q c (f w) = rootWeylLength P b w := by
  apply Nat.le_antisymm
  · obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec P b w
    have he : rootWeylWord P b l = w := by
      apply Subtype.ext
      simpa only [rootWeylWord_val] using hl
    have hb := rootWeylWord_length_le Q c (l.map k)
    rw [← rootWeylHom_word P b Q c f k hs, he, List.length_map, hlen] at hb
    exact hb
  · have hmem : f w ∈ rootParabolicSubgroup Q c J := by
      rw [← rootWeylHom_range_eq_parabolic P b Q c f k hs J hk]
      exact ⟨w, rfl⟩
    obtain ⟨l, hl, he, hred⟩ := rootParabolic_exists_reduced_word Q c J (f w) hmem
    obtain ⟨r, hr⟩ := word_lift k J hk l hl
    have hrw : rootWeylWord P b r = w := by
      apply hf
      rw [rootWeylHom_word P b Q c f k hs, hr, he]
    have hb := rootWeylWord_length_le P b r
    have hlen : r.length = l.length := by
      simpa only [List.length_map] using congrArg List.length hr
    change rootWeylLength Q c (rootWeylWord Q c l) = l.length at hred
    rw [he] at hred
    rw [hrw, hlen, ← hred] at hb
    exact hb

def rootWeylHomParabolicEquiv (hf : Function.Injective f)
    (J : Finset c.support) (hk : ∀ j, j ∈ J ↔ ∃ i, k i = j) :
    P.weylGroupToPerm.range ≃* rootParabolicSubgroup Q c J :=
  (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (rootWeylHom_range_eq_parabolic P b Q c f k hs J hk))

theorem rootWeylHomParabolicEquiv_length (hf : Function.Injective f)
    (J : Finset c.support) (hk : ∀ j, j ∈ J ↔ ∃ i, k i = j)
    (w : P.weylGroupToPerm.range) :
    rootWeylLength Q c (rootWeylHomParabolicEquiv P b Q c f k hs hf J hk w).val =
      rootWeylLength P b w :=
  rootWeylHom_length P b Q c f k hs hf J hk w

end Atlas.Chevalley.RootData
