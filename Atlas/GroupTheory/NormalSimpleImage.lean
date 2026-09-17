import Mathlib.GroupTheory.Subgroup.Simple

namespace Atlas.GroupTheory

theorem normal_eq_top_of_simple_image {G M : Type*} [Group G] [Group M] [IsSimpleGroup M]
    (f : G →* M) (hf : Function.Surjective f) (L : Subgroup G) [hL : L.Normal]
    (hk : f.ker ≤ L) (x : G) (hx : x ∈ L) (hfx : f x ≠ 1) : L = ⊤ := by
  have hm := hL.map f hf
  have he : L.map f = ⊤ := by
    rcases hm.eq_bot_or_eq_top with he | he
    · have hh : f x ∈ L.map f := ⟨x,hx,rfl⟩
      rw [he,Subgroup.mem_bot] at hh
      exact (hfx hh).elim
    · exact he
  have hc := Subgroup.comap_map_eq_self hk
  rw [he,Subgroup.comap_top] at hc
  exact hc.symm

end Atlas.GroupTheory
