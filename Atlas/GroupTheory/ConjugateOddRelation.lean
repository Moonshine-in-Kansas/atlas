import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

namespace Atlas.GroupTheory

/-- An odd relation among conjugate involution generators kills the abelianization. -/
theorem perfect_of_conjugate_seven_relation {G X : Type*} [Group G]
    (r : X → G) (hgen : Subgroup.closure (Set.range r)=⊤)
    (hconj : ∀ x y, ∃ g : G, g*r x*g⁻¹=r y)
    (hsq : ∀ x, r x ^ 2=1) (l : List X) (hlen : l.length=7)
    (hrel : (l.map r).prod=1) : Group.IsPerfect G := by
  let q : G →* Abelianization G := Abelianization.of
  have heq (x y : X) : q (r x)=q (r y) := by
    obtain ⟨g,hg⟩ := hconj x y
    rw [← hg]
    simp [map_mul,mul_comm,mul_left_comm]
  have hz (x : X) : q (r x)=1 := by
    have h2 : q (r x)^2=1 := by rw [← map_pow,hsq,map_one]
    have h7 : q (r x)^7=1 := by
      have h := congrArg q hrel
      rw [map_list_prod,map_one] at h
      have hl : (l.map r).map q=List.replicate l.length (q (r x)) := by
        simp only [List.map_map]
        have hf : (⇑q ∘ r) = fun _ : X => q (r x) := funext (fun y => heq y x)
        rw [hf]
        simp
      rw [hl,List.prod_replicate,hlen] at h
      exact h
    have h6 : q (r x)^6=1 := by
      calc
        q (r x)^6=(q (r x)^2)^3 := by rw [← pow_mul]
        _=1 := by rw [h2,one_pow]
    simpa only [show 7=6+1 from rfl,pow_succ,h6,one_mul] using h7
  have hle : Subgroup.closure (Set.range r)≤commutator G := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    rw [← Abelianization.ker_of G]
    exact hz x
  exact ⟨top_unique (hgen ▸ hle)⟩

end Atlas.GroupTheory
