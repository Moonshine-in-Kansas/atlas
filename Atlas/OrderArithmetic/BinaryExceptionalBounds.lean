import Atlas.OrderArithmetic.BinaryTables

namespace Atlas.OrderArithmetic

/-- No admissible exceptional-family formula in characteristic two has scaled
top index at most six. Thus the small-index branch is genuinely classical. -/
theorem binary_small_top_classical {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hf : 1 ≤ f)
    (hq : fieldSize x = 2 ^ f) (hm : f * topIndex x ≤ 6) : IsClassicalLie x := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear _ _ | unitary _ _ | B _ _ | C _ _ | Dplus _ _ | Dminus _ _ => trivial
  | G2 q =>
    have h3 := hx.2
    have he : f = 1 := by simp only [topIndex] at hm; omega
    norm_num [fieldSize, he] at hq
    omega
  | suzuki q =>
    obtain ⟨m, hm1, hpow⟩ := hx
    have he := primePower_witness_unique (by decide : Nat.Prime 2)
      (by decide : Nat.Prime 2) hf (by omega : 1 ≤ 2 * m + 1) (hq.symm.trans hpow)
    simp only [topIndex] at hm
    omega
  | smallRee q =>
    obtain ⟨m, hm1, hpow⟩ := hx
    have he := primePower_witness_unique (by decide : Nat.Prime 2)
      (by decide : Nat.Prime 3) hf (by omega : 1 ≤ 2 * m + 1) (hq.symm.trans hpow)
    omega
  | _ => simp only [topIndex] at hm; omega

/-- The finite binary comparison applies to all Lie labels satisfying the
displayed small-top bounds, without a separate classical-tag assumption. -/
theorem binary_lie_top_bounded_collision {x y : RawEntry} {f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hf : 1 ≤ f) (hg : 1 ≤ g) (hqx : fieldSize x = 2 ^ f) (hqy : fieldSize y = 2 ^ g)
    (hbx : f * topIndex x ≤ 6) (hby : g * topIndex y ≤ 6)
    (he : order x = order y) : Collision x y :=
  binary_top_bounded_collision hx hy
    (binary_small_top_classical hx hlx hf hqx hbx)
    (binary_small_top_classical hy hly hg hqy hby) hf hg hqx hqy hbx hby he

end Atlas.OrderArithmetic
