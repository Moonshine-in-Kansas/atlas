import Atlas.Comparisons.Classical.OrthogonalInvolutions

/-! # A same-order pair distinguished by its actual involution conjugacy classes -/
namespace Atlas.Comparisons.Classical.Checks

theorem b3_three_k2 : Atlas.k2 (Atlas.Orthogonal.B 3 (ZMod 3)) = 3 :=
  Atlas.Orthogonal.B_k2 3 (by decide) (by decide)

theorem c3_three_k2 : Atlas.k2 (Atlas.Symplectic.PSp 3 (ZMod 3)) = 2 :=
  Atlas.Symplectic.k2_psp (by decide) (by decide)

theorem b3_three_not_equiv_c3 :
    ¬ Nonempty (Atlas.Orthogonal.B 3 (ZMod 3) ≃* Atlas.Symplectic.PSp 3 (ZMod 3)) :=
  oddB_not_equiv_C 3 (by decide) (by decide)

theorem b3_three_same_order_c3 :
    Nat.card (Atlas.Orthogonal.B 3 (ZMod 3)) = Nat.card (Atlas.Symplectic.PSp 3 (ZMod 3)) :=
  oddB_card_eq_C 3 (by decide) (by decide)
end Atlas.Comparisons.Classical.Checks
