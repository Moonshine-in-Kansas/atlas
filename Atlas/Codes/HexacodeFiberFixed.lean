import Atlas.Codes.HexacodeFiberKlein

noncomputable section
namespace Atlas.Codes

theorem even_perm_three_fixed {X : Type*} [Fintype X] [DecidableEq X]
    (hc : Fintype.card X = 3) (σ : Equiv.Perm X) (hs : Equiv.Perm.sign σ = 1)
    (x : X) (hx : σ x = x) : σ = 1 := by
  have hsub : σ.support ⊆ Finset.univ.erase x := by
    intro y hy
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro he
    subst y
    exact Equiv.Perm.mem_support.mp hy hx
  have hcard : σ.support.card ≤ 2 := (Finset.card_le_card hsub).trans_eq (by simp [hc])
  by_contra hn
  have hlow := Equiv.Perm.two_le_card_support_of_ne_one hn
  have hswap := Equiv.Perm.card_support_eq_two.mp (Nat.le_antisymm hcard hlow)
  have he := hswap.sign_eq
  rw [hs] at he
  exact (by decide : (1 : ℤˣ) ≠ -1) he

theorem hexFiber_fixed_nonzero_kernel (i j : HexIndex) (hij : i ≠ j)
    (g : hexFiberStabilizer i j) (h : hexDoubleZero i j) (hh : h ≠ 0)
    (hg : hexAction g.val.val.val h.val = h.val) : g ∈ (hexFiberPermutationHom i j).ker := by
  classical
  letI : Fintype {u : hexDoubleZero i j // u ≠ 0} := Fintype.ofFinite _
  apply even_perm_three_fixed
    (by rw [← Nat.card_eq_fintype_card]; exact hexDoubleZero_nonzero_card i j hij)
    _ (hexFiberPermutation_even i j g) ⟨h,hh⟩
  exact Subtype.ext (Subtype.ext hg)

theorem hexFiber_fixed_word_position (i j : HexIndex) (hij : i ≠ j)
    (g : hexFiberStabilizer i j) (h : hexDoubleZero i j) (hh : h ≠ 0)
    (hg : hexAction g.val.val.val h.val = h.val)
    (k : (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex))
    (hk : hexPointKernelCoordinate i g.val k.val = k.val) : g = 1 := by
  let u : (hexFiberPermutationHom i j).ker := ⟨g,hexFiber_fixed_nonzero_kernel i j hij g h hh hg⟩
  obtain ⟨v,hv,huniq⟩ := hexFiberKernel_regular i j hij k k
  have hu : u = 1 := (huniq u hk).trans (huniq 1 rfl).symm
  exact congrArg Subtype.val hu

end Atlas.Codes
