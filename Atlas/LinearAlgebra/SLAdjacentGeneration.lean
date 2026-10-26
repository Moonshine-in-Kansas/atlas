import Atlas.LinearGroups.Elementary

/-! Adjacent upper and lower transvections generate SL in arbitrary dimension
over every field. The proof expands longer transvections by commutators. -/
namespace Atlas
open Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement

theorem sl_eq_top_of_adjacent_transvections {r : ℕ} (hr : 1 ≤ r)
    {F : Type*} [Field F]
    (H : Subgroup (SpecialLinearGroup (Fin (r + 1)) F))
    (hx : ∀ (i : Fin r) (h : i.castSucc ≠ i.succ) (t : F), transvection h t ∈ H)
    (hy : ∀ (i : Fin r) (h : i.succ ≠ i.castSucc) (t : F), transvection h t ∈ H) :
    H = ⊤ := by
  have hc (x y : SpecialLinearGroup (Fin (r + 1)) F)
      (hx' : x ∈ H) (hy' : y ∈ H) : ⁅x, y⁆ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hx' hy') (H.inv_mem hx')) (H.inv_mem hy')
  have hpair : ∀ d : ℕ, ∀ (i j : Fin (r + 1)), i.val + d + 1 = j.val →
      ∀ (hij : i ≠ j) (t : F), transvection hij t ∈ H ∧
        transvection hij.symm t ∈ H := by
    intro d
    induction d with
    | zero =>
      intro i j he hij t
      let k : Fin r := ⟨i.val, by omega⟩
      have hki : k.castSucc = i := Fin.ext rfl
      have hkj : k.succ = j := Fin.ext (by simpa using he)
      have hk : k.castSucc ≠ k.succ := by rw [hki, hkj]; exact hij
      simpa only [hki, hkj] using And.intro (hx k hk t) (hy k hk.symm t)
    | succ d ih =>
      intro i j he hij t
      let k : Fin (r + 1) := ⟨i.val + d + 1, by omega⟩
      have hek : i.val + d + 1 = k.val := rfl
      have hekj : k.val + 1 = j.val := by dsimp [k]; omega
      have hik : i ≠ k := by intro h; have hv := congrArg Fin.val h; dsimp [k] at hv; omega
      have hkj : k ≠ j := by intro h; have hv := congrArg Fin.val h; omega
      let a : Fin r := ⟨k.val, by omega⟩
      have hak : a.castSucc = k := Fin.ext rfl
      have haj : a.succ = j := Fin.ext hekj
      have ha : a.castSucc ≠ a.succ := by rw [hak, haj]; exact hkj
      have hupper (s : F) : transvection hkj s ∈ H := by
        simpa only [hak, haj] using hx a ha s
      have hlower (s : F) : transvection hkj.symm s ∈ H := by
        simpa only [hak, haj] using hy a ha.symm s
      constructor
      · have hm := hc _ _ (ih i k hek hik t).1 (hupper 1)
        simpa only [elementary_commutator hij hik hkj, mul_one] using hm
      · have hm := hc _ _ (hlower t) (ih i k hek hik 1).2
        simpa only [elementary_commutator hij.symm hkj.symm hik.symm, mul_one] using hm
  have ht (i j : Fin (r + 1)) (hij : i ≠ j) (t : F) : transvection hij t ∈ H := by
    have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
    · exact (hpair (j.val - i.val - 1) i j (by omega) hij t).1
    · exact (hpair (i.val - j.val - 1) j i (by omega) hij.symm t).2
  letI : Nontrivial (Fin (r + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply top_unique
  intro g _
  exact sl_elementary_induction (fun g => g ∈ H) ht
    (fun _ _ => H.mul_mem) g

end Atlas
