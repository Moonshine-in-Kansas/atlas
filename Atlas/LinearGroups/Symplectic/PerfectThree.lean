import Atlas.LinearGroups.Symplectic.TernaryIdentity

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Uniform perfectness over the three-element field, starting at symplectic rank two. -/
theorem perfect_of_card_three (hn : 2 ≤ n) (hq : Nat.card F = 3) : Group.IsPerfect (Sp n F) := by
  classical
  let := Fintype.ofFinite F
  have hq' : Fintype.card F = 3 := by simpa only [Nat.card_eq_fintype_card] using hq
  letI : CharP F 3 := charP_of_card_eq_prime hq'
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  let u : Vector n F := e i
  let v : Vector n F := e j
  have hu : u ≠ 0 := by intro h; have := congrFun h (.inl i); simp [u,e] at this
  have hv : v ≠ 0 := by intro h; have := congrFun h (.inl j); simp [v,e] at this
  have hp : u+v ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,e,Pi.single_apply,hij,hij.symm] at this
  have hm : u-v ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,e,Pi.single_apply,hij,hij.symm] at this
  have huv : form u v = 0 := by
    change form (e i) (e j) = 0
    rw [form_e_right]
    simp [e]
  let f : Sp n F →* Abelianization (Sp n F) := Abelianization.of
  let z := f (transvection u 1)
  have hz3 : z^3=1 := by
    change f (transvection u 1)^3=1
    rw [← map_pow,transvection_pow]
    have h3 : (3 : ℕ) • (1 : F) = 0 := by
      simpa only [nsmul_eq_mul,mul_one] using (CharP.cast_eq_zero F 3)
    rw [h3,transvection_zero,map_one]
  have hz4 : z^4=1 := by
    have h := congrArg f (ternary_four_transvections u v huv)
    simp only [map_mul,map_one] at h
    rw [← abelian_transvection_images f hu hv,← abelian_transvection_images f hu hp,
      ← abelian_transvection_images f hu hm] at h
    simpa only [z,pow_succ,pow_zero,one_mul] using h
  have hz : z=1 := by
    simpa only [pow_succ,hz3,one_mul] using hz4
  have hunit (w : Vector n F) (hw : w ≠ 0) : f (transvection w 1)=1 := by
    rw [← abelian_transvection_images f hu hw]
    exact hz
  apply perfect_of_abelian_images
  intro w a
  change f (transvection w a)=1
  by_cases hw : w=0
  · subst w; simp [f]
  have ha : a ∈ ({0,1,-1} : Finset F) := by
    rw [← Finset.univ_of_card_le_three hq'.le]
    exact Finset.mem_univ a
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · simp
  · exact hunit w hw
  · rw [← transvection_inverse,map_inv,hunit w hw,inv_one]

end Atlas.Symplectic
