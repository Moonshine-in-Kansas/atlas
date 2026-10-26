import Atlas.LinearGroups.SuzukiFamily.Matrices

/-! Uniform anisotropy of the Suzuki ovoid polynomial. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem twist_sum_ne_one (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (c : F) :
    c + theta F m c ≠ 1 := by
  intro hc
  have hs : theta F m c = 1+c := calc
    theta F m c = (c+theta F m c)+c := by ring_nf; reduce_mod_char!
    _ = 1+c := by rw [hc]
  have ht := congrArg (theta F m) hs
  rw [theta_square hcard,map_add,map_one,hs] at ht
  have he : c^2=c := by simpa [← add_assoc,CharTwo.add_self_eq_zero] using ht
  have hz : c*(c-1)=0 := by linear_combination he
  rcases mul_eq_zero.mp hz with h0 | h1
  · simp [h0,-theta_apply] at hc
  · have h1' : c=1 := sub_eq_zero.mp h1
    simp [h1',-theta_apply,CharTwo.add_self_eq_zero] at hc

theorem norm_scaled (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a c : F) :
    norm m a (a*theta F m a*c) = a^2*theta F m a*(1+c+theta F m c) := by
  simp only [norm,map_mul,theta_square hcard]
  ring

theorem norm_eq_zero_iff (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    norm m a b = 0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro hn
    by_cases ha : a=0
    · subst a
      have ht : theta F m b=0 := by simpa [norm] using hn
      exact ⟨rfl,(theta F m).injective (by simpa only [map_zero] using ht)⟩
    · have ht : theta F m a ≠ 0 := (map_ne_zero (theta F m)).mpr ha
      let c := b/(a*theta F m a)
      have hb : a*theta F m a*c=b := by dsimp [c]; field_simp
      rw [← hb,norm_scaled m hcard] at hn
      have he : 1+c+theta F m c=0 := (mul_eq_zero.mp hn).resolve_left (mul_ne_zero (pow_ne_zero _ ha) ht)
      apply False.elim
      apply twist_sum_ne_one m hcard c
      calc
        c+theta F m c = (1+c+theta F m c)+1 := by ring_nf; reduce_mod_char!
        _ = 1 := by rw [he,zero_add]
  · rintro ⟨rfl,rfl⟩
    simp [norm]
end Atlas.SuzukiFamily
