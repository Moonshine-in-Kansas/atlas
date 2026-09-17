import Atlas.LinearGroups.Symplectic.BinaryIdentity

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Uniform perfectness over the two-element field, starting at symplectic rank three. -/
theorem perfect_of_card_two (hn : 3 ≤ n) (hq : Nat.card F = 2) : Group.IsPerfect (Sp n F) := by
  classical
  let := Fintype.ofFinite F
  have hq' : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hq
  letI : CharP F 2 := charP_of_card_eq_prime hq'
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  let k : Fin n := ⟨2,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  have hik : i ≠ k := by intro h; have := congrArg Fin.val h; simp [i,k] at this
  have hjk : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j,k] at this
  let u : Vector n F := e i
  let v : Vector n F := e j
  let w : Vector n F := e k
  have hu : u ≠ 0 := by intro h; have := congrFun h (.inl i); simp [u,e] at this
  have hv : v ≠ 0 := by intro h; have := congrFun h (.inl j); simp [v,e] at this
  have hw : w ≠ 0 := by intro h; have := congrFun h (.inl k); simp [w,e] at this
  have huv' : u+v ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,e,hij,hij.symm] at this
  have huw' : u+w ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,w,e,hik,hik.symm] at this
  have hvw' : v+w ≠ 0 := by
    intro h; have := congrFun h (.inl j); simp [v,w,e,hjk,hjk.symm] at this
  have huvw : u+v+w ≠ 0 := by
    intro h; have := congrFun h (.inl i); simp [u,v,w,e,hij,hij.symm,hik,hik.symm] at this
  have horth (a b : Fin n) : form (e (F := F) a) (e b) = 0 := by
    rw [form_e_right]; simp [e]
  let f : Sp n F →* Abelianization (Sp n F) := Abelianization.of
  let z := f (transvection u 1)
  have hz2 : z^2=1 := by
    change f (transvection u 1)^2=1
    rw [← map_pow,transvection_pow]
    have h2 : (2 : ℕ) • (1 : F) = 0 := by
      simpa only [nsmul_eq_mul,mul_one] using (CharP.cast_eq_zero F 2)
    rw [h2,transvection_zero,map_one]
  have hz7 : z^7=1 := by
    have h := congrArg f (binary_seven_transvections u v w (horth i j) (horth i k) (horth j k))
    simp only [map_mul,map_one] at h
    rw [← abelian_transvection_images f hu hv,← abelian_transvection_images f hu hw,
      ← abelian_transvection_images f hu huv',← abelian_transvection_images f hu huw',
      ← abelian_transvection_images f hu hvw',← abelian_transvection_images f hu huvw] at h
    simpa only [z,pow_succ,pow_zero,one_mul] using h
  have hz : z=1 := by
    have hp : z^7=(z^2)^3*z := by rw [← pow_mul,← pow_succ]
    rw [hp,hz2,one_pow,one_mul] at hz7
    exact hz7
  have hunit (v : Vector n F) (hv : v ≠ 0) : f (transvection v 1)=1 := by
    rw [← abelian_transvection_images f hu hv]
    exact hz
  apply perfect_of_abelian_images
  intro v a
  change f (transvection v a)=1
  by_cases hv : v=0
  · subst v; simp [f]
  have ha : a ∈ ({0,1} : Finset F) := by
    rw [← Finset.univ_of_card_le_two hq'.le]
    exact Finset.mem_univ a
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl
  · simp
  · exact hunit v hv

end Atlas.Symplectic
