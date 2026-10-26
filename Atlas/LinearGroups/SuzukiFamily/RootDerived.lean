import Atlas.LinearGroups.SuzukiFamily.DerivedSubgroup

/-! Solving the triangular torus commutator equations puts the whole root group in G'. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem add_one_ne_zero_of_ne_one {x : F} (hx : x≠1) : x+1≠0 := by
  intro he
  apply hx
  calc x = (x+1)+1 := by ring_nf; reduce_mod_char!
       _ = 1 := by rw [he,zero_add]

theorem root_central_mem_derived (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (hm : 1≤m) (b : F) : rootElement m 0 b ∈ derivedAmbient m := by
  obtain ⟨t,_,ht⟩ := exists_nontrivial_weights m hcard hm
  have hn := add_one_ne_zero_of_ne_one ht
  let x := b/((t:F)^2*theta F m (t:F)+1)
  have hx : (t:F)^2*theta F m (t:F)*x+x=b := by
    dsimp only [x]
    field_simp [hn]
  have hh := commutator_mem_derivedAmbient m
    ((generated m).inv_mem (torusElement_mem m t)) (rootElement_mem m 0 x)
  rw [torus_root_commutator m hcard] at hh
  simpa only [mul_zero,zero_mul,map_zero,zero_add,add_zero,hx] using hh

theorem root_mem_derivedAmbient (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (hm : 1≤m) (a b : F) : rootElement m a b ∈ derivedAmbient m := by
  obtain ⟨t,ht,_⟩ := exists_nontrivial_weights m hcard hm
  have hn := add_one_ne_zero_of_ne_one ht
  let x := a/(theta F m (t:F)+1)
  have hx : theta F m (t:F)*x+x=a := by
    dsimp only [x]
    field_simp [hn]
  let z := x*theta F m x+(theta F m (t:F)*x)*theta F m x
  have hh := commutator_mem_derivedAmbient m
    ((generated m).inv_mem (torusElement_mem m t)) (rootElement_mem m x 0)
  rw [torus_root_commutator m hcard] at hh
  have hz : rootElement m a z ∈ derivedAmbient m := by
    simpa only [mul_zero,zero_add,hx] using hh
  have hc := (derivedAmbient m).mul_mem hz (root_central_mem_derived m hcard hm (b+z))
  rw [rootElement_mul m hcard] at hc
  have he : z+(b+z)=b := by ring_nf; reduce_mod_char!
  simpa only [map_zero,mul_zero,add_zero,he] using hc
end Atlas.SuzukiFamily
