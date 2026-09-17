import Atlas.Codes.TernaryConstantHexadPairs

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes
open scoped Pointwise

private theorem hexad_compl_smul (g : TernaryPureAutomorphism) (s : Finset (Fin 12)) :
    g • sᶜ = (g • s)ᶜ := by
  rw [ternaryFinset_smul,ternaryFinset_smul]
  ext i; simp

private theorem hexad_fixed_of_pair_fixed (g : TernaryPureAutomorphism) (hg : g^11=1)
    (s : Finset (Fin 12)) (h : g • ternaryConstantHexadPair s = ternaryConstantHexadPair s) :
    g • s=s := by
  rw [ternaryConstantHexadPair_smul,ternaryConstantHexadPair_eq_iff] at h
  rcases h with h|h
  · exact h
  · have htwo : (g^2) • s=s := by
      rw [pow_two,mul_smul,h,hexad_compl_smul,h,compl_compl]
    have hp (k : ℕ) : (g^(2*k)) • s=s := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2*(k+1)=2*k+2 by omega,pow_add,mul_smul,htwo,ih]
    have hten := hp 5
    have he : (g^11) • s=g • s := by
      rw [show 11=1+10 by rfl,pow_add,mul_smul,hten,pow_one]
    rw [hg,one_smul] at he
    exact he.symm

private theorem hexad_not_fixed (g : TernaryPureAutomorphism) (a : Fin 12)
    (htrans : ∀ i, i≠a → ∀ j, j≠a → ∃ k : ℕ, (g.val.symm^k) i=j)
    (s : Finset (Fin 12)) (hs : s ∈ ternaryConstantHexads) : g • s ≠ s := by
  intro he
  obtain ⟨hcard,hcode⟩ := (mem_ternaryConstantHexads s).mp hs
  have hw : ∀ i, ternaryTriadWord s (g.val.symm i)=ternaryTriadWord s i := by
    intro i
    have hh := congrArg (fun t : Finset (Fin 12) => ternaryTriadWord t i) he
    rw [ternaryFinset_smul,ternaryTriadWord_permute] at hh
    exact hh
  obtain ⟨c,hc⟩ := ternaryGolay_fixed_eq_constant g.val.symm a htrans ⟨_,hcode⟩ hw
  have hnon : s.Nonempty := Finset.card_pos.mp (by omega)
  have hcompl : sᶜ.Nonempty := Finset.card_pos.mp (by simp [Finset.card_compl,hcard])
  obtain ⟨i,hi⟩ := hnon
  obtain ⟨j,hj⟩ := hcompl
  have hh := (hc i).trans (hc j).symm
  simpa [ternaryTriadWord,hi,Finset.mem_compl.mp hj] using hh

/-- The actual M11 coordinate action is transitive on the eleven complementary
constant-hexad partitions. Cauchy's existing eleven-cycle supplies the orbit. -/
theorem ternaryConstantHexadPairs_transitive (p q : TernaryConstantHexadPair) :
    ∃ g : TernaryPureAutomorphism, g • p=q := by
  classical
  obtain ⟨g,hg,a,ha⟩ := ternaryPure_exists_eleven_cycle
  let σ : Equiv.Perm TernaryConstantHexadPair := MulAction.toPerm g
  have hn (p : TernaryConstantHexadPair) : σ p ≠ p := by
    intro h
    obtain ⟨s,hs,hsp⟩ := Finset.mem_image.mp p.property
    have he := congrArg Subtype.val h
    change g • p.val=p.val at he
    rw [← hsp] at he
    exact hexad_not_fixed g a ha s hs (hexad_fixed_of_pair_fixed g hg s he)
  have hpow : σ^11=1 := by
    change (MulAction.toPermHom TernaryPureAutomorphism TernaryConstantHexadPair g)^11=1
    rw [← map_pow,hg,map_one]
  have ho : orderOf σ=11 := by
    have hd := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hd with h|h
    · have he : σ=1 := orderOf_eq_one_iff.mp h
      exact (hn p (by rw [he]; rfl)).elim
    · exact h
  have hcard : Fintype.card TernaryConstantHexadPair=11 := by
    rw [Fintype.card_coe,ternaryConstantHexadPairs_card]
  have hcycle : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [ho]; decide) (by rw [hcard,ho]; norm_num)
  obtain ⟨k,hk⟩ := (hcycle.sameCycle (hn p) (hn q)).exists_nat_pow_eq
  refine ⟨g^k,?_⟩
  change (MulAction.toPermHom TernaryPureAutomorphism TernaryConstantHexadPair (g^k)) p=q
  rw [map_pow]
  exact hk

end Atlas.Codes
