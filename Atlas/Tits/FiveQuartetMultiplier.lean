import Atlas.Tits.FiveQuartetImageOrder

/-! The multiplier is conjugation on the actual normal Sylow five subgroup of
 the actual five-quartet permutation image. -/
namespace Atlas.Tits
open Atlas.GroupTheory
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable def fiveQuartetSylow : Sylow 5 fiveQuartetImage :=
  Classical.choice inferInstance

theorem fiveQuartetSylow_order : Nat.card fiveQuartetSylow = 5 :=
  sylow_card_prime 5 (by rw [fiveQuartetImage_order]; decide)
    (by rw [fiveQuartetImage_order]; decide) fiveQuartetSylow

theorem fiveQuartetSylow_unique : Nat.card (Sylow 5 fiveQuartetImage) = 1 := by
  have hi := fiveQuartetSylow.toSubgroup.card_mul_index
  rw [fiveQuartetSylow_order, fiveQuartetImage_order] at hi
  have hindex : fiveQuartetSylow.index = 4 := by omega
  have hd := fiveQuartetSylow.card_dvd_index
  rw [hindex] at hd
  have hm := card_sylow_modEq_one 5 fiveQuartetImage
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hmod : Nat.card (Sylow 5 fiveQuartetImage) % 5 = 1 := by
    simpa only [Nat.ModEq] using hm
  omega

instance fiveQuartetSylow_normal : (fiveQuartetSylow : Subgroup fiveQuartetImage).Normal := by
  haveI : Subsingleton (Sylow 5 fiveQuartetImage) :=
    (Nat.card_eq_one_iff_unique.mp fiveQuartetSylow_unique).1
  exact Sylow.normal_of_subsingleton fiveQuartetSylow

noncomputable instance fiveQuartetSylow_transitive :
    MulAction.IsPretransitive fiveQuartetSylow FiveQuartets :=
  prime_subgroup_pretransitive 5 cardFiveQuartets _ fiveQuartetSylow_order

instance fiveQuartetSylow_cyclic : IsCyclic fiveQuartetSylow :=
  isCyclic_of_prime_card fiveQuartetSylow_order

noncomputable def fiveQuartetNormalizerHom : fiveQuartetImage →*
    Subgroup.normalizer (fiveQuartetSylow : Set fiveQuartetImage) where
  toFun g := ⟨g, by
    change g ∈ Subgroup.normalizer ((fiveQuartetSylow : Subgroup fiveQuartetImage) : Set _)
    rw [Subgroup.normalizer_eq_top]; trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def fiveQuartetConjugation : fiveQuartetImage →* MulAut fiveQuartetSylow :=
  (fiveQuartetSylow : Subgroup fiveQuartetImage).normalizerMonoidHom.comp
    fiveQuartetNormalizerHom

theorem fiveQuartetImage_point_stabilizer_order :
    Nat.card (MulAction.stabilizer fiveQuartetImage referenceQuartet) = 4 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup fiveQuartetImage referenceQuartet)
  rw [Nat.card_prod, MulAction.orbit_eq_univ] at h
  have hu : Nat.card (Set.univ : Set FiveQuartets) = 5 := by simpa using cardFiveQuartets
  rw [hu, fiveQuartetImage_order] at h
  omega

theorem fiveQuartetConjugation_stabilizer_injective :
    Function.Injective (fiveQuartetConjugation.comp
      (MulAction.stabilizer fiveQuartetImage referenceQuartet).subtype) := by
  intro g h he
  apply Subtype.ext
  have hn := normalizer_action_injective
    (fiveQuartetSylow : Subgroup fiveQuartetImage) referenceQuartet
  have hh : fiveQuartetNormalizerHom g.val = fiveQuartetNormalizerHom h.val := by
    apply hn
    apply Prod.ext
    · exact he
    · change g.val • referenceQuartet = h.val • referenceQuartet
      exact g.prop.trans h.prop.symm
  exact congrArg (fun n : Subgroup.normalizer (fiveQuartetSylow : Set fiveQuartetImage) => n.val) hh

theorem fiveQuartetConjugation_surjective : Function.Surjective fiveQuartetConjugation := by
  have hc : Nat.card (MulAut fiveQuartetSylow) = 4 := by
    rw [IsCyclic.card_mulAut, fiveQuartetSylow_order]
    decide
  have hs := (fiveQuartetConjugation_stabilizer_injective.bijective_of_nat_card_le
    (by rw [hc, fiveQuartetImage_point_stabilizer_order])).2
  intro a
  obtain ⟨g, hg⟩ := hs a
  exact ⟨g.val, hg⟩

noncomputable def fiveQuartetAutomorphismUnits : MulAut fiveQuartetSylow ≃* (ZMod 5)ˣ := by
  have hc : Nat.card (fiveQuartetSylow : Subgroup fiveQuartetImage) = 5 := fiveQuartetSylow_order
  exact (IsCyclic.mulAutMulEquiv fiveQuartetSylow).trans (Units.mapEquiv (ZMod.ringEquivCongr hc).toMulEquiv)

/-- The intrinsic multiplier of the actual twenty-element permutation image. -/
noncomputable def fiveQuartetImageMultiplier : fiveQuartetImage →* (ZMod 5)ˣ :=
  fiveQuartetAutomorphismUnits.toMonoidHom.comp fiveQuartetConjugation

theorem fiveQuartetImageMultiplier_surjective :
    Function.Surjective fiveQuartetImageMultiplier :=
  fiveQuartetAutomorphismUnits.surjective.comp fiveQuartetConjugation_surjective

/-- The multiplier of the actual pair stabilizer, through its five-quartet action. -/
noncomputable def fiveQuartetMultiplier : pairStabilizer →* (ZMod 5)ˣ :=
  fiveQuartetImageMultiplier.comp fiveQuartetHom.rangeRestrict

theorem fiveQuartetMultiplier_surjective : Function.Surjective fiveQuartetMultiplier :=
  fiveQuartetImageMultiplier_surjective.comp fiveQuartetHom.rangeRestrict_surjective

theorem fiveQuartetImageMultiplier_kernel_order :
    Nat.card fiveQuartetImageMultiplier.ker = 5 := by
  have hi : fiveQuartetImageMultiplier.ker.index = 4 := by
    change Nat.card (fiveQuartetImage ⧸ fiveQuartetImageMultiplier.ker) = 4
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      fiveQuartetImageMultiplier fiveQuartetImageMultiplier_surjective).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have h := fiveQuartetImageMultiplier.ker.card_mul_index
  rw [hi, fiveQuartetImage_order] at h
  omega

theorem fiveQuartetMultiplier_kernel_order : Nat.card fiveQuartetMultiplier.ker = 5120 := by
  have hi : fiveQuartetMultiplier.ker.index = 4 := by
    change Nat.card (pairStabilizer ⧸ fiveQuartetMultiplier.ker) = 4
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      fiveQuartetMultiplier fiveQuartetMultiplier_surjective).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have h := fiveQuartetMultiplier.ker.card_mul_index
  rw [hi, cardPairStabilizer] at h
  omega

/-- Every nonidentity involution of the actual image has multiplier minus one. -/
theorem fiveQuartetImageMultiplier_involution (g : fiveQuartetImage)
    (hg : g ^ 2 = 1) (hne : g ≠ 1) : fiveQuartetImageMultiplier g = -1 := by
  have hm : fiveQuartetImageMultiplier g ≠ 1 := by
    intro he
    have hd := Subgroup.orderOf_dvd_natCard fiveQuartetImageMultiplier.ker he
    rw [fiveQuartetImageMultiplier_kernel_order] at hd
    have h2 := orderOf_dvd_of_pow_eq_one hg
    have h1 : orderOf g = 1 := Nat.dvd_one.mp (by
      simpa using Nat.dvd_gcd hd h2)
    exact hne (orderOf_eq_one_iff.mp h1)
  have hp : fiveQuartetImageMultiplier g ^ 2 = 1 := by rw [← map_pow, hg, map_one]
  have units_five (u : (ZMod 5)ˣ) : u ^ 2 = 1 → u ≠ 1 → u = -1 := by
    decide +kernel +revert
  exact units_five _ hp hm

end Atlas.Tits
