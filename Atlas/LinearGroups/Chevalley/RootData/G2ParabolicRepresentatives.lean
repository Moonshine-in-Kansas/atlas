import Atlas.LinearGroups.Chevalley.RootData.G2ParabolicOrbit

/-! The six actual minimal right-parabolic representatives have lengths
0,1,2,3,4,5. Exhaustion is proved through the six-point orbit and its actual
stabilizer; it does not enumerate all Weyl permutations. -/
noncomputable section
namespace Atlas.Chevalley.G2Parabolic
open Classical RootData

theorem root_height (β : G2Data.Root) :
    G2Data.base.height β = G2Table.coordinates β 0 + G2Table.coordinates β 1 := by
  have hs : G2Data.base.support = {0, 1} := by decide +kernel
  let f : G2Data.Root → ℤ := fun γ =>
    if γ = 0 then G2Table.coordinates β 0 else G2Table.coordinates β 1
  have he : G2Data.pairing.root β =
      ∑ γ ∈ G2Data.base.support, f γ • G2Data.pairing.root γ := by
    simp only [hs]
    simp [f, show (0 : G2Data.Root) ≠ 1 by decide]
    change G2Table.coordinates β =
      G2Table.coordinates β 0 • G2Table.coordinates 0 +
        G2Table.coordinates β 1 • G2Table.coordinates 1
    funext i
    fin_cases i <;> simp [G2Table.coordinates, G2Table.rootTable]
  have hh := G2Data.base.height_eq_sum he
  simpa [hs, f, show (0 : G2Data.Root) ≠ 1 by decide] using hh

theorem orbitRepresentative_minimal (k : Fin 6) :
    ∀ i ∈ J, G2Data.base.IsPos ((orbitRepresentative k).val i.val) := by
  intro i hi
  have hi1 : i = simple 1 := Finset.mem_singleton.mp hi
  subst i
  rw [G2Data.base.isPos_iff, root_height, orbitRepresentative_apply]
  change 0 < G2Table.coordinates (tableAction (orbitWord k) 1) 0 +
    G2Table.coordinates (tableAction (orbitWord k) 1) 1
  exact (show ∀ k : Fin 6,
    0 < G2Table.coordinates (tableAction (orbitWord k) 1) 0 +
      G2Table.coordinates (tableAction (orbitWord k) 1) 1 from by decide +kernel) k

theorem orbitRepresentative_length (k : Fin 6) :
    rootWeylLength G2Data.pairing G2Data.base (orbitRepresentative k) = k.val := by
  rw [← rootInversionCount_eq_rootWeylLength]
  unfold rootInversionCount rootInversions
  simp_rw [G2Data.base.isPos_iff, root_height, orbitRepresentative_apply]
  exact (show ∀ k : Fin 6,
    (Finset.univ.filter (fun β : G2Data.Root =>
      0 < G2Table.coordinates β 0 + G2Table.coordinates β 1 ∧
      ¬ 0 < G2Table.coordinates (tableAction (orbitWord k) β) 0 +
        G2Table.coordinates (tableAction (orbitWord k) β) 1)).card = k.val
    from by decide +kernel) k

def representativeMap : Fin 6 → rootParabolicRepresentatives G2Data.pairing G2Data.base J :=
  fun k => ⟨orbitRepresentative k, orbitRepresentative_minimal k⟩

theorem representativeMap_bijective : Function.Bijective representativeMap := by
  constructor
  · intro k l h
    apply orbitLabel_injective
    have he := congrArg (fun x : rootParabolicRepresentatives G2Data.pairing G2Data.base J =>
      x.val.val 7) h
    simpa only [representativeMap, orbitRepresentative_seed] using he
  · intro x
    obtain ⟨k, hk⟩ := exists_orbitLabel x.val
    have hfix : ((orbitRepresentative k)⁻¹ * x.val).val 7 = 7 := by
      change (orbitRepresentative k).val.symm (x.val.val 7) = 7
      rw [hk, ← orbitRepresentative_seed]
      exact (orbitRepresentative k).val.symm_apply_apply 7
    have hmem := (fixes_seed_iff_parabolic _).mp hfix
    have he := rootWeyl_parabolic_minimal_unique G2Data.pairing G2Data.base J
      (orbitRepresentative k) x.val (orbitRepresentative_minimal k) x.property hmem
    exact ⟨k, Subtype.ext he⟩

/-- Actual minimal representatives are indexed by the six labels of the orbit. -/
def representativeEquiv : Fin 6 ≃ rootParabolicRepresentatives G2Data.pairing G2Data.base J :=
  Equiv.ofBijective representativeMap representativeMap_bijective

theorem representativeEquiv_length (k : Fin 6) :
    rootWeylLength G2Data.pairing G2Data.base (representativeEquiv k).val = k.val :=
  orbitRepresentative_length k

end Atlas.Chevalley.G2Parabolic
