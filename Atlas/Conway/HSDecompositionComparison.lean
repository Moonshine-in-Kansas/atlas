import Atlas.Sporadic.HigmanSimsLattice
import Atlas.Conway.MinimumDecompositionMembership

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem hs_decomposition_range_iff (D : Atlas.Sporadic.Conway3.Points) :
    D ∈ Set.range hsGraphDecomposition ↔ ∃ v ∈ D.val, integerDot hsEndpoint.val v.val = 16 := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.val,Finset.mem_insert_self _ _,y.prop.2.2⟩
  · rintro ⟨v,hv,hd⟩
    obtain ⟨hn,hc,hD⟩ := minimum_decomposition_member (normSixVector co3MarkedCoordinate) D v hv
    have hx := normSix_decomposition_dot co3MarkedCoordinate v hn hc
    exact ⟨⟨v,hn,hx,hd⟩,Subtype.ext hD.symm⟩

theorem hs_decomposition_pairing_values (D : Atlas.Sporadic.Conway3.Points)
    (v : leech) (hv : v ∈ D.val) :
    integerDot hsEndpoint.val v.val = 0 ∨ integerDot hsEndpoint.val v.val = 8 ∨
      integerDot hsEndpoint.val v.val = 16 := by
  obtain ⟨p,rfl⟩ := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).surjective D
  change v ∈ ({(co3EvenEndpointMap _ p).val,
    normSixVector co3MarkedCoordinate-(co3EvenEndpointMap _ p).val} : Finset leech) at hv
  rw [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · cases p with
    | inl b =>
      change integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val = 0 ∨
        integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val = 8 ∨
        integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val = 16
      rw [hs_point_dot]; split_ifs <;> simp
    | inr B =>
      change integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val = 0 ∨
        integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val = 8 ∨
        integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val = 16
      rw [hs_heptad_dot]; split_ifs <;> simp
  · rw [hs_complement_dot]
    cases p with
    | inl b =>
      change 16-integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val = 0 ∨
        16-integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val = 8 ∨
        16-integerDot hsEndpoint.val (minimumPairPlus co3MarkedCoordinate b.val).val = 16
      rw [hs_point_dot]; split_ifs <;> norm_num
    | inr B =>
      change 16-integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val = 0 ∨
        16-integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val = 8 ∨
        16-integerDot hsEndpoint.val (co3HeptadEndpoint co3MarkedCoordinate B).val = 16
      rw [hs_heptad_dot]; split_ifs <;> norm_num

theorem hs_decomposition_complement_iff (D : Atlas.Sporadic.Conway3.Points) :
    D ∉ Set.range hsGraphDecomposition ↔ ∀ v ∈ D.val, integerDot hsEndpoint.val v.val = 8 := by
  constructor
  · intro hn v hv
    rcases hs_decomposition_pairing_values D v hv with hd | hd | hd
    · have hm := (minimum_decomposition_member (normSixVector co3MarkedCoordinate) D v hv).2.2
      have hz : normSixVector co3MarkedCoordinate-v ∈ D.val := by
        rw [hm]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact False.elim (hn ((hs_decomposition_range_iff D).mpr ⟨_,hz,by rw [hs_complement_dot,hd]; norm_num⟩))
    · exact hd
    · exact False.elim (hn ((hs_decomposition_range_iff D).mpr ⟨v,hv,hd⟩))
  · intro hv hn
    obtain ⟨v,hvD,hd⟩ := (hs_decomposition_range_iff D).mp hn
    have hh := hv v hvD
    omega

theorem hsGraphDecomposition_equivariant (g : HSModel) (y : HSGraphPoints) :
    hsGraphDecomposition (g • y) = Atlas.Sporadic.HigmanSims.toConway3 g • hsGraphDecomposition y := by
  apply Subtype.ext
  change {g.val.val.val y.val,normSixVector co3MarkedCoordinate-g.val.val.val y.val} =
    ({y.val,normSixVector co3MarkedCoordinate-y.val} : Finset leech).image g.val.val.val
  have hx : g.val.val.val (normSixVector co3MarkedCoordinate) = normSixVector co3MarkedCoordinate := g.val.prop
  simp [Finset.image_insert,Finset.image_singleton,map_sub,hx]

end Atlas.Conway
