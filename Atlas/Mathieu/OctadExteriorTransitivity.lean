import Atlas.Mathieu.OctadPairNormalization
import Atlas.Mathieu.SextetColumnPairTransport

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem hexQuad_injective (i j k l : HexIndex) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l) :
    Function.Injective (![i,j,k,l] : Fin 4 → HexIndex) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all

theorem mathieu24_octad_exterior_pair_transitive (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (a b c d : Omega)
    (ha : a ∉ O) (hb : b ∉ O) (hab : a ≠ b)
    (hc : c ∉ P) (hd : d ∉ P) (hcd : c ≠ d) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P ∧ g.val a = c ∧ g.val b = d := by
  obtain ⟨g,i,j,hij,hg,hai,haj,hbi,hbj,hab'⟩ := octad_exterior_pair_normalize O hO a b ha hb hab
  obtain ⟨h,k,l,hkl,hh,hck,hcl,hdk,hdl,hcd'⟩ := octad_exterior_pair_normalize P hP c d hc hd hcd
  obtain ⟨s,hs,hsa,hsb⟩ := sextet_column_pair_transport i j k l
    (g.val a) (g.val b) (h.val c) (h.val d)
    (hexQuad_injective _ _ _ _ hij hai haj hbi hbj hab')
    (hexQuad_injective _ _ _ _ hkl hck hcl hdk hdl hcd')
  refine ⟨h⁻¹*s.val*g,?_,?_,?_⟩
  · change permuteBlock (h.val⁻¹*s.val.val*g.val) O = P
    rw [permuteBlock_mul,permuteBlock_mul,hg,hs,← hh,← permuteBlock_mul,
      inv_mul_cancel,permuteBlock_one]
  · change h.val.symm (s.val.val (g.val a)) = c
    rw [hsa,Equiv.symm_apply_apply]
  · change h.val.symm (s.val.val (g.val b)) = d
    rw [hsb,Equiv.symm_apply_apply]

theorem mathieu24_pair_fixing_octad_avoiding_transitive (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (a b : Omega) (hab : a ≠ b)
    (haO : a ∉ O) (hbO : b ∉ O) (haP : a ∉ P) (hbP : b ∉ P) :
    ∃ g : Mathieu24CodeModel, g.val a = a ∧ g.val b = b ∧ permuteBlock g.val O = P := by
  obtain ⟨g,hg,ha,hb⟩ := mathieu24_octad_exterior_pair_transitive O P hO hP
    a b a b haO hbO hab haP hbP hab
  exact ⟨g,ha,hb,hg⟩

end Atlas.Codes
