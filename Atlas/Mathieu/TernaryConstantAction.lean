import Atlas.Codes.TernaryConstantOctad
import Atlas.Mathieu.TernaryWittMathieuAction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def ternaryCoordinateMap (σ : Equiv.Perm (Fin 12)) : TernaryWord →ₗ[ZMod 3] TernaryWord where
  toFun w := fun i => w (σ.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ternaryCoordinateMap_indicator (σ : Equiv.Perm (Fin 12)) (B : Finset (Fin 12)) :
    ternaryCoordinateMap σ (ternarySupportIndicator B) =
      ternarySupportIndicator (B.image σ) := by
  classical
  funext i
  have h : i ∈ B.image σ ↔ σ.symm i ∈ B := by
    constructor
    · rintro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      simpa using hj
    · intro hi
      exact Finset.mem_image.mpr ⟨σ.symm i,hi,σ.apply_symm_apply i⟩
  simp only [ternaryCoordinateMap, LinearMap.coe_mk, AddHom.coe_mk,
    ternarySupportIndicator, h]

theorem ternaryConstantSign_positive_eq (w : TernaryWord)
    (hw : ∀ i, w i = 0 ∨ w i = 1) : ternarySupportIndicator (ternarySupport w) = w := by
  funext i
  rcases hw i with h | h <;> simp [ternarySupportIndicator, ternarySupport,h]

theorem ternaryWitt_octad_transport (g : Mathieu12DodecadModel ternaryComparisonDodecad)
    (u v : TernaryWord) (hu : u ∈ ternaryGolay) (hv : v ∈ ternaryGolay)
    (huw : ternaryWeight u = 6) (hvw : ternaryWeight v = 6)
    (hs : ternarySupport v = (ternarySupport u).image (ternaryWittMathieuHom g)) :
    support (ternaryBinaryOctadWord v) =
      permuteBlock g.val.val (support (ternaryBinaryOctadWord u)) := by
  have hO (w : TernaryWord) (hw : w ∈ ternaryGolay) (h6 : ternaryWeight w = 6) :
      support (ternaryBinaryOctadWord w) ∈ octads := (octads_mem _).mpr
    ⟨⟨_, ternaryBinaryOctadWord_mem _⟩, (ternaryBinaryOctadLift_spec w hw h6).1, rfl⟩
  apply mathieu12_hexad_determines_octad ternaryComparisonDodecad
    _ _ (hO v hv hvw)
    ((codePreserving_octadPreserving g.val.val g.val.prop _).mp (hO u hu huw))
  · rw [← ternaryWitt_trace v hv hvw, Finset.card_map, ternarySupport_card, hvw]
  · rw [← mathieu12_trace_permute, ← ternaryWitt_trace v hv hvw,
      ← ternaryWitt_trace u hu huw, hs, ternaryWittMathieu_blocks]

theorem ternaryWitt_constant_indicator_preserved
    (g : Mathieu12DodecadModel ternaryComparisonDodecad)
    (hg : g.val.val ternaryConstantPoint = ternaryConstantPoint)
    (u : TernaryWord) (hu : u ∈ ternaryGolay) (huw : ternaryWeight u = 6)
    (hc : TernaryConstantSign u) :
    ternarySupportIndicator ((ternarySupport u).image (ternaryWittMathieuHom g)) ∈
      ternaryGolay := by
  have hs := ternaryWittMathieu_preserves g (ternarySupport u) ⟨⟨u,hu⟩,huw,rfl⟩
  obtain ⟨v,hvw,hvs⟩ := hs
  have he := ternaryWitt_octad_transport g u v.val hu v.prop huw hvw hvs
  have hi : ternaryConstantPoint ∈ support (ternaryBinaryOctadWord u) := by
    have hc' := (ternaryConstantOctad_iff u hu huw).mpr hc
    simp [support,hc']
  have hj : ternaryConstantPoint ∈ support (ternaryBinaryOctadWord v.val) := by
    rw [he]
    exact Finset.mem_image.mpr ⟨ternaryConstantPoint, hi, hg⟩
  have hvone : ternaryBinaryOctadWord v.val ternaryConstantPoint = 1 := by
    have hn : ternaryBinaryOctadWord v.val ternaryConstantPoint ≠ 0 := by
      simpa [support] using hj
    exact (by decide : ∀ a : Bit, a ≠ 0 → a = 1) _ hn
  rw [← hvs]
  exact ternaryConstantSign_indicator v.val v.prop
    ((ternaryConstantOctad_iff v.val v.prop hvw).mp hvone)

theorem ternaryWitt_fix_constant_preserves_code
    (g : Mathieu12DodecadModel ternaryComparisonDodecad)
    (hg : g.val.val ternaryConstantPoint = ternaryConstantPoint)
    (w : TernaryWord) (hw : w ∈ ternaryGolay) :
    ternaryCoordinateMap (ternaryWittMathieuHom g) w ∈ ternaryGolay := by
  obtain ⟨p,rfl⟩ := hw
  rw [ternaryConstantGenerator_decompose p, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul, map_sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro k _
  rw [map_smul]
  apply Submodule.smul_mem
  have hk := ternaryConstantGenerator_spec k
  rw [← ternaryConstantSign_positive_eq _ hk.2, ternaryCoordinateMap_indicator]
  exact ternaryWitt_constant_indicator_preserved g hg _
    (ternaryConstantGenerator_mem k) hk.1 (Or.inl hk.2)

end Atlas.Codes
