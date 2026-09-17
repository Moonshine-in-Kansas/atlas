import Atlas.Mathieu.GolayOctadTransitivity
import Atlas.Mathieu.Mathieu24Order
import Atlas.Fischer.OctadAffineEvaluations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual marked-coordinate action on the retained Golay octads. -/
instance mathieuOctadAction : MulAction Mathieu24CodeModel Octad where
  smul g O := ⟨permuteBlock g.val O.val, codePreserving_octad_forward g.val g.prop O.val O.prop⟩
  one_smul O := by apply Subtype.ext; exact permuteBlock_one O.val
  mul_smul g h O := by apply Subtype.ext; exact permuteBlock_mul g.val h.val O.val

@[simp] theorem mathieuOctadAction_val (g : Mathieu24CodeModel) (O : Octad) :
    (g • O).val = permuteBlock g.val O.val := rfl

/-- The full setwise octad stabilizer in the existing Mathieu group. -/
def mathieuOctadStabilizer (O : Octad) : Subgroup Mathieu24CodeModel :=
  MulAction.stabilizer Mathieu24CodeModel O

abbrev MathieuOctadStabilizer (O : Octad) := mathieuOctadStabilizer O

theorem mathieuOctadStabilizer_iff (O : Octad) (g : Mathieu24CodeModel) :
    g ∈ mathieuOctadStabilizer O ↔ permuteBlock g.val O.val = O.val := by
  change g • O = O ↔ _
  exact Subtype.ext_iff

instance mathieuOctadPretransitive : MulAction.IsPretransitive Mathieu24CodeModel Octad := by
  constructor
  intro O P
  obtain ⟨g,hg⟩ := mathieu24_octad_transitive O.val P.val O.prop P.prop
  exact ⟨g,Subtype.ext hg⟩

def mathieuOctadOrbitEquiv (O : Octad) : MulAction.orbit Mathieu24CodeModel O ≃ Octad :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, by
    intro P
    obtain ⟨g,hg⟩ := mathieu24_octad_transitive O.val P.val O.prop P.prop
    exact ⟨⟨P,(MulAction.mem_orbit_iff).mpr ⟨g,Subtype.ext hg⟩⟩,rfl⟩⟩

theorem mathieuOctadStabilizer_order (O : Octad) : Nat.card (MathieuOctadStabilizer O) = 322560 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Mathieu24CodeModel O)
  rw [Nat.card_prod, Nat.card_congr (mathieuOctadOrbitEquiv O), mathieu24_order] at he
  have ho : Nat.card Octad = 759 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,octads_card]
  rw [ho] at he
  change 759 * Nat.card (MathieuOctadStabilizer O) = 244823040 at he
  omega

theorem mathieuOctadStabilizer_mem_iff (O : Octad) (g : MathieuOctadStabilizer O) (i : Omega) :
    g.val.val i ∈ O.val ↔ i ∈ O.val := by
  classical
  have hg := (mathieuOctadStabilizer_iff O g.val).mp g.prop
  conv_lhs => rw [← hg]
  change g.val.val i ∈ O.val.image g.val.val ↔ _
  simp only [Finset.mem_image, g.val.val.injective.eq_iff, exists_eq_right]

def mathieuOctadExteriorPerm (O : Octad) (g : MathieuOctadStabilizer O) : Equiv.Perm (OctadExterior O) where
  toFun i := ⟨g.val.val i.val,fun h => i.prop ((mathieuOctadStabilizer_mem_iff O g i.val).mp h)⟩
  invFun i := ⟨g⁻¹.val.val i.val,fun h => i.prop ((mathieuOctadStabilizer_mem_iff O g⁻¹ i.val).mp h)⟩
  left_inv i := by apply Subtype.ext; exact g.val.val.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact g.val.val.apply_symm_apply i.val

def mathieuOctadExteriorHom (O : Octad) : MathieuOctadStabilizer O →* Equiv.Perm (OctadExterior O) where
  toFun := mathieuOctadExteriorPerm O
  map_one' := rfl
  map_mul' _ _ := rfl

end Atlas.Fischer
