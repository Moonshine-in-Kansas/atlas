import Atlas.Rudvalis.LocalFusionGroup
import Atlas.Rudvalis.OrthogonalPairs
import Atlas.Rudvalis.LatticeCrossOrbits

/-! Global consequences of the still-explicit local orbit-size alternatives.
No unconditional R5 transitivity is asserted here. -/
namespace Atlas.Rudvalis

noncomputable def localFusionGeneratedHom : localFusionGroup →* generatedGaussianGroup :=
  Subgroup.inclusion localFusionGroup_le_generated

theorem codeGeneratedHom_cross (g : codeGroup) (x : MinimalCross) :
    codeGeneratedHom g • x=g • x := codeGaussianHom_cross g x

theorem localFusionGeneratedHom_cross (g : localFusionGroup) (x : MinimalCross) :
    localFusionGeneratedHom g • x=g • x := rfl

theorem generated_reference_to_third :
    ∃g : generatedGaussianGroup,g • localReferenceCross=localThirdCross := by
  obtain ⟨a,ha⟩ := coordinateCross_mem (localFusionSourceCoordinate 0)
  obtain ⟨b,hb⟩ := coordinateCross_mem (localFusionSourceCoordinate 2)
  obtain ⟨g,hg⟩ := coordinateCrosses_transitive a b
  rw [ha,hb] at hg
  exact ⟨codeGeneratedHom g,(codeGeneratedHom_cross g _).trans hg⟩

noncomputable def referenceOrthogonalPair : OrthogonalPairs :=
  ⟨(localReferenceCross,localThirdCross),localFusion_first_third_orthogonal⟩

variable (hsizes : Nat.card (MulAction.orbit localFusionGroup localThirdCross)=27 ∨
  Nat.card (MulAction.orbit localFusionGroup localThirdCross)=219 ∨
  Nat.card (MulAction.orbit localFusionGroup localThirdCross)=1563 ∨
  Nat.card (MulAction.orbit localFusionGroup localThirdCross)=1755)
include hsizes

theorem generated_reference_to_piece (s : SubMulAction codeGroup MinimalShell)
    (ht : ∀a b : ShellPieceCross s,∃g : codeGroup,
      g • shellPieceCrossMap s a=shellPieceCrossMap s b)
    (hw : ∃a : ShellPieceCross s,CrossOrthogonal localReferenceCross (shellPieceCrossMap s a))
    (b : ShellPieceCross s) :
    ∃g : generatedGaussianGroup,g • localReferenceCross=shellPieceCrossMap s b := by
  obtain ⟨a,ha⟩ := hw
  obtain ⟨h,hh⟩ := ht a b
  obtain ⟨u,hu⟩ := generated_reference_to_third
  have hk : shellPieceCrossMap s a∈MulAction.orbit localFusionGroup localThirdCross := by
    rw [localFusionGroup_full_orthogonal_orbit hsizes]
    exact ha
  obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hk
  refine ⟨codeGeneratedHom h*localFusionGeneratedHom k*u,?_⟩
  rw [mul_smul,mul_smul,hu,localFusionGeneratedHom_cross,hk,codeGeneratedHom_cross,hh]

theorem generated_reference_to_cross (x : MinimalCross) :
    ∃g : generatedGaussianGroup,g • localReferenceCross=x := by
  have hcoord : ∃a : CoordinateCrosses,CrossOrthogonal localReferenceCross
      (shellPieceCrossMap coordinateShellPiece a) := by
    have hn := (Nat.card_pos_iff.mp (show 0<Nat.card {c : CoordinateCrosses //
        CrossOrthogonal localReferenceCross (shellPieceCrossMap coordinateShellPiece c)} from by
      rw [coordinateOrthogonalCrosses_card]; decide)).1
    obtain ⟨a⟩ := hn
    exact ⟨a.val,a.prop⟩
  have hfour : ∃a : FourBlockCrosses,CrossOrthogonal localReferenceCross
      (shellPieceCrossMap fourShellPiece a) := by
    have hn := (Nat.card_pos_iff.mp (show 0<Nat.card {c : FourBlockCrosses //
        CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece c)} from by
      rw [fourOrthogonalCrosses_card]; decide)).1
    obtain ⟨a⟩ := hn
    exact ⟨a.val,a.prop⟩
  have hheavy : ∃a : HeavyCrosses,CrossOrthogonal localReferenceCross
      (shellPieceCrossMap heavyShellPiece a) := by
    have hn := (Nat.card_pos_iff.mp (show 0<Nat.card {c : HeavyCrosses //
        CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece c)} from by
      rw [heavyOrthogonalCrosses_card]; decide)).1
    obtain ⟨a⟩ := hn
    exact ⟨a.val,a.prop⟩
  rcases minimalCross_piece_cases x with ⟨a,rfl⟩|⟨a,rfl⟩|⟨a,rfl⟩
  · exact generated_reference_to_piece hsizes _ coordinateCrosses_transitive hcoord a
  · exact generated_reference_to_piece hsizes _ fourBlockCrosses_transitive hfour a
  · exact generated_reference_to_piece hsizes _ heavyCrosses_transitive hheavy a

theorem generated_cross_pretransitive :
    MulAction.IsPretransitive generatedGaussianGroup MinimalCross := by
  constructor
  intro a b
  obtain ⟨g,hg⟩ := generated_reference_to_cross hsizes a
  obtain ⟨h,hh⟩ := generated_reference_to_cross hsizes b
  refine ⟨h*g⁻¹,?_⟩
  rw [mul_smul,←hg,inv_smul_smul,hh]

theorem generated_uniform_orthogonal_degree (x : MinimalCross) :
    Nat.card (OrthogonalCrosses x)=1755 := by
  obtain ⟨g,hg⟩ := generated_reference_to_cross hsizes x
  rw [←hg]
  exact orthogonalCross_card_coordinate_orbit g.val _ _

theorem generated_ordered_orthogonal_pairs_card : Nat.card OrthogonalPairs=7125300 :=
  orthogonalPairs_card_of_uniform (generated_uniform_orthogonal_degree hsizes)

theorem generated_reference_to_orthogonal_pair (z : OrthogonalPairs) :
    ∃g : generatedGaussianGroup,g • referenceOrthogonalPair=z := by
  obtain ⟨a,ha⟩ := generated_reference_to_cross hsizes z.val.1
  have hback : a⁻¹ • z.val.1=localReferenceCross := by rw [←ha,inv_smul_smul]
  have ho : CrossOrthogonal localReferenceCross (a⁻¹ • z.val.2) := by
    have h := (crossOrthogonal_gaussian a.val⁻¹ z.val.1 z.val.2).mpr z.prop
    change CrossOrthogonal (a⁻¹ • z.val.1) (a⁻¹ • z.val.2) at h
    rw [hback] at h
    exact h
  have hm : a⁻¹ • z.val.2∈MulAction.orbit localFusionGroup localThirdCross := by
    rw [localFusionGroup_full_orthogonal_orbit hsizes]
    exact ho
  obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hm
  refine ⟨a*localFusionGeneratedHom k,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (a*localFusionGeneratedHom k) • localReferenceCross=z.val.1
    rw [mul_smul,localFusionGeneratedHom_cross,localFusionGroup_fix,ha]
  · change (a*localFusionGeneratedHom k) • localThirdCross=z.val.2
    rw [mul_smul,localFusionGeneratedHom_cross,hk,smul_inv_smul]

theorem generated_orthogonal_pairs_pretransitive :
    MulAction.IsPretransitive generatedGaussianGroup OrthogonalPairs := by
  constructor
  intro a b
  obtain ⟨g,hg⟩ := generated_reference_to_orthogonal_pair hsizes a
  obtain ⟨h,hh⟩ := generated_reference_to_orthogonal_pair hsizes b
  refine ⟨h*g⁻¹,?_⟩
  rw [mul_smul,←hg,inv_smul_smul,hh]

end Atlas.Rudvalis

