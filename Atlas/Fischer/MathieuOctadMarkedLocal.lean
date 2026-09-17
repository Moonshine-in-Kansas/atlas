import Atlas.Fischer.MathieuOctadRestrictedLocal
import Atlas.Fischer.MathieuTranslationNormal
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def octadMarkedPoints (O : Octad) (S : Finset Omega) : Finset (OctadInterior O) :=
  S.subtype (fun i => i ∈ O.val)

@[simp] theorem mem_octadMarkedPoints (O : Octad) (S : Finset Omega) (i : OctadInterior O) :
    i ∈ octadMarkedPoints O S ↔ i.val ∈ S := Finset.mem_subtype

theorem octadMarkedPoints_card (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val) :
    (octadMarkedPoints O S).card=S.card := by
  classical
  rw [octadMarkedPoints,Finset.card_subtype,Finset.filter_eq_self.mpr hSO]

theorem octadUnmarkedPoints_card (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val) :
    Nat.card (↑((octadMarkedPoints O S)ᶜ))=8-S.card := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl,
    ← Nat.card_eq_fintype_card,octadInterior_card,octadMarkedPoints_card O S hSO]

theorem mathieuOctadMarkedLocal_iff (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (g : MathieuOctadStabilizer O) :
    g ∈ mathieuOctadRestrictedLocal O (octadMarkedPoints O S) ↔ ∀ i ∈ S, g.val.val i=i := by
  constructor
  · intro hg i hi
    have h := hg ⟨⟨i,hSO hi⟩,mem_octadMarkedPoints O S _ |>.mpr hi⟩
    exact congrArg Subtype.val h
  · intro hg i
    apply Subtype.ext
    exact hg i.val.val ((mem_octadMarkedPoints O S i.val).mp i.prop)

def mathieuOctadMarkedEmbedding (O : Octad) (S : Finset Omega) (hSO : S ⊆ O.val) :
    mathieuOctadRestrictedLocal O (octadMarkedPoints O S) →*
      fixingSubgroup Mathieu24CodeModel (S : Set Omega) where
  toFun g := ⟨g.val.val,fun i => (mathieuOctadMarkedLocal_iff O S hSO g.val).mp g.prop i.val i.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mathieuOctadMarked_perfect_quotient (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card ≤ 2) :
    commutator (alternatingGroup (↑((octadMarkedPoints O S)ᶜ)))=⊤ :=
  commutator_alternatingGroup_eq_top (by rw [octadUnmarkedPoints_card O S hSO]; omega)

/-- The five-point local quotient is cyclic of order three. -/
theorem mathieuOctadFive_quotient_order (O : Octad) (P : Finset Omega)
    (hPO : P ⊆ O.val) (hP : P.card=5) :
    Nat.card (alternatingGroup (↑((octadMarkedPoints O P)ᶜ)))=3 := by
  have hc : Nat.card (↑((octadMarkedPoints O P)ᶜ))=3 := by
    rw [octadUnmarkedPoints_card O P hPO,hP]
  letI : Nontrivial (↑((octadMarkedPoints O P)ᶜ)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  rw [nat_card_alternatingGroup,hc]
  decide

end Atlas.Fischer
