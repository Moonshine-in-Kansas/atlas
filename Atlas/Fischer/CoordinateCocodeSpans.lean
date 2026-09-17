import Atlas.Fischer.SmallCoordinateCocode
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem coordinateCocodeSpan_mono {S T : Finset Omega} (h : S ⊆ T) :
    coordinateCocodeSpan S ≤ coordinateCocodeSpan T :=
  Submodule.span_mono (Set.image_mono h)

theorem coordinateCocodeSpan_union (S T : Finset Omega) :
    coordinateCocodeSpan (S ∪ T)=coordinateCocodeSpan S ⊔ coordinateCocodeSpan T := by
  classical
  simp only [coordinateCocodeSpan,Finset.coe_union,Set.image_union,Submodule.span_union]

theorem coordinateCocodeSpan_finrank (S : Finset Omega) (hS : S.card<8) :
    Module.finrank Bit (coordinateCocodeSpan S)=S.card := by
  have hr : Set.range (fun i : S => coordinateCocode i.val)=coordinateCocode '' (S : Set Omega) := by
    ext d
    simp only [Set.mem_range,Set.mem_image,Finset.mem_coe]
    exact ⟨fun ⟨i,h⟩ => ⟨i.val,i.prop,h⟩,fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩⟩
  rw [coordinateCocodeSpan,← hr,finrank_span_eq_card (coordinateCocode_small_independent S hS),
    Fintype.card_coe]

theorem coordinateCocodeSpan_card (S : Finset Omega) (hS : S.card<8) :
    Nat.card (coordinateCocodeSpan S)=2^S.card := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),coordinateCocodeSpan_finrank S hS]
  simp [Bit]

/-- On a union of fewer than eight coordinates, cocode spans intersect exactly
as the marked coordinate sets do. -/
theorem coordinateCocodeSpan_inter (S T : Finset Omega) (h : (S ∪ T).card<8) :
    coordinateCocodeSpan S ⊓ coordinateCocodeSpan T=coordinateCocodeSpan (S ∩ T) := by
  classical
  have hS : S.card<8 := lt_of_le_of_lt (Finset.card_le_card Finset.subset_union_left) h
  have hT : T.card<8 := lt_of_le_of_lt (Finset.card_le_card Finset.subset_union_right) h
  have hI : (S ∩ T).card<8 := lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left) hS
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
    (le_inf (coordinateCocodeSpan_mono Finset.inter_subset_left)
      (coordinateCocodeSpan_mono Finset.inter_subset_right))
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (coordinateCocodeSpan S) (coordinateCocodeSpan T)
  rw [← coordinateCocodeSpan_union,coordinateCocodeSpan_finrank _ h,
    coordinateCocodeSpan_finrank _ hS,coordinateCocodeSpan_finrank _ hT] at hd
  rw [coordinateCocodeSpan_finrank _ hI]
  have hc := Finset.card_union_add_card_inter S T
  omega

theorem coordinateCocodeSpan_pair_inter_pair (i j k : Omega)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    coordinateCocodeSpan {i,j} ⊓ coordinateCocodeSpan {i,k}=coordinateCocodeSpan {i} := by
  classical
  rw [coordinateCocodeSpan_inter _ _ (by
    have h := Finset.card_union_le ({i,j} : Finset Omega) {i,k}
    have hS : ({i,j} : Finset Omega).card=2 := by simp [hij]
    have hT : ({i,k} : Finset Omega).card=2 := by simp [hik]
    rw [hS,hT] at h
    omega)]
  congr 1
  ext x
  simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
  aesop

end Atlas.Fischer
