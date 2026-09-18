/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.SextetCompletion

namespace Atlas.Codes
open Finset
open scoped BigOperators

noncomputable instance : Fintype UnorderedSextet := Fintype.ofFinite _

abbrev SextetIncidence := Σ S : UnorderedSextet, {T : Finset Omega // T ∈ S.val}

def sextetIncidenceProjection (x : SextetIncidence) : FourSet :=
  ⟨x.2.val,x.1.prop.tetrad_size _ x.2.prop⟩

theorem sextetIncidenceProjection_bijective : Function.Bijective sextetIncidenceProjection := by
  constructor
  · rintro ⟨S,T⟩ ⟨R,U⟩ h
    have ht : T.val = U.val := congrArg Subtype.val h
    have hR : S = R := (sextet_eq_completion S ⟨T.val,S.prop.tetrad_size _ T.prop⟩ T.prop).trans
      (sextet_eq_completion R ⟨T.val,S.prop.tetrad_size _ T.prop⟩ (ht ▸ U.prop)).symm
    subst R
    have hU : T = U := Subtype.ext ht
    subst U
    rfl
  · intro T
    exact ⟨⟨sextetCompletion T,⟨T.val,tetrad_mem_completion T⟩⟩,rfl⟩

noncomputable def sextetIncidenceEquiv : SextetIncidence ≃ FourSet :=
  Equiv.ofBijective sextetIncidenceProjection sextetIncidenceProjection_bijective

theorem sextet_incidence_count : (24 : ℕ).choose 4 = 6 * Nat.card UnorderedSextet := by
  classical
  have h := Nat.card_congr sextetIncidenceEquiv
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at h
  change Fintype.card (Σ S : UnorderedSextet, {T : Finset Omega // T ∈ S.val}) =
    Fintype.card {T : Finset Omega // T.card = 4} at h
  rw [Fintype.card_sigma,Fintype.card_finset_len] at h
  have hf (S : UnorderedSextet) : Fintype.card {T : Finset Omega // T ∈ S.val} = 6 := by
    rw [Fintype.card_coe,S.prop.six_parts]
  simp only [hf,sum_const,card_univ,smul_eq_mul] at h
  norm_num only [Omega,HexIndex,Fintype.card_prod,Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card,mul_comm]
  exact h.symm

theorem unordered_sextets_card : Nat.card UnorderedSextet = 1771 := by
  have h := sextet_incidence_count
  norm_num [Nat.choose] at h
  rw [Nat.card_eq_fintype_card]
  omega

noncomputable def completionFiberEquiv (S : UnorderedSextet) :
    {T : FourSet // sextetCompletion T = S} ≃ {T : Finset Omega // T ∈ S.val} where
  toFun T := ⟨T.val.val, by
    have hh := congrArg Subtype.val T.prop
    exact Eq.mp (congrArg (fun U => T.val.val ∈ U) hh) (tetrad_mem_completion T.val)⟩
  invFun U := ⟨⟨U.val,S.prop.tetrad_size _ U.prop⟩,(sextet_eq_completion S _ U.prop).symm⟩
  left_inv := by intro T; apply Subtype.ext; rfl
  right_inv := by intro U; rfl

theorem completion_fiber_card (S : UnorderedSextet) :
    Nat.card {T : FourSet // sextetCompletion T = S} = 6 := by
  rw [Nat.card_congr (completionFiberEquiv S),Nat.card_eq_fintype_card,Fintype.card_coe,S.prop.six_parts]

end Atlas.Codes
