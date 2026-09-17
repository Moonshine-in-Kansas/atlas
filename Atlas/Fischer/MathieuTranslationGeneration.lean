import Atlas.Fischer.MathieuFiveOctadLocal
import Atlas.GroupTheory.PerfectLocalQuotient

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped commutatorElement

/-- Octad translations containing at most two prescribed coordinates generate
the full pointwise Mathieu stabilizer. The proof uses the actual octad local
quotients, not simplicity of any Mathieu group. -/
theorem mathieuTranslationGenerated_eq_fixing_of_octad (O : Octad) (S : Finset Omega)
    (hSO : S ⊆ O.val) (hS : S.card ≤ 2) :
    mathieuTranslationGenerated S=fixingSubgroup Mathieu24CodeModel (S : Set Omega) := by
  classical
  obtain ⟨P,hSP,hPO,hP⟩ := Finset.exists_subsuperset_card_eq hSO (show S.card ≤ 5 by omega)
    (show 5 ≤ O.val.card by rw [octad_size O.val O.prop]; decide)
  let M := fixingSubgroup Mathieu24CodeModel (S : Set Omega)
  let H := fixingSubgroup Mathieu24CodeModel (P : Set Omega)
  let K := mathieuOctadRestrictedLocal O (octadMarkedPoints O S)
  let N := mathieuTranslationNormalSubgroup S
  let i : H →* M := Subgroup.inclusion (by
    intro g hg x
    exact hg ⟨x.val,hSP x.prop⟩)
  let j : K →* M := mathieuOctadMarkedEmbedding O S hSO
  let f := mathieuOctadComplementHom O (octadMarkedPoints O S)
  let b := mathieuFiveFixerComplementHom O P hPO hP
  have hbcard : Nat.card (alternatingGroup (↑((octadMarkedPoints O P)ᶜ)))=3 :=
    mathieuOctadFive_quotient_order O P hPO hP
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI := isCyclic_of_prime_card hbcard
  have hN : N=⊤ := Atlas.GroupTheory.normal_eq_top_of_local_quotients N i j f
    (mathieuOctadComplementHom_surjective O _) (mathieuOctadMarked_perfect_quotient O S hSO hS)
    (by
      intro g
      obtain ⟨r,k,hg⟩ := mathieuTranslationGenerated_factorization S P hSP (by omega) g.val
        (fun a ha => g.prop ⟨a,ha⟩)
      refine ⟨⟨⟨r.val,mathieuTranslationGenerated_le_fixing S r.prop⟩,r.prop⟩,k,?_⟩
      exact Subtype.ext hg)
    (by
      intro h h'
      have hb : b ⁅h,h'⁆=1 := by
        rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm' _ _
      have hr := mathieuFiveFixerComplement_kernel O S P hSO hPO hP ⁅h,h'⁆ hb
      exact hr)
    (by
      intro k hk
      rw [mathieuOctadComplementHom_ker] at hk
      exact Subgroup.subset_closure ⟨O,hSO,⟨k.val,hk⟩,rfl⟩)
    (by
      intro h
      let l := mathieuFiveFixerLocalHom O P hPO hP h
      have hl : l.val ∈ K := (mathieuOctadMarkedLocal_iff O S hSO l.val).mpr
        (fun a ha => h.prop ⟨a,hSP ha⟩)
      exact ⟨⟨l.val,hl⟩,rfl⟩)
  apply le_antisymm (mathieuTranslationGenerated_le_fixing S)
  intro g hg
  have hmem : (⟨g,hg⟩ : M) ∈ N := by rw [hN]; trivial
  exact hmem

/-- The unconditional source generation statement for zero, one or two fixed points. -/
theorem mathieuTranslationGenerated_eq_fixing (S : Finset Omega) (hS : S.card ≤ 2) :
    mathieuTranslationGenerated S=fixingSubgroup Mathieu24CodeModel (S : Set Omega) := by
  classical
  have hex : ∃ x : Omega, x ∉ S := by
    by_contra! hn
    have he : S=Finset.univ := Finset.eq_univ_of_forall hn
    have hc : S.card=24 := by rw [he]; decide
    omega
  obtain ⟨x,hx⟩ := hex
  obtain ⟨O,hSO,_,_⟩ := octad_contains_avoids_two S (by omega) x x hx hx
  exact mathieuTranslationGenerated_eq_fixing_of_octad O S hSO hS

end Atlas.Fischer
