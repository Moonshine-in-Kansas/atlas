import Atlas.Fischer.FischerDoubleCoverGenerators
import Atlas.Fischer.OctadAvoidance
import Mathlib.GroupTheory.Abelianization.Defs

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The two actual octad relations kill both kinds of generators in the abelianization. -/
theorem doubleCover_perfect (i j : Omega) (hij : i≠j) : Group.IsPerfect (FischerDoubleCover i j) := by
  classical
  let S : Finset Omega := {i,j}
  let q : FischerDoubleCover i j →* Abelianization (FischerDoubleCover i j) := Abelianization.of
  let c : Multiplicative Cocode →* FischerDoubleCover i j :=
    (QuotientGroup.mk' (doubleCentralizerFirstKernel i j)).comp (residueCocodeCentralizer S)
  let f := q.comp c
  obtain ⟨Oi,hii,hji,_⟩ := octad_contains_avoids_two {i} (by simp) j j
    (by simpa using hij.symm) (by simpa using hij.symm)
  obtain ⟨Oj,hjj,hijO,_⟩ := octad_contains_avoids_two {j} (by simp) i i
    (by simpa using hij) (by simpa using hij)
  have hii : i∈Oi.val := hii (by simp)
  have hjj : j∈Oj.val := hjj (by simp)
  have hcard : (Oi.val.erase i).card=7 := by
    rw [Finset.card_erase_of_mem hii,octad_size Oi.val Oi.prop]
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (show 0<(Oi.val.erase i).card by omega)
  have hkS : k∉S := by
    simp only [S,Finset.mem_insert,Finset.mem_singleton]
    obtain ⟨hki,hkO⟩ := Finset.mem_erase.mp hk
    exact fun h => h.elim hki (fun h => hji (h ▸ hkO))
  let x := residueBasicPoint S k hkS
  let u := q (doubleCoverResidualElement i j x)
  have he (y : ResiduePoint S) : q (doubleCoverResidualElement i j y)=u := by
    obtain ⟨g,hg⟩ := doubleCoverResidualElement_conjugate i j y x
    change q (doubleCoverResidualElement i j y)=q (doubleCoverResidualElement i j x)
    rw [← hg]
    simp
  have ho (l : Omega) (hl : l∉S) : f (cocodeInvolution l)=u := by
    change q (doubleCoverMarkedElement i j l)=u
    rw [← doubleCoverResidualElement_basic i j l hl]
    exact he _
  have hO (O : Octad) (t : Omega) (ht : t∈O.val)
      (hrest : ∀ l∈O.val, l≠t → l∉S) : u^7*f (cocodeInvolution t)=1 := by
    have hc : (O.val.erase t).card=7 := by
      rw [Finset.card_erase_of_mem ht,octad_size O.val O.prop]
    have hp : (∏ l ∈ O.val.erase t,f (cocodeInvolution l))=u^7 := by
      rw [Finset.prod_eq_pow_card (fun l hl => ho l
        (hrest l (Finset.mem_erase.mp hl).2 (Finset.mem_erase.mp hl).1)),hc]
    rw [← hp,Finset.prod_erase_mul _ _ ht,← map_prod]
    have hw := binarySupportEquiv.symm_apply_apply (octadWord O).val
    change binarySupportEquiv.symm (support (octadWord O).val)=(octadWord O).val at hw
    rw [octadWord_support] at hw
    rw [(cocodeInvolutions_relation O.val).mpr (hw ▸ (octadWord O).prop),map_one]
  have hi0 : f (cocodeInvolution i)=1 := by
    change q (doubleCoverMarkedElement i j i)=1
    rw [doubleCoverMarkedElement_first,map_one]
  have h7 : u^7=1 := by
    have h := hO Oi i hii (by
      intro l hl hli
      simp only [S,Finset.mem_insert,Finset.mem_singleton]
      exact fun h => h.elim hli (fun h => hji (h ▸ hl)))
    simpa only [hi0,mul_one] using h
  have h2 : u^2=1 := by
    change q (doubleCoverResidualElement i j x)^2=1
    rw [← map_pow,doubleCoverResidualElement_square,map_one]
  have hu : u=1 := by
    have h6 : u^6=1 := by
      calc
        u^6=(u^2)^3 := by rw [← pow_mul]
        _=1 := by rw [h2,one_pow]
    simpa only [show 7=6+1 from rfl,pow_succ,h6,one_mul] using h7
  have hj0 : q (doubleCoverMarkedElement i j j)=1 := by
    have h := hO Oj j hjj (by
      intro l hl hlj
      simp only [S,Finset.mem_insert,Finset.mem_singleton]
      exact fun h => h.elim (fun h => hijO (h ▸ hl)) hlj)
    change u^7*q (doubleCoverMarkedElement i j j)=1 at h
    simpa only [hu,one_pow,one_mul] using h
  have hle : Subgroup.closure (insert (doubleCoverMarkedElement i j j)
      (Set.range (doubleCoverResidualElement i j))) ≤ commutator (FischerDoubleCover i j) := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rw [← Abelianization.ker_of]
    rcases ha with rfl | ⟨y,rfl⟩
    · exact hj0
    · exact (he y).trans hu
  exact ⟨top_unique (doubleCover_generators i j ▸ hle)⟩

end Atlas.Fischer
