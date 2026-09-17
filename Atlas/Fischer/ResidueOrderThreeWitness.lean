import Atlas.Fischer.ResidueKernelDuads
import Atlas.Fischer.ResidueProductOrders

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A basic point outside a duad and a duadic point on it are actual noncommuting residue points. -/
theorem residue_exists_order_three_pair (S : Finset Omega) (hS : S.card≤2) :
    ∃ x y : ResiduePoint S, orderOf (x.val*y.val)=3 := by
  classical
  obtain ⟨p,hSp,hpU,hp⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ S) hS (show 2 ≤ (Finset.univ : Finset Omega).card by decide)
  have hex : ∃ i : Omega, i ∉ p := by
    by_contra h
    have he : p=Finset.univ := by
      ext i
      simp only [Finset.mem_univ,iff_true]
      exact not_not.mp (fun hi => h ⟨i,hi⟩)
    rw [he] at hp
    norm_num [Omega,HexIndex] at hp
  obtain ⟨i,hi⟩ := hex
  let d : RootDuad := ⟨p,hp⟩
  refine ⟨residueBasicPoint S i (fun his => hi (hSp his)),residueDuadicPoint S d hSp 0,?_⟩
  change orderOf (distinguishedRootElement (.inl i) *
    distinguishedRootElement (.inr (.inr ⟨d,0⟩)))=3
  rw [distinguishedRootElement_product_order _ _ (by intro h; cases h)]
  change (if hermitian (basicAxis i) (chosenDuadicRoot d 0)=0 then 3 else 2)=3
  rw [hermitian_basicAxis_duadic,if_neg hi,if_pos rfl]

end Atlas.Fischer
