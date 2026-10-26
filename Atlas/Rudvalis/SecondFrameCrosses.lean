import Atlas.Rudvalis.SecondFrameGaussian
import Atlas.Rudvalis.SecondFrameCyclic
import Atlas.Rudvalis.SecondFrameUnitAction
import Atlas.Rudvalis.GaussianFrame
import Atlas.Rudvalis.LatticeCrossPartition
import Atlas.Rudvalis.CrossOrthogonality

/-! The 28 actual Gaussian crosses of the independent second real frame. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

abbrev SecondFrameCrossIndex := Fin 7 × Fin 4

def secondFrameOddIndex (i : SecondFrameCrossIndex) : SeedCoordinate :=
  (i.1,⟨2*i.2.val+1,by omega⟩)

theorem secondFrameOddIndex_injective : Function.Injective secondFrameOddIndex := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun z : SeedCoordinate => z.2.val) h
  apply Prod.ext (show a.1=b.1 from h1)
  apply Fin.ext
  change 2*a.2.val+1=2*b.2.val+1 at h2
  omega

noncomputable def secondFrameShell (z : SeedCoordinate) : MinimalShell :=
  ⟨⟨secondFrame z,secondFrame_mem z⟩,by simpa using secondFrame_pairing z z⟩

noncomputable def secondFrameCross (i : SecondFrameCrossIndex) : MinimalCross :=
  minimalCross (secondFrameShell (secondFrameOddIndex i))

noncomputable def secondFrameCrosses : Set MinimalCross := Set.range secondFrameCross

theorem secondFrameOdd_pairing (i j : SecondFrameCrossIndex) :
    rationalDot (secondFrame (secondFrameOddIndex i)) (secondFrame (secondFrameOddIndex j))=
      if i=j then 4 else 0 := by
  rw [secondFrame_pairing]
  simp only [secondFrameOddIndex_injective.eq_iff]

theorem secondFrameOdd_pairing_I (i j : SecondFrameCrossIndex) :
    rationalDot (secondFrame (secondFrameOddIndex i))
      (rationalI (secondFrame (secondFrameOddIndex j)))=0 := by
  rw [secondFrame_I]
  have hodd : (secondFrameOddIndex j).2.val%2≠0 := by
    change (2*j.2.val+1)%2≠0
    omega
  rw [ite_eq_right hodd]
  have hne : secondFrameOddIndex i≠((secondFrameOddIndex j).1,seedIIndex (secondFrameOddIndex j).2) := by
    intro h
    have hv := congrArg (fun z : SeedCoordinate => z.2.val%2) h
    have he : ∀k : Fin 8,(seedIIndex k).val%2=1-k.val%2 := by decide +kernel
    rw [he] at hv
    change (2*i.2.val+1)%2=1-(2*j.2.val+1)%2 at hv
    omega
  simp only [rationalDot,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]
  change -rationalDot (secondFrame (secondFrameOddIndex i))
    (secondFrame ((secondFrameOddIndex j).1,seedIIndex (secondFrameOddIndex j).2))=0
  rw [secondFrame_pairing,ite_eq_right hne,neg_zero]

theorem secondFrameCross_injective : Function.Injective secondFrameCross := by
  intro i j h
  by_contra hne
  apply minimalCross_ne_of_orthogonal (secondFrameShell (secondFrameOddIndex i))
    (secondFrameShell (secondFrameOddIndex j)) ?_ (secondFrameOdd_pairing_I i j) h
  exact (secondFrameOdd_pairing i j).trans (ite_eq_right hne)

theorem secondFrameCrosses_card : Nat.card secondFrameCrosses=28 := by
  unfold secondFrameCrosses
  rw [←Nat.card_congr (Equiv.ofInjective secondFrameCross secondFrameCross_injective)]
  norm_num [Nat.card_eq_fintype_card]


theorem secondFrameCross_orthogonal (i j : SecondFrameCrossIndex) (hij : i≠j) :
    CrossOrthogonal (secondFrameCross i) (secondFrameCross j) := by
  apply (crossOrthogonal_mk _ _).mpr
  constructor
  · exact (secondFrameOdd_pairing i j).trans (ite_eq_right hij)
  · rw [rationalDot_comm]
    exact secondFrameOdd_pairing_I j i

theorem secondFrameCrosses_pairwise_orthogonal : secondFrameCrosses.Pairwise CrossOrthogonal := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ h
  exact secondFrameCross_orthogonal i j (fun hij => h (congrArg secondFrameCross hij))

noncomputable def secondFrameBaseHeavyWord : HeavyMinimumWords :=
  ⟨⟨quaternarySeed (0,0,0,1),quaternaryCode_seed _⟩,quaternary_base_seed_weight 1,by
    rw [quaternarySeed_reduce]
    exact ⟨seedBParameters,by decide,seedB_residue.symm⟩⟩

theorem secondFrame_base_integerLift : integerLift (quaternarySeed (0,0,0,1))=secondFrameInteger (0,1) := by
  have hb : secondFrameInteger (0,1)=seedBWord := by
    change (1 : ℤ) • signedSeedTransport ((seedPOperator^0) ((seedIOperator^0) (seedJOperator 0 seedBArray)))=seedBWord
    simp [seedJOperator,seedBWord]
  rw [hb]
  funext i
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective i
  change integerRepresentative ((signedSeedTransport seedBArray (seedCoordinateEquiv (r,k)) : ℤ) : ZMod 4)=
    signedSeedTransport seedBArray (seedCoordinateEquiv (r,k))
  rw [signedSeedTransport_apply]
  decide +kernel +revert

theorem secondFrame_base_heavy : secondFrameShell (0,1)∈heavyShellPiece := by
  refine ⟨secondFrameBaseHeavyWord,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change halfCoordinates (integerLift (quaternarySeed (0,0,0,1)))=halfCoordinates (secondFrameInteger (0,1))
  rw [secondFrame_base_integerLift]

/-- Every chosen second-frame representative is an actual P/unit translate of B. -/
theorem secondFrameOdd_base_orbit (i : SecondFrameCrossIndex) :
    ∃g : codeGroup,g • secondFrameShell (0,1)=secondFrameShell (secondFrameOddIndex i) := by
  let u : Fin 8 := ⟨i.2.val,by omega⟩
  let n := (secondFrameRow i.1).val
  refine ⟨codeP^n*codeUnit u,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change rationalMonomialHom ((codeP^n*codeUnit u).val) (secondFrame (0,1))=_
  rw [Subgroup.coe_mul,map_mul]
  change rationalMonomialHom (codeP^n).val (rationalMonomialHom (codeUnit u).val (secondFrame (0,1)))=_
  rw [secondFrame_unit]
  have hu : seedUnitSource u 1=(secondFrameOddIndex i).2 ∧ seedUnitSign u (seedUnitSource u 1)=false := by
    change seedUnitSource ⟨i.2.val,by omega⟩ 1=(secondFrameOddIndex i).2 ∧ _
    rcases i with ⟨r,k⟩
    fin_cases k <;> decide +kernel +revert
  rw [hu.2,ite_eq_right Bool.false_ne_true,hu.1,secondFrame_P_power]
  have hn : (secondFrameCyclicPerm^n) (0,(secondFrameOddIndex i).2)=secondFrameOddIndex i := by
    change (secondFrameCyclicPerm^(secondFrameRow i.1).val) (0,(secondFrameOddIndex i).2)=_
    decide +kernel +revert
  rw [hn]
  rfl

theorem secondFrameOdd_heavy (i : SecondFrameCrossIndex) :
    secondFrameShell (secondFrameOddIndex i)∈heavyShellPiece := by
  obtain ⟨g,hg⟩ := secondFrameOdd_base_orbit i
  rw [←hg]
  exact SMulMemClass.smul_mem g secondFrame_base_heavy

theorem secondFrameCross_heavy (i : SecondFrameCrossIndex) :
    secondFrameCross i∈Set.range (shellPieceCrossMap heavyShellPiece) :=
  ⟨Quotient.mk _ ⟨secondFrameShell (secondFrameOddIndex i),secondFrameOdd_heavy i⟩,rfl⟩

theorem secondFrameCrosses_disjoint_coordinateFrame : Disjoint secondFrameCrosses coordinateFrame := by
  rw [Set.disjoint_left]
  rintro c ⟨i,rfl⟩ hc
  exact coordinate_heavy_shell_disjoint _ ((minimalCross_mem_coordinateFrame _).mp hc)
    (secondFrameOdd_heavy i)

end Atlas.Rudvalis
