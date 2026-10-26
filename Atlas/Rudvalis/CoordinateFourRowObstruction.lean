import Atlas.Rudvalis.FanoFourRows

namespace Atlas.Rudvalis
/-- Three zero Gaussian pairs and a fourth nonzero pair can be prescribed on an affine Fano plane. -/
theorem heavy_four_rows_test (p : Fin 4→Point) (x : Fin 4→E)
    (hdet : (pairBasisMatrix (p 0) (p 1) (p 2).val).det=1)
    (hsum : (p 3).val=(p 0).val+(p 1).val+(p 2).val)
    (c : Point) (hc : ∀i : Fin 4,p i≠c)
    (h03 : (p 0).val≠(p 3).val) (h0c : (p 0).val≠c.val)
    (h0c3 : (p 0).val≠c.val+(p 3).val) :
    ∃z : MinimalCross,z∉coordinateFrame ∧
      (∀i : Fin 4,i≠3 → CrossOrthogonal z (coordinateCross (p i,x i))) ∧
      ¬CrossOrthogonal z (coordinateCross (p 3,x 3)) := by
  classical
  obtain ⟨v⟩ : Nonempty (FixedHeavyParameters c) :=
    (Nat.card_pos_iff.mp (show 0<Nat.card (FixedHeavyParameters c) by
      rw [fixedHeavyParameters_card];decide)).1
  obtain ⟨a,ha0,ha1⟩ := fixedHeavy_pair_avoid_translate (p 0) c (hc 0) v (x 0)
  obtain ⟨b,hb0,hb1⟩ := fixedHeavy_pair_avoid_translate (p 1) c (hc 1) v (x 1)
  obtain ⟨d,hd0,hd1⟩ := fixedHeavy_pair_avoid_translate (p 2) c (hc 2) v (x 2)
  let good (y : E) : Prop := fixedHeavyWord c v (p 3,y)=0 ∧
    fixedHeavyWord c v (p 3,y+(p 3).val)=0
  have hcomp := fixedHeavy_pair_complement (p 3) c (hc 3) (p 0).val (p 0).prop
    h03 h0c h0c3 v (x 3+(a+b+d))
  have hchoice : ∃a' : E,
      (fixedHeavyWord c v (p 0,x 0+a')=0 ∧
        fixedHeavyWord c v (p 0,x 0+(p 0).val+a')=0) ∧
      ¬good (x 3+(a'+b+d)) := by
    by_cases h : good (x 3+(a+b+d))
    · refine ⟨a+(p 0).val,?_,?_⟩
      · constructor
        · have he : x 0+(a+(p 0).val)=x 0+(p 0).val+a := by abel
          rw [he];exact ha1
        · have he : x 0+(p 0).val+(a+(p 0).val)=x 0+a := by
            calc _=(x 0+a)+((p 0).val+(p 0).val) := by abel
                 _=x 0+a := by rw [vector_add_self,add_zero]
          rw [he];exact ha0
      · have hn := hcomp.mp h
        have he : x 3+(a+(p 0).val+b+d)=(x 3+(a+b+d))+(p 0).val := by abel
        rw [he]
        exact hn
    · exact ⟨a,⟨ha0,ha1⟩,h⟩
  obtain ⟨a',ha',hn⟩ := hchoice
  obtain ⟨B,hB0,hB1,hB2⟩ := matrixAt_three_points (p 0) (p 1) (p 2) hdet a' b d
  have hB3 : matrixAt B (p 3).val=a'+b+d := by
    rw [hsum]
    change (binaryMatrixLinear B) ((p 0).val+(p 1).val+(p 2).val)=_
    rw [map_add,map_add]
    exact congrArg₂ (·+·) (congrArg₂ (·+·) hB0 hB1) hB2
  let v' := fixedHeavyTranslate c B v
  obtain ⟨z,hz,ht⟩ := fixedHeavy_test_cross c v'
  have he (i : Fin 4) (y : E) : fixedHeavyWord c v' (p i,y)=
      fixedHeavyWord c v (p i,y+matrixAt B (p i).val) :=
    congrFun (fixedHeavyTranslate_word c B v) (p i,y)
  refine ⟨z,hz,?_,?_⟩
  · intro i hi
    rw [ht,he,he]
    fin_cases i
    · change fixedHeavyWord c v (p 0,x 0+matrixAt B (p 0).val)=0 ∧
        fixedHeavyWord c v (p 0,x 0+(p 0).val+matrixAt B (p 0).val)=0
      rw [hB0];exact ha'
    · change fixedHeavyWord c v (p 1,x 1+matrixAt B (p 1).val)=0 ∧
        fixedHeavyWord c v (p 1,x 1+(p 1).val+matrixAt B (p 1).val)=0
      rw [hB1];exact ⟨hb0,hb1⟩
    · change fixedHeavyWord c v (p 2,x 2+matrixAt B (p 2).val)=0 ∧
        fixedHeavyWord c v (p 2,x 2+(p 2).val+matrixAt B (p 2).val)=0
      rw [hB2];exact ⟨hd0,hd1⟩
    · exact (hi rfl).elim
  · rw [ht,he,he,hB3]
    simpa only [good,add_assoc,add_comm,add_left_comm] using hn

theorem coordinateQuartet_not_four_distinct_rows (Q : Set MinimalCross) (hQ : IsQuartet Q)
    (p : Fin 4→Point) (x : Fin 4→E) (hp : Function.Injective p)
    (hQeq : Q=Set.range (fun i => coordinateCross (p i,x i))) : False := by
  have hmem (i : Fin 4) : coordinateCross (p i,x i)∈Q := by rw [hQeq];exact ⟨i,rfl⟩
  have hF : Q⊆coordinateFrame := by
    rintro z hz
    rw [hQeq] at hz
    obtain ⟨i,rfl⟩ := hz
    exact coordinateCross_mem _
  rcases fano_four_rows_alternative p hp with ⟨a,i,hai,hrest⟩ | ⟨hd,hs,c,hc,h03,h0c,h0c3⟩
  · apply coordinateQuartet_no_single_linear_label Q hQ hF a (p i) (x i) (hmem i) hai
    intro z hz hne
    rw [hQeq] at hz
    obtain ⟨j,rfl⟩ := hz
    exact ⟨p j,x j,rfl,hrest j (by intro h;subst j;exact hne rfl)⟩
  · obtain ⟨z,hz,ht,hn⟩ := heavy_four_rows_test p x hd hs c hc h03 h0c h0c3
    apply hn
    apply hQ.2.2 z (fun h => hz (hF h)) (coordinateCross (p 3,x 3)) (hmem 3)
    intro y hy hne
    rw [hQeq] at hy
    obtain ⟨i,rfl⟩ := hy
    exact ht i (by intro h;subst i;exact hne rfl)

end Atlas.Rudvalis
