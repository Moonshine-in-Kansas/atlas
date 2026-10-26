import Atlas.Rudvalis.CoordinatePlaneParity

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

private theorem plane_orthogonal_real_count (w : MinimumWords) (p a : Point)
    (hap : dot a.val p.val=0) (δ : Bit) :
    Nat.card {x : E // dot a.val x=δ ∧ reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0}=
      2*Nat.card {c : coordinatePlaneSlice p a δ // CrossOrthogonal (minimalCross (minimumWordShellLift w)) c.val} := by
  have h := coordinatePlane_predicate_card p a hap δ (CrossOrthogonal (minimalCross (minimumWordShellLift w)))
  have he (x : E) :
      (dot a.val x=δ ∧ CrossOrthogonal (minimalCross (minimumWordShellLift w)) (coordinateCross (p,x))) ↔
      dot a.val x=δ ∧ reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0 := by
    rw [crossOrthogonal_symm,coordinateCross,crossOrthogonal_mk]
    change (dot a.val x=δ ∧ HermitianOrthogonal (coordinateMinimum (p,x)) (minimumWordShellLift w).val.val) ↔ _
    rw [coordinate_hermitianOrthogonal_pair,minimumWordShellLift_zero_iff,minimumWordShellLift_zero_iff]
  rwa [Nat.card_congr (Equiv.subtypeEquivRight he)] at h

private theorem four_plane_orthogonal_even (w : MinimumWords) (hw : admissibleFourSupport (reduce w.val.val))
    (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) :
    Nat.card {c : coordinatePlaneSlice p a δ // CrossOrthogonal (minimalCross (minimumWordShellLift w)) c.val}%2=0 := by
  classical
  have hc := plane_orthogonal_real_count w p a hap δ
  have he (x : E) :
      (dot a.val x=δ ∧ reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0) ↔
      dot a.val x=δ ∧ ∀y : E,reduce w.val.val (p,y)=0 := by rw [fourSupport_pair_zero_iff _ hw]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)] at hc
  by_cases h : ∀y : E,reduce w.val.val (p,y)=0
  · simp only [h,forall_const,and_true] at hc
    have hd : Nat.card {x : E // dot a.val x=δ}=4 := by
      rw [Nat.card_eq_fintype_card]
      have cert : ∀a : Point,∀δ : Bit,Fintype.card {x : E // dot a.val x=δ}=4 := by decide +kernel
      exact cert a δ
    rw [hd] at hc
    omega
  · simp [h] at hc
    omega

private theorem heavy_plane_orthogonal_parity (w : MinimumWords) (v : BinaryParameters)
    (hv : v.2.2≠0) (hr : binaryNormalMap v=reduce w.val.val)
    (p a : Point) (hap : dot a.val p.val=0) (δ : Bit) :
    (2*Nat.card {c : coordinatePlaneSlice p a δ // CrossOrthogonal (minimalCross (minimumWordShellLift w)) c.val})%4=
      if dot a.val v.2.2=0 then 0 else 2 := by
  classical
  rw [←plane_orthogonal_real_count w p a hap δ,←hr]
  have hw : hammingNorm (binaryNormalMap v)=16 := by
    rw [hr]
    exact quaternary_minimum_residue_weight _ w.val.prop w.prop
  have hb := (binaryNormalMap_quadratic_weight_sixteen v hv).mp hw p
  have he (x : E) : binaryNormalMap v (p,x)=v.1 p+dot (matrixAt v.2.1 p.val+eta p v.2.2) x+quadratic v.2.2 x := by
    change v.1 p+dot (matrixAt v.2.1 p.val) x+theta p v.2.2 x=_
    simp only [theta,dot_add_left]
    ring
  simp_rw [he]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact quadratic_plane_pair_parity p a hap v.2.2 _ hv _ δ hb

theorem disjoint_union_predicate_card (S T : Set MinimalCross) (hd : Disjoint S T) (P : MinimalCross→Prop) :
    Nat.card {c : ↥(S∪T) // P c.val}=Nat.card {c : S // P c.val}+Nat.card {c : T // P c.val} := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun c => c∈S∪T) P)]
  have he : {c | c∈S∪T ∧ P c}={c | c∈S ∧ P c}∪{c | c∈T ∧ P c} := by
    ext c
    simp only [Set.mem_ofPred_eq,Set.mem_union,or_and_right]
  change Nat.card ↥{c | c∈S∪T ∧ P c}=_
  rw [he,Nat.card_congr (Equiv.Set.union (hd.mono (fun _ h => h.1) (fun _ h => h.1))),Nat.card_sum]
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun c => c∈S) P),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun c => c∈T) P)]
  rfl

theorem minimumWord_plane_quartet_orthogonal_even (w : MinimumWords) (p q a : Point)
    (hpq : p≠q) (hap : dot a.val p.val=0) (haq : dot a.val q.val=0) (δ ε : Bit) :
    Nat.card {c : coordinatePlaneQuartet p q a δ ε // CrossOrthogonal (minimalCross (minimumWordShellLift w)) c.val}%2=0 := by
  have hd : Disjoint (coordinatePlaneSlice p a δ) (coordinatePlaneSlice q a ε) :=
    (coordinateRowFrame_disjoint hpq).mono (coordinatePlaneSlice_subset p a δ) (coordinatePlaneSlice_subset q a ε)
  rw [coordinatePlaneQuartet,disjoint_union_predicate_card _ _ hd]
  rcases quaternary_minimum_support_cases w.val.val w.val.prop w.prop with hf|⟨v,hv,hr⟩
  · rw [Nat.add_mod,four_plane_orthogonal_even w hf p a hap δ,four_plane_orthogonal_even w hf q a haq ε]
  · have h1 := heavy_plane_orthogonal_parity w v hv hr p a hap δ
    have h2 := heavy_plane_orthogonal_parity w v hv hr q a haq ε
    split_ifs at h1 h2 <;> omega

theorem coordinateQuartet_of_minimumWord_counts (Q : Set MinimalCross) (hQ : Q⊆coordinateFrame)
    (h4 : Nat.card Q=4)
    (hcounts : ∀w : MinimumWords,Nat.card {c : Q // CrossOrthogonal (minimalCross (minimumWordShellLift w)) c.val}≠3) :
    IsQuartet Q := by
  classical
  refine ⟨h4,?_,?_⟩
  · intro x hx y hy hxy
    exact (coordinateFrame_orthogonal_iff _ _ (hQ hx) (hQ hy)).mpr hxy
  · intro x hx q hq hall
    induction x using Quotient.inductionOn with | h v =>
      rcases rudvalisLattice_shell_cases v.val.val v.val.prop v.prop with hv|⟨w,hw⟩
      · have hvf : minimalCross v∈coordinateFrame :=
          (minimalCross_mem_coordinateFrame v).mpr ((coordinateShellPiece_iff v).mpr hv)
        exact (coordinateFrame_orthogonal_iff _ _ hvf (hQ hq)).mpr
          (by intro he; apply hx; change minimalCross v∈Q; rwa [he])
      · have he : v=minimumWordShellLift w := Subtype.ext (Subtype.ext hw)
        subst v
        by_contra hnq
        have heq (y : Q) : CrossOrthogonal (minimalCross (minimumWordShellLift w)) y.val ↔ ¬y.val=q := by
          constructor
          · intro hy hyq
            exact hnq (hyq ▸ hy)
          · intro hy
            exact hall y.val y.prop hy
        let e : {y : Q // CrossOrthogonal (minimalCross (minimumWordShellLift w)) y.val} ≃
            {y : Q // ¬y=⟨q,hq⟩} :=
          Equiv.subtypeEquivRight (fun y => (heq y).trans
            (not_congr (show y.val=q ↔ y=⟨q,hq⟩ from ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩)))
        apply hcounts w
        let : Fintype Q := Fintype.ofFinite _
        rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
        have hc : Fintype.card Q=4 := by simpa [Nat.card_eq_fintype_card] using h4
        simp [hc]

/-- The two affine-plane pairs in distinct rows form an intrinsic quartet. -/
theorem coordinatePlaneQuartet_isQuartet (p q a : Point) (hpq : p≠q)
    (hap : dot a.val p.val=0) (haq : dot a.val q.val=0) (δ ε : Bit) :
    IsQuartet (coordinatePlaneQuartet p q a δ ε) := by
  apply coordinateQuartet_of_minimumWord_counts _ (coordinatePlaneQuartet_subset p q a δ ε)
    (coordinatePlaneQuartet_card p q a hpq hap haq δ ε)
  intro w h
  have he := minimumWord_plane_quartet_orthogonal_even w p q a hpq hap haq δ ε
  rw [h] at he
  contradiction

end Atlas.Rudvalis
