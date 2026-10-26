import Atlas.LinearGroups.F4.WhiteZeroPoints
import Atlas.Algebra.Albert.UniversalCriterion
import Atlas.Algebra.Albert.CrossProduct

/-! Faithfulness reconstructed from explicit trace-zero rank-one lines.
Integral coordinate certificates below concern at most pairs of the 24 marked
basis vectors. No group order, simplicity or characteristic restriction is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization BigOperators
variable {F : Type*} [Field F]

private theorem coefficient_map_zero {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) : Atlas.Albert.map φ (0 : Carrier R)=0 := by
  apply Prod.ext <;> funext i
  · simp [Atlas.Albert.map]
  · funext j; simp [Atlas.Albert.map]

private theorem coefficient_map_neg {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (x : Carrier R) : Atlas.Albert.map φ (-x)= -Atlas.Albert.map φ x := by
  apply Prod.ext <;> funext i
  · simp [Atlas.Albert.map]
  · funext j; simp [Atlas.Albert.map]

private theorem off_basis_white (i : Fin 3 × Fin 8) :
    trace (basisVector (.inr i) : Carrier F)=0 ∧ adjoint (basisVector (.inr i) : Carrier F)=0 := by
  have hz : ∀i : Fin 3 × Fin 8,trace (basisVector (.inr i) : Carrier ℤ)=0 ∧
      adjoint (basisVector (.inr i) : Carrier ℤ)=0 := by decide +kernel
  let φ : ℤ →+* F := Int.castRingHom F
  constructor
  · rw [←map_basisVector φ (.inr i),trace_map,(hz i).1,_root_.map_zero]
  · rw [←map_basisVector φ (.inr i),adjoint_map,(hz i).2,coefficient_map_zero]

private theorem off_same_slot_white (i : Fin 3) (j k : Fin 8) (hjk : j.val+k.val≠7) :
    trace (basisVector (.inr (i,j))+basisVector (.inr (i,k)) : Carrier F)=0 ∧
    adjoint (basisVector (.inr (i,j))+basisVector (.inr (i,k)) : Carrier F)=0 := by
  have hz : ∀i : Fin 3,∀j k : Fin 8,j.val+k.val≠7 →
      trace (basisVector (.inr (i,j))+basisVector (.inr (i,k)) : Carrier ℤ)=0 ∧
      adjoint (basisVector (.inr (i,j))+basisVector (.inr (i,k)) : Carrier ℤ)=0 := by decide +kernel
  let φ : ℤ →+* F := Int.castRingHom F
  have he : Atlas.Albert.map φ (basisVector (.inr (i,j))+basisVector (.inr (i,k)))=
      (basisVector (.inr (i,j))+basisVector (.inr (i,k)) : Carrier F) := by
    rw [Atlas.Albert.map_add,map_basisVector,map_basisVector]
  constructor
  · rw [←he,trace_map,(hz i j k hjk).1,_root_.map_zero]
  · rw [←he,adjoint_map,(hz i j k hjk).2,coefficient_map_zero]

private theorem off_anchor_white (i j : Fin 3) :
    trace (basisVector (.inr (i,0))+basisVector (.inr (j,0)) : Carrier F)=0 ∧
    adjoint (basisVector (.inr (i,0))+basisVector (.inr (j,0)) : Carrier F)=0 := by
  have hz : ∀i j : Fin 3,
      trace (basisVector (.inr (i,0))+basisVector (.inr (j,0)) : Carrier ℤ)=0 ∧
      adjoint (basisVector (.inr (i,0))+basisVector (.inr (j,0)) : Carrier ℤ)=0 := by decide +kernel
  let φ : ℤ →+* F := Int.castRingHom F
  have he : Atlas.Albert.map φ (basisVector (.inr (i,0))+basisVector (.inr (j,0)))=
      (basisVector (.inr (i,0))+basisVector (.inr (j,0)) : Carrier F) := by
    rw [Atlas.Albert.map_add,map_basisVector,map_basisVector]
  constructor
  · rw [←he,trace_map,(hz i j).1,_root_.map_zero]
  · rw [←he,adjoint_map,(hz i j).2,coefficient_map_zero]

private theorem off_opposite_adjoint (i : Fin 3) :
    adjoint (basisVector (.inr (i,0))+basisVector (.inr (i,7)) : Carrier F)= -basisVector (.inl i) := by
  have hz : ∀i : Fin 3,
      adjoint (basisVector (.inr (i,0))+basisVector (.inr (i,7)) : Carrier ℤ)= -basisVector (.inl i) := by
    decide +kernel
  have h := congrArg (Atlas.Albert.map (Int.castRingHom F)) (hz i)
  rw [←adjoint_map,Atlas.Albert.map_add,map_basisVector,map_basisVector,
    coefficient_map_neg,map_basisVector] at h
  exact h

private theorem off_cross_anchor :
    cross (basisVector (.inr (0,0))) (basisVector (.inr (1,4)) : Carrier F)= -basisVector (.inr (2,0)) := by
  have hz : adjoint (basisVector (.inr (0,0))+basisVector (.inr (1,4)) : Carrier ℤ)=
      -basisVector (.inr (2,0)) := by decide +kernel
  have h := congrArg (Atlas.Albert.map (Int.castRingHom F)) hz
  rw [←adjoint_map,Atlas.Albert.map_add,map_basisVector,map_basisVector,
    coefficient_map_neg,map_basisVector] at h
  rw [cross,(off_basis_white (F:=F) (0,0)).2,(off_basis_white (F:=F) (1,4)).2,
    sub_zero,sub_zero]
  exact h

private theorem albert_basis_scalars_equal (g : Carrier F →ₗ[F] Carrier F)
    (i j : Coordinate) (hij : i≠j) (a b c : F)
    (hi : g (basisVector i)=a • basisVector i)
    (hj : g (basisVector j)=b • basisVector j)
    (hc : g (basisVector i+basisVector j)=c • (basisVector i+basisVector j)) : a=b := by
  rw [_root_.map_add,hi,hj] at hc
  have he := congrArg coordinateEquiv hc
  simp only [_root_.map_add,_root_.map_smul,coordinate_basisVector] at he
  have h1 := congrFun he i
  have h2 := congrFun he j
  simp [Pi.single_apply,hij,Ne.symm hij] at h1 h2
  exact h1.trans h2.symm

theorem whiteZero_lines_kernel_trivial (g : Model F)
    (hg : ∀p : WhiteZeroPoints F,g • p=p) : g=1 := by
  have hx : ∀x : Carrier F,trace x=0 → adjoint x=0 → ∃c : F,g.val x=c • x := by
    intro x ht ha
    by_cases hz : x=0
    · subst x; exact ⟨1,by simp⟩
    · have h := congrArg Subtype.val (hg (whiteZeroPointMk F x hz ht ha))
      change g.val • Projectivization.mk F x hz=Projectivization.mk F x hz at h
      rw [Projectivization.smul_mk,Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c,hc⟩ := h
      exact ⟨c,hc.symm⟩
  choose c hc using fun i : Fin 3 × Fin 8=>
    hx (basisVector (.inr i)) (off_basis_white i).1 (off_basis_white i).2
  have hpair (i j : Fin 3 × Fin 8) (hij : i≠j)
      (hw : trace (basisVector (.inr i)+basisVector (.inr j) : Carrier F)=0 ∧
        adjoint (basisVector (.inr i)+basisVector (.inr j) : Carrier F)=0) : c i=c j := by
    obtain ⟨d,hd⟩ := hx _ hw.1 hw.2
    exact albert_basis_scalars_equal g.val.toLinearMap _ _ (by simpa using hij)
      _ _ _ (hc i) (hc j) hd
  have hblock (i : Fin 3) (j : Fin 8) : c (i,j)=c (i,0) := by
    by_cases hj0 : j=0
    · subst j; rfl
    by_cases hj7 : j=7
    · subst j
      exact (hpair (i,7) (i,1) (by simp) (off_same_slot_white i 7 1 (by decide))).trans
        (hpair (i,1) (i,0) (by simp) (off_same_slot_white i 1 0 (by decide)))
    · exact hpair (i,j) (i,0) (by simpa using hj0)
        (off_same_slot_white i j 0 (by intro h; apply hj7; apply Fin.ext; omega))
  have hcommon (i : Fin 3 × Fin 8) : c i=c (0,0) := by
    rw [hblock]
    by_cases hi : i.1=0
    · rw [hi]
    · exact hpair (i.1,0) (0,0) (by simpa using hi) (off_anchor_white i.1 0)
  have hscale (i : Fin 3 × Fin 8) :
      g.val (basisVector (.inr i))=c (0,0) • basisVector (.inr i) := by rw [hc,hcommon]
  let a := c (0,0)
  have hdiag (i : Fin 3) : g.val (basisVector (.inl i))=a^2 • basisVector (.inl i) := by
    have h := stabilizer_adjoint g (basisVector (.inr (i,0))+basisVector (.inr (i,7)))
    rw [_root_.map_add,hscale,hscale,←smul_add,adjoint_smul] at h
    simp only [off_opposite_adjoint,_root_.map_neg,smul_neg] at h
    exact (neg_injective h).symm
  have hu : (unit : Carrier F)=∑i : Fin 3,basisVector (.inl i) := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [unit,basisVector,Fin.sum_univ_succ]
    · funext i j; simp [unit,basisVector,Fin.sum_univ_succ]
  have ha2 : a^2=1 := by
    have h := stabilizer_unit g
    rw [hu,_root_.map_sum] at h
    simp_rw [hdiag] at h
    rw [←Finset.smul_sum,←hu] at h
    have h0 := congrArg (fun x : Carrier F=>x.1 0) h
    simpa [unit] using h0
  have ha : a=1 := by
    have h := stabilizer_cross g (basisVector (.inr (0,0))) (basisVector (.inr (1,4)))
    rw [hscale,hscale,cross_smul_left,cross_smul_right,smul_smul] at h
    simp only [off_cross_anchor,_root_.map_neg,hscale] at h
    have h0 := congrArg (fun x : Carrier F=>x.2 2 0) h
    have he : -(a*a)= -a := by simpa [basisVector,a] using h0
    have hae : a*a=a := neg_injective he
    exact hae.symm.trans ((pow_two a).symm.trans ha2)
  have hb (i : Coordinate) : g.val (basisVector i)=basisVector i := by
    cases i with
    | inl i => rw [hdiag,ha2,one_smul]
    | inr i => rw [hscale,show c (0,0)=1 from ha,one_smul]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext_basis _ _ hb

instance whiteZeroPointsFaithful : FaithfulSMul (Model F) (WhiteZeroPoints F) :=
  faithfulSMul_iff.mpr whiteZero_lines_kernel_trivial

end Atlas.F4
