import Atlas.LinearGroups.Symplectic.ProjectiveInvolutionClassification
import Atlas.GroupTheory.InvolutionClasses

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

theorem projection_lift_types_not_isConj (hn : 0<n) (h2 : (2:F) ≠ 0)
    (g h : Sp n F) (hg : g^2=negativeIdentity) (hh : h^2=1) :
    ¬ IsConj (projection g) (projection h) := by
  intro hc
  rcases (projection_isConj_iff_signed hn g h).mp hc with hc|hc
  · have he := IsConj.pow 2 hc
    rw [hg,hh] at he
    exact negativeIdentity_ne_one hn h2 (by simpa using he)
  · have he := IsConj.pow 2 hc
    rw [hg,negative_mul_square_one h hh] at he
    exact negativeIdentity_ne_one hn h2 (by simpa using he)

theorem rankSignRepresentative_not_central (hn : 0<n) (h2 : (2:F) ≠ 0)
    (r : ℕ) (hr : 0<r) (hrn : r<n) :
    (rankSignRepresentative r : Sp n F) ∉ Subgroup.center (Sp n F) := by
  intro hc
  have hd := rankSignRepresentative_minusDimension (F := F) r (by omega : r≤n) h2
  rcases (center_iff_eq_one_or_negativeIdentity hn _).mp hc with he|he
  · rw [he,minusDimension_one h2] at hd
    omega
  · have hm := minusDimension_neg_add (1 : Sp n F) (one_pow 2) h2
    rw [mul_one,minusDimension_one h2] at hm
    rw [he] at hd
    omega

def projectiveInvolutionRepresentative : Option (Fin (n/2)) → Sp n F
  | none => complexRepresentative
  | some i => rankSignRepresentative (i.val+1)

theorem projectiveInvolutionRepresentative_order (hn : 0<n) (h2 : (2:F) ≠ 0)
    (i : Option (Fin (n/2))) : orderOf (projection (projectiveInvolutionRepresentative (F := F) i))=2 := by
  rw [projection_order_two_iff hn]
  have hc : projectiveInvolutionRepresentative (F := F) i ∉ Subgroup.center (Sp n F) := by
    cases i with
    | none => exact complexRepresentative_not_central hn
    | some i => exact rankSignRepresentative_not_central hn h2 (i.val+1) (by omega) (by omega)
  have hh := (not_congr (center_iff_eq_one_or_negativeIdentity hn _)).mp hc
  simp only [not_or] at hh
  refine ⟨?_,hh⟩
  cases i with
  | none => exact Or.inr complexRepresentative_square
  | some i => exact Or.inl (rankSignRepresentative_square _)

theorem projectiveInvolutionRepresentative_injective (hn : 0<n) (h2 : (2:F) ≠ 0)
    (i j : Option (Fin (n/2)))
    (hc : IsConj (projection (projectiveInvolutionRepresentative (F := F) i))
      (projection (projectiveInvolutionRepresentative (F := F) j))) : i=j := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim (projection_lift_types_not_isConj hn h2 _ _
        complexRepresentative_square (rankSignRepresentative_square _) hc)
  | some i =>
    cases j with
    | none => exact False.elim (projection_lift_types_not_isConj hn h2 _ _
        complexRepresentative_square (rankSignRepresentative_square _) hc.symm)
    | some j =>
      have hd := (projection_square_one_isConj_iff hn _ _
        (rankSignRepresentative_square (i.val+1)) (rankSignRepresentative_square (j.val+1)) h2).mp hc
      rw [rankSignRepresentative_minusDimension _ (by omega) h2,
        rankSignRepresentative_minusDimension _ (by omega) h2] at hd
      have he : i.val=j.val := by omega
      exact congrArg some (Fin.ext he)

theorem projectiveInvolutionRepresentative_exhaustive [Finite F] (hn : 0<n) (h2 : (2:F) ≠ 0)
    (g : PSp n F) (hg : orderOf g=2) :
    ∃i : Option (Fin (n/2)), IsConj g (projection (projectiveInvolutionRepresentative (F := F) i)) := by
  obtain ⟨a,rfl⟩ := projection_surjective g
  obtain ⟨ha,han,haz⟩ := (projection_order_two_iff hn a).mp hg
  rcases ha with ha|ha
  · have hc : a ∉ Subgroup.center (Sp n F) := by
      rw [center_iff_eq_one_or_negativeIdentity hn]
      exact not_or.mpr ⟨han,haz⟩
    obtain ⟨hp,hu⟩ := square_one_minusDimension_bounds a ha h2 hc
    obtain ⟨r,hr⟩ := square_one_minusDimension_even a ha h2
    let s := min r (n-r)
    have hs : 0<s ∧ s≤n/2 := by dsimp [s]; omega
    refine ⟨some ⟨s-1,by omega⟩,?_⟩
    change IsConj (projection a) (projection (rankSignRepresentative (s-1+1)))
    rw [projection_square_one_isConj_iff hn _ _ ha (rankSignRepresentative_square _) h2,
      rankSignRepresentative_minusDimension _ (by omega) h2]
    dsimp [s]
    omega
  · refine ⟨none,?_⟩
    exact projection.map_isConj (square_negativeIdentity_isConj a complexRepresentative ha
      complexRepresentative_square h2)

def projectiveInvolutionClass (hn : 0<n) (h2 : (2:F) ≠ 0)
    (i : Option (Fin (n/2))) : Atlas.InvolutionClasses (PSp n F) :=
  ⟨ConjClasses.mk (projection (projectiveInvolutionRepresentative i)),
    ⟨_,rfl,projectiveInvolutionRepresentative_order hn h2 i⟩⟩

theorem projectiveInvolutionClass_bijective [Finite F] (hn : 0<n) (h2 : (2:F) ≠ 0) :
    Function.Bijective (projectiveInvolutionClass (n := n) hn h2) := by
  constructor
  · intro i j he
    apply projectiveInvolutionRepresentative_injective hn h2
    exact ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val he)
  · intro c
    obtain ⟨g,hg,ho⟩ := c.prop
    obtain ⟨i,hi⟩ := projectiveInvolutionRepresentative_exhaustive hn h2 g ho
    refine ⟨i,Subtype.ext ?_⟩
    exact (ConjClasses.mk_eq_mk_iff_isConj.mpr hi).symm.trans hg

/-- Exact conjugacy-class count for actual projective symplectic involutions. -/
theorem k2_psp [Finite F] (hn : 0<n) (h2 : (2:F) ≠ 0) : Atlas.k2 (PSp n F)=n/2+1 := by
  unfold Atlas.k2
  have he := Equiv.ofBijective (projectiveInvolutionClass (n := n) hn h2)
    (projectiveInvolutionClass_bijective hn h2)
  rw [←Nat.card_congr he]
  simp

end Atlas.Symplectic
