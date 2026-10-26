import Atlas.Rudvalis.QuadraticWords

/-! The rank-one matrices underlying the four-balanced-block stratum. -/
namespace Atlas.Rudvalis

theorem outerMatrix_nonzero (b u : E) (hb : b ≠ 0) (hu : u ≠ 0) : outerMatrix b u ≠ 0 := by
  obtain ⟨i,hi⟩ := point_has_one (⟨b,hb⟩ : Point)
  obtain ⟨j,hj⟩ := point_has_one (⟨u,hu⟩ : Point)
  change b i = 1 at hi
  change u j = 1 at hj
  intro h
  have he := congrFun (congrFun h i) j
  simp [outerMatrix,hi,hj] at he

theorem outerMatrix_nonzero_injective :
    Function.Injective (fun a : Point × Point => outerMatrix a.1.val a.2.val) := by
  rintro ⟨b,u⟩ ⟨d,v⟩ h
  obtain ⟨i,hi⟩ := point_has_one b
  have hr (j : Fin 3) : u.val j = d.val i * v.val j := by
    have he := congrFun (congrFun h i) j
    simpa [outerMatrix,hi] using he
  have hd : d.val i = 1 := by
    rcases Atlas.Codes.bit_cases (d.val i) with hd | hd
    · apply False.elim
      apply u.prop
      funext j
      simpa [hd] using hr j
    · exact hd
  have huv : u = v := by
    apply Subtype.ext
    funext j
    simpa [hd] using hr j
  subst v
  obtain ⟨j,hj⟩ := point_has_one u
  have hbd : b = d := by
    apply Subtype.ext
    funext k
    have he := congrFun (congrFun h k) j
    simpa [outerMatrix,hj] using he
  subst d
  rfl

def isBinaryRankOne (M : BinaryMatrix) : Prop :=
  ∃ b u : Point, M = outerMatrix b.val u.val

noncomputable def binaryRankOneEquiv : (Point × Point) ≃ {M : BinaryMatrix // isBinaryRankOne M} :=
  Equiv.ofBijective (fun a => ⟨outerMatrix a.1.val a.2.val,⟨a.1,a.2,rfl⟩⟩) (by
    constructor
    · intro a b h
      exact outerMatrix_nonzero_injective (congrArg Subtype.val h)
    · rintro ⟨M,b,u,h⟩
      exact ⟨(b,u),Subtype.ext h.symm⟩)

theorem binaryRankOne_card : Nat.card {M : BinaryMatrix // isBinaryRankOne M} = 49 := by
  rw [← Nat.card_congr binaryRankOneEquiv]
  simp [Nat.card_prod,Nat.card_eq_fintype_card]

end Atlas.Rudvalis
