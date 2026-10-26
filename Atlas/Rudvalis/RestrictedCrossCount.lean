import Atlas.Rudvalis.LatticeCrossPieces

/-! A Gaussian-invariant cross condition removes exactly four shell phases. -/
namespace Atlas.Rudvalis

abbrev RestrictedShellPiece (s : SubMulAction codeGroup MinimalShell) (P : MinimalCross→Prop) :=
  {v : s // P (minimalCross v.val)}

noncomputable instance restrictedShellPieceAction (s : SubMulAction codeGroup MinimalShell)
    (P : MinimalCross→Prop) : MulAction GaussianUnits (RestrictedShellPiece s P) where
  smul u v := ⟨u • v.val,by
    have he : minimalCross (u • v.val.val)=minimalCross v.val.val :=
      (minimalCross_eq_iff _ _).mpr ⟨u,rfl⟩
    change P (minimalCross (u • v.val.val))
    rw [he]
    exact v.prop⟩
  one_smul v := Subtype.ext (one_smul _ _)
  mul_smul u t v := Subtype.ext (mul_smul _ _ _)

noncomputable def restrictedCrossEquiv (s : SubMulAction codeGroup MinimalShell) (P : MinimalCross→Prop) :
    Quotient (MulAction.orbitRel GaussianUnits (RestrictedShellPiece s P)) ≃
      {c : ShellPieceCross s // P (shellPieceCrossMap s c)} :=
  Equiv.ofBijective (Quotient.lift (fun v : RestrictedShellPiece s P =>
    (⟨Quotient.mk _ v.val,v.prop⟩ : {c : ShellPieceCross s // P (shellPieceCrossMap s c)})) (by
      intro v w h
      apply Subtype.ext
      apply Quotient.sound
      obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp h
      exact MulAction.mem_orbit_iff.mpr ⟨u,congrArg Subtype.val hu⟩)) (by
    constructor
    · intro a b
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      intro h
      apply Quotient.sound
      have hh := congrArg Subtype.val h
      obtain ⟨u,hu⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hh)
      exact MulAction.mem_orbit_iff.mpr ⟨u,Subtype.ext hu⟩
    · rintro ⟨c,hc⟩
      induction c using Quotient.inductionOn with
      | h v => exact ⟨Quotient.mk _ ⟨v,hc⟩,rfl⟩)

theorem restricted_shell_cross_card (s : SubMulAction codeGroup MinimalShell) (P : MinimalCross→Prop) :
    Nat.card (RestrictedShellPiece s P)=Nat.card {c : ShellPieceCross s // P (shellPieceCrossMap s c)}*4 := by
  have hf (u : GaussianUnits) (v : RestrictedShellPiece s P) (h : u • v=v) : u=1 :=
    gaussianUnits_free u v.val.val (congrArg (fun w : RestrictedShellPiece s P => w.val.val) h)
  have hh := Atlas.free_action_card GaussianUnits (RestrictedShellPiece s P) hf
  rw [gaussianUnits_card,Nat.card_congr (restrictedCrossEquiv s P)] at hh
  exact hh

end Atlas.Rudvalis
