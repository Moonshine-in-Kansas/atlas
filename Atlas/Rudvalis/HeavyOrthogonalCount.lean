import Atlas.Rudvalis.HeavyAvoidingCount
import Atlas.Rudvalis.FourOrthogonalCount

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

abbrev HeavyAvoidingResidues (p : Point) (x : E) :=
  {d : HeavyMinimumResidues // d.val.val (p,x)=0 ∧ d.val.val (p,x+p.val)=0}

noncomputable def heavyAvoidingResidueEquiv (p : Point) (x : E) :
    (Σ c : Point,HeavyAvoidingPair c p x) ≃ HeavyAvoidingResidues p x :=
  (show (Σ c : Point,HeavyAvoidingPair c p x) ≃
    {a : QuadraticMinimumParameters // fixedHeavyWord a.1 a.2 (p,x)=0 ∧
      fixedHeavyWord a.1 a.2 (p,x+p.val)=0} from
    {toFun := fun a => ⟨⟨a.1,a.2.val⟩,a.2.prop⟩
     invFun := fun a => ⟨a.val.1,⟨a.val.2,a.prop⟩⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}).trans
    (Equiv.subtypeEquiv quadraticMinimumWordEquiv (fun _ => Iff.rfl))

theorem heavyAvoidingResidues_card (p : Point) (x : E) : Nat.card (HeavyAvoidingResidues p x)=384 := by
  classical
  rw [←Nat.card_congr (heavyAvoidingResidueEquiv p x),Nat.card_sigma]
  simp_rw [heavyAvoidingPair_card]
  have he : (Finset.univ.filter (fun c : Point => p≠c)).card=6 := by decide +kernel +revert
  have hs : (∑c : Point,if p=c then 0 else 64)=
      ∑c ∈ Finset.univ.filter (fun c : Point => p≠c),(64 : ℕ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : p=c <;> simp [h]
  rw [hs,Finset.sum_const,he]
  rfl

abbrev HeavyOrthogonalWords (p : Point) (x : E) :=
  {w : HeavyMinimumWords // reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0}

noncomputable def heavyOrthogonalWordsEquiv (p : Point) (x : E) :
    HeavyOrthogonalWords p x ≃ Σ d : HeavyAvoidingResidues p x,minimumLift d.val.val.val :=
  (Equiv.subtypeEquiv heavyMinimumWordsEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv (fun d : HeavyMinimumResidues => minimumLift d.val.val)
      (fun d => d.val.val (p,x)=0 ∧ d.val.val (p,x+p.val)=0))

theorem heavyOrthogonalWords_card (p : Point) (x : E) : Nat.card (HeavyOrthogonalWords p x)=6144 := by
  classical
  rw [Nat.card_congr (heavyOrthogonalWordsEquiv p x),Nat.card_sigma]
  have hh (d : HeavyAvoidingResidues p x) : Nat.card (minimumLift d.val.val.val)=16 :=
    heavy_minimum_fibre_card _ d.val.prop.1 d.val.prop.2
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,heavyAvoidingResidues_card]

noncomputable def heavyWordShellEquiv : HeavyMinimumWords ≃ heavyShellPiece :=
  Equiv.ofInjective (fun w : HeavyMinimumWords => minimumWordShellLift (heavyMinimumWord w)) (by
    intro a b h
    exact Subtype.ext (congrArg (fun u : MinimumWords => u.val) (minimumWordShellLift_injective h)))

theorem heavyWord_coordinate_orthogonal_iff (w : HeavyMinimumWords) (p : Point) (x : E) :
    CrossOrthogonal (coordinateCross (p,x)) (minimalCross (minimumWordShellLift (heavyMinimumWord w))) ↔
      reduce w.val.val (p,x)=0 ∧ reduce w.val.val (p,x+p.val)=0 := by
  rw [coordinateCross,crossOrthogonal_mk]
  change HermitianOrthogonal (coordinateMinimum (p,x)) (minimumWordShellLift (heavyMinimumWord w)).val.val ↔ _
  rw [coordinate_hermitianOrthogonal_pair,minimumWordShellLift_zero_iff,minimumWordShellLift_zero_iff]
  rfl

noncomputable def heavyOrthogonalShellEquiv (p : Point) (x : E) :
    HeavyOrthogonalWords p x ≃ RestrictedShellPiece heavyShellPiece (CrossOrthogonal (coordinateCross (p,x))) :=
  Equiv.subtypeEquiv heavyWordShellEquiv (fun w => (heavyWord_coordinate_orthogonal_iff w p x).symm)

theorem heavyOrthogonalShell_card (p : Point) (x : E) :
    Nat.card (RestrictedShellPiece heavyShellPiece (CrossOrthogonal (coordinateCross (p,x))))=6144 := by
  rw [←Nat.card_congr (heavyOrthogonalShellEquiv p x),heavyOrthogonalWords_card]

theorem heavyOrthogonalCrosses_card (p : Point) (x : E) :
    Nat.card {c : HeavyCrosses //
      CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap heavyShellPiece c)}=1536 := by
  have h := restricted_shell_cross_card heavyShellPiece (CrossOrthogonal (coordinateCross (p,x)))
  rw [heavyOrthogonalShell_card] at h
  change 6144=Nat.card {c : HeavyCrosses // CrossOrthogonal (coordinateCross (p,x)) (shellPieceCrossMap heavyShellPiece c)}*4 at h
  omega

end Atlas.Rudvalis
