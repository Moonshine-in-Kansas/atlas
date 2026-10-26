import Atlas.LinearGroups.F4.HalfRootCentralLayer
import Atlas.LinearGroups.F4.OppositeCellTransitivity
import Atlas.LinearGroups.F4.OppositeCellFaithfulness

/-! Actual commutation of the seven central root directions with all eight
half roots, proved on the faithful opposite-cell action. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem centralSeven_lower (p : Fin 7 → F) (x : Carrier F) :
    oppositeLowerCoordinates ((centralSeven p).val x)=oppositeLowerCoordinates x := by
  change negativeSpinCoordinates (centralSevenApply p x)=negativeSpinCoordinates x
  exact centralSeven_negative p x

theorem centralSeven_middle (p : Fin 7 → F) (x : Carrier F) (hx : x.2 2 7=1) :
    centralSevenCoordinates ((centralSeven p).val x)=centralSevenCoordinates x+p :=
  centralSeven_coordinates_chart p x hx

def halfRootOpposite (i : Fin 8) (t : F) (x : OppositeCell F) : OppositeCell F :=
  ⟨(halfRoot i t).val x.val,by
    refine ⟨?_,?_,?_⟩
    · rw [stabilizer_adjoint,x.prop.1,map_zero]
    · rw [stabilizer_trace,x.prop.2.1]
    · exact (halfRoot_lower i t x.val).1.trans x.prop.2.2⟩

theorem centralSevenOpposite_halfRootOpposite (p : Fin 7 → F) (i : Fin 8) (t : F)
    (x : OppositeCell F) :
    centralSevenOpposite p (halfRootOpposite i t x)=
      halfRootOpposite i t (centralSevenOpposite p x) := by
  apply oppositeCell_coordinate_ext
  · change oppositeLowerCoordinates ((centralSeven p).val ((halfRoot i t).val x.val)) =
      oppositeLowerCoordinates ((halfRoot i t).val ((centralSeven p).val x.val))
    rw [centralSeven_lower,(halfRoot_lower i t x.val).2,
      (halfRoot_lower i t ((centralSeven p).val x.val)).2,centralSeven_lower]
    rw [centralSeven_apply,centralSeven_C7]
  · change centralSevenCoordinates ((centralSeven p).val ((halfRoot i t).val x.val)) =
      centralSevenCoordinates ((halfRoot i t).val ((centralSeven p).val x.val))
    rw [centralSeven_middle p _ ((halfRoot_lower i t x.val).1.trans x.prop.2.2),
      halfRoot_central,halfRoot_central,centralSeven_middle p x.val x.prop.2.2,centralSeven_lower]
    abel

theorem centralSeven_commute_halfRoot (p : Fin 7 → F) (i : Fin 8) (t : F) :
    Commute (centralSeven p) (halfRoot i t) := by
  change centralSeven p*halfRoot i t=halfRoot i t*centralSeven p
  apply oppositeCell_action_ext
  intro x
  exact congrArg Subtype.val (centralSevenOpposite_halfRootOpposite p i t x)

theorem centralSeven_commute_halfWordList (p : Fin 7 → F) (t : Fin 8 → F)
    (l : List (Fin 8)) : Commute (centralSeven p) (halfWordList t l) := by
  unfold halfWordList
  apply Commute.list_prod_right
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
  exact centralSeven_commute_halfRoot p i (t i)

theorem centralSeven_commute_halfWord (p : Fin 7 → F) (t : Fin 8 → F) :
    Commute (centralSeven p) (halfWord t) :=
  centralSeven_commute_halfWordList p t (List.finRange 8)

end Atlas.F4
