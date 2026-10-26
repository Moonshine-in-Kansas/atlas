import Atlas.GroupTheory.PrimitivePointMoves

/-! Primitivity from finite chains of genuine point-stabilizer moves.
The escape hypothesis is a concrete inductive certificate and does not quantify
over blocks or assume a maximal subgroup. -/
namespace Atlas.GroupTheory
open MulAction
variable {G X : Type*} [Group G] [MulAction G X]

/-- Points obtainable from two seeds by repeatedly moving a known point with an
element fixing another known point. Every derivation is finite. -/
inductive StabilizerMoveChain (G : Type*) [Group G] [MulAction G X] (a b : X) : X → Prop
  | left : StabilizerMoveChain G a b a
  | right : StabilizerMoveChain G a b b
  | move (x y : X) (hx : StabilizerMoveChain G a b x)
      (hy : StabilizerMoveChain G a b y) (g : stabilizer G x) :
      StabilizerMoveChain G a b (g • y)

def stabilizerMoveClosure (G : Type*) [Group G] [MulAction G X] (a b : X) : Set X :=
  {x | StabilizerMoveChain G a b x}

theorem stabilizerMoveChain_mem_block {a b c : X} {B : Set X}
    (hB : IsBlock G B) (ha : a∈B) (hb : b∈B) (hc : StabilizerMoveChain G a b c) : c∈B := by
  induction hc with
  | left => exact ha
  | right => exact hb
  | move x y hx hy g ihx ihy =>
      exact block_contains_stabilizer_transport hB ihx ihy ⟨g,rfl⟩

theorem stabilizerMoveClosure_subset_block {a b : X} {B : Set X}
    (hB : IsBlock G B) (ha : a∈B) (hb : b∈B) :
    stabilizerMoveClosure G a b ⊆ B :=
  fun _ hc => stabilizerMoveChain_mem_block hB ha hb hc

theorem stabilizerMoveChain_substitute {a b c u v : X}
    (ha : StabilizerMoveChain G u v a) (hb : StabilizerMoveChain G u v b)
    (hc : StabilizerMoveChain G a b c) : StabilizerMoveChain G u v c := by
  induction hc with
  | left => exact ha
  | right => exact hb
  | move x y hx hy g ihx ihy => exact .move x y ihx ihy g

theorem stabilizerMoveChain_symm {a b c : X} (hc : StabilizerMoveChain G a b c) :
    StabilizerMoveChain G b a c :=
  stabilizerMoveChain_substitute .right .left hc

variable [IsPretransitive G X]

/-- One nonrelated stabilizer orbit, common nonrelated witnesses, and explicit
finite stabilizer-move escapes force primitivity. -/
theorem primitive_of_nonrelated_orbit_and_chains (a : X) (R : X → X → Prop)
    (hSymm : Symmetric R)
    (hOrbit : ∀ x y z, ¬ R x y → ¬ R x z → ∃ g : stabilizer G x, g • y = z)
    (hBridge : ∀ x y, x ≠ y → R x y → ∃ z, ¬ R x z ∧ ¬ R y z)
    (hEscape : ∀ x y, x ≠ y → R x y →
      ∃ z, StabilizerMoveChain G x y z ∧ ¬ R x z) : IsPreprimitive G X := by
  classical
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases hs : ∀ x ∈ B, x=a
  · exact Or.inl (fun x hx y hy => (hs x hx).trans (hs y hy).symm)
  · push_neg at hs
    obtain ⟨b,hb,hba⟩ := hs
    have hn : ∃ c∈B, ¬R a c := by
      by_cases hab : R a b
      · obtain ⟨c,hc,hac⟩ := hEscape a b (Ne.symm hba) hab
        exact ⟨c,stabilizerMoveChain_mem_block hB ha hb hc,hac⟩
      · exact ⟨b,hb,hab⟩
    obtain ⟨c,hc,hac⟩ := hn
    have hAll (x : X) (hax : ¬R a x) : x∈B :=
      block_contains_stabilizer_transport hB ha hc (hOrbit a c x hac hax)
    right
    apply Set.eq_univ_of_forall
    intro r
    by_cases hra : r=a
    · simpa [hra] using ha
    by_cases har : R a r
    · obtain ⟨z,haz,hrz⟩ := hBridge a r (Ne.symm hra) har
      exact block_contains_stabilizer_transport hB (hAll z haz) ha
        (hOrbit z a r (fun h => haz (hSymm h)) (fun h => hrz (hSymm h)))
    · exact hAll r har

end Atlas.GroupTheory
