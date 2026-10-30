import Atlas.Sporadic.Janko1.WhitelawInvarianceReduction

/-!
Uncompiled source-only finite-search interface. All search parameters are Fin
types, and all deciders below are constructive. Executable coordinate views
are definitionally equal to the existing formulas; no carrier is replaced.
The square guard only rejects candidates. The final test retains all seven
UNSQUARED sign equations. This module contains no classical/noncomputable block.
-/
namespace Atlas.Janko1

def whitelawSearchSign : Fin 8 → SignParameters :=
  ![0, ![0,0,1], ![0,1,0], ![0,1,1],
    ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]]

set_option maxRecDepth 8192 in
theorem whitelawSearchSign_surjective : Function.Surjective whitelawSearchSign := by
  decide

/-- The ten nonzero elements of the actual field, with no Units/classical enumeration. -/
def whitelawSearchScalar (c : Fin 10) : Field := (c.val + 1 : ℕ)

theorem whitelawSearchScalar_ne_zero : ∀ c : Fin 10, whitelawSearchScalar c ≠ 0 := by
  decide

theorem whitelawSearchScalar_surjective :
    ∀ x : Field, x ≠ 0 → ∃ c : Fin 10, whitelawSearchScalar c = x := by
  decide

/-- Executable source-identical view of the existing ten seeds. -/
def whitelawSearchSeed : Fin 10 → (Fin 7 → Field) :=
  ![![0, 0, 1, 0, -2, -4, 1],
    ![0, 1, -3, -2, -2, 0, 2],
    ![0, 1, -1, -1, -1, -2, 5],
    ![0, 1, -1, -3, -3, 2, 3],
    ![0, 1, -1, -3, -5, 2, -2],
    ![0, 1, -2, -1, -3, -2, -5],
    ![0, 1, -3, -5, -2, -1, -2],
    ![1, -1, -3, -2, 2, 3, 4],
    ![1, -1, -4, -2, -4, -1, -4],
    ![1, -1, -2, -5, 2, 4, 2]]

theorem whitelawSearchSeed_eq (r : Fin 10) :
    whitelawSearchSeed r = whitelawSeed r := rfl

def whitelawSearchImage (r : Fin 10) (a : Fin 8) : Fin 7 → Field :=
  Matrix.mulVec (imaginaryGeneratorMatrix 3)
    (fun k => signCharacter (whitelawSearchSign a) k * whitelawSearchSeed r k)

theorem whitelawSearchImage_eq (r : Fin 10) (a : Fin 8) :
    whitelawSearchImage r a = sCoordinateAction (signedWhitelawSeed r (whitelawSearchSign a)) :=
  rfl

/-- The existing P^i Q^j coordinate formula, using only executable lambdas. -/
def whitelawSearchUnsigned (s : Fin 10) (i : Fin 7) (j : Fin 3) : Fin 7 → Field :=
  (fun v : Fin 7 → Field => fun k => v (k - 1))^[i.val]
    ((fun v : Fin 7 → Field => fun k => v (4 * k))^[j.val] (whitelawSearchSeed s))

theorem whitelawSearchUnsigned_eq (s : Fin 10) (i : Fin 7) (j : Fin 3) :
    whitelawSearchUnsigned s i j =
      coordinateShift^[i.val] (coordinateDouble^[j.val] (whitelawSeed s)) := rfl

/-- Only after the square guard succeeds are the eight output signs inspected. -/
def WhitelawSSearchMatch (v : Fin 7 → Field) (s : Fin 10)
    (i : Fin 7) (j : Fin 3) (c : Fin 10) : Prop :=
  (∀ k : Fin 7, (whitelawSearchScalar c * v k) ^ 2 =
    (whitelawSearchUnsigned s i j k) ^ 2) ∧
  ∃ b : Fin 8, ∀ k : Fin 7,
    whitelawSearchScalar c * v k =
      signCharacter (whitelawSearchSign b) k * whitelawSearchUnsigned s i j k

instance whitelawSSearchMatchDecidable (v : Fin 7 → Field) (s : Fin 10)
    (i : Fin 7) (j : Fin 3) (c : Fin 10) : Decidable (WhitelawSSearchMatch v s i j c) := by
  unfold WhitelawSSearchMatch
  infer_instance

/-- The guard follows from the unsquared test; it introduces no mathematical premise. -/
theorem whitelawSSearchMatch_iff (v : Fin 7 → Field) (s : Fin 10)
    (i : Fin 7) (j : Fin 3) (c : Fin 10) :
    WhitelawSSearchMatch v s i j c ↔
      ∃ b : Fin 8, ∀ k : Fin 7,
        whitelawSearchScalar c * v k =
          signCharacter (whitelawSearchSign b) k * whitelawSearchUnsigned s i j k := by
  constructor
  · exact fun h => h.2
  · rintro ⟨b, hb⟩
    refine ⟨?_, b, hb⟩
    intro k
    have hs : signCharacter (whitelawSearchSign b) k ^ 2 = 1 := by
      simpa only [pow_two] using signCharacter_square (whitelawSearchSign b) k
    calc
      (whitelawSearchScalar c * v k) ^ 2 =
          (signCharacter (whitelawSearchSign b) k * whitelawSearchUnsigned s i j k) ^ 2 :=
        congrArg (fun z : Field => z ^ 2) (hb k)
      _ = (whitelawSearchUnsigned s i j k) ^ 2 := by rw [mul_pow, hs, one_mul]

/-- At most 10*7*3*10 outer candidates, then at most eight signs after the guard. -/
def WhitelawSSearch (r : Fin 10) (a : Fin 8) : Prop :=
  ∃ (s : Fin 10) (i : Fin 7) (j : Fin 3) (c : Fin 10),
    WhitelawSSearchMatch (whitelawSearchImage r a) s i j c

instance whitelawSSearchDecidable (r : Fin 10) (a : Fin 8) :
    Decidable (WhitelawSSearch r a) := by
  unfold WhitelawSSearch
  infer_instance

/-- Every successful local finite search gives the original actual-coordinate row. -/
theorem whitelawSSearch_sound (r : Fin 10) (a : Fin 8)
    (h : WhitelawSSearch r a) : WhitelawSRow r (whitelawSearchSign a) := by
  obtain ⟨s, i, j, c, _, b, hb⟩ := h
  refine ⟨s, (whitelawSearchSign b, i, j), whitelawSearchScalar c, ?_⟩
  funext k
  exact hb k

end Atlas.Janko1
