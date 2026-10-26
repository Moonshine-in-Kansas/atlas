import Atlas.LinearGroups.SuzukiFamily.ExactStabilizer
import Atlas.LinearGroups.SuzukiFamily.RootSolvable
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! The full point stabilizer, with unique root and torus parameters. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def infinityOvoid (m : ℕ) : pointSet (F := F) m := ⟨infinityPoint,⟨none,rfl⟩⟩

def borel (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) : Subgroup (Group F m) := by
  letI := pointAction m hcard
  exact MulAction.stabilizer (Group F m) (infinityOvoid (F := F) m)

theorem mem_borel (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (g : Group F m) :
    g ∈ borel m hcard ↔ pointLeft g.val infinityPoint=infinityPoint := by
  change (Subtype.mk (pointLeft g.val infinityPoint) _ : pointSet m)=infinityOvoid m ↔ _
  exact Subtype.ext_iff

def shortInBorel (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) (t : Fˣ) :
    borel m hcard := ⟨⟨shortForm m a b t,shortForm_mem m a b t⟩,
      (mem_borel m hcard _).mpr (shortForm_infinity m a b t)⟩

theorem shortInBorel_bijective (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Function.Bijective (fun p : F × F × Fˣ => shortInBorel m hcard p.1 p.2.1 p.2.2) := by
  constructor
  · intro p q he
    exact shortForm_injective m (congrArg (fun g : borel m hcard => g.val.val) he)
  · intro g
    obtain ⟨a,b,t,he⟩ := (fixes_infinity_iff_short m hcard g.val.val g.val.property).mp
      ((mem_borel m hcard g.val).mp g.property)
    exact ⟨(a,b,t),Subtype.ext (Subtype.ext he.symm)⟩

def borelParameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    (F × F × Fˣ) ≃ borel m hcard :=
  Equiv.ofBijective _ (shortInBorel_bijective m hcard)

theorem shortInBorel_mul (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b c d : F) (s t : Fˣ) :
    shortInBorel m hcard a b s * shortInBorel m hcard c d t =
      shortInBorel m hcard (a+theta F m ((s⁻¹:Fˣ):F)*c)
        (b+((s⁻¹:Fˣ):F)^2*theta F m ((s⁻¹:Fˣ):F)*d+
          a*theta F m (theta F m ((s⁻¹:Fˣ):F)*c)) (s*t) := by
  apply Subtype.ext
  apply Subtype.ext
  change shortForm m a b s * shortForm m c d t=shortForm m _ _ (s*t)
  simp only [shortForm,mul_assoc]
  rw [← mul_assoc (torusElement m s),torus_root_swap m hcard]
  simp only [← mul_assoc,rootElement_mul m hcard,torusElement_mul]

theorem card_borel (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Nat.card (borel m hcard)=(Nat.card F)^2*(Nat.card F-1) := by
  rw [← Nat.card_congr (borelParameters m hcard)]
  simp only [Nat.card_prod,Nat.card_units]
  ring
end Atlas.SuzukiFamily
