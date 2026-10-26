import Atlas.Algebra.Albert.CrossProduct
import Mathlib.Tactic

/-! Six actual middle-coordinate cross operators on the lower eight-dimensional
space. Their common centralizer is scalar, by a vacuum and creation argument;
no characteristic restriction or abstract Clifford algebra theorem is used. -/
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [CommRing F]

abbrev LowerSpinSpace (F : Type*) := Fin 8 → F

def lowerSpinEmbed (v : LowerSpinSpace F) : Carrier F :=
  (0, ![![0,0,0,0,v 0,v 1,v 2,v 3],
    ![0,0,0,v 4,0,v 5,v 6,v 7],0])

def middleSpinEmbed (a b : F) (z : Fin 6 → F) : Carrier F :=
  (![a,b,0], ![0,0,![0,z 0,z 1,z 2,z 3,z 4,z 5,0]])

def lowerSpinAction (a b : F) (z : Fin 6 → F) (v : LowerSpinSpace F) : LowerSpinSpace F :=
  ![-a*v 0-z 0*v 6-z 1*v 5+z 2*v 4,
    -a*v 1+z 0*v 7-z 3*v 5-z 4*v 4,
    -a*v 2-z 1*v 7-z 3*v 6-z 5*v 4,
    -a*v 3-z 2*v 7+z 4*v 6-z 5*v 5,
    -b*v 4-z 0*v 2-z 1*v 1+z 3*v 0,
    -b*v 5-z 0*v 3-z 2*v 1-z 4*v 0,
    -b*v 6+z 1*v 3-z 2*v 2-z 5*v 0,
    -b*v 7-z 3*v 3-z 4*v 2+z 5*v 1]

set_option maxHeartbeats 1500000 in
theorem middle_cross_lowerSpin (a b : F) (z : Fin 6 → F) (v : LowerSpinSpace F) :
    cross (middleSpinEmbed a b z) (lowerSpinEmbed v)=
      lowerSpinEmbed (lowerSpinAction a b z v) := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [cross,adjoint,middleSpinEmbed,lowerSpinEmbed,lowerSpinAction,
        SplitOctonion.norm,Matrix.vecHead,Matrix.vecTail] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cross,adjoint,middleSpinEmbed,lowerSpinEmbed,lowerSpinAction,
        SplitOctonion.mul,SplitOctonion.conjugate,SplitOctonion.trace,
        SplitOctonion.unit,Matrix.vecHead,Matrix.vecTail] <;> ring

def lowerSpinOperatorValue (i : Fin 6) (v : LowerSpinSpace F) : LowerSpinSpace F :=
  ![![-v 6,v 7,0,0,-v 2,-v 3,0,0],
    ![-v 5,0,-v 7,0,-v 1,0,v 3,0],
    ![v 4,0,0,-v 7,0,-v 1,-v 2,0],
    ![0,-v 5,-v 6,0,v 0,0,0,-v 3],
    ![0,-v 4,0,v 6,0,-v 0,0,-v 2],
    ![0,0,-v 4,-v 5,0,0,-v 0,v 1]] i

def lowerSpinOperator (i : Fin 6) : LowerSpinSpace F →ₗ[F] LowerSpinSpace F where
  toFun := lowerSpinOperatorValue i
  map_add' v w := by
    ext j; fin_cases i <;> fin_cases j <;> simp [lowerSpinOperatorValue,add_comm]
  map_smul' t v := by
    ext j; fin_cases i <;> fin_cases j <;> simp [lowerSpinOperatorValue]

theorem lowerSpinOperator_cross (i : Fin 6) (v : LowerSpinSpace F) :
    cross (middleSpinEmbed 0 0 (Pi.single i 1)) (lowerSpinEmbed v)=
      lowerSpinEmbed (lowerSpinOperator i v) := by
  rw [middle_cross_lowerSpin]
  congr 1
  ext j; fin_cases i <;> fin_cases j <;>
    simp [lowerSpinAction,lowerSpinOperator,lowerSpinOperatorValue,Pi.single_apply]

def lowerSpinVacuum : LowerSpinSpace F := Pi.single 0 1

def lowerSpinBasisWord : Fin 8 → LowerSpinSpace F :=
  ![lowerSpinVacuum,
    lowerSpinOperator 3 (lowerSpinOperator 4 lowerSpinVacuum),
    lowerSpinOperator 3 (lowerSpinOperator 5 lowerSpinVacuum),
    -lowerSpinOperator 4 (lowerSpinOperator 5 lowerSpinVacuum),
    lowerSpinOperator 3 lowerSpinVacuum,
    -lowerSpinOperator 4 lowerSpinVacuum,
    -lowerSpinOperator 5 lowerSpinVacuum,
    lowerSpinOperator 3 (lowerSpinOperator 4 (lowerSpinOperator 5 lowerSpinVacuum))]

theorem lowerSpinBasisWord_eq (i : Fin 8) :
    lowerSpinBasisWord (F:=F) i=Pi.single i 1 := by
  ext j; fin_cases i <;> fin_cases j <;>
    simp [lowerSpinBasisWord,lowerSpinVacuum,lowerSpinOperator,
      lowerSpinOperatorValue,Pi.single_apply]

theorem lowerSpinVacuum_unique (v : LowerSpinSpace F)
    (h0 : lowerSpinOperator 0 v=0) (h1 : lowerSpinOperator 1 v=0)
    (h2 : lowerSpinOperator 2 v=0) : v=v 0 • lowerSpinVacuum := by
  have h01 := congrFun h0 1
  have h04 := congrFun h0 4
  have h05 := congrFun h0 5
  have h00 := congrFun h0 0
  have h10 := congrFun h1 0
  have h14 := congrFun h1 4
  have h20 := congrFun h2 0
  simp [lowerSpinOperator,lowerSpinOperatorValue] at h01 h04 h05 h00 h10 h14 h20
  ext j; fin_cases j <;>
    simp [lowerSpinVacuum,Pi.single_apply,h01,h04,h05,h00,h10,h14,h20]

theorem lowerSpinOperator_centralizer (T : LowerSpinSpace F →ₗ[F] LowerSpinSpace F)
    (hc : ∀ (i : Fin 6) v, T (lowerSpinOperator i v)=lowerSpinOperator i (T v)) :
    ∃ c : F, ∀ v, T v=c • v := by
  let c := T lowerSpinVacuum 0
  have hv (i : Fin 3) : lowerSpinOperator (F:=F) i.castSucc.castSucc.castSucc lowerSpinVacuum=0 := by
    ext j; fin_cases i <;> fin_cases j <;>
      simp [lowerSpinOperator,lowerSpinOperatorValue,lowerSpinVacuum,Pi.single_apply]
  have ht (i : Fin 3) : lowerSpinOperator i.castSucc.castSucc.castSucc (T lowerSpinVacuum)=0 := by
    rw [←hc,hv,map_zero]
  have h0 : T lowerSpinVacuum=c • lowerSpinVacuum :=
    lowerSpinVacuum_unique _ (ht 0) (ht 1) (ht 2)
  have hw (i : Fin 8) : T (lowerSpinBasisWord i)=c • lowerSpinBasisWord i := by
    fin_cases i <;>
      simp [lowerSpinBasisWord,map_neg,hc,h0,map_smul,smul_neg]
  have hb (i : Fin 8) : T (Pi.single i 1)=c • Pi.single i 1 := by
    simpa only [lowerSpinBasisWord_eq] using hw i
  have he : T=c • LinearMap.id := by
    apply (Pi.basisFun F (Fin 8)).ext
    intro i
    simpa using hb i
  exact ⟨c,fun v => by rw [he]; rfl⟩
/-- The residual interchange of the two diagonal middle coordinates cannot be
intertwined by an invertible lower-spin map fixing the six other middle entries. -/
theorem lowerSpinOperator_no_diagonal_swap [Nontrivial F]
    (T : LowerSpinSpace F →ₗ[F] LowerSpinSpace F) (hi : Function.Injective T)
    (hc : ∀ (i : Fin 6) v, T (lowerSpinOperator i v)=lowerSpinOperator i (T v))
    (hs : ∀ v, T (lowerSpinAction 1 0 0 v)=lowerSpinAction 0 1 0 (T v)) : False := by
  obtain ⟨c,hc⟩ := lowerSpinOperator_centralizer T hc
  have h := congrFun (hs lowerSpinVacuum) 0
  simp [hc,lowerSpinAction,lowerSpinVacuum,Pi.single_apply] at h
  have hc0 : c=0 := by simpa using h
  have hz : T lowerSpinVacuum=T 0 := by simp [hc,hc0]
  have he := congrFun (hi hz) 0
  simpa [lowerSpinVacuum,Pi.single_apply] using he

end Atlas.F4

