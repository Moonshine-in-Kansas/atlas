import Atlas.Rudvalis.QuaternaryMinimumShape
import Atlas.Rudvalis.CodeGroup
import Atlas.Rudvalis.BinaryDoubleTransitivity

/-! The explicit two-row pairing obstruction from Version 33. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

/-- The ten translates in the manuscript's witness `w_*`. -/
def twoRowWitnessIndex (i : Fin 10) : SeedOrbitIndex :=
  ![(0,0,0,0),(0,0,1,0),(0,0,2,0),(1,0,1,0),(4,0,0,0),(6,0,0,0),
    (0,0,0,1),(0,0,1,1),(1,0,0,1),(1,0,1,1)] i

noncomputable def twoRowWitness : QuaternaryWord := ∑ i : Fin 10,quaternarySeed (twoRowWitnessIndex i)

theorem twoRowWitness_mem : twoRowWitness∈quaternaryCode :=
  Submodule.sum_mem _ (fun _ _ => quaternaryCode_seed _)

def twoRowWitnessTable (r : Fin 2) (k : Fin 8) : ZMod 4 :=
  ![![2,2,0,2,0,2,2,0],![2,2,2,2,2,0,2,0]] r k

set_option maxHeartbeats 2000000 in
theorem twoRowWitness_coordinates (r : Fin 2) (k : Fin 8) :
    twoRowWitness (seedCoordinateEquiv (r.castLE (by decide),k))=twoRowWitnessTable r k := by
  simp only [twoRowWitness,Finset.sum_apply,quaternarySeed_coordinates]
  decide +kernel +revert

theorem twoRowWitness_pairing (w : QuaternaryWord)
    (hr : reduce w=rowWord (rowLabel 0)+rowWord (rowLabel 1))
    (hn : ∀ z,w z≠2) : quaternaryForm twoRowWitness w=2 := by
  have hs (r : Fin 7) (k : Fin 8) :
      reduceScalar (w (seedCoordinateEquiv (r,k)))=if r=0 ∨ r=1 then 1 else 0 := by
    have he := congrFun hr (seedCoordinateEquiv (r,k))
    change reduceScalar (w (seedCoordinateEquiv (r,k)))=_ at he
    rw [he]
    change (if rowLabel r=rowLabel 0 then (1 : Bit) else 0)+
      (if rowLabel r=rowLabel 1 then 1 else 0)=_
    simp only [rowLabel_bijective.injective.eq_iff]
    fin_cases r <;> decide
  have hodd : ∀ a b : ZMod 4,(b=0 ∨ b=2) → reduceScalar a=1 → b*a=b := by decide +kernel
  have heven : ∀ a : ZMod 4,a≠2 → reduceScalar a=0 → a=0 := by decide +kernel
  have hp (r : Fin 7) (k : Fin 8) :
      twoRowWitness (seedCoordinateEquiv (r,k))*w (seedCoordinateEquiv (r,k))=
      if r=0 then twoRowWitnessTable 0 k else if r=1 then twoRowWitnessTable 1 k else 0 := by
    by_cases h0 : r=0
    · subst r
      rw [show (0 : Fin 7)=(0 : Fin 2).castLE (by decide) from rfl,twoRowWitness_coordinates]
      simpa using hodd _ _ (by fin_cases k <;> decide) (by simpa using hs 0 k)
    by_cases h1 : r=1
    · subst r
      rw [show (1 : Fin 7)=(1 : Fin 2).castLE (by decide) from rfl,twoRowWitness_coordinates]
      simpa using hodd _ _ (by fin_cases k <;> decide) (by simpa using hs 1 k)
    · have hz := heven _ (hn _) (by simpa [h0,h1] using hs r k)
      simp [hz,h0,h1]
  change (∑ z : Coordinate,twoRowWitness z*w z)=2
  rw [← Equiv.sum_comp seedCoordinateEquiv,Fintype.sum_prod_type]
  simp_rw [hp]
  decide +kernel

theorem quaternary_no_twos_not_first_two_rows (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hn : ∀ z,w z≠2) : reduce w≠rowWord (rowLabel 0)+rowWord (rowLabel 1) := by
  intro hr
  have hp := twoRowWitness_pairing w hr hn
  have hz := quaternaryCode_self_orthogonal hw twoRowWitness twoRowWitness_mem
  rw [hp] at hz
  exact (by decide : (2 : ZMod 4)≠0) hz

theorem quaternary_minimum_not_first_two_rows (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : euclideanWeight w=16) :
    reduce w≠rowWord (rowLabel 0)+rowWord (rowLabel 1) :=
  quaternary_no_twos_not_first_two_rows w hw (quaternary_minimum_no_twos w hw hweight)

/-- Any actual signed code symmetry transports the explicit obstruction. -/
theorem quaternary_minimum_not_transported_two_rows (g : codeGroup) (w : QuaternaryWord)
    (hw : w∈quaternaryCode) (hweight : euclideanWeight w=16) (d : BinaryWord)
    (hd : d ∘ g.val.right.symm=rowWord (rowLabel 0)+rowWord (rowLabel 1)) : reduce w≠d := by
  intro hr
  have hn := quaternary_minimum_no_twos w hw hweight
  have hs : ∀ b : Bit,∀ a : ZMod 4,a≠2 → signedScalar b a≠2 := by decide +kernel
  apply quaternary_no_twos_not_first_two_rows (monomialHom g.val w) ((g.prop w).mp hw)
    (fun z => hs _ _ (hn _))
  change reduce (monomialAction g.val w)=_
  rw [monomialAction_reduce,hr,hd]

/-- Exclusion whenever an actual signed symmetry sends the two rows to the displayed pair. -/
theorem quaternary_minimum_not_two_rows_of_transporter (g : codeGroup) (p q : Point)
    (hp : binaryBlockHom (codePermutationHom g) p=rowLabel 0)
    (hq : binaryBlockHom (codePermutationHom g) q=rowLabel 1)
    (w : QuaternaryWord) (hw : w∈quaternaryCode) (hweight : euclideanWeight w=16) :
    reduce w≠rowWord p+rowWord q := by
  apply quaternary_minimum_not_transported_two_rows g w hw hweight
  have hp' : rowWord p ∘ g.val.right.symm=rowWord (rowLabel 0) :=
    (binaryRowImage_spec (codePermutationHom g) p).trans (congrArg rowWord hp)
  have hq' : rowWord q ∘ g.val.right.symm=rowWord (rowLabel 1) :=
    (binaryRowImage_spec (codePermutationHom g) q).trans (congrArg rowWord hq)
  exact congrArg₂ (fun f h : BinaryWord => f+h) hp' hq'

/-- Surjectivity of the signed projection excludes all two-full-row minimum supports. -/
theorem quaternary_minimum_not_two_rows_of_surjective
    (hsurj : Function.Surjective codePermutationHom) (p q : Point) (hpq : p≠q)
    (w : QuaternaryWord) (hw : w∈quaternaryCode) (hweight : euclideanWeight w=16) :
    reduce w≠rowWord p+rowWord q := by
  obtain ⟨g,hp,hq⟩ := binaryBlockHom_doubly_transitive p q (rowLabel 0) (rowLabel 1) hpq
    (by decide)
  obtain ⟨h,rfl⟩ := hsurj g
  exact quaternary_minimum_not_two_rows_of_transporter h p q hp hq w hw hweight

end Atlas.Rudvalis
