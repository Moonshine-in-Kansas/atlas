import Atlas.Fischer.CountingTypeBTable

namespace Atlas.Fischer
open Atlas.Codes

/-- A Type C target has one triple column and five singleton columns. -/
def countingTypeCColumnProfile (j : Fin 6) : CountingColumnVector :=
  fun i => if i=j then 3 else 1

def countingTypeCTargetWeight (r : Fin 14) (j : Fin 6) (h : CountingColumnVector) : Option ℤ :=
  countingColumnWeight (countingTableEpsilon r) countingTableD (countingTableE r) (countingTableF r)
    (countingTableProfile r) (countingTypeCColumnProfile j) h

/-- Joint columns for a normalized Type C source and a target with zero-set Z. -/
def countingSingletonJointColumns (r : Fin 14) (j : Fin 6) (Z : Finset (Fin 6)) : CountingColumnVector :=
  fun i => if countingTableProfile r i=3 then
    (if i=j then (if i ∈ Z then 3 else 2) else (if i ∈ Z then 0 else 1))
    else (if i=j then (if i ∈ Z then 0 else 1) else (if i ∈ Z then 1 else 0))

/-- Sum over all source-code words, using proved trace fibers or zero-set fibers. -/
def countingTypeCWordHistogram (r : Fin 14) (j k : Fin 6) : ℕ :=
  if countingTableType r=0 then
    64*countingWeightHistogram (countingTypeCTargetWeight r j
      (fun i => if countingTableProfile r i=4 then countingTypeCColumnProfile j i else 0)) k
  else if countingTableType r=1 then
    ∑ m : Fin 5 → Bit, if countingTableMaskSupported (countingTableBSourceSupport r) m then
      8*countingWeightHistogram (countingTypeCTargetWeight r j
        (fun i => if i ∈ countingTableBSourceSupport r then
          (if i=j then 1+countingTableMask m i else 1-countingTableMask m i) else 0)) k else 0
  else
    countingWeightHistogram (countingTypeCTargetWeight r j
      (countingSingletonJointColumns r j Finset.univ)) k +
    (∑ Z ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
      3*countingWeightHistogram (countingTypeCTargetWeight r j
        (countingSingletonJointColumns r j Z)) k) +
    18*countingWeightHistogram (countingTypeCTargetWeight r j
      (countingSingletonJointColumns r j ∅)) k

def countingTypeCTargetHistogram (r : Fin 14) : CountingSignedHistogram :=
  fun k => ∑ j : Fin 6, countingTypeCWordHistogram r j k

/-- Every displayed Type C target subtotal, retaining signs and multiplicities. -/
def countingTypeCExpectedHistogram (r : Fin 14) : CountingSignedHistogram :=
  ![![0,0,0,64,0,0],![0,0,0,0,0,0],![0,0,0,0,0,0],
    ![0,0,0,0,16,0],![0,0,16,16,0,0],![0,0,0,16,0,0],![0,0,9,19,3,0],
    ![0,0,0,0,0,0],![0,0,0,64,0,0],![0,0,0,32,0,0],
    ![0,0,0,0,0,0],![0,0,0,0,0,0],![0,0,0,16,0,0],![0,0,0,20,0,0]] r

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
-- Each row uses six distinguished columns and only the trace/zero-set fibers already proved.
/-- All fourteen Type C target rows; actual-octad interpretation is a separate bridge. -/
theorem countingTypeCTargetHistogram_all :
    ∀ r : Fin 14, countingTypeCTargetHistogram r=countingTypeCExpectedHistogram r := by
  intro r
  fin_cases r <;> decide

end Atlas.Fischer
