import Atlas.Fischer.CountingTypeATable

namespace Atlas.Fischer
open Atlas.Codes

/-- Source types A, B and C for the fourteen displayed normalized profiles. -/
def countingTableType (r : Fin 14) : Fin 3 :=
  ![0,0,0,1,1,1,2,0,0,1,0,1,1,2] r

/-- All even six-bit masks, using the retained parity encoder. -/
def countingTableMask (m : Fin 5 → Bit) (i : Fin 6) : ℕ := (parityEncoder 5 m i).val

def countingTableMaskSupported (T : Finset (Fin 6)) (m : Fin 5 → Bit) : Prop :=
  ∀ i : Fin 6, i ∉ T → countingTableMask m i=0

instance (T : Finset (Fin 6)) (m : Fin 5 → Bit) : Decidable (countingTableMaskSupported T m) :=
  inferInstanceAs (Decidable (∀ i : Fin 6, i ∉ T → countingTableMask m i=0))

def countingTypeBColumnProfile (T : Finset (Fin 6)) : CountingColumnVector :=
  fun i => if i ∈ T then 2 else 0

def countingTableBSourceSupport (r : Fin 14) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => countingTableProfile r i=2)

/-- Literal pair-intersection-rule for a normalized Type B source. -/
def countingPairJointColumns (I Z : Finset (Fin 6)) (m : Fin 5 → Bit) : CountingColumnVector :=
  fun i => if i ∈ I then (if i ∈ Z then 2*(1-countingTableMask m i) else 1) else 0

def countingTypeBTargetWeight (r : Fin 14) (T : Finset (Fin 6))
    (h : CountingColumnVector) : Option ℤ :=
  countingColumnWeight (countingTableEpsilon r) countingTableD (countingTableE r) (countingTableF r)
    (countingTableProfile r) (countingTypeBColumnProfile T) h

/-- Sum over the three support words, using the proved ratio multiplicities. -/
def countingTypeBWordHistogram (r : Fin 14) (T : Finset (Fin 6)) (m : Fin 5 → Bit)
    (j : Fin 6) : ℕ :=
  if countingTableType r=0 then
    3*countingWeightHistogram (countingTypeBTargetWeight r T
      (fun i => if countingTableProfile r i=4 then countingTypeBColumnProfile T i else 0)) j
  else if countingTableType r=2 then
    3*countingWeightHistogram (countingTypeBTargetWeight r T
      (fun i => if i ∈ T then (if countingTableProfile r i=3 then
        1+countingTableMask m i else 1-countingTableMask m i) else 0)) j
  else
    let I := countingTableBSourceSupport r ∩ T
    if I.card=3 then
      ∑ k ∈ I, countingWeightHistogram
        (countingTypeBTargetWeight r T (countingPairJointColumns I {k} m)) j
    else countingWeightHistogram
      (countingTypeBTargetWeight r T (countingPairJointColumns I I m)) j +
      2*countingWeightHistogram (countingTypeBTargetWeight r T (countingPairJointColumns I ∅ m)) j

def countingTypeBTargetHistogram (r : Fin 14) : CountingSignedHistogram :=
  fun j => ∑ T ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
    ∑ m : Fin 5 → Bit, if countingTableMaskSupported T m then countingTypeBWordHistogram r T m j else 0

/-- Every displayed Type B target subtotal, retaining signs and multiplicities. -/
def countingTypeBExpectedHistogram (r : Fin 14) : CountingSignedHistogram :=
  ![![0,0,0,72,0,0],![0,0,0,24,0,0],![0,0,0,0,24,0],
    ![0,0,0,0,24,0],![0,0,16,28,2,0],![0,0,16,16,8,0],![0,0,9,18,3,0],
    ![0,0,0,24,48,0],![0,0,0,24,0,0],![0,4,0,54,2,2],
    ![0,0,0,24,0,0],![0,2,4,24,0,0],![0,0,0,24,0,0],![0,0,0,18,0,0]] r

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
-- Each row has fifteen supports and thirty-two parity masks, with eight admitted per support.
/-- All fourteen Type B target rows; actual-octad interpretation is a separate bridge. -/
theorem countingTypeBTargetHistogram_all :
    ∀ r : Fin 14, countingTypeBTargetHistogram r=countingTypeBExpectedHistogram r := by
  intro r
  fin_cases r <;> decide

end Atlas.Fischer
