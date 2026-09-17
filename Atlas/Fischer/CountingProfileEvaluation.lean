import Atlas.Fischer.CountingTypeCTable

namespace Atlas.Fischer
open Atlas.Codes

/-- Data for a normalized source profile. These finite column formulas are
interpreted by actual source octads in separate theorems. -/
structure CountingProfileData where
  epsilon : ℕ
  D : Finset (Fin 6)
  E : Finset (Fin 6)
  F : Finset (Fin 6)
  g : CountingColumnVector
  sourceType : Fin 3

def countingRepresentativeData (r : Fin 14) : CountingProfileData :=
  ⟨countingTableEpsilon r, countingTableD, countingTableE r, countingTableF r,
    countingTableProfile r, countingTableType r⟩

def CountingProfileData.weight (p : CountingProfileData) (b h : CountingColumnVector) : Option ℤ :=
  countingColumnWeight p.epsilon p.D p.E p.F p.g b h

def CountingProfileData.support (p : CountingProfileData) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => p.g i=2)

def CountingProfileData.histogramA (p : CountingProfileData) : CountingSignedHistogram :=
  fun j => ∑ T ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
    countingWeightHistogram (p.weight (countingTypeAColumnProfile T)
      (fun i => if i ∈ T then p.g i else 0)) j

def CountingProfileData.wordHistogramB (p : CountingProfileData) (T : Finset (Fin 6))
    (m : Fin 5 → Bit) (j : Fin 6) : ℕ :=
  if p.sourceType=0 then
    3*countingWeightHistogram (p.weight (countingTypeBColumnProfile T)
      (fun i => if p.g i=4 then countingTypeBColumnProfile T i else 0)) j
  else if p.sourceType=2 then
    3*countingWeightHistogram (p.weight (countingTypeBColumnProfile T)
      (fun i => if i ∈ T then (if p.g i=3 then
        1+countingTableMask m i else 1-countingTableMask m i) else 0)) j
  else
    let I := p.support ∩ T
    if I.card=3 then
      ∑ k ∈ I, countingWeightHistogram
        (p.weight (countingTypeBColumnProfile T) (countingPairJointColumns I {k} m)) j
    else countingWeightHistogram
      (p.weight (countingTypeBColumnProfile T) (countingPairJointColumns I I m)) j +
      2*countingWeightHistogram
        (p.weight (countingTypeBColumnProfile T) (countingPairJointColumns I ∅ m)) j

def CountingProfileData.histogramB (p : CountingProfileData) : CountingSignedHistogram :=
  fun j => ∑ T ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
    ∑ m : Fin 5 → Bit, if countingTableMaskSupported T m then p.wordHistogramB T m j else 0

def CountingProfileData.singletonJoint (p : CountingProfileData) (j : Fin 6)
    (Z : Finset (Fin 6)) : CountingColumnVector :=
  fun i => if p.g i=3 then
    (if i=j then (if i ∈ Z then 3 else 2) else (if i ∈ Z then 0 else 1))
    else (if i=j then (if i ∈ Z then 0 else 1) else (if i ∈ Z then 1 else 0))

def CountingProfileData.wordHistogramC (p : CountingProfileData) (j k : Fin 6) : ℕ :=
  if p.sourceType=0 then
    64*countingWeightHistogram (p.weight (countingTypeCColumnProfile j)
      (fun i => if p.g i=4 then countingTypeCColumnProfile j i else 0)) k
  else if p.sourceType=1 then
    ∑ m : Fin 5 → Bit, if countingTableMaskSupported p.support m then
      8*countingWeightHistogram (p.weight (countingTypeCColumnProfile j)
        (fun i => if i ∈ p.support then
          (if i=j then 1+countingTableMask m i else 1-countingTableMask m i) else 0)) k else 0
  else
    countingWeightHistogram (p.weight (countingTypeCColumnProfile j)
      (p.singletonJoint j Finset.univ)) k +
    (∑ Z ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
      3*countingWeightHistogram (p.weight (countingTypeCColumnProfile j)
        (p.singletonJoint j Z)) k) +
    18*countingWeightHistogram (p.weight (countingTypeCColumnProfile j)
      (p.singletonJoint j ∅)) k

def CountingProfileData.histogramC (p : CountingProfileData) : CountingSignedHistogram :=
  fun k => ∑ j : Fin 6, p.wordHistogramC j k

theorem countingProfile_representative_A (r : Fin 14) :
    (countingRepresentativeData r).histogramA=countingTypeATargetHistogram r := rfl

theorem countingProfile_representative_B (r : Fin 14) :
    (countingRepresentativeData r).histogramB=countingTypeBTargetHistogram r := rfl

theorem countingProfile_representative_C (r : Fin 14) :
    (countingRepresentativeData r).histogramC=countingTypeCTargetHistogram r := rfl

end Atlas.Fischer
