import Atlas.OrderArithmetic.PolynomialRowReversal

namespace Atlas.OrderArithmetic

def exceptionalPairChunk0 : Finset (RawEntry × RawEntry) :=
  {((.linear 2 0), (.suzuki 0)),
   ((.linear 2 0), (.smallRee 0)),
   ((.linear 3 0), (.G2 0)),
   ((.linear 3 0), (.trialityD4 0)),
   ((.linear 3 0), (.largeRee 0)),
   ((.linear 5 0), (.F4 0)),
   ((.linear 5 0), (.twistedE6 0)),
   ((.linear 7 0), (.E6 0)),
   ((.linear 8 0), (.E7 0)),
   ((.linear 9 0), (.E8 0))}

def exceptionalPairChunk1 : Finset (RawEntry × RawEntry) :=
  {((.unitary 3 0), (.suzuki 0)),
   ((.unitary 3 0), (.smallRee 0)),
   ((.unitary 4 0), (.G2 0)),
   ((.unitary 4 0), (.trialityD4 0)),
   ((.unitary 4 0), (.largeRee 0)),
   ((.unitary 5 0), (.G2 0)),
   ((.unitary 5 0), (.trialityD4 0)),
   ((.unitary 5 0), (.largeRee 0)),
   ((.unitary 8 0), (.F4 0)),
   ((.unitary 8 0), (.twistedE6 0))}

def exceptionalPairChunk2 : Finset (RawEntry × RawEntry) :=
  {((.unitary 9 0), (.F4 0)),
   ((.unitary 9 0), (.twistedE6 0)),
   ((.unitary 12 0), (.E6 0)),
   ((.unitary 13 0), (.E6 0)),
   ((.unitary 14 0), (.E7 0)),
   ((.unitary 15 0), (.E7 0)),
   ((.unitary 16 0), (.E8 0)),
   ((.unitary 17 0), (.E8 0)),
   ((.B 2 0), (.G2 0)),
   ((.B 2 0), (.trialityD4 0))}

def exceptionalPairChunk3 : Finset (RawEntry × RawEntry) :=
  {((.B 2 0), (.largeRee 0)),
   ((.B 4 0), (.F4 0)),
   ((.B 4 0), (.twistedE6 0)),
   ((.B 6 0), (.E6 0)),
   ((.B 7 0), (.E7 0)),
   ((.B 8 0), (.E8 0)),
   ((.C 2 0), (.G2 0)),
   ((.C 2 0), (.trialityD4 0)),
   ((.C 2 0), (.largeRee 0)),
   ((.C 4 0), (.F4 0))}

def exceptionalPairChunk4 : Finset (RawEntry × RawEntry) :=
  {((.C 4 0), (.twistedE6 0)),
   ((.C 6 0), (.E6 0)),
   ((.C 7 0), (.E7 0)),
   ((.C 8 0), (.E8 0)),
   ((.Dplus 4 0), (.F4 0)),
   ((.Dplus 4 0), (.twistedE6 0)),
   ((.Dplus 6 0), (.E6 0)),
   ((.Dplus 7 0), (.E7 0)),
   ((.Dplus 8 0), (.E8 0)),
   ((.Dminus 5 0), (.F4 0))}

def exceptionalPairChunk5 : Finset (RawEntry × RawEntry) :=
  {((.Dminus 5 0), (.twistedE6 0)),
   ((.Dminus 7 0), (.E6 0)),
   ((.Dminus 8 0), (.E7 0)),
   ((.Dminus 9 0), (.E8 0)),
   ((.G2 0), (.trialityD4 0)),
   ((.G2 0), (.largeRee 0)),
   ((.F4 0), (.twistedE6 0)),
   ((.trialityD4 0), (.largeRee 0)),
   ((.suzuki 0), (.smallRee 0))}

/-- One orientation of each of the59 exceptional-ratio family/rank pairs. -/
def canonicalExceptionalPairs : Finset (RawEntry × RawEntry) :=
  exceptionalPairChunk0 ∪ (exceptionalPairChunk1 ∪ (exceptionalPairChunk2 ∪ (exceptionalPairChunk3 ∪ (exceptionalPairChunk4 ∪ (exceptionalPairChunk5)))))

set_option maxRecDepth 16384 in
theorem canonicalExceptionalPairs_cover :
    ∀ pair ∈ exceptionalPairCandidates,
      pair ∈ canonicalExceptionalPairs ∨ pair.swap ∈ canonicalExceptionalPairs := by
  decide +kernel

end Atlas.OrderArithmetic
