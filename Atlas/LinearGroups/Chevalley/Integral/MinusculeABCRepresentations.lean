import Atlas.LinearGroups.Chevalley.Integral.MinusculeOrbitRepresentation
import Atlas.LinearGroups.Chevalley.Integral.MinusculeA
import Atlas.LinearGroups.Chevalley.Integral.MinusculeB
import Atlas.LinearGroups.Chevalley.Integral.MinusculeC

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

namespace TypeA

def actualStrings (r : ℕ) : Strings (TypeAData.Root (r+1))
    (WeightOrbit (TypeAData.pairing (r+1)) (naturalOrbit r)) :=
  stringsOfWeightOrbit (TypeAData.pairing (r+1)) (naturalOrbit r)
    (naturalOrbit_closed r) (by
      intro μ hμ a
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hμ
      exact naturalWeight_minuscule k a)

end TypeA
namespace TypeB

def actualStrings (n : ℕ) : Strings (ClassicalData.BRoot (n+1))
    (WeightOrbit (ClassicalData.pairingB (n+1)) (spinOrbit n)) :=
  stringsOfWeightOrbit (ClassicalData.pairingB (n+1)) (spinOrbit n)
    (spinOrbit_closed n) (by
      intro μ hμ a
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hμ
      exact spinWeight_minuscule n σ a)

end TypeB
namespace TypeC

def actualStrings (r : ℕ) : Strings (ClassicalData.BRoot r)
    (WeightOrbit (ClassicalData.pairingC r) (orbit r)) :=
  stringsOfWeightOrbit (ClassicalData.pairingC r) (orbit r)
    orbit_closed (by
      intro μ hμ a
      obtain ⟨⟨k,s⟩, _, rfl⟩ := Finset.mem_image.mp hμ
      exact naturalWeight_minuscule k (sign s) (by cases s <;> simp [sign]) a)

end TypeC
end Atlas.Chevalley.Integral.Minuscule
