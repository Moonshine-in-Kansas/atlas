import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row0D0
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row0D1
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row000
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row001
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row002
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row003
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row004
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row005
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row006
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row007
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row010
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row011
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row012
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row013
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row014
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row015
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row016
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row017
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row020
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row021
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row022
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row023
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row024
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row025
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row026
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row027
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row1D0
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row1D1
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row100
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row101
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row102
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row103
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row104
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row105
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row106
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row107
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row110
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row111
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row112
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row113
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row114
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row115
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row116
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row117
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row120
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row121
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row122
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row123
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row124
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row125
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row126
import Atlas.LinearGroups.ReeF4.WeylStarChecks.Row127

/-! Full local coefficient identities, including the diagonal directions. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem weylStarCoefficient_binary : ∀ (g : Fin 2) (i j : TraceZeroCoordinate),
    weylStarCoefficient (F := ZMod 2) g i j =
      weylOperator g (extensionCoefficient i j) +
        weylStarCorrection g (traceZeroCross (starMarkedVector i) (starMarkedVector j)) := by
  intro g i j
  fin_cases g
  · rcases i with i | ⟨b,k⟩
    · fin_cases i
      · exact weylStarCheckRow0D0 j
      · exact weylStarCheckRow0D1 j
    · fin_cases b <;> fin_cases k
      · exact weylStarCheckRow000 j
      · exact weylStarCheckRow001 j
      · exact weylStarCheckRow002 j
      · exact weylStarCheckRow003 j
      · exact weylStarCheckRow004 j
      · exact weylStarCheckRow005 j
      · exact weylStarCheckRow006 j
      · exact weylStarCheckRow007 j
      · exact weylStarCheckRow010 j
      · exact weylStarCheckRow011 j
      · exact weylStarCheckRow012 j
      · exact weylStarCheckRow013 j
      · exact weylStarCheckRow014 j
      · exact weylStarCheckRow015 j
      · exact weylStarCheckRow016 j
      · exact weylStarCheckRow017 j
      · exact weylStarCheckRow020 j
      · exact weylStarCheckRow021 j
      · exact weylStarCheckRow022 j
      · exact weylStarCheckRow023 j
      · exact weylStarCheckRow024 j
      · exact weylStarCheckRow025 j
      · exact weylStarCheckRow026 j
      · exact weylStarCheckRow027 j
  · rcases i with i | ⟨b,k⟩
    · fin_cases i
      · exact weylStarCheckRow1D0 j
      · exact weylStarCheckRow1D1 j
    · fin_cases b <;> fin_cases k
      · exact weylStarCheckRow100 j
      · exact weylStarCheckRow101 j
      · exact weylStarCheckRow102 j
      · exact weylStarCheckRow103 j
      · exact weylStarCheckRow104 j
      · exact weylStarCheckRow105 j
      · exact weylStarCheckRow106 j
      · exact weylStarCheckRow107 j
      · exact weylStarCheckRow110 j
      · exact weylStarCheckRow111 j
      · exact weylStarCheckRow112 j
      · exact weylStarCheckRow113 j
      · exact weylStarCheckRow114 j
      · exact weylStarCheckRow115 j
      · exact weylStarCheckRow116 j
      · exact weylStarCheckRow117 j
      · exact weylStarCheckRow120 j
      · exact weylStarCheckRow121 j
      · exact weylStarCheckRow122 j
      · exact weylStarCheckRow123 j
      · exact weylStarCheckRow124 j
      · exact weylStarCheckRow125 j
      · exact weylStarCheckRow126 j
      · exact weylStarCheckRow127 j

theorem weylStarCoefficient_eq (g : Fin 2) (i j : TraceZeroCoordinate) :
    weylStarCoefficient (F := F) g i j =
      weylOperator g (extensionCoefficient i j) +
        weylStarCorrection g (traceZeroCross (starMarkedVector i) (starMarkedVector j)) := by
  let f : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  have h := congrArg (traceZeroScalarMap f) (weylStarCoefficient_binary g i j)
  simp only [_root_.map_add, traceZeroScalarMap_apply, weylStarCoefficient_map,
    weylOperator_map, extensionCoefficient_map, weylStarCorrection_map,
    ← traceZeroMap_cross, starMarkedVector_map] at h
  exact h

end Atlas.ReeF4
