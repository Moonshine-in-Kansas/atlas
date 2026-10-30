import F4Work.F4GeckExponentials
import F4Work.F4GeckOppositionRoot0
import F4Work.F4GeckOppositionRoot1
import F4Work.F4GeckOppositionRoot2
import F4Work.F4GeckOppositionRoot3

noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Integral F4Data
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000


variable (R : Type*) [CommRing R]

theorem geck_negative_table : ∀ (i : Fin 4) (a c : Fin 52),
    geckMatrix (Fin.natAdd 4 i) a c =
      geckMatrix (Fin.castAdd 4 i) (opposite52 a) (opposite52 c) := by
  intro i a c
  fin_cases i
  · exact geck_negative_root0 a c
  · exact geck_negative_root1 a c
  · exact geck_negative_root2 a c
  · exact geck_negative_root3 a c

theorem geck_negative_second_table : ∀ (i : Fin 4) (a c : Fin 52),
    geckSecondMatrix (Fin.natAdd 4 i) a c =
      geckSecondMatrix (Fin.castAdd 4 i) (opposite52 a) (opposite52 c) := by
  intro i a c
  fin_cases i
  · exact geck_negative_second_root0 a c
  · exact geck_negative_second_root1 a c
  · exact geck_negative_second_root2 a c
  · exact geck_negative_second_root3 a c

theorem opposition52_geckOver (i : Fin 4) (t : R) :
    opposition52 R * geckOver R (Fin.castAdd 4 i) t * opposition52 R =
      geckOver R (Fin.natAdd 4 i) t := by
  ext a c
  rw [opposition52_conjugation]
  have he : opposite52 a=opposite52 c ↔ a=c :=
    opposite52_involutive.injective.eq_iff
  simp only [geckOver, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.one_apply, he, geck_negative_table,
    geck_negative_second_table]

theorem chevalleyMatrixHom_Y (i : Fin 4) (t : R) :
    chevalleyMatrixHom (modelY .F4 R i t) = geckOver R (Fin.natAdd 4 i) t := by
  change reindex52 R (oppositionOver pairing base R *
    raisingExponential pairing base R (baseIndexEquiv i) t *
      oppositionOver pairing base R) = _
  rw [map_mul, map_mul, reindex52_opposition, actual_raising_exponential,
    opposition52_geckOver]

end Atlas.Chevalley.Comparison.F4
