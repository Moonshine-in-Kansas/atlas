import Atlas.Lattices.ConwayWales.AmbientSymmetry
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Module.RingHom
import Mathlib.RingTheory.Finiteness.Basic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales

/-- Restrict the actual complex scalar action along the Gaussian-integer embedding. -/
scoped instance gaussianSpaceModule : Module GaussianInt Space :=
  Module.compHom Space GaussianInt.toComplex
open scoped Atlas.ConwayWales

def quaternionBasis : Fin 4 → Q := ![1, j, k, l]
def translate (d : Row) (v : Space) : Space := fun r => v (r - d)

/-- The 84 Gaussian generators: coordinate vectors and right basis multiples of
all seven translates of the two half-integral seeds. -/
def seedGenerator (t : Fin 3) (d : Row) (u : Fin 4) : Space :=
  ![(fun r => if r = d then (2 : ℂ) • quaternionBasis u else 0),
    (fun r => a (r - d) * quaternionBasis u),
    (fun r => b (r - d) * quaternionBasis u)] t

abbrev GeneratorIndex := Fin 3 × Row × Fin 4

def seedLattice : Submodule GaussianInt Space :=
  Submodule.span GaussianInt (Set.range fun p : GeneratorIndex => seedGenerator p.1 p.2.1 p.2.2)

theorem seedGenerator_mem (t : Fin 3) (d : Row) (u : Fin 4) :
    seedGenerator t d u ∈ seedLattice := Submodule.subset_span ⟨(t,d,u), rfl⟩

theorem seedLattice_gaussian_smul (z : GaussianInt) (v : Space) (hv : v ∈ seedLattice) :
    (GaussianInt.toComplex z : ℂ) • v ∈ seedLattice :=
  seedLattice.smul_mem z hv

theorem a_mem_seedLattice : a ∈ seedLattice := by
  simpa [seedGenerator, quaternionBasis] using seedGenerator_mem 1 0 0

theorem b_mem_seedLattice : b ∈ seedLattice := by
  simpa [seedGenerator, quaternionBasis] using seedGenerator_mem 2 0 0

theorem coordinate_mem_seedLattice (d : Row) (u : Fin 4) :
    (fun r => if r = d then (2 : ℂ) • quaternionBasis u else 0) ∈ seedLattice := by
  exact seedGenerator_mem 0 d u

theorem seedLattice_fg : seedLattice.FG := by
  exact Submodule.fg_span (Set.finite_range _)


theorem translate_generator (d : Row) (t : Fin 3) (e : Row) (u : Fin 4) :
    translate d (seedGenerator t e u) = seedGenerator t (d + e) u := by
  fin_cases t
  · funext r
    simp [translate, seedGenerator, sub_eq_iff_eq_add, add_comm]
  · funext r
    change a ((r - d) - e) * quaternionBasis u = a (r - (d + e)) * quaternionBasis u
    congr 2
    abel
  · funext r
    change b ((r - d) - e) * quaternionBasis u = b (r - (d + e)) * quaternionBasis u
    congr 2
    abel

def translateLinear (d : Row) : Space →ₗ[GaussianInt] Space where
  toFun := translate d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem translate_mem_seedLattice (d : Row) (v : Space) (hv : v ∈ seedLattice) :
    translate d v ∈ seedLattice := by
  change v ∈ Submodule.span GaussianInt _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [translate_generator]
    exact seedGenerator_mem _ _ _
  | zero => exact seedLattice.zero_mem
  | add x y hx hy ihx ihy => exact seedLattice.add_mem ihx ihy
  | smul z x hx ih => exact seedLattice.smul_mem z ih

theorem translate_translate (d e : Row) (v : Space) :
    translate d (translate e v) = translate (d + e) v := by
  funext r
  change v ((r - d) - e) = v (r - (d + e))
  congr 1
  abel

theorem translate_mem_iff (d : Row) (v : Space) :
    translate d v ∈ seedLattice ↔ v ∈ seedLattice := by
  constructor
  · intro h
    have := translate_mem_seedLattice (-d) _ h
    rw [translate_translate, neg_add_cancel] at this
    change (fun r => v (r - 0)) ∈ seedLattice at this
    simpa only [sub_zero] using this
  · exact translate_mem_seedLattice d v

theorem convolution_translate (d : Row) (v : Space) :
    convolution (translate d v) = translate (-d) (convolution v) := by
  funext r
  simp only [convolution, translate, sub_neg_eq_add]
  congr 1
  apply Fintype.sum_bijective (fun s : Row => s - d) (Equiv.subRight d).bijective
  intro s
  congr 2
  abel


def coordinateVector (d : Row) (u : Fin 4) : Space :=
  fun r => if r = d then quaternionBasis u else 0

theorem coordinateVector_mem_complex_span (d : Row) (u : Fin 4) :
    coordinateVector d u ∈ Submodule.span ℂ (seedLattice : Set Space) := by
  have h := (Submodule.span ℂ (seedLattice : Set Space)).smul_mem (1 / 2 : ℂ)
    (Submodule.subset_span (coordinate_mem_seedLattice d u))
  have he : (1 / 2 : ℂ) • (fun r => if r = d then (2 : ℂ) • quaternionBasis u else 0) =
      coordinateVector d u := by
    funext r
    by_cases hr : r = d <;> simp [coordinateVector, hr, smul_smul]
  rw [he] at h
  exact h

theorem quaternion_expansion (q : Q) :
    q.re • quaternionBasis 0 + q.imI • quaternionBasis 1 +
      q.imJ • quaternionBasis 2 + q.imK • quaternionBasis 3 = q := by
  ext <;> simp [quaternionBasis,j,k,l]

theorem coordinate_expansion (v : Space) :
    (∑ d : Row, ((v d).re • coordinateVector d 0 + (v d).imI • coordinateVector d 1 +
      (v d).imJ • coordinateVector d 2 + (v d).imK • coordinateVector d 3)) = v := by
  funext r
  simp [coordinateVector, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
    smul_ite, Finset.sum_ite_eq, quaternion_expansion]

theorem seedLattice_complex_span : Submodule.span ℂ (seedLattice : Set Space) = ⊤ := by
  apply top_unique
  intro v _
  rw [← coordinate_expansion v]
  apply Submodule.sum_mem
  intro d _
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (coordinateVector_mem_complex_span d 0))
    (Submodule.smul_mem _ _ (coordinateVector_mem_complex_span d 1)))
    (Submodule.smul_mem _ _ (coordinateVector_mem_complex_span d 2)))
    (Submodule.smul_mem _ _ (coordinateVector_mem_complex_span d 3))

end Atlas.ConwayWales
