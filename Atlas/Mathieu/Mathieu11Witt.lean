import Atlas.Mathieu.Mathieu11PointStabilizer
import Atlas.Mathieu.Mathieu12Witt
import Atlas.Combinatorics.DerivedSteiner

noncomputable section
namespace Atlas.Codes
open Finset
local instance (D : Dodecad) (a : Mathieu12Points D) : Fintype (Mathieu11Points D a) := Fintype.ofFinite _

def mathieu11Blocks (D : Dodecad) (a : Mathieu12Points D) : Finset (Finset (Mathieu11Points D a)) :=
  Atlas.Combinatorics.derivedBlocks (mathieu12Blocks D) a

theorem mathieu11Blocks_size (D : Dodecad) (a : Mathieu12Points D)
    (B : Finset (Mathieu11Points D a)) (hB : B ∈ mathieu11Blocks D a) : B.card = 5 :=
  Atlas.Combinatorics.derivedBlocks_size (mathieu12Blocks D) a 5 (mathieu12Blocks_size D) B hB

theorem mathieu11_steiner (D : Dodecad) (a : Mathieu12Points D)
    (T : Finset (Mathieu11Points D a)) (hT : T.card = 4) :
    ∃! B, B ∈ mathieu11Blocks D a ∧ T ⊆ B :=
  Atlas.Combinatorics.derived_steiner (mathieu12Blocks D) a 4 (mathieu12_steiner D) T hT

theorem mathieu11Blocks_card (D : Dodecad) (a : Mathieu12Points D) : (mathieu11Blocks D a).card = 66 := by
  have h := Atlas.Combinatorics.steiner_block_count (mathieu11Blocks D a) 4 5
    (mathieu11Blocks_size D a) (mathieu11_steiner D a)
  have hd : Fintype.card (Mathieu11Points D a) = 11 := by
    rw [← Nat.card_eq_fintype_card,mathieu11_degree]
  rw [hd] at h
  norm_num [Nat.choose] at h
  omega

def mathieu11BlockLift (D : Dodecad) (a : Mathieu12Points D)
    (B : Finset (Mathieu11Points D a)) : Finset (Mathieu12Points D) :=
  Atlas.Combinatorics.complementBlockLift a B

theorem mathieu11Blocks_mem (D : Dodecad) (a : Mathieu12Points D)
    (B : Finset (Mathieu11Points D a)) :
    B ∈ mathieu11Blocks D a ↔ insert a (mathieu11BlockLift D a B) ∈ mathieu12Blocks D :=
  Atlas.Combinatorics.derivedBlocks_mem (mathieu12Blocks D) a B

def mathieu11PermuteBlock (D : Dodecad) (a : Mathieu12Points D) (g : Mathieu11PointModel D a)
    (B : Finset (Mathieu11Points D a)) : Finset (Mathieu11Points D a) := by
  classical
  exact B.image (fun x => g • x)

theorem mathieu11BlockLift_permute (D : Dodecad) (a : Mathieu12Points D) (g : Mathieu11PointModel D a)
    (B : Finset (Mathieu11Points D a)) :
    mathieu11BlockLift D a (mathieu11PermuteBlock D a g B) =
      mathieu12PermuteBlock D g.val (mathieu11BlockLift D a B) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨z.val,mem_map.mpr ⟨z,hz,rfl⟩,rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨g • (show Mathieu11Points D a from z),mem_image.mpr ⟨z,hz,rfl⟩,rfl⟩

theorem mathieu11Blocks_preserved (D : Dodecad) (a : Mathieu12Points D) (g : Mathieu11PointModel D a)
    (B : Finset (Mathieu11Points D a)) (hB : B ∈ mathieu11Blocks D a) :
    mathieu11PermuteBlock D a g B ∈ mathieu11Blocks D a := by
  classical
  have hB := (mathieu11Blocks_mem D a B).mp hB
  apply (mathieu11Blocks_mem D a _).mpr
  rw [mathieu11BlockLift_permute]
  have h := mathieu12Blocks_preserved D g.val (insert a (mathieu11BlockLift D a B)) hB
  have hg : g.val • a = a := g.prop
  simpa [mathieu12PermuteBlock,hg] using h

theorem mathieu11Blocks_octad_recovery (D : Dodecad) (a : Mathieu12Points D)
    (B : Finset (Mathieu11Points D a)) (hB : B ∈ mathieu11Blocks D a) :
    ∃! O : Finset Omega, O ∈ octads ∧ mathieu12OctadTrace D O = insert a (mathieu11BlockLift D a B) := by
  have hH := (mathieu11Blocks_mem D a B).mp hB
  obtain ⟨O,hO,hc,htrace⟩ := (mathieu12Blocks_mem D _).mp hH
  refine ⟨O,⟨hO,htrace⟩,?_⟩
  intro P hP
  exact mathieu12_hexad_determines_octad D P O hP.1 hO
    (hP.2 ▸ mathieu12Blocks_size D _ hH) (hP.2.trans htrace.symm)

end Atlas.Codes
