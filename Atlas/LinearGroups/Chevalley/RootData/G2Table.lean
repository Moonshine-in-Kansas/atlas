import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.Tactic.FinCases

/-! Integral root/coroot coordinates with ordinary kernel-checked certificates. -/
namespace Atlas.Chevalley.G2Table
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
abbrev Root := Fin 12
abbrev Vector := Fin 2 → ℤ
def cartan : Matrix (Fin 2) (Fin 2) ℤ := CartanMatrix.G₂
def rootTable : Array (Array ℤ) := #[#[1,0],#[0,1],#[-1,0],#[1,3],#[1,1],#[0,-1],#[-1,-3],#[2,3],#[1,2],#[-1,-1],#[-2,-3],#[-1,-2]]
def coordinates (a : Root) (i : Fin 2) : ℤ := (rootTable[a.val]!)[i.val]!
def corootCoefficientTable : Array (Array ℤ) := #[#[1,0],#[0,1],#[-1,0],#[1,1],#[3,1],#[0,-1],#[-1,-1],#[2,1],#[3,2],#[-3,-1],#[-2,-1],#[-3,-2]]
def corootCoefficientCoordinates (a : Root) (i : Fin 2) : ℤ := (corootCoefficientTable[a.val]!)[i.val]!
def dualTable : Array (Array ℤ) := #[#[2,-1],#[-3,2],#[-2,1],#[-1,1],#[3,-1],#[3,-2],#[1,-1],#[1,0],#[0,1],#[-3,1],#[-1,0],#[0,-1]]
def dualCoordinates (a : Root) (i : Fin 2) : ℤ := (dualTable[a.val]!)[i.val]!
def primitiveWitnessTable : Array (Array ℤ) := #[#[1,0],#[0,1],#[-1,0],#[1,0],#[0,1],#[0,-1],#[-1,0],#[-1,1],#[1,0],#[0,-1],#[1,-1],#[-1,0]]
def primitiveWitnessCoordinates (a : Root) (i : Fin 2) : ℤ := (primitiveWitnessTable[a.val]!)[i.val]!
def dualDecode (x : Vector) : Root := if x 0 = (-3 : ℤ) then if x 1 = (1 : ℤ) then 9 else 1 else if x 0 = (-2 : ℤ) then 2 else if x 0 = (-1 : ℤ) then if x 1 = (0 : ℤ) then 10 else 3 else if x 0 = (0 : ℤ) then if x 1 = (-1 : ℤ) then 11 else 8 else if x 0 = (1 : ℤ) then if x 1 = (-1 : ℤ) then 6 else 7 else if x 0 = (2 : ℤ) then 0 else if x 1 = (-2 : ℤ) then 5 else 4
def simpleIndex (i : Fin 2) : Root := Fin.ofNat 12 (#[0,1][i.val]!)
def reflectionTable : Array (Array ℕ) := #[#[2,4,0,7,1,9,10,3,8,5,6,11],#[3,5,6,0,8,1,2,7,4,11,10,9],#[2,4,0,7,1,9,10,3,8,5,6,11],#[7,11,10,6,4,8,3,0,5,9,2,1],#[10,8,7,3,9,11,6,2,1,4,0,5],#[3,5,6,0,8,1,2,7,4,11,10,9],#[7,11,10,6,4,8,3,0,5,9,2,1],#[6,1,3,2,11,5,0,10,9,8,7,4],#[0,9,2,10,5,4,7,6,11,1,3,8],#[10,8,7,3,9,11,6,2,1,4,0,5],#[6,1,3,2,11,5,0,10,9,8,7,4],#[0,9,2,10,5,4,7,6,11,1,3,8]]
def reflectionIndex (a b : Root) : Root := Fin.ofNat 12 ((reflectionTable[a.val]!)[b.val]!)
def dot (x y : Vector) : ℤ := ∑ i, x i * y i
theorem coordinates_injective : Function.Injective coordinates := by decide +kernel
private theorem dual_decode_0 : dualDecode (dualCoordinates 0) = 0 := by decide +kernel
private theorem dual_decode_1 : dualDecode (dualCoordinates 1) = 1 := by decide +kernel
private theorem dual_decode_2 : dualDecode (dualCoordinates 2) = 2 := by decide +kernel
private theorem dual_decode_3 : dualDecode (dualCoordinates 3) = 3 := by decide +kernel
private theorem dual_decode_4 : dualDecode (dualCoordinates 4) = 4 := by decide +kernel
private theorem dual_decode_5 : dualDecode (dualCoordinates 5) = 5 := by decide +kernel
private theorem dual_decode_6 : dualDecode (dualCoordinates 6) = 6 := by decide +kernel
private theorem dual_decode_7 : dualDecode (dualCoordinates 7) = 7 := by decide +kernel
private theorem dual_decode_8 : dualDecode (dualCoordinates 8) = 8 := by decide +kernel
private theorem dual_decode_9 : dualDecode (dualCoordinates 9) = 9 := by decide +kernel
private theorem dual_decode_10 : dualDecode (dualCoordinates 10) = 10 := by decide +kernel
private theorem dual_decode_11 : dualDecode (dualCoordinates 11) = 11 := by decide +kernel
theorem dual_decode : ∀ a : Root, dualDecode (dualCoordinates a) = a := by
  intro a
  fin_cases a
  · exact dual_decode_0
  · exact dual_decode_1
  · exact dual_decode_2
  · exact dual_decode_3
  · exact dual_decode_4
  · exact dual_decode_5
  · exact dual_decode_6
  · exact dual_decode_7
  · exact dual_decode_8
  · exact dual_decode_9
  · exact dual_decode_10
  · exact dual_decode_11
theorem dualCoordinates_injective : Function.Injective dualCoordinates := Function.LeftInverse.injective dual_decode
private theorem pairing_two_0 : dot (dualCoordinates 0) (coordinates 0) = 2 := by decide +kernel
private theorem pairing_two_1 : dot (dualCoordinates 1) (coordinates 1) = 2 := by decide +kernel
private theorem pairing_two_2 : dot (dualCoordinates 2) (coordinates 2) = 2 := by decide +kernel
private theorem pairing_two_3 : dot (dualCoordinates 3) (coordinates 3) = 2 := by decide +kernel
private theorem pairing_two_4 : dot (dualCoordinates 4) (coordinates 4) = 2 := by decide +kernel
private theorem pairing_two_5 : dot (dualCoordinates 5) (coordinates 5) = 2 := by decide +kernel
private theorem pairing_two_6 : dot (dualCoordinates 6) (coordinates 6) = 2 := by decide +kernel
private theorem pairing_two_7 : dot (dualCoordinates 7) (coordinates 7) = 2 := by decide +kernel
private theorem pairing_two_8 : dot (dualCoordinates 8) (coordinates 8) = 2 := by decide +kernel
private theorem pairing_two_9 : dot (dualCoordinates 9) (coordinates 9) = 2 := by decide +kernel
private theorem pairing_two_10 : dot (dualCoordinates 10) (coordinates 10) = 2 := by decide +kernel
private theorem pairing_two_11 : dot (dualCoordinates 11) (coordinates 11) = 2 := by decide +kernel
theorem pairing_two : ∀ a : Root, dot (dualCoordinates a) (coordinates a) = 2 := by
  intro a
  fin_cases a
  · exact pairing_two_0
  · exact pairing_two_1
  · exact pairing_two_2
  · exact pairing_two_3
  · exact pairing_two_4
  · exact pairing_two_5
  · exact pairing_two_6
  · exact pairing_two_7
  · exact pairing_two_8
  · exact pairing_two_9
  · exact pairing_two_10
  · exact pairing_two_11
private theorem primitive_0 : dot (primitiveWitnessCoordinates 0) (coordinates 0) = 1 := by decide +kernel
private theorem primitive_1 : dot (primitiveWitnessCoordinates 1) (coordinates 1) = 1 := by decide +kernel
private theorem primitive_2 : dot (primitiveWitnessCoordinates 2) (coordinates 2) = 1 := by decide +kernel
private theorem primitive_3 : dot (primitiveWitnessCoordinates 3) (coordinates 3) = 1 := by decide +kernel
private theorem primitive_4 : dot (primitiveWitnessCoordinates 4) (coordinates 4) = 1 := by decide +kernel
private theorem primitive_5 : dot (primitiveWitnessCoordinates 5) (coordinates 5) = 1 := by decide +kernel
private theorem primitive_6 : dot (primitiveWitnessCoordinates 6) (coordinates 6) = 1 := by decide +kernel
private theorem primitive_7 : dot (primitiveWitnessCoordinates 7) (coordinates 7) = 1 := by decide +kernel
private theorem primitive_8 : dot (primitiveWitnessCoordinates 8) (coordinates 8) = 1 := by decide +kernel
private theorem primitive_9 : dot (primitiveWitnessCoordinates 9) (coordinates 9) = 1 := by decide +kernel
private theorem primitive_10 : dot (primitiveWitnessCoordinates 10) (coordinates 10) = 1 := by decide +kernel
private theorem primitive_11 : dot (primitiveWitnessCoordinates 11) (coordinates 11) = 1 := by decide +kernel
theorem primitive : ∀ a : Root, dot (primitiveWitnessCoordinates a) (coordinates a) = 1 := by
  intro a
  fin_cases a
  · exact primitive_0
  · exact primitive_1
  · exact primitive_2
  · exact primitive_3
  · exact primitive_4
  · exact primitive_5
  · exact primitive_6
  · exact primitive_7
  · exact primitive_8
  · exact primitive_9
  · exact primitive_10
  · exact primitive_11
private theorem dual_reconstruct_0 : dualCoordinates 0 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 0 i := by decide +kernel
private theorem dual_reconstruct_1 : dualCoordinates 1 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 1 i := by decide +kernel
private theorem dual_reconstruct_2 : dualCoordinates 2 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 2 i := by decide +kernel
private theorem dual_reconstruct_3 : dualCoordinates 3 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 3 i := by decide +kernel
private theorem dual_reconstruct_4 : dualCoordinates 4 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 4 i := by decide +kernel
private theorem dual_reconstruct_5 : dualCoordinates 5 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 5 i := by decide +kernel
private theorem dual_reconstruct_6 : dualCoordinates 6 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 6 i := by decide +kernel
private theorem dual_reconstruct_7 : dualCoordinates 7 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 7 i := by decide +kernel
private theorem dual_reconstruct_8 : dualCoordinates 8 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 8 i := by decide +kernel
private theorem dual_reconstruct_9 : dualCoordinates 9 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 9 i := by decide +kernel
private theorem dual_reconstruct_10 : dualCoordinates 10 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 10 i := by decide +kernel
private theorem dual_reconstruct_11 : dualCoordinates 11 = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates 11 i := by decide +kernel
theorem dual_reconstruct : ∀ a : Root, dualCoordinates a = fun j => ∑ i : Fin 2, cartan j i * corootCoefficientCoordinates a i := by
  intro a
  fin_cases a
  · exact dual_reconstruct_0
  · exact dual_reconstruct_1
  · exact dual_reconstruct_2
  · exact dual_reconstruct_3
  · exact dual_reconstruct_4
  · exact dual_reconstruct_5
  · exact dual_reconstruct_6
  · exact dual_reconstruct_7
  · exact dual_reconstruct_8
  · exact dual_reconstruct_9
  · exact dual_reconstruct_10
  · exact dual_reconstruct_11
private theorem reflection_involutive_0 : ∀ b : Root, reflectionIndex 0 (reflectionIndex 0 b) = b := by decide +kernel
private theorem reflection_involutive_1 : ∀ b : Root, reflectionIndex 1 (reflectionIndex 1 b) = b := by decide +kernel
private theorem reflection_involutive_2 : ∀ b : Root, reflectionIndex 2 (reflectionIndex 2 b) = b := by decide +kernel
private theorem reflection_involutive_3 : ∀ b : Root, reflectionIndex 3 (reflectionIndex 3 b) = b := by decide +kernel
private theorem reflection_involutive_4 : ∀ b : Root, reflectionIndex 4 (reflectionIndex 4 b) = b := by decide +kernel
private theorem reflection_involutive_5 : ∀ b : Root, reflectionIndex 5 (reflectionIndex 5 b) = b := by decide +kernel
private theorem reflection_involutive_6 : ∀ b : Root, reflectionIndex 6 (reflectionIndex 6 b) = b := by decide +kernel
private theorem reflection_involutive_7 : ∀ b : Root, reflectionIndex 7 (reflectionIndex 7 b) = b := by decide +kernel
private theorem reflection_involutive_8 : ∀ b : Root, reflectionIndex 8 (reflectionIndex 8 b) = b := by decide +kernel
private theorem reflection_involutive_9 : ∀ b : Root, reflectionIndex 9 (reflectionIndex 9 b) = b := by decide +kernel
private theorem reflection_involutive_10 : ∀ b : Root, reflectionIndex 10 (reflectionIndex 10 b) = b := by decide +kernel
private theorem reflection_involutive_11 : ∀ b : Root, reflectionIndex 11 (reflectionIndex 11 b) = b := by decide +kernel
theorem reflection_involutive : ∀ a b : Root, reflectionIndex a (reflectionIndex a b) = b := by
  intro a
  fin_cases a
  · exact reflection_involutive_0
  · exact reflection_involutive_1
  · exact reflection_involutive_2
  · exact reflection_involutive_3
  · exact reflection_involutive_4
  · exact reflection_involutive_5
  · exact reflection_involutive_6
  · exact reflection_involutive_7
  · exact reflection_involutive_8
  · exact reflection_involutive_9
  · exact reflection_involutive_10
  · exact reflection_involutive_11
private theorem reflection_root_0 : ∀ b : Root, coordinates (reflectionIndex 0 b) = coordinates b - dot (dualCoordinates 0) (coordinates b) • coordinates 0 := by decide +kernel
private theorem reflection_root_1 : ∀ b : Root, coordinates (reflectionIndex 1 b) = coordinates b - dot (dualCoordinates 1) (coordinates b) • coordinates 1 := by decide +kernel
private theorem reflection_root_2 : ∀ b : Root, coordinates (reflectionIndex 2 b) = coordinates b - dot (dualCoordinates 2) (coordinates b) • coordinates 2 := by decide +kernel
private theorem reflection_root_3 : ∀ b : Root, coordinates (reflectionIndex 3 b) = coordinates b - dot (dualCoordinates 3) (coordinates b) • coordinates 3 := by decide +kernel
private theorem reflection_root_4 : ∀ b : Root, coordinates (reflectionIndex 4 b) = coordinates b - dot (dualCoordinates 4) (coordinates b) • coordinates 4 := by decide +kernel
private theorem reflection_root_5 : ∀ b : Root, coordinates (reflectionIndex 5 b) = coordinates b - dot (dualCoordinates 5) (coordinates b) • coordinates 5 := by decide +kernel
private theorem reflection_root_6 : ∀ b : Root, coordinates (reflectionIndex 6 b) = coordinates b - dot (dualCoordinates 6) (coordinates b) • coordinates 6 := by decide +kernel
private theorem reflection_root_7 : ∀ b : Root, coordinates (reflectionIndex 7 b) = coordinates b - dot (dualCoordinates 7) (coordinates b) • coordinates 7 := by decide +kernel
private theorem reflection_root_8 : ∀ b : Root, coordinates (reflectionIndex 8 b) = coordinates b - dot (dualCoordinates 8) (coordinates b) • coordinates 8 := by decide +kernel
private theorem reflection_root_9 : ∀ b : Root, coordinates (reflectionIndex 9 b) = coordinates b - dot (dualCoordinates 9) (coordinates b) • coordinates 9 := by decide +kernel
private theorem reflection_root_10 : ∀ b : Root, coordinates (reflectionIndex 10 b) = coordinates b - dot (dualCoordinates 10) (coordinates b) • coordinates 10 := by decide +kernel
private theorem reflection_root_11 : ∀ b : Root, coordinates (reflectionIndex 11 b) = coordinates b - dot (dualCoordinates 11) (coordinates b) • coordinates 11 := by decide +kernel
theorem reflection_root : ∀ a b : Root, coordinates (reflectionIndex a b) = coordinates b - dot (dualCoordinates a) (coordinates b) • coordinates a := by
  intro a
  fin_cases a
  · exact reflection_root_0
  · exact reflection_root_1
  · exact reflection_root_2
  · exact reflection_root_3
  · exact reflection_root_4
  · exact reflection_root_5
  · exact reflection_root_6
  · exact reflection_root_7
  · exact reflection_root_8
  · exact reflection_root_9
  · exact reflection_root_10
  · exact reflection_root_11
private theorem reflection_coroot_0 : ∀ b : Root, dualCoordinates (reflectionIndex 0 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 0) • dualCoordinates 0 := by decide +kernel
private theorem reflection_coroot_1 : ∀ b : Root, dualCoordinates (reflectionIndex 1 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 1) • dualCoordinates 1 := by decide +kernel
private theorem reflection_coroot_2 : ∀ b : Root, dualCoordinates (reflectionIndex 2 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 2) • dualCoordinates 2 := by decide +kernel
private theorem reflection_coroot_3 : ∀ b : Root, dualCoordinates (reflectionIndex 3 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 3) • dualCoordinates 3 := by decide +kernel
private theorem reflection_coroot_4 : ∀ b : Root, dualCoordinates (reflectionIndex 4 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 4) • dualCoordinates 4 := by decide +kernel
private theorem reflection_coroot_5 : ∀ b : Root, dualCoordinates (reflectionIndex 5 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 5) • dualCoordinates 5 := by decide +kernel
private theorem reflection_coroot_6 : ∀ b : Root, dualCoordinates (reflectionIndex 6 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 6) • dualCoordinates 6 := by decide +kernel
private theorem reflection_coroot_7 : ∀ b : Root, dualCoordinates (reflectionIndex 7 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 7) • dualCoordinates 7 := by decide +kernel
private theorem reflection_coroot_8 : ∀ b : Root, dualCoordinates (reflectionIndex 8 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 8) • dualCoordinates 8 := by decide +kernel
private theorem reflection_coroot_9 : ∀ b : Root, dualCoordinates (reflectionIndex 9 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 9) • dualCoordinates 9 := by decide +kernel
private theorem reflection_coroot_10 : ∀ b : Root, dualCoordinates (reflectionIndex 10 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 10) • dualCoordinates 10 := by decide +kernel
private theorem reflection_coroot_11 : ∀ b : Root, dualCoordinates (reflectionIndex 11 b) = dualCoordinates b - dot (dualCoordinates b) (coordinates 11) • dualCoordinates 11 := by decide +kernel
theorem reflection_coroot : ∀ a b : Root, dualCoordinates (reflectionIndex a b) = dualCoordinates b - dot (dualCoordinates b) (coordinates a) • dualCoordinates a := by
  intro a
  fin_cases a
  · exact reflection_coroot_0
  · exact reflection_coroot_1
  · exact reflection_coroot_2
  · exact reflection_coroot_3
  · exact reflection_coroot_4
  · exact reflection_coroot_5
  · exact reflection_coroot_6
  · exact reflection_coroot_7
  · exact reflection_coroot_8
  · exact reflection_coroot_9
  · exact reflection_coroot_10
  · exact reflection_coroot_11
private theorem root_sign_0 : (∀ i, 0 ≤ coordinates 0 i) ∨ (∀ i, coordinates 0 i ≤ 0) := by decide +kernel
private theorem root_sign_1 : (∀ i, 0 ≤ coordinates 1 i) ∨ (∀ i, coordinates 1 i ≤ 0) := by decide +kernel
private theorem root_sign_2 : (∀ i, 0 ≤ coordinates 2 i) ∨ (∀ i, coordinates 2 i ≤ 0) := by decide +kernel
private theorem root_sign_3 : (∀ i, 0 ≤ coordinates 3 i) ∨ (∀ i, coordinates 3 i ≤ 0) := by decide +kernel
private theorem root_sign_4 : (∀ i, 0 ≤ coordinates 4 i) ∨ (∀ i, coordinates 4 i ≤ 0) := by decide +kernel
private theorem root_sign_5 : (∀ i, 0 ≤ coordinates 5 i) ∨ (∀ i, coordinates 5 i ≤ 0) := by decide +kernel
private theorem root_sign_6 : (∀ i, 0 ≤ coordinates 6 i) ∨ (∀ i, coordinates 6 i ≤ 0) := by decide +kernel
private theorem root_sign_7 : (∀ i, 0 ≤ coordinates 7 i) ∨ (∀ i, coordinates 7 i ≤ 0) := by decide +kernel
private theorem root_sign_8 : (∀ i, 0 ≤ coordinates 8 i) ∨ (∀ i, coordinates 8 i ≤ 0) := by decide +kernel
private theorem root_sign_9 : (∀ i, 0 ≤ coordinates 9 i) ∨ (∀ i, coordinates 9 i ≤ 0) := by decide +kernel
private theorem root_sign_10 : (∀ i, 0 ≤ coordinates 10 i) ∨ (∀ i, coordinates 10 i ≤ 0) := by decide +kernel
private theorem root_sign_11 : (∀ i, 0 ≤ coordinates 11 i) ∨ (∀ i, coordinates 11 i ≤ 0) := by decide +kernel
theorem root_sign : ∀ a : Root, (∀ i, 0 ≤ coordinates a i) ∨ (∀ i, coordinates a i ≤ 0) := by
  intro a
  fin_cases a
  · exact root_sign_0
  · exact root_sign_1
  · exact root_sign_2
  · exact root_sign_3
  · exact root_sign_4
  · exact root_sign_5
  · exact root_sign_6
  · exact root_sign_7
  · exact root_sign_8
  · exact root_sign_9
  · exact root_sign_10
  · exact root_sign_11
private theorem coroot_sign_0 : (∀ i, 0 ≤ corootCoefficientCoordinates 0 i) ∨ (∀ i, corootCoefficientCoordinates 0 i ≤ 0) := by decide +kernel
private theorem coroot_sign_1 : (∀ i, 0 ≤ corootCoefficientCoordinates 1 i) ∨ (∀ i, corootCoefficientCoordinates 1 i ≤ 0) := by decide +kernel
private theorem coroot_sign_2 : (∀ i, 0 ≤ corootCoefficientCoordinates 2 i) ∨ (∀ i, corootCoefficientCoordinates 2 i ≤ 0) := by decide +kernel
private theorem coroot_sign_3 : (∀ i, 0 ≤ corootCoefficientCoordinates 3 i) ∨ (∀ i, corootCoefficientCoordinates 3 i ≤ 0) := by decide +kernel
private theorem coroot_sign_4 : (∀ i, 0 ≤ corootCoefficientCoordinates 4 i) ∨ (∀ i, corootCoefficientCoordinates 4 i ≤ 0) := by decide +kernel
private theorem coroot_sign_5 : (∀ i, 0 ≤ corootCoefficientCoordinates 5 i) ∨ (∀ i, corootCoefficientCoordinates 5 i ≤ 0) := by decide +kernel
private theorem coroot_sign_6 : (∀ i, 0 ≤ corootCoefficientCoordinates 6 i) ∨ (∀ i, corootCoefficientCoordinates 6 i ≤ 0) := by decide +kernel
private theorem coroot_sign_7 : (∀ i, 0 ≤ corootCoefficientCoordinates 7 i) ∨ (∀ i, corootCoefficientCoordinates 7 i ≤ 0) := by decide +kernel
private theorem coroot_sign_8 : (∀ i, 0 ≤ corootCoefficientCoordinates 8 i) ∨ (∀ i, corootCoefficientCoordinates 8 i ≤ 0) := by decide +kernel
private theorem coroot_sign_9 : (∀ i, 0 ≤ corootCoefficientCoordinates 9 i) ∨ (∀ i, corootCoefficientCoordinates 9 i ≤ 0) := by decide +kernel
private theorem coroot_sign_10 : (∀ i, 0 ≤ corootCoefficientCoordinates 10 i) ∨ (∀ i, corootCoefficientCoordinates 10 i ≤ 0) := by decide +kernel
private theorem coroot_sign_11 : (∀ i, 0 ≤ corootCoefficientCoordinates 11 i) ∨ (∀ i, corootCoefficientCoordinates 11 i ≤ 0) := by decide +kernel
theorem coroot_sign : ∀ a : Root, (∀ i, 0 ≤ corootCoefficientCoordinates a i) ∨ (∀ i, corootCoefficientCoordinates a i ≤ 0) := by
  intro a
  fin_cases a
  · exact coroot_sign_0
  · exact coroot_sign_1
  · exact coroot_sign_2
  · exact coroot_sign_3
  · exact coroot_sign_4
  · exact coroot_sign_5
  · exact coroot_sign_6
  · exact coroot_sign_7
  · exact coroot_sign_8
  · exact coroot_sign_9
  · exact coroot_sign_10
  · exact coroot_sign_11
theorem simple_coordinates : ∀ i : Fin 2, coordinates (simpleIndex i) = Pi.single i 1 := by decide +kernel
theorem simple_coroot_coefficients : ∀ i : Fin 2, corootCoefficientCoordinates (simpleIndex i) = Pi.single i 1 := by decide +kernel
theorem simple_dual_coordinates : ∀ i j : Fin 2, dualCoordinates (simpleIndex i) j = cartan j i := by decide +kernel
end Atlas.Chevalley.G2Table
