import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.Tactic.FinCases

/-! Integral E7 root coordinates with kernel-checked reflection and word certificates. -/

namespace Atlas.Chevalley.E7Table
set_option maxRecDepth 32768
/- Generated candidate root data; mathematical claims below require kernel replay. -/
abbrev Root := Fin 126
abbrev Vector := Fin 7 → ℤ
def coordinateTable : Array (Array ℤ) :=
  #[#[1,0,0,0,0,0,0],
    #[-1,0,0,0,0,0,0],
    #[1,0,1,0,0,0,0],
    #[-1,0,-1,0,0,0,0],
    #[0,0,1,0,0,0,0],
    #[1,0,1,1,0,0,0],
    #[0,0,-1,0,0,0,0],
    #[-1,0,-1,-1,0,0,0],
    #[0,0,1,1,0,0,0],
    #[1,1,1,1,0,0,0],
    #[1,0,1,1,1,0,0],
    #[0,0,-1,-1,0,0,0],
    #[-1,-1,-1,-1,0,0,0],
    #[-1,0,-1,-1,-1,0,0],
    #[0,1,1,1,0,0,0],
    #[0,0,0,1,0,0,0],
    #[0,0,1,1,1,0,0],
    #[1,1,1,1,1,0,0],
    #[1,0,1,1,1,1,0],
    #[0,-1,-1,-1,0,0,0],
    #[0,0,0,-1,0,0,0],
    #[0,0,-1,-1,-1,0,0],
    #[-1,-1,-1,-1,-1,0,0],
    #[-1,0,-1,-1,-1,-1,0],
    #[0,1,0,1,0,0,0],
    #[0,1,1,1,1,0,0],
    #[0,0,0,1,1,0,0],
    #[0,0,1,1,1,1,0],
    #[1,1,1,2,1,0,0],
    #[1,1,1,1,1,1,0],
    #[1,0,1,1,1,1,1],
    #[0,-1,0,-1,0,0,0],
    #[0,-1,-1,-1,-1,0,0],
    #[0,0,0,-1,-1,0,0],
    #[0,0,-1,-1,-1,-1,0],
    #[-1,-1,-1,-2,-1,0,0],
    #[-1,-1,-1,-1,-1,-1,0],
    #[-1,0,-1,-1,-1,-1,-1],
    #[0,1,0,0,0,0,0],
    #[0,1,0,1,1,0,0],
    #[0,1,1,2,1,0,0],
    #[0,1,1,1,1,1,0],
    #[0,0,0,0,1,0,0],
    #[0,0,0,1,1,1,0],
    #[0,0,1,1,1,1,1],
    #[1,1,2,2,1,0,0],
    #[1,1,1,2,1,1,0],
    #[1,1,1,1,1,1,1],
    #[0,-1,0,0,0,0,0],
    #[0,-1,0,-1,-1,0,0],
    #[0,-1,-1,-2,-1,0,0],
    #[0,-1,-1,-1,-1,-1,0],
    #[0,0,0,0,-1,0,0],
    #[0,0,0,-1,-1,-1,0],
    #[0,0,-1,-1,-1,-1,-1],
    #[-1,-1,-2,-2,-1,0,0],
    #[-1,-1,-1,-2,-1,-1,0],
    #[-1,-1,-1,-1,-1,-1,-1],
    #[0,1,0,1,1,1,0],
    #[0,1,1,2,1,1,0],
    #[0,1,1,1,1,1,1],
    #[0,0,0,0,1,1,0],
    #[0,0,0,1,1,1,1],
    #[1,1,2,2,1,1,0],
    #[1,1,1,2,2,1,0],
    #[1,1,1,2,1,1,1],
    #[0,-1,0,-1,-1,-1,0],
    #[0,-1,-1,-2,-1,-1,0],
    #[0,-1,-1,-1,-1,-1,-1],
    #[0,0,0,0,-1,-1,0],
    #[0,0,0,-1,-1,-1,-1],
    #[-1,-1,-2,-2,-1,-1,0],
    #[-1,-1,-1,-2,-2,-1,0],
    #[-1,-1,-1,-2,-1,-1,-1],
    #[0,1,0,1,1,1,1],
    #[0,1,1,2,2,1,0],
    #[0,1,1,2,1,1,1],
    #[0,0,0,0,0,1,0],
    #[0,0,0,0,1,1,1],
    #[1,1,2,2,2,1,0],
    #[1,1,2,2,1,1,1],
    #[1,1,1,2,2,1,1],
    #[0,-1,0,-1,-1,-1,-1],
    #[0,-1,-1,-2,-2,-1,0],
    #[0,-1,-1,-2,-1,-1,-1],
    #[0,0,0,0,0,-1,0],
    #[0,0,0,0,-1,-1,-1],
    #[-1,-1,-2,-2,-2,-1,0],
    #[-1,-1,-2,-2,-1,-1,-1],
    #[-1,-1,-1,-2,-2,-1,-1],
    #[0,1,1,2,2,1,1],
    #[0,0,0,0,0,1,1],
    #[1,1,2,3,2,1,0],
    #[1,1,2,2,2,1,1],
    #[1,1,1,2,2,2,1],
    #[0,-1,-1,-2,-2,-1,-1],
    #[0,0,0,0,0,-1,-1],
    #[-1,-1,-2,-3,-2,-1,0],
    #[-1,-1,-2,-2,-2,-1,-1],
    #[-1,-1,-1,-2,-2,-2,-1],
    #[0,1,1,2,2,2,1],
    #[0,0,0,0,0,0,1],
    #[1,2,2,3,2,1,0],
    #[1,1,2,3,2,1,1],
    #[1,1,2,2,2,2,1],
    #[0,-1,-1,-2,-2,-2,-1],
    #[0,0,0,0,0,0,-1],
    #[-1,-2,-2,-3,-2,-1,0],
    #[-1,-1,-2,-3,-2,-1,-1],
    #[-1,-1,-2,-2,-2,-2,-1],
    #[1,2,2,3,2,1,1],
    #[1,1,2,3,2,2,1],
    #[-1,-2,-2,-3,-2,-1,-1],
    #[-1,-1,-2,-3,-2,-2,-1],
    #[1,2,2,3,2,2,1],
    #[1,1,2,3,3,2,1],
    #[-1,-2,-2,-3,-2,-2,-1],
    #[-1,-1,-2,-3,-3,-2,-1],
    #[1,2,2,3,3,2,1],
    #[-1,-2,-2,-3,-3,-2,-1],
    #[1,2,2,4,3,2,1],
    #[-1,-2,-2,-4,-3,-2,-1],
    #[1,2,3,4,3,2,1],
    #[-1,-2,-3,-4,-3,-2,-1],
    #[2,2,3,4,3,2,1],
    #[-2,-2,-3,-4,-3,-2,-1]]
def coordinates (a : Root) (i : Fin 7) : ℤ := (coordinateTable[a.val]!)[i.val]!
def decode (x : Vector) : Root := if x 0 = (-2 : ℤ) then 125 else if x 0 = (-1 : ℤ) then if x 1 = (-2 : ℤ) then if x 2 = (-3 : ℤ) then 123 else if x 3 = (-4 : ℤ) then 121 else if x 4 = (-3 : ℤ) then 119 else if x 5 = (-2 : ℤ) then 116 else if x 6 = (-1 : ℤ) then 112 else 107 else if x 1 = (-1 : ℤ) then if x 2 = (-2 : ℤ) then if x 3 = (-3 : ℤ) then if x 4 = (-3 : ℤ) then 117 else if x 5 = (-2 : ℤ) then 113 else if x 6 = (-1 : ℤ) then 108 else 97 else if x 4 = (-2 : ℤ) then if x 5 = (-2 : ℤ) then 109 else if x 6 = (-1 : ℤ) then 98 else 87 else if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 88 else 71 else 55 else if x 3 = (-2 : ℤ) then if x 4 = (-2 : ℤ) then if x 5 = (-2 : ℤ) then 99 else if x 6 = (-1 : ℤ) then 89 else 72 else if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 73 else 56 else 35 else if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 57 else 36 else 22 else 12 else if x 2 = (-1 : ℤ) then if x 3 = (-1 : ℤ) then if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 37 else 23 else 13 else 7 else 3 else 1 else if x 0 = (0 : ℤ) then if x 1 = (-1 : ℤ) then if x 2 = (-1 : ℤ) then if x 3 = (-2 : ℤ) then if x 4 = (-2 : ℤ) then if x 5 = (-2 : ℤ) then 105 else if x 6 = (-1 : ℤ) then 95 else 83 else if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 84 else 67 else 50 else if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 68 else 51 else 32 else 19 else if x 3 = (-1 : ℤ) then if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 82 else 66 else 49 else 31 else 48 else if x 1 = (0 : ℤ) then if x 2 = (-1 : ℤ) then if x 3 = (-1 : ℤ) then if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 54 else 34 else 21 else 11 else 6 else if x 2 = (0 : ℤ) then if x 3 = (-1 : ℤ) then if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 70 else 53 else 33 else 20 else if x 3 = (0 : ℤ) then if x 4 = (-1 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 86 else 69 else 52 else if x 4 = (0 : ℤ) then if x 5 = (-1 : ℤ) then if x 6 = (-1 : ℤ) then 96 else 85 else if x 5 = (0 : ℤ) then if x 6 = (-1 : ℤ) then 106 else 101 else if x 6 = (0 : ℤ) then 77 else 91 else if x 5 = (0 : ℤ) then 42 else if x 6 = (0 : ℤ) then 61 else 78 else if x 4 = (0 : ℤ) then 15 else if x 5 = (0 : ℤ) then 26 else if x 6 = (0 : ℤ) then 43 else 62 else if x 3 = (0 : ℤ) then 4 else if x 4 = (0 : ℤ) then 8 else if x 5 = (0 : ℤ) then 16 else if x 6 = (0 : ℤ) then 27 else 44 else if x 2 = (0 : ℤ) then if x 3 = (0 : ℤ) then 38 else if x 4 = (0 : ℤ) then 24 else if x 5 = (0 : ℤ) then 39 else if x 6 = (0 : ℤ) then 58 else 74 else if x 3 = (1 : ℤ) then if x 4 = (0 : ℤ) then 14 else if x 5 = (0 : ℤ) then 25 else if x 6 = (0 : ℤ) then 41 else 60 else if x 4 = (1 : ℤ) then if x 5 = (0 : ℤ) then 40 else if x 6 = (0 : ℤ) then 59 else 76 else if x 5 = (1 : ℤ) then if x 6 = (0 : ℤ) then 75 else 90 else 100 else if x 0 = (1 : ℤ) then if x 1 = (0 : ℤ) then if x 2 = (0 : ℤ) then 0 else if x 3 = (0 : ℤ) then 2 else if x 4 = (0 : ℤ) then 5 else if x 5 = (0 : ℤ) then 10 else if x 6 = (0 : ℤ) then 18 else 30 else if x 1 = (1 : ℤ) then if x 2 = (1 : ℤ) then if x 3 = (1 : ℤ) then if x 4 = (0 : ℤ) then 9 else if x 5 = (0 : ℤ) then 17 else if x 6 = (0 : ℤ) then 29 else 47 else if x 4 = (1 : ℤ) then if x 5 = (0 : ℤ) then 28 else if x 6 = (0 : ℤ) then 46 else 65 else if x 5 = (1 : ℤ) then if x 6 = (0 : ℤ) then 64 else 81 else 94 else if x 3 = (2 : ℤ) then if x 4 = (1 : ℤ) then if x 5 = (0 : ℤ) then 45 else if x 6 = (0 : ℤ) then 63 else 80 else if x 5 = (1 : ℤ) then if x 6 = (0 : ℤ) then 79 else 93 else 104 else if x 4 = (2 : ℤ) then if x 5 = (1 : ℤ) then if x 6 = (0 : ℤ) then 92 else 103 else 111 else 115 else if x 2 = (2 : ℤ) then if x 3 = (3 : ℤ) then if x 4 = (2 : ℤ) then if x 5 = (1 : ℤ) then if x 6 = (0 : ℤ) then 102 else 110 else 114 else 118 else 120 else 122 else 124
def simpleIndex (i : Fin 7) : Root := Fin.ofNat 126 (#[0,38,4,15,42,77,101][i.val]!)
def transitionTable : Array (Array ℕ) :=
  #[#[1,0,4,6,2,8,3,11,5,14,16,7,19,21,9,15,10,25,27,12,20,13,32,34,24,17,26,18,40,41,44,31,22,33,23,50,51,54,38,39,28,29,42,43,30,45,59,60,48,49,35,36,52,53,37,55,67,68,58,46,47,61,62,63,75,76,66,56,57,69,70,71,83,84,74,64,65,77,78,79,80,90,82,72,73,85,86,87,88,95,81,91,92,93,100,89,96,97,98,105,94,101,102,103,104,99,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,124,125,122,123],
    #[0,1,2,3,4,9,6,12,14,5,17,19,7,22,8,24,25,10,29,11,31,32,13,36,15,16,39,41,28,18,47,20,21,49,51,35,23,57,48,26,40,27,42,58,60,45,46,30,38,33,50,34,52,66,68,55,56,37,43,59,44,61,74,63,64,65,53,67,54,69,82,71,72,73,62,75,76,77,78,79,80,81,70,83,84,85,86,87,88,89,90,91,102,93,94,95,96,107,98,99,100,101,92,110,104,105,106,97,112,109,103,114,108,116,111,118,113,119,115,117,120,121,122,123,124,125],
    #[2,3,0,1,6,5,4,7,15,9,10,20,12,13,24,8,26,17,18,31,11,33,22,23,14,39,16,43,45,29,30,19,49,21,53,55,36,37,38,25,40,58,42,27,62,28,63,47,48,32,50,66,52,34,70,35,71,57,41,59,74,61,44,46,79,80,51,67,82,69,54,56,87,88,60,75,76,77,78,64,65,93,68,83,84,85,86,72,73,98,90,91,92,81,104,95,96,97,89,109,100,101,102,103,94,105,106,107,108,99,110,111,112,113,114,115,116,117,118,119,122,123,120,121,124,125],
    #[0,1,5,7,8,2,11,3,4,9,10,6,12,13,14,20,16,28,18,19,15,21,35,23,38,40,42,27,17,46,30,48,50,52,34,22,56,37,24,39,25,59,26,61,44,45,29,65,31,49,32,67,33,69,54,55,36,73,58,41,76,43,78,63,64,47,66,51,84,53,86,71,72,57,74,75,60,77,62,92,80,81,82,83,68,85,70,97,88,89,90,91,79,103,94,95,96,87,108,99,100,101,102,93,111,105,106,107,98,113,110,104,112,109,114,115,116,117,120,121,118,119,122,123,124,125],
    #[0,1,2,3,4,10,6,13,16,17,5,21,22,7,25,26,8,9,18,32,33,11,12,23,39,14,15,27,28,29,30,49,19,20,34,35,36,37,38,24,40,41,52,43,44,45,64,47,48,31,50,51,42,53,54,55,72,57,58,75,60,77,62,79,46,81,66,83,68,85,70,87,56,89,74,59,90,61,91,63,93,65,82,67,95,69,96,71,98,73,76,78,92,80,94,84,86,97,88,99,100,101,102,103,104,105,106,107,108,109,110,115,112,117,118,111,119,113,114,116,120,121,122,123,124,125],
    #[0,1,2,3,4,5,6,7,8,9,18,11,12,23,14,15,27,29,10,19,20,34,36,13,24,41,43,16,46,17,30,31,51,53,21,56,22,37,38,58,59,25,61,26,44,63,28,47,48,66,67,32,69,33,54,71,35,57,39,40,60,42,62,45,64,65,49,50,68,52,70,55,72,73,74,75,76,85,78,79,80,94,82,83,84,77,86,87,88,99,100,101,92,104,81,105,106,97,109,89,90,91,102,111,93,95,96,107,113,98,114,103,116,108,110,115,112,117,118,119,120,121,122,123,124,125],
    #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,30,19,20,21,22,37,24,25,26,44,28,47,18,31,32,33,54,35,57,23,38,39,40,60,42,62,27,45,65,29,48,49,50,68,52,70,34,55,73,36,74,76,41,78,43,80,81,46,82,84,51,86,53,88,89,56,58,90,59,91,61,93,63,64,66,95,67,96,69,98,71,72,75,77,103,79,94,83,85,108,87,99,100,106,110,92,104,105,101,112,97,109,102,111,107,113,114,115,116,117,118,119,120,121,122,123,124,125]]
def simpleReflectionIndex (i : Fin 7) (a : Root) : Root := Fin.ofNat 126 ((transitionTable[i.val]!)[a.val]!)
def wordTable : Array (List (Fin 7)) :=
  #[[],
    [0],
    [2],
    [0,2],
    [2,0],
    [2,3],
    [0,2,0],
    [0,2,3],
    [2,0,3],
    [2,3,1],
    [2,3,4],
    [0,2,0,3],
    [0,2,3,1],
    [0,2,3,4],
    [2,0,3,1],
    [2,0,3,2],
    [2,0,3,4],
    [2,3,1,4],
    [2,3,4,5],
    [0,2,0,3,1],
    [0,2,0,3,2],
    [0,2,0,3,4],
    [0,2,3,1,4],
    [0,2,3,4,5],
    [2,0,3,1,2],
    [2,0,3,1,4],
    [2,0,3,2,4],
    [2,0,3,4,5],
    [2,3,1,4,3],
    [2,3,1,4,5],
    [2,3,4,5,6],
    [0,2,0,3,1,2],
    [0,2,0,3,1,4],
    [0,2,0,3,2,4],
    [0,2,0,3,4,5],
    [0,2,3,1,4,3],
    [0,2,3,1,4,5],
    [0,2,3,4,5,6],
    [2,0,3,1,2,3],
    [2,0,3,1,2,4],
    [2,0,3,1,4,3],
    [2,0,3,1,4,5],
    [2,0,3,2,4,3],
    [2,0,3,2,4,5],
    [2,0,3,4,5,6],
    [2,3,1,4,3,2],
    [2,3,1,4,3,5],
    [2,3,1,4,5,6],
    [0,2,0,3,1,2,3],
    [0,2,0,3,1,2,4],
    [0,2,0,3,1,4,3],
    [0,2,0,3,1,4,5],
    [0,2,0,3,2,4,3],
    [0,2,0,3,2,4,5],
    [0,2,0,3,4,5,6],
    [0,2,3,1,4,3,2],
    [0,2,3,1,4,3,5],
    [0,2,3,1,4,5,6],
    [2,0,3,1,2,4,5],
    [2,0,3,1,4,3,5],
    [2,0,3,1,4,5,6],
    [2,0,3,2,4,3,5],
    [2,0,3,2,4,5,6],
    [2,3,1,4,3,2,5],
    [2,3,1,4,3,5,4],
    [2,3,1,4,3,5,6],
    [0,2,0,3,1,2,4,5],
    [0,2,0,3,1,4,3,5],
    [0,2,0,3,1,4,5,6],
    [0,2,0,3,2,4,3,5],
    [0,2,0,3,2,4,5,6],
    [0,2,3,1,4,3,2,5],
    [0,2,3,1,4,3,5,4],
    [0,2,3,1,4,3,5,6],
    [2,0,3,1,2,4,5,6],
    [2,0,3,1,4,3,5,4],
    [2,0,3,1,4,3,5,6],
    [2,0,3,2,4,3,5,4],
    [2,0,3,2,4,3,5,6],
    [2,3,1,4,3,2,5,4],
    [2,3,1,4,3,2,5,6],
    [2,3,1,4,3,5,4,6],
    [0,2,0,3,1,2,4,5,6],
    [0,2,0,3,1,4,3,5,4],
    [0,2,0,3,1,4,3,5,6],
    [0,2,0,3,2,4,3,5,4],
    [0,2,0,3,2,4,3,5,6],
    [0,2,3,1,4,3,2,5,4],
    [0,2,3,1,4,3,2,5,6],
    [0,2,3,1,4,3,5,4,6],
    [2,0,3,1,4,3,5,4,6],
    [2,0,3,2,4,3,5,4,6],
    [2,3,1,4,3,2,5,4,3],
    [2,3,1,4,3,2,5,4,6],
    [2,3,1,4,3,5,4,6,5],
    [0,2,0,3,1,4,3,5,4,6],
    [0,2,0,3,2,4,3,5,4,6],
    [0,2,3,1,4,3,2,5,4,3],
    [0,2,3,1,4,3,2,5,4,6],
    [0,2,3,1,4,3,5,4,6,5],
    [2,0,3,1,4,3,5,4,6,5],
    [2,0,3,2,4,3,5,4,6,5],
    [2,3,1,4,3,2,5,4,3,1],
    [2,3,1,4,3,2,5,4,3,6],
    [2,3,1,4,3,2,5,4,6,5],
    [0,2,0,3,1,4,3,5,4,6,5],
    [0,2,0,3,2,4,3,5,4,6,5],
    [0,2,3,1,4,3,2,5,4,3,1],
    [0,2,3,1,4,3,2,5,4,3,6],
    [0,2,3,1,4,3,2,5,4,6,5],
    [2,3,1,4,3,2,5,4,3,1,6],
    [2,3,1,4,3,2,5,4,3,6,5],
    [0,2,3,1,4,3,2,5,4,3,1,6],
    [0,2,3,1,4,3,2,5,4,3,6,5],
    [2,3,1,4,3,2,5,4,3,1,6,5],
    [2,3,1,4,3,2,5,4,3,6,5,4],
    [0,2,3,1,4,3,2,5,4,3,1,6,5],
    [0,2,3,1,4,3,2,5,4,3,6,5,4],
    [2,3,1,4,3,2,5,4,3,1,6,5,4],
    [0,2,3,1,4,3,2,5,4,3,1,6,5,4],
    [2,3,1,4,3,2,5,4,3,1,6,5,4,3],
    [0,2,3,1,4,3,2,5,4,3,1,6,5,4,3],
    [2,3,1,4,3,2,5,4,3,1,6,5,4,3,2],
    [0,2,3,1,4,3,2,5,4,3,1,6,5,4,3,2],
    [2,3,1,4,3,2,5,4,3,1,6,5,4,3,2,0],
    [0,2,3,1,4,3,2,5,4,3,1,6,5,4,3,2,0]]
def rootWord (a : Root) : List (Fin 7) := wordTable[a.val]!
def parent (a : Root) : Root := Fin.ofNat 126 (#[0,0,0,1,2,2,3,3,4,5,5,6,7,7,8,8,8,9,10,11,11,11,12,13,14,14,15,16,17,17,18,19,19,20,21,22,22,23,24,24,25,25,26,26,27,28,28,29,31,31,32,32,33,33,34,35,35,36,39,40,41,42,43,45,46,46,49,50,51,52,53,55,56,56,58,59,59,61,61,63,63,64,66,67,67,69,69,71,71,72,75,77,79,79,81,83,85,87,87,89,90,91,92,92,93,95,96,97,97,98,102,103,107,108,110,111,112,113,114,116,118,119,120,121,122,123][a.val]!)
def lastStep (a : Root) : Fin 7 := Fin.ofNat 7 (#[0,0,2,2,0,3,0,3,3,1,4,3,1,4,1,2,4,4,5,1,2,4,4,5,2,4,4,5,3,5,6,2,4,4,5,3,5,6,3,4,3,5,3,5,6,2,5,6,3,4,3,5,3,5,6,2,5,6,5,5,6,5,6,5,4,6,5,5,6,5,6,5,4,6,6,4,6,4,6,4,6,6,6,4,6,4,6,4,6,6,6,6,3,6,5,6,6,3,6,5,5,5,1,6,5,5,5,1,6,5,6,5,6,5,5,4,5,4,4,4,3,3,2,2,0,0][a.val]!)
def pair (x y : Vector) : ℤ := ∑ i, ∑ j, x i * CartanMatrix.E 7 i j * y j
def reflect (i : Fin 7) (x : Vector) : Vector :=
  Function.update x i (x i - ∑ j, CartanMatrix.E 7 i j * x j)
def wordAction : List (Fin 7) → Vector → Vector
  | [], x => x
  | i :: w, x => wordAction w (reflect i x)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_0 : decode (coordinates 0) = 0 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_1 : decode (coordinates 1) = 1 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_2 : decode (coordinates 2) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_3 : decode (coordinates 3) = 3 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_4 : decode (coordinates 4) = 4 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_5 : decode (coordinates 5) = 5 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_6 : decode (coordinates 6) = 6 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_7 : decode (coordinates 7) = 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_8 : decode (coordinates 8) = 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_9 : decode (coordinates 9) = 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_10 : decode (coordinates 10) = 10 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_11 : decode (coordinates 11) = 11 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_12 : decode (coordinates 12) = 12 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_13 : decode (coordinates 13) = 13 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_14 : decode (coordinates 14) = 14 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_15 : decode (coordinates 15) = 15 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_16 : decode (coordinates 16) = 16 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_17 : decode (coordinates 17) = 17 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_18 : decode (coordinates 18) = 18 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_19 : decode (coordinates 19) = 19 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_20 : decode (coordinates 20) = 20 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_21 : decode (coordinates 21) = 21 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_22 : decode (coordinates 22) = 22 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_23 : decode (coordinates 23) = 23 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_24 : decode (coordinates 24) = 24 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_25 : decode (coordinates 25) = 25 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_26 : decode (coordinates 26) = 26 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_27 : decode (coordinates 27) = 27 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_28 : decode (coordinates 28) = 28 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_29 : decode (coordinates 29) = 29 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_30 : decode (coordinates 30) = 30 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_31 : decode (coordinates 31) = 31 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_32 : decode (coordinates 32) = 32 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_33 : decode (coordinates 33) = 33 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_34 : decode (coordinates 34) = 34 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_35 : decode (coordinates 35) = 35 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_36 : decode (coordinates 36) = 36 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_37 : decode (coordinates 37) = 37 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_38 : decode (coordinates 38) = 38 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_39 : decode (coordinates 39) = 39 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_40 : decode (coordinates 40) = 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_41 : decode (coordinates 41) = 41 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_42 : decode (coordinates 42) = 42 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_43 : decode (coordinates 43) = 43 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_44 : decode (coordinates 44) = 44 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_45 : decode (coordinates 45) = 45 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_46 : decode (coordinates 46) = 46 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_47 : decode (coordinates 47) = 47 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_48 : decode (coordinates 48) = 48 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_49 : decode (coordinates 49) = 49 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_50 : decode (coordinates 50) = 50 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_51 : decode (coordinates 51) = 51 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_52 : decode (coordinates 52) = 52 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_53 : decode (coordinates 53) = 53 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_54 : decode (coordinates 54) = 54 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_55 : decode (coordinates 55) = 55 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_56 : decode (coordinates 56) = 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_57 : decode (coordinates 57) = 57 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_58 : decode (coordinates 58) = 58 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_59 : decode (coordinates 59) = 59 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_60 : decode (coordinates 60) = 60 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_61 : decode (coordinates 61) = 61 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_62 : decode (coordinates 62) = 62 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_63 : decode (coordinates 63) = 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_64 : decode (coordinates 64) = 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_65 : decode (coordinates 65) = 65 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_66 : decode (coordinates 66) = 66 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_67 : decode (coordinates 67) = 67 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_68 : decode (coordinates 68) = 68 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_69 : decode (coordinates 69) = 69 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_70 : decode (coordinates 70) = 70 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_71 : decode (coordinates 71) = 71 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_72 : decode (coordinates 72) = 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_73 : decode (coordinates 73) = 73 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_74 : decode (coordinates 74) = 74 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_75 : decode (coordinates 75) = 75 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_76 : decode (coordinates 76) = 76 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_77 : decode (coordinates 77) = 77 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_78 : decode (coordinates 78) = 78 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_79 : decode (coordinates 79) = 79 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_80 : decode (coordinates 80) = 80 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_81 : decode (coordinates 81) = 81 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_82 : decode (coordinates 82) = 82 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_83 : decode (coordinates 83) = 83 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_84 : decode (coordinates 84) = 84 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_85 : decode (coordinates 85) = 85 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_86 : decode (coordinates 86) = 86 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_87 : decode (coordinates 87) = 87 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_88 : decode (coordinates 88) = 88 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_89 : decode (coordinates 89) = 89 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_90 : decode (coordinates 90) = 90 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_91 : decode (coordinates 91) = 91 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_92 : decode (coordinates 92) = 92 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_93 : decode (coordinates 93) = 93 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_94 : decode (coordinates 94) = 94 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_95 : decode (coordinates 95) = 95 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_96 : decode (coordinates 96) = 96 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_97 : decode (coordinates 97) = 97 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_98 : decode (coordinates 98) = 98 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_99 : decode (coordinates 99) = 99 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_100 : decode (coordinates 100) = 100 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_101 : decode (coordinates 101) = 101 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_102 : decode (coordinates 102) = 102 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_103 : decode (coordinates 103) = 103 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_104 : decode (coordinates 104) = 104 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_105 : decode (coordinates 105) = 105 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_106 : decode (coordinates 106) = 106 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_107 : decode (coordinates 107) = 107 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_108 : decode (coordinates 108) = 108 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_109 : decode (coordinates 109) = 109 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_110 : decode (coordinates 110) = 110 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_111 : decode (coordinates 111) = 111 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_112 : decode (coordinates 112) = 112 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_113 : decode (coordinates 113) = 113 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_114 : decode (coordinates 114) = 114 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_115 : decode (coordinates 115) = 115 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_116 : decode (coordinates 116) = 116 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_117 : decode (coordinates 117) = 117 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_118 : decode (coordinates 118) = 118 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_119 : decode (coordinates 119) = 119 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_120 : decode (coordinates 120) = 120 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_121 : decode (coordinates 121) = 121 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_122 : decode (coordinates 122) = 122 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_123 : decode (coordinates 123) = 123 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_124 : decode (coordinates 124) = 124 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem decode_coordinates_125 : decode (coordinates 125) = 125 := by decide +kernel
theorem decode_coordinates : ∀ a : Root, decode (coordinates a) = a := by
  intro a
  fin_cases a
  · exact decode_coordinates_0
  · exact decode_coordinates_1
  · exact decode_coordinates_2
  · exact decode_coordinates_3
  · exact decode_coordinates_4
  · exact decode_coordinates_5
  · exact decode_coordinates_6
  · exact decode_coordinates_7
  · exact decode_coordinates_8
  · exact decode_coordinates_9
  · exact decode_coordinates_10
  · exact decode_coordinates_11
  · exact decode_coordinates_12
  · exact decode_coordinates_13
  · exact decode_coordinates_14
  · exact decode_coordinates_15
  · exact decode_coordinates_16
  · exact decode_coordinates_17
  · exact decode_coordinates_18
  · exact decode_coordinates_19
  · exact decode_coordinates_20
  · exact decode_coordinates_21
  · exact decode_coordinates_22
  · exact decode_coordinates_23
  · exact decode_coordinates_24
  · exact decode_coordinates_25
  · exact decode_coordinates_26
  · exact decode_coordinates_27
  · exact decode_coordinates_28
  · exact decode_coordinates_29
  · exact decode_coordinates_30
  · exact decode_coordinates_31
  · exact decode_coordinates_32
  · exact decode_coordinates_33
  · exact decode_coordinates_34
  · exact decode_coordinates_35
  · exact decode_coordinates_36
  · exact decode_coordinates_37
  · exact decode_coordinates_38
  · exact decode_coordinates_39
  · exact decode_coordinates_40
  · exact decode_coordinates_41
  · exact decode_coordinates_42
  · exact decode_coordinates_43
  · exact decode_coordinates_44
  · exact decode_coordinates_45
  · exact decode_coordinates_46
  · exact decode_coordinates_47
  · exact decode_coordinates_48
  · exact decode_coordinates_49
  · exact decode_coordinates_50
  · exact decode_coordinates_51
  · exact decode_coordinates_52
  · exact decode_coordinates_53
  · exact decode_coordinates_54
  · exact decode_coordinates_55
  · exact decode_coordinates_56
  · exact decode_coordinates_57
  · exact decode_coordinates_58
  · exact decode_coordinates_59
  · exact decode_coordinates_60
  · exact decode_coordinates_61
  · exact decode_coordinates_62
  · exact decode_coordinates_63
  · exact decode_coordinates_64
  · exact decode_coordinates_65
  · exact decode_coordinates_66
  · exact decode_coordinates_67
  · exact decode_coordinates_68
  · exact decode_coordinates_69
  · exact decode_coordinates_70
  · exact decode_coordinates_71
  · exact decode_coordinates_72
  · exact decode_coordinates_73
  · exact decode_coordinates_74
  · exact decode_coordinates_75
  · exact decode_coordinates_76
  · exact decode_coordinates_77
  · exact decode_coordinates_78
  · exact decode_coordinates_79
  · exact decode_coordinates_80
  · exact decode_coordinates_81
  · exact decode_coordinates_82
  · exact decode_coordinates_83
  · exact decode_coordinates_84
  · exact decode_coordinates_85
  · exact decode_coordinates_86
  · exact decode_coordinates_87
  · exact decode_coordinates_88
  · exact decode_coordinates_89
  · exact decode_coordinates_90
  · exact decode_coordinates_91
  · exact decode_coordinates_92
  · exact decode_coordinates_93
  · exact decode_coordinates_94
  · exact decode_coordinates_95
  · exact decode_coordinates_96
  · exact decode_coordinates_97
  · exact decode_coordinates_98
  · exact decode_coordinates_99
  · exact decode_coordinates_100
  · exact decode_coordinates_101
  · exact decode_coordinates_102
  · exact decode_coordinates_103
  · exact decode_coordinates_104
  · exact decode_coordinates_105
  · exact decode_coordinates_106
  · exact decode_coordinates_107
  · exact decode_coordinates_108
  · exact decode_coordinates_109
  · exact decode_coordinates_110
  · exact decode_coordinates_111
  · exact decode_coordinates_112
  · exact decode_coordinates_113
  · exact decode_coordinates_114
  · exact decode_coordinates_115
  · exact decode_coordinates_116
  · exact decode_coordinates_117
  · exact decode_coordinates_118
  · exact decode_coordinates_119
  · exact decode_coordinates_120
  · exact decode_coordinates_121
  · exact decode_coordinates_122
  · exact decode_coordinates_123
  · exact decode_coordinates_124
  · exact decode_coordinates_125
#check decode_coordinates
theorem coordinates_injective : Function.Injective coordinates := Function.LeftInverse.injective decode_coordinates
#check coordinates_injective
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_0 : pair (coordinates 0) (coordinates 0) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_1 : pair (coordinates 1) (coordinates 1) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_2 : pair (coordinates 2) (coordinates 2) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_3 : pair (coordinates 3) (coordinates 3) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_4 : pair (coordinates 4) (coordinates 4) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_5 : pair (coordinates 5) (coordinates 5) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_6 : pair (coordinates 6) (coordinates 6) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_7 : pair (coordinates 7) (coordinates 7) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_8 : pair (coordinates 8) (coordinates 8) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_9 : pair (coordinates 9) (coordinates 9) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_10 : pair (coordinates 10) (coordinates 10) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_11 : pair (coordinates 11) (coordinates 11) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_12 : pair (coordinates 12) (coordinates 12) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_13 : pair (coordinates 13) (coordinates 13) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_14 : pair (coordinates 14) (coordinates 14) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_15 : pair (coordinates 15) (coordinates 15) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_16 : pair (coordinates 16) (coordinates 16) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_17 : pair (coordinates 17) (coordinates 17) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_18 : pair (coordinates 18) (coordinates 18) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_19 : pair (coordinates 19) (coordinates 19) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_20 : pair (coordinates 20) (coordinates 20) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_21 : pair (coordinates 21) (coordinates 21) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_22 : pair (coordinates 22) (coordinates 22) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_23 : pair (coordinates 23) (coordinates 23) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_24 : pair (coordinates 24) (coordinates 24) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_25 : pair (coordinates 25) (coordinates 25) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_26 : pair (coordinates 26) (coordinates 26) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_27 : pair (coordinates 27) (coordinates 27) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_28 : pair (coordinates 28) (coordinates 28) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_29 : pair (coordinates 29) (coordinates 29) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_30 : pair (coordinates 30) (coordinates 30) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_31 : pair (coordinates 31) (coordinates 31) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_32 : pair (coordinates 32) (coordinates 32) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_33 : pair (coordinates 33) (coordinates 33) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_34 : pair (coordinates 34) (coordinates 34) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_35 : pair (coordinates 35) (coordinates 35) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_36 : pair (coordinates 36) (coordinates 36) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_37 : pair (coordinates 37) (coordinates 37) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_38 : pair (coordinates 38) (coordinates 38) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_39 : pair (coordinates 39) (coordinates 39) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_40 : pair (coordinates 40) (coordinates 40) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_41 : pair (coordinates 41) (coordinates 41) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_42 : pair (coordinates 42) (coordinates 42) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_43 : pair (coordinates 43) (coordinates 43) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_44 : pair (coordinates 44) (coordinates 44) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_45 : pair (coordinates 45) (coordinates 45) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_46 : pair (coordinates 46) (coordinates 46) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_47 : pair (coordinates 47) (coordinates 47) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_48 : pair (coordinates 48) (coordinates 48) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_49 : pair (coordinates 49) (coordinates 49) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_50 : pair (coordinates 50) (coordinates 50) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_51 : pair (coordinates 51) (coordinates 51) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_52 : pair (coordinates 52) (coordinates 52) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_53 : pair (coordinates 53) (coordinates 53) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_54 : pair (coordinates 54) (coordinates 54) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_55 : pair (coordinates 55) (coordinates 55) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_56 : pair (coordinates 56) (coordinates 56) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_57 : pair (coordinates 57) (coordinates 57) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_58 : pair (coordinates 58) (coordinates 58) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_59 : pair (coordinates 59) (coordinates 59) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_60 : pair (coordinates 60) (coordinates 60) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_61 : pair (coordinates 61) (coordinates 61) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_62 : pair (coordinates 62) (coordinates 62) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_63 : pair (coordinates 63) (coordinates 63) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_64 : pair (coordinates 64) (coordinates 64) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_65 : pair (coordinates 65) (coordinates 65) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_66 : pair (coordinates 66) (coordinates 66) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_67 : pair (coordinates 67) (coordinates 67) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_68 : pair (coordinates 68) (coordinates 68) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_69 : pair (coordinates 69) (coordinates 69) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_70 : pair (coordinates 70) (coordinates 70) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_71 : pair (coordinates 71) (coordinates 71) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_72 : pair (coordinates 72) (coordinates 72) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_73 : pair (coordinates 73) (coordinates 73) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_74 : pair (coordinates 74) (coordinates 74) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_75 : pair (coordinates 75) (coordinates 75) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_76 : pair (coordinates 76) (coordinates 76) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_77 : pair (coordinates 77) (coordinates 77) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_78 : pair (coordinates 78) (coordinates 78) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_79 : pair (coordinates 79) (coordinates 79) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_80 : pair (coordinates 80) (coordinates 80) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_81 : pair (coordinates 81) (coordinates 81) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_82 : pair (coordinates 82) (coordinates 82) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_83 : pair (coordinates 83) (coordinates 83) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_84 : pair (coordinates 84) (coordinates 84) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_85 : pair (coordinates 85) (coordinates 85) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_86 : pair (coordinates 86) (coordinates 86) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_87 : pair (coordinates 87) (coordinates 87) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_88 : pair (coordinates 88) (coordinates 88) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_89 : pair (coordinates 89) (coordinates 89) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_90 : pair (coordinates 90) (coordinates 90) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_91 : pair (coordinates 91) (coordinates 91) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_92 : pair (coordinates 92) (coordinates 92) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_93 : pair (coordinates 93) (coordinates 93) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_94 : pair (coordinates 94) (coordinates 94) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_95 : pair (coordinates 95) (coordinates 95) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_96 : pair (coordinates 96) (coordinates 96) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_97 : pair (coordinates 97) (coordinates 97) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_98 : pair (coordinates 98) (coordinates 98) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_99 : pair (coordinates 99) (coordinates 99) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_100 : pair (coordinates 100) (coordinates 100) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_101 : pair (coordinates 101) (coordinates 101) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_102 : pair (coordinates 102) (coordinates 102) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_103 : pair (coordinates 103) (coordinates 103) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_104 : pair (coordinates 104) (coordinates 104) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_105 : pair (coordinates 105) (coordinates 105) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_106 : pair (coordinates 106) (coordinates 106) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_107 : pair (coordinates 107) (coordinates 107) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_108 : pair (coordinates 108) (coordinates 108) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_109 : pair (coordinates 109) (coordinates 109) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_110 : pair (coordinates 110) (coordinates 110) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_111 : pair (coordinates 111) (coordinates 111) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_112 : pair (coordinates 112) (coordinates 112) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_113 : pair (coordinates 113) (coordinates 113) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_114 : pair (coordinates 114) (coordinates 114) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_115 : pair (coordinates 115) (coordinates 115) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_116 : pair (coordinates 116) (coordinates 116) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_117 : pair (coordinates 117) (coordinates 117) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_118 : pair (coordinates 118) (coordinates 118) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_119 : pair (coordinates 119) (coordinates 119) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_120 : pair (coordinates 120) (coordinates 120) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_121 : pair (coordinates 121) (coordinates 121) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_122 : pair (coordinates 122) (coordinates 122) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_123 : pair (coordinates 123) (coordinates 123) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_124 : pair (coordinates 124) (coordinates 124) = 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_norm_125 : pair (coordinates 125) (coordinates 125) = 2 := by decide +kernel
theorem root_norm : ∀ a : Root, pair (coordinates a) (coordinates a) = 2 := by
  intro a
  fin_cases a
  · exact root_norm_0
  · exact root_norm_1
  · exact root_norm_2
  · exact root_norm_3
  · exact root_norm_4
  · exact root_norm_5
  · exact root_norm_6
  · exact root_norm_7
  · exact root_norm_8
  · exact root_norm_9
  · exact root_norm_10
  · exact root_norm_11
  · exact root_norm_12
  · exact root_norm_13
  · exact root_norm_14
  · exact root_norm_15
  · exact root_norm_16
  · exact root_norm_17
  · exact root_norm_18
  · exact root_norm_19
  · exact root_norm_20
  · exact root_norm_21
  · exact root_norm_22
  · exact root_norm_23
  · exact root_norm_24
  · exact root_norm_25
  · exact root_norm_26
  · exact root_norm_27
  · exact root_norm_28
  · exact root_norm_29
  · exact root_norm_30
  · exact root_norm_31
  · exact root_norm_32
  · exact root_norm_33
  · exact root_norm_34
  · exact root_norm_35
  · exact root_norm_36
  · exact root_norm_37
  · exact root_norm_38
  · exact root_norm_39
  · exact root_norm_40
  · exact root_norm_41
  · exact root_norm_42
  · exact root_norm_43
  · exact root_norm_44
  · exact root_norm_45
  · exact root_norm_46
  · exact root_norm_47
  · exact root_norm_48
  · exact root_norm_49
  · exact root_norm_50
  · exact root_norm_51
  · exact root_norm_52
  · exact root_norm_53
  · exact root_norm_54
  · exact root_norm_55
  · exact root_norm_56
  · exact root_norm_57
  · exact root_norm_58
  · exact root_norm_59
  · exact root_norm_60
  · exact root_norm_61
  · exact root_norm_62
  · exact root_norm_63
  · exact root_norm_64
  · exact root_norm_65
  · exact root_norm_66
  · exact root_norm_67
  · exact root_norm_68
  · exact root_norm_69
  · exact root_norm_70
  · exact root_norm_71
  · exact root_norm_72
  · exact root_norm_73
  · exact root_norm_74
  · exact root_norm_75
  · exact root_norm_76
  · exact root_norm_77
  · exact root_norm_78
  · exact root_norm_79
  · exact root_norm_80
  · exact root_norm_81
  · exact root_norm_82
  · exact root_norm_83
  · exact root_norm_84
  · exact root_norm_85
  · exact root_norm_86
  · exact root_norm_87
  · exact root_norm_88
  · exact root_norm_89
  · exact root_norm_90
  · exact root_norm_91
  · exact root_norm_92
  · exact root_norm_93
  · exact root_norm_94
  · exact root_norm_95
  · exact root_norm_96
  · exact root_norm_97
  · exact root_norm_98
  · exact root_norm_99
  · exact root_norm_100
  · exact root_norm_101
  · exact root_norm_102
  · exact root_norm_103
  · exact root_norm_104
  · exact root_norm_105
  · exact root_norm_106
  · exact root_norm_107
  · exact root_norm_108
  · exact root_norm_109
  · exact root_norm_110
  · exact root_norm_111
  · exact root_norm_112
  · exact root_norm_113
  · exact root_norm_114
  · exact root_norm_115
  · exact root_norm_116
  · exact root_norm_117
  · exact root_norm_118
  · exact root_norm_119
  · exact root_norm_120
  · exact root_norm_121
  · exact root_norm_122
  · exact root_norm_123
  · exact root_norm_124
  · exact root_norm_125
#check root_norm
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem simple_coordinates : ∀ i : Fin 7, coordinates (simpleIndex i) = Pi.single i 1 := by
  intro i
  fin_cases i <;> decide +kernel
#check simple_coordinates
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_0 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 0) = reflect i (coordinates 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_1 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 1) = reflect i (coordinates 1) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_2 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 2) = reflect i (coordinates 2) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_3 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 3) = reflect i (coordinates 3) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_4 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 4) = reflect i (coordinates 4) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_5 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 5) = reflect i (coordinates 5) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_6 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 6) = reflect i (coordinates 6) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_7 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 7) = reflect i (coordinates 7) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_8 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 8) = reflect i (coordinates 8) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_9 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 9) = reflect i (coordinates 9) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_10 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 10) = reflect i (coordinates 10) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_11 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 11) = reflect i (coordinates 11) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_12 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 12) = reflect i (coordinates 12) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_13 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 13) = reflect i (coordinates 13) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_14 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 14) = reflect i (coordinates 14) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_15 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 15) = reflect i (coordinates 15) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_16 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 16) = reflect i (coordinates 16) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_17 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 17) = reflect i (coordinates 17) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_18 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 18) = reflect i (coordinates 18) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_19 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 19) = reflect i (coordinates 19) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_20 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 20) = reflect i (coordinates 20) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_21 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 21) = reflect i (coordinates 21) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_22 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 22) = reflect i (coordinates 22) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_23 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 23) = reflect i (coordinates 23) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_24 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 24) = reflect i (coordinates 24) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_25 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 25) = reflect i (coordinates 25) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_26 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 26) = reflect i (coordinates 26) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_27 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 27) = reflect i (coordinates 27) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_28 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 28) = reflect i (coordinates 28) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_29 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 29) = reflect i (coordinates 29) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_30 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 30) = reflect i (coordinates 30) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_31 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 31) = reflect i (coordinates 31) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_32 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 32) = reflect i (coordinates 32) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_33 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 33) = reflect i (coordinates 33) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_34 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 34) = reflect i (coordinates 34) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_35 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 35) = reflect i (coordinates 35) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_36 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 36) = reflect i (coordinates 36) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_37 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 37) = reflect i (coordinates 37) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_38 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 38) = reflect i (coordinates 38) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_39 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 39) = reflect i (coordinates 39) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_40 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 40) = reflect i (coordinates 40) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_41 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 41) = reflect i (coordinates 41) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_42 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 42) = reflect i (coordinates 42) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_43 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 43) = reflect i (coordinates 43) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_44 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 44) = reflect i (coordinates 44) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_45 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 45) = reflect i (coordinates 45) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_46 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 46) = reflect i (coordinates 46) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_47 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 47) = reflect i (coordinates 47) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_48 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 48) = reflect i (coordinates 48) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_49 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 49) = reflect i (coordinates 49) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_50 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 50) = reflect i (coordinates 50) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_51 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 51) = reflect i (coordinates 51) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_52 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 52) = reflect i (coordinates 52) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_53 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 53) = reflect i (coordinates 53) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_54 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 54) = reflect i (coordinates 54) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_55 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 55) = reflect i (coordinates 55) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_56 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 56) = reflect i (coordinates 56) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_57 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 57) = reflect i (coordinates 57) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_58 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 58) = reflect i (coordinates 58) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_59 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 59) = reflect i (coordinates 59) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_60 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 60) = reflect i (coordinates 60) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_61 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 61) = reflect i (coordinates 61) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_62 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 62) = reflect i (coordinates 62) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_63 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 63) = reflect i (coordinates 63) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_64 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 64) = reflect i (coordinates 64) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_65 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 65) = reflect i (coordinates 65) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_66 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 66) = reflect i (coordinates 66) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_67 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 67) = reflect i (coordinates 67) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_68 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 68) = reflect i (coordinates 68) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_69 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 69) = reflect i (coordinates 69) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_70 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 70) = reflect i (coordinates 70) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_71 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 71) = reflect i (coordinates 71) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_72 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 72) = reflect i (coordinates 72) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_73 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 73) = reflect i (coordinates 73) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_74 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 74) = reflect i (coordinates 74) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_75 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 75) = reflect i (coordinates 75) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_76 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 76) = reflect i (coordinates 76) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_77 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 77) = reflect i (coordinates 77) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_78 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 78) = reflect i (coordinates 78) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_79 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 79) = reflect i (coordinates 79) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_80 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 80) = reflect i (coordinates 80) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_81 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 81) = reflect i (coordinates 81) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_82 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 82) = reflect i (coordinates 82) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_83 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 83) = reflect i (coordinates 83) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_84 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 84) = reflect i (coordinates 84) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_85 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 85) = reflect i (coordinates 85) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_86 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 86) = reflect i (coordinates 86) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_87 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 87) = reflect i (coordinates 87) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_88 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 88) = reflect i (coordinates 88) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_89 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 89) = reflect i (coordinates 89) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_90 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 90) = reflect i (coordinates 90) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_91 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 91) = reflect i (coordinates 91) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_92 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 92) = reflect i (coordinates 92) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_93 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 93) = reflect i (coordinates 93) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_94 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 94) = reflect i (coordinates 94) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_95 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 95) = reflect i (coordinates 95) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_96 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 96) = reflect i (coordinates 96) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_97 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 97) = reflect i (coordinates 97) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_98 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 98) = reflect i (coordinates 98) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_99 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 99) = reflect i (coordinates 99) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_100 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 100) = reflect i (coordinates 100) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_101 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 101) = reflect i (coordinates 101) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_102 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 102) = reflect i (coordinates 102) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_103 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 103) = reflect i (coordinates 103) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_104 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 104) = reflect i (coordinates 104) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_105 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 105) = reflect i (coordinates 105) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_106 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 106) = reflect i (coordinates 106) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_107 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 107) = reflect i (coordinates 107) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_108 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 108) = reflect i (coordinates 108) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_109 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 109) = reflect i (coordinates 109) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_110 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 110) = reflect i (coordinates 110) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_111 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 111) = reflect i (coordinates 111) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_112 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 112) = reflect i (coordinates 112) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_113 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 113) = reflect i (coordinates 113) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_114 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 114) = reflect i (coordinates 114) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_115 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 115) = reflect i (coordinates 115) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_116 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 116) = reflect i (coordinates 116) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_117 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 117) = reflect i (coordinates 117) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_118 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 118) = reflect i (coordinates 118) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_119 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 119) = reflect i (coordinates 119) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_120 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 120) = reflect i (coordinates 120) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_121 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 121) = reflect i (coordinates 121) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_122 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 122) = reflect i (coordinates 122) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_123 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 123) = reflect i (coordinates 123) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_124 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 124) = reflect i (coordinates 124) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_simple_reflection_coordinates_125 : ∀ i : Fin 7, coordinates (simpleReflectionIndex i 125) = reflect i (coordinates 125) := by decide +kernel
theorem root_simple_reflection_coordinates : ∀ a : Root, ∀ i : Fin 7, coordinates (simpleReflectionIndex i a) = reflect i (coordinates a) := by
  intro a
  fin_cases a
  · exact root_simple_reflection_coordinates_0
  · exact root_simple_reflection_coordinates_1
  · exact root_simple_reflection_coordinates_2
  · exact root_simple_reflection_coordinates_3
  · exact root_simple_reflection_coordinates_4
  · exact root_simple_reflection_coordinates_5
  · exact root_simple_reflection_coordinates_6
  · exact root_simple_reflection_coordinates_7
  · exact root_simple_reflection_coordinates_8
  · exact root_simple_reflection_coordinates_9
  · exact root_simple_reflection_coordinates_10
  · exact root_simple_reflection_coordinates_11
  · exact root_simple_reflection_coordinates_12
  · exact root_simple_reflection_coordinates_13
  · exact root_simple_reflection_coordinates_14
  · exact root_simple_reflection_coordinates_15
  · exact root_simple_reflection_coordinates_16
  · exact root_simple_reflection_coordinates_17
  · exact root_simple_reflection_coordinates_18
  · exact root_simple_reflection_coordinates_19
  · exact root_simple_reflection_coordinates_20
  · exact root_simple_reflection_coordinates_21
  · exact root_simple_reflection_coordinates_22
  · exact root_simple_reflection_coordinates_23
  · exact root_simple_reflection_coordinates_24
  · exact root_simple_reflection_coordinates_25
  · exact root_simple_reflection_coordinates_26
  · exact root_simple_reflection_coordinates_27
  · exact root_simple_reflection_coordinates_28
  · exact root_simple_reflection_coordinates_29
  · exact root_simple_reflection_coordinates_30
  · exact root_simple_reflection_coordinates_31
  · exact root_simple_reflection_coordinates_32
  · exact root_simple_reflection_coordinates_33
  · exact root_simple_reflection_coordinates_34
  · exact root_simple_reflection_coordinates_35
  · exact root_simple_reflection_coordinates_36
  · exact root_simple_reflection_coordinates_37
  · exact root_simple_reflection_coordinates_38
  · exact root_simple_reflection_coordinates_39
  · exact root_simple_reflection_coordinates_40
  · exact root_simple_reflection_coordinates_41
  · exact root_simple_reflection_coordinates_42
  · exact root_simple_reflection_coordinates_43
  · exact root_simple_reflection_coordinates_44
  · exact root_simple_reflection_coordinates_45
  · exact root_simple_reflection_coordinates_46
  · exact root_simple_reflection_coordinates_47
  · exact root_simple_reflection_coordinates_48
  · exact root_simple_reflection_coordinates_49
  · exact root_simple_reflection_coordinates_50
  · exact root_simple_reflection_coordinates_51
  · exact root_simple_reflection_coordinates_52
  · exact root_simple_reflection_coordinates_53
  · exact root_simple_reflection_coordinates_54
  · exact root_simple_reflection_coordinates_55
  · exact root_simple_reflection_coordinates_56
  · exact root_simple_reflection_coordinates_57
  · exact root_simple_reflection_coordinates_58
  · exact root_simple_reflection_coordinates_59
  · exact root_simple_reflection_coordinates_60
  · exact root_simple_reflection_coordinates_61
  · exact root_simple_reflection_coordinates_62
  · exact root_simple_reflection_coordinates_63
  · exact root_simple_reflection_coordinates_64
  · exact root_simple_reflection_coordinates_65
  · exact root_simple_reflection_coordinates_66
  · exact root_simple_reflection_coordinates_67
  · exact root_simple_reflection_coordinates_68
  · exact root_simple_reflection_coordinates_69
  · exact root_simple_reflection_coordinates_70
  · exact root_simple_reflection_coordinates_71
  · exact root_simple_reflection_coordinates_72
  · exact root_simple_reflection_coordinates_73
  · exact root_simple_reflection_coordinates_74
  · exact root_simple_reflection_coordinates_75
  · exact root_simple_reflection_coordinates_76
  · exact root_simple_reflection_coordinates_77
  · exact root_simple_reflection_coordinates_78
  · exact root_simple_reflection_coordinates_79
  · exact root_simple_reflection_coordinates_80
  · exact root_simple_reflection_coordinates_81
  · exact root_simple_reflection_coordinates_82
  · exact root_simple_reflection_coordinates_83
  · exact root_simple_reflection_coordinates_84
  · exact root_simple_reflection_coordinates_85
  · exact root_simple_reflection_coordinates_86
  · exact root_simple_reflection_coordinates_87
  · exact root_simple_reflection_coordinates_88
  · exact root_simple_reflection_coordinates_89
  · exact root_simple_reflection_coordinates_90
  · exact root_simple_reflection_coordinates_91
  · exact root_simple_reflection_coordinates_92
  · exact root_simple_reflection_coordinates_93
  · exact root_simple_reflection_coordinates_94
  · exact root_simple_reflection_coordinates_95
  · exact root_simple_reflection_coordinates_96
  · exact root_simple_reflection_coordinates_97
  · exact root_simple_reflection_coordinates_98
  · exact root_simple_reflection_coordinates_99
  · exact root_simple_reflection_coordinates_100
  · exact root_simple_reflection_coordinates_101
  · exact root_simple_reflection_coordinates_102
  · exact root_simple_reflection_coordinates_103
  · exact root_simple_reflection_coordinates_104
  · exact root_simple_reflection_coordinates_105
  · exact root_simple_reflection_coordinates_106
  · exact root_simple_reflection_coordinates_107
  · exact root_simple_reflection_coordinates_108
  · exact root_simple_reflection_coordinates_109
  · exact root_simple_reflection_coordinates_110
  · exact root_simple_reflection_coordinates_111
  · exact root_simple_reflection_coordinates_112
  · exact root_simple_reflection_coordinates_113
  · exact root_simple_reflection_coordinates_114
  · exact root_simple_reflection_coordinates_115
  · exact root_simple_reflection_coordinates_116
  · exact root_simple_reflection_coordinates_117
  · exact root_simple_reflection_coordinates_118
  · exact root_simple_reflection_coordinates_119
  · exact root_simple_reflection_coordinates_120
  · exact root_simple_reflection_coordinates_121
  · exact root_simple_reflection_coordinates_122
  · exact root_simple_reflection_coordinates_123
  · exact root_simple_reflection_coordinates_124
  · exact root_simple_reflection_coordinates_125
#check root_simple_reflection_coordinates
theorem simple_reflection_coordinates (i : Fin 7) (a : Root) :
    coordinates (simpleReflectionIndex i a) = reflect i (coordinates a) := root_simple_reflection_coordinates a i
theorem wordAction_append (u v : List (Fin 7)) (x : Vector) :
    wordAction (u ++ v) x = wordAction v (wordAction u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons i u ih => exact ih (reflect i x)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_0 : (0 : Root) ≠ 0 → parent 0 < 0 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_1 : (1 : Root) ≠ 0 → parent 1 < 1 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_2 : (2 : Root) ≠ 0 → parent 2 < 2 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_3 : (3 : Root) ≠ 0 → parent 3 < 3 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_4 : (4 : Root) ≠ 0 → parent 4 < 4 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_5 : (5 : Root) ≠ 0 → parent 5 < 5 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_6 : (6 : Root) ≠ 0 → parent 6 < 6 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_7 : (7 : Root) ≠ 0 → parent 7 < 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_8 : (8 : Root) ≠ 0 → parent 8 < 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_9 : (9 : Root) ≠ 0 → parent 9 < 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_10 : (10 : Root) ≠ 0 → parent 10 < 10 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_11 : (11 : Root) ≠ 0 → parent 11 < 11 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_12 : (12 : Root) ≠ 0 → parent 12 < 12 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_13 : (13 : Root) ≠ 0 → parent 13 < 13 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_14 : (14 : Root) ≠ 0 → parent 14 < 14 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_15 : (15 : Root) ≠ 0 → parent 15 < 15 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_16 : (16 : Root) ≠ 0 → parent 16 < 16 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_17 : (17 : Root) ≠ 0 → parent 17 < 17 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_18 : (18 : Root) ≠ 0 → parent 18 < 18 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_19 : (19 : Root) ≠ 0 → parent 19 < 19 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_20 : (20 : Root) ≠ 0 → parent 20 < 20 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_21 : (21 : Root) ≠ 0 → parent 21 < 21 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_22 : (22 : Root) ≠ 0 → parent 22 < 22 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_23 : (23 : Root) ≠ 0 → parent 23 < 23 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_24 : (24 : Root) ≠ 0 → parent 24 < 24 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_25 : (25 : Root) ≠ 0 → parent 25 < 25 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_26 : (26 : Root) ≠ 0 → parent 26 < 26 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_27 : (27 : Root) ≠ 0 → parent 27 < 27 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_28 : (28 : Root) ≠ 0 → parent 28 < 28 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_29 : (29 : Root) ≠ 0 → parent 29 < 29 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_30 : (30 : Root) ≠ 0 → parent 30 < 30 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_31 : (31 : Root) ≠ 0 → parent 31 < 31 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_32 : (32 : Root) ≠ 0 → parent 32 < 32 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_33 : (33 : Root) ≠ 0 → parent 33 < 33 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_34 : (34 : Root) ≠ 0 → parent 34 < 34 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_35 : (35 : Root) ≠ 0 → parent 35 < 35 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_36 : (36 : Root) ≠ 0 → parent 36 < 36 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_37 : (37 : Root) ≠ 0 → parent 37 < 37 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_38 : (38 : Root) ≠ 0 → parent 38 < 38 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_39 : (39 : Root) ≠ 0 → parent 39 < 39 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_40 : (40 : Root) ≠ 0 → parent 40 < 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_41 : (41 : Root) ≠ 0 → parent 41 < 41 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_42 : (42 : Root) ≠ 0 → parent 42 < 42 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_43 : (43 : Root) ≠ 0 → parent 43 < 43 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_44 : (44 : Root) ≠ 0 → parent 44 < 44 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_45 : (45 : Root) ≠ 0 → parent 45 < 45 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_46 : (46 : Root) ≠ 0 → parent 46 < 46 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_47 : (47 : Root) ≠ 0 → parent 47 < 47 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_48 : (48 : Root) ≠ 0 → parent 48 < 48 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_49 : (49 : Root) ≠ 0 → parent 49 < 49 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_50 : (50 : Root) ≠ 0 → parent 50 < 50 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_51 : (51 : Root) ≠ 0 → parent 51 < 51 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_52 : (52 : Root) ≠ 0 → parent 52 < 52 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_53 : (53 : Root) ≠ 0 → parent 53 < 53 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_54 : (54 : Root) ≠ 0 → parent 54 < 54 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_55 : (55 : Root) ≠ 0 → parent 55 < 55 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_56 : (56 : Root) ≠ 0 → parent 56 < 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_57 : (57 : Root) ≠ 0 → parent 57 < 57 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_58 : (58 : Root) ≠ 0 → parent 58 < 58 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_59 : (59 : Root) ≠ 0 → parent 59 < 59 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_60 : (60 : Root) ≠ 0 → parent 60 < 60 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_61 : (61 : Root) ≠ 0 → parent 61 < 61 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_62 : (62 : Root) ≠ 0 → parent 62 < 62 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_63 : (63 : Root) ≠ 0 → parent 63 < 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_64 : (64 : Root) ≠ 0 → parent 64 < 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_65 : (65 : Root) ≠ 0 → parent 65 < 65 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_66 : (66 : Root) ≠ 0 → parent 66 < 66 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_67 : (67 : Root) ≠ 0 → parent 67 < 67 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_68 : (68 : Root) ≠ 0 → parent 68 < 68 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_69 : (69 : Root) ≠ 0 → parent 69 < 69 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_70 : (70 : Root) ≠ 0 → parent 70 < 70 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_71 : (71 : Root) ≠ 0 → parent 71 < 71 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_72 : (72 : Root) ≠ 0 → parent 72 < 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_73 : (73 : Root) ≠ 0 → parent 73 < 73 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_74 : (74 : Root) ≠ 0 → parent 74 < 74 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_75 : (75 : Root) ≠ 0 → parent 75 < 75 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_76 : (76 : Root) ≠ 0 → parent 76 < 76 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_77 : (77 : Root) ≠ 0 → parent 77 < 77 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_78 : (78 : Root) ≠ 0 → parent 78 < 78 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_79 : (79 : Root) ≠ 0 → parent 79 < 79 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_80 : (80 : Root) ≠ 0 → parent 80 < 80 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_81 : (81 : Root) ≠ 0 → parent 81 < 81 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_82 : (82 : Root) ≠ 0 → parent 82 < 82 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_83 : (83 : Root) ≠ 0 → parent 83 < 83 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_84 : (84 : Root) ≠ 0 → parent 84 < 84 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_85 : (85 : Root) ≠ 0 → parent 85 < 85 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_86 : (86 : Root) ≠ 0 → parent 86 < 86 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_87 : (87 : Root) ≠ 0 → parent 87 < 87 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_88 : (88 : Root) ≠ 0 → parent 88 < 88 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_89 : (89 : Root) ≠ 0 → parent 89 < 89 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_90 : (90 : Root) ≠ 0 → parent 90 < 90 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_91 : (91 : Root) ≠ 0 → parent 91 < 91 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_92 : (92 : Root) ≠ 0 → parent 92 < 92 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_93 : (93 : Root) ≠ 0 → parent 93 < 93 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_94 : (94 : Root) ≠ 0 → parent 94 < 94 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_95 : (95 : Root) ≠ 0 → parent 95 < 95 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_96 : (96 : Root) ≠ 0 → parent 96 < 96 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_97 : (97 : Root) ≠ 0 → parent 97 < 97 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_98 : (98 : Root) ≠ 0 → parent 98 < 98 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_99 : (99 : Root) ≠ 0 → parent 99 < 99 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_100 : (100 : Root) ≠ 0 → parent 100 < 100 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_101 : (101 : Root) ≠ 0 → parent 101 < 101 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_102 : (102 : Root) ≠ 0 → parent 102 < 102 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_103 : (103 : Root) ≠ 0 → parent 103 < 103 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_104 : (104 : Root) ≠ 0 → parent 104 < 104 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_105 : (105 : Root) ≠ 0 → parent 105 < 105 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_106 : (106 : Root) ≠ 0 → parent 106 < 106 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_107 : (107 : Root) ≠ 0 → parent 107 < 107 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_108 : (108 : Root) ≠ 0 → parent 108 < 108 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_109 : (109 : Root) ≠ 0 → parent 109 < 109 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_110 : (110 : Root) ≠ 0 → parent 110 < 110 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_111 : (111 : Root) ≠ 0 → parent 111 < 111 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_112 : (112 : Root) ≠ 0 → parent 112 < 112 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_113 : (113 : Root) ≠ 0 → parent 113 < 113 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_114 : (114 : Root) ≠ 0 → parent 114 < 114 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_115 : (115 : Root) ≠ 0 → parent 115 < 115 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_116 : (116 : Root) ≠ 0 → parent 116 < 116 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_117 : (117 : Root) ≠ 0 → parent 117 < 117 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_118 : (118 : Root) ≠ 0 → parent 118 < 118 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_119 : (119 : Root) ≠ 0 → parent 119 < 119 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_120 : (120 : Root) ≠ 0 → parent 120 < 120 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_121 : (121 : Root) ≠ 0 → parent 121 < 121 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_122 : (122 : Root) ≠ 0 → parent 122 < 122 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_123 : (123 : Root) ≠ 0 → parent 123 < 123 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_124 : (124 : Root) ≠ 0 → parent 124 < 124 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_lt_125 : (125 : Root) ≠ 0 → parent 125 < 125 := by decide +kernel
theorem parent_lt : ∀ a : Root, a ≠ 0 → parent a < a := by
  intro a
  fin_cases a
  · exact parent_lt_0
  · exact parent_lt_1
  · exact parent_lt_2
  · exact parent_lt_3
  · exact parent_lt_4
  · exact parent_lt_5
  · exact parent_lt_6
  · exact parent_lt_7
  · exact parent_lt_8
  · exact parent_lt_9
  · exact parent_lt_10
  · exact parent_lt_11
  · exact parent_lt_12
  · exact parent_lt_13
  · exact parent_lt_14
  · exact parent_lt_15
  · exact parent_lt_16
  · exact parent_lt_17
  · exact parent_lt_18
  · exact parent_lt_19
  · exact parent_lt_20
  · exact parent_lt_21
  · exact parent_lt_22
  · exact parent_lt_23
  · exact parent_lt_24
  · exact parent_lt_25
  · exact parent_lt_26
  · exact parent_lt_27
  · exact parent_lt_28
  · exact parent_lt_29
  · exact parent_lt_30
  · exact parent_lt_31
  · exact parent_lt_32
  · exact parent_lt_33
  · exact parent_lt_34
  · exact parent_lt_35
  · exact parent_lt_36
  · exact parent_lt_37
  · exact parent_lt_38
  · exact parent_lt_39
  · exact parent_lt_40
  · exact parent_lt_41
  · exact parent_lt_42
  · exact parent_lt_43
  · exact parent_lt_44
  · exact parent_lt_45
  · exact parent_lt_46
  · exact parent_lt_47
  · exact parent_lt_48
  · exact parent_lt_49
  · exact parent_lt_50
  · exact parent_lt_51
  · exact parent_lt_52
  · exact parent_lt_53
  · exact parent_lt_54
  · exact parent_lt_55
  · exact parent_lt_56
  · exact parent_lt_57
  · exact parent_lt_58
  · exact parent_lt_59
  · exact parent_lt_60
  · exact parent_lt_61
  · exact parent_lt_62
  · exact parent_lt_63
  · exact parent_lt_64
  · exact parent_lt_65
  · exact parent_lt_66
  · exact parent_lt_67
  · exact parent_lt_68
  · exact parent_lt_69
  · exact parent_lt_70
  · exact parent_lt_71
  · exact parent_lt_72
  · exact parent_lt_73
  · exact parent_lt_74
  · exact parent_lt_75
  · exact parent_lt_76
  · exact parent_lt_77
  · exact parent_lt_78
  · exact parent_lt_79
  · exact parent_lt_80
  · exact parent_lt_81
  · exact parent_lt_82
  · exact parent_lt_83
  · exact parent_lt_84
  · exact parent_lt_85
  · exact parent_lt_86
  · exact parent_lt_87
  · exact parent_lt_88
  · exact parent_lt_89
  · exact parent_lt_90
  · exact parent_lt_91
  · exact parent_lt_92
  · exact parent_lt_93
  · exact parent_lt_94
  · exact parent_lt_95
  · exact parent_lt_96
  · exact parent_lt_97
  · exact parent_lt_98
  · exact parent_lt_99
  · exact parent_lt_100
  · exact parent_lt_101
  · exact parent_lt_102
  · exact parent_lt_103
  · exact parent_lt_104
  · exact parent_lt_105
  · exact parent_lt_106
  · exact parent_lt_107
  · exact parent_lt_108
  · exact parent_lt_109
  · exact parent_lt_110
  · exact parent_lt_111
  · exact parent_lt_112
  · exact parent_lt_113
  · exact parent_lt_114
  · exact parent_lt_115
  · exact parent_lt_116
  · exact parent_lt_117
  · exact parent_lt_118
  · exact parent_lt_119
  · exact parent_lt_120
  · exact parent_lt_121
  · exact parent_lt_122
  · exact parent_lt_123
  · exact parent_lt_124
  · exact parent_lt_125
#check parent_lt
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_0 : (0 : Root) ≠ 0 → coordinates 0 = reflect (lastStep 0) (coordinates (parent 0)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_1 : (1 : Root) ≠ 0 → coordinates 1 = reflect (lastStep 1) (coordinates (parent 1)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_2 : (2 : Root) ≠ 0 → coordinates 2 = reflect (lastStep 2) (coordinates (parent 2)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_3 : (3 : Root) ≠ 0 → coordinates 3 = reflect (lastStep 3) (coordinates (parent 3)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_4 : (4 : Root) ≠ 0 → coordinates 4 = reflect (lastStep 4) (coordinates (parent 4)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_5 : (5 : Root) ≠ 0 → coordinates 5 = reflect (lastStep 5) (coordinates (parent 5)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_6 : (6 : Root) ≠ 0 → coordinates 6 = reflect (lastStep 6) (coordinates (parent 6)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_7 : (7 : Root) ≠ 0 → coordinates 7 = reflect (lastStep 7) (coordinates (parent 7)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_8 : (8 : Root) ≠ 0 → coordinates 8 = reflect (lastStep 8) (coordinates (parent 8)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_9 : (9 : Root) ≠ 0 → coordinates 9 = reflect (lastStep 9) (coordinates (parent 9)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_10 : (10 : Root) ≠ 0 → coordinates 10 = reflect (lastStep 10) (coordinates (parent 10)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_11 : (11 : Root) ≠ 0 → coordinates 11 = reflect (lastStep 11) (coordinates (parent 11)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_12 : (12 : Root) ≠ 0 → coordinates 12 = reflect (lastStep 12) (coordinates (parent 12)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_13 : (13 : Root) ≠ 0 → coordinates 13 = reflect (lastStep 13) (coordinates (parent 13)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_14 : (14 : Root) ≠ 0 → coordinates 14 = reflect (lastStep 14) (coordinates (parent 14)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_15 : (15 : Root) ≠ 0 → coordinates 15 = reflect (lastStep 15) (coordinates (parent 15)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_16 : (16 : Root) ≠ 0 → coordinates 16 = reflect (lastStep 16) (coordinates (parent 16)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_17 : (17 : Root) ≠ 0 → coordinates 17 = reflect (lastStep 17) (coordinates (parent 17)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_18 : (18 : Root) ≠ 0 → coordinates 18 = reflect (lastStep 18) (coordinates (parent 18)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_19 : (19 : Root) ≠ 0 → coordinates 19 = reflect (lastStep 19) (coordinates (parent 19)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_20 : (20 : Root) ≠ 0 → coordinates 20 = reflect (lastStep 20) (coordinates (parent 20)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_21 : (21 : Root) ≠ 0 → coordinates 21 = reflect (lastStep 21) (coordinates (parent 21)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_22 : (22 : Root) ≠ 0 → coordinates 22 = reflect (lastStep 22) (coordinates (parent 22)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_23 : (23 : Root) ≠ 0 → coordinates 23 = reflect (lastStep 23) (coordinates (parent 23)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_24 : (24 : Root) ≠ 0 → coordinates 24 = reflect (lastStep 24) (coordinates (parent 24)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_25 : (25 : Root) ≠ 0 → coordinates 25 = reflect (lastStep 25) (coordinates (parent 25)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_26 : (26 : Root) ≠ 0 → coordinates 26 = reflect (lastStep 26) (coordinates (parent 26)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_27 : (27 : Root) ≠ 0 → coordinates 27 = reflect (lastStep 27) (coordinates (parent 27)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_28 : (28 : Root) ≠ 0 → coordinates 28 = reflect (lastStep 28) (coordinates (parent 28)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_29 : (29 : Root) ≠ 0 → coordinates 29 = reflect (lastStep 29) (coordinates (parent 29)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_30 : (30 : Root) ≠ 0 → coordinates 30 = reflect (lastStep 30) (coordinates (parent 30)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_31 : (31 : Root) ≠ 0 → coordinates 31 = reflect (lastStep 31) (coordinates (parent 31)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_32 : (32 : Root) ≠ 0 → coordinates 32 = reflect (lastStep 32) (coordinates (parent 32)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_33 : (33 : Root) ≠ 0 → coordinates 33 = reflect (lastStep 33) (coordinates (parent 33)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_34 : (34 : Root) ≠ 0 → coordinates 34 = reflect (lastStep 34) (coordinates (parent 34)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_35 : (35 : Root) ≠ 0 → coordinates 35 = reflect (lastStep 35) (coordinates (parent 35)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_36 : (36 : Root) ≠ 0 → coordinates 36 = reflect (lastStep 36) (coordinates (parent 36)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_37 : (37 : Root) ≠ 0 → coordinates 37 = reflect (lastStep 37) (coordinates (parent 37)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_38 : (38 : Root) ≠ 0 → coordinates 38 = reflect (lastStep 38) (coordinates (parent 38)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_39 : (39 : Root) ≠ 0 → coordinates 39 = reflect (lastStep 39) (coordinates (parent 39)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_40 : (40 : Root) ≠ 0 → coordinates 40 = reflect (lastStep 40) (coordinates (parent 40)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_41 : (41 : Root) ≠ 0 → coordinates 41 = reflect (lastStep 41) (coordinates (parent 41)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_42 : (42 : Root) ≠ 0 → coordinates 42 = reflect (lastStep 42) (coordinates (parent 42)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_43 : (43 : Root) ≠ 0 → coordinates 43 = reflect (lastStep 43) (coordinates (parent 43)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_44 : (44 : Root) ≠ 0 → coordinates 44 = reflect (lastStep 44) (coordinates (parent 44)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_45 : (45 : Root) ≠ 0 → coordinates 45 = reflect (lastStep 45) (coordinates (parent 45)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_46 : (46 : Root) ≠ 0 → coordinates 46 = reflect (lastStep 46) (coordinates (parent 46)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_47 : (47 : Root) ≠ 0 → coordinates 47 = reflect (lastStep 47) (coordinates (parent 47)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_48 : (48 : Root) ≠ 0 → coordinates 48 = reflect (lastStep 48) (coordinates (parent 48)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_49 : (49 : Root) ≠ 0 → coordinates 49 = reflect (lastStep 49) (coordinates (parent 49)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_50 : (50 : Root) ≠ 0 → coordinates 50 = reflect (lastStep 50) (coordinates (parent 50)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_51 : (51 : Root) ≠ 0 → coordinates 51 = reflect (lastStep 51) (coordinates (parent 51)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_52 : (52 : Root) ≠ 0 → coordinates 52 = reflect (lastStep 52) (coordinates (parent 52)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_53 : (53 : Root) ≠ 0 → coordinates 53 = reflect (lastStep 53) (coordinates (parent 53)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_54 : (54 : Root) ≠ 0 → coordinates 54 = reflect (lastStep 54) (coordinates (parent 54)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_55 : (55 : Root) ≠ 0 → coordinates 55 = reflect (lastStep 55) (coordinates (parent 55)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_56 : (56 : Root) ≠ 0 → coordinates 56 = reflect (lastStep 56) (coordinates (parent 56)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_57 : (57 : Root) ≠ 0 → coordinates 57 = reflect (lastStep 57) (coordinates (parent 57)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_58 : (58 : Root) ≠ 0 → coordinates 58 = reflect (lastStep 58) (coordinates (parent 58)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_59 : (59 : Root) ≠ 0 → coordinates 59 = reflect (lastStep 59) (coordinates (parent 59)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_60 : (60 : Root) ≠ 0 → coordinates 60 = reflect (lastStep 60) (coordinates (parent 60)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_61 : (61 : Root) ≠ 0 → coordinates 61 = reflect (lastStep 61) (coordinates (parent 61)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_62 : (62 : Root) ≠ 0 → coordinates 62 = reflect (lastStep 62) (coordinates (parent 62)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_63 : (63 : Root) ≠ 0 → coordinates 63 = reflect (lastStep 63) (coordinates (parent 63)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_64 : (64 : Root) ≠ 0 → coordinates 64 = reflect (lastStep 64) (coordinates (parent 64)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_65 : (65 : Root) ≠ 0 → coordinates 65 = reflect (lastStep 65) (coordinates (parent 65)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_66 : (66 : Root) ≠ 0 → coordinates 66 = reflect (lastStep 66) (coordinates (parent 66)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_67 : (67 : Root) ≠ 0 → coordinates 67 = reflect (lastStep 67) (coordinates (parent 67)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_68 : (68 : Root) ≠ 0 → coordinates 68 = reflect (lastStep 68) (coordinates (parent 68)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_69 : (69 : Root) ≠ 0 → coordinates 69 = reflect (lastStep 69) (coordinates (parent 69)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_70 : (70 : Root) ≠ 0 → coordinates 70 = reflect (lastStep 70) (coordinates (parent 70)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_71 : (71 : Root) ≠ 0 → coordinates 71 = reflect (lastStep 71) (coordinates (parent 71)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_72 : (72 : Root) ≠ 0 → coordinates 72 = reflect (lastStep 72) (coordinates (parent 72)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_73 : (73 : Root) ≠ 0 → coordinates 73 = reflect (lastStep 73) (coordinates (parent 73)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_74 : (74 : Root) ≠ 0 → coordinates 74 = reflect (lastStep 74) (coordinates (parent 74)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_75 : (75 : Root) ≠ 0 → coordinates 75 = reflect (lastStep 75) (coordinates (parent 75)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_76 : (76 : Root) ≠ 0 → coordinates 76 = reflect (lastStep 76) (coordinates (parent 76)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_77 : (77 : Root) ≠ 0 → coordinates 77 = reflect (lastStep 77) (coordinates (parent 77)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_78 : (78 : Root) ≠ 0 → coordinates 78 = reflect (lastStep 78) (coordinates (parent 78)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_79 : (79 : Root) ≠ 0 → coordinates 79 = reflect (lastStep 79) (coordinates (parent 79)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_80 : (80 : Root) ≠ 0 → coordinates 80 = reflect (lastStep 80) (coordinates (parent 80)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_81 : (81 : Root) ≠ 0 → coordinates 81 = reflect (lastStep 81) (coordinates (parent 81)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_82 : (82 : Root) ≠ 0 → coordinates 82 = reflect (lastStep 82) (coordinates (parent 82)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_83 : (83 : Root) ≠ 0 → coordinates 83 = reflect (lastStep 83) (coordinates (parent 83)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_84 : (84 : Root) ≠ 0 → coordinates 84 = reflect (lastStep 84) (coordinates (parent 84)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_85 : (85 : Root) ≠ 0 → coordinates 85 = reflect (lastStep 85) (coordinates (parent 85)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_86 : (86 : Root) ≠ 0 → coordinates 86 = reflect (lastStep 86) (coordinates (parent 86)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_87 : (87 : Root) ≠ 0 → coordinates 87 = reflect (lastStep 87) (coordinates (parent 87)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_88 : (88 : Root) ≠ 0 → coordinates 88 = reflect (lastStep 88) (coordinates (parent 88)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_89 : (89 : Root) ≠ 0 → coordinates 89 = reflect (lastStep 89) (coordinates (parent 89)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_90 : (90 : Root) ≠ 0 → coordinates 90 = reflect (lastStep 90) (coordinates (parent 90)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_91 : (91 : Root) ≠ 0 → coordinates 91 = reflect (lastStep 91) (coordinates (parent 91)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_92 : (92 : Root) ≠ 0 → coordinates 92 = reflect (lastStep 92) (coordinates (parent 92)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_93 : (93 : Root) ≠ 0 → coordinates 93 = reflect (lastStep 93) (coordinates (parent 93)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_94 : (94 : Root) ≠ 0 → coordinates 94 = reflect (lastStep 94) (coordinates (parent 94)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_95 : (95 : Root) ≠ 0 → coordinates 95 = reflect (lastStep 95) (coordinates (parent 95)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_96 : (96 : Root) ≠ 0 → coordinates 96 = reflect (lastStep 96) (coordinates (parent 96)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_97 : (97 : Root) ≠ 0 → coordinates 97 = reflect (lastStep 97) (coordinates (parent 97)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_98 : (98 : Root) ≠ 0 → coordinates 98 = reflect (lastStep 98) (coordinates (parent 98)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_99 : (99 : Root) ≠ 0 → coordinates 99 = reflect (lastStep 99) (coordinates (parent 99)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_100 : (100 : Root) ≠ 0 → coordinates 100 = reflect (lastStep 100) (coordinates (parent 100)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_101 : (101 : Root) ≠ 0 → coordinates 101 = reflect (lastStep 101) (coordinates (parent 101)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_102 : (102 : Root) ≠ 0 → coordinates 102 = reflect (lastStep 102) (coordinates (parent 102)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_103 : (103 : Root) ≠ 0 → coordinates 103 = reflect (lastStep 103) (coordinates (parent 103)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_104 : (104 : Root) ≠ 0 → coordinates 104 = reflect (lastStep 104) (coordinates (parent 104)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_105 : (105 : Root) ≠ 0 → coordinates 105 = reflect (lastStep 105) (coordinates (parent 105)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_106 : (106 : Root) ≠ 0 → coordinates 106 = reflect (lastStep 106) (coordinates (parent 106)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_107 : (107 : Root) ≠ 0 → coordinates 107 = reflect (lastStep 107) (coordinates (parent 107)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_108 : (108 : Root) ≠ 0 → coordinates 108 = reflect (lastStep 108) (coordinates (parent 108)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_109 : (109 : Root) ≠ 0 → coordinates 109 = reflect (lastStep 109) (coordinates (parent 109)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_110 : (110 : Root) ≠ 0 → coordinates 110 = reflect (lastStep 110) (coordinates (parent 110)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_111 : (111 : Root) ≠ 0 → coordinates 111 = reflect (lastStep 111) (coordinates (parent 111)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_112 : (112 : Root) ≠ 0 → coordinates 112 = reflect (lastStep 112) (coordinates (parent 112)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_113 : (113 : Root) ≠ 0 → coordinates 113 = reflect (lastStep 113) (coordinates (parent 113)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_114 : (114 : Root) ≠ 0 → coordinates 114 = reflect (lastStep 114) (coordinates (parent 114)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_115 : (115 : Root) ≠ 0 → coordinates 115 = reflect (lastStep 115) (coordinates (parent 115)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_116 : (116 : Root) ≠ 0 → coordinates 116 = reflect (lastStep 116) (coordinates (parent 116)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_117 : (117 : Root) ≠ 0 → coordinates 117 = reflect (lastStep 117) (coordinates (parent 117)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_118 : (118 : Root) ≠ 0 → coordinates 118 = reflect (lastStep 118) (coordinates (parent 118)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_119 : (119 : Root) ≠ 0 → coordinates 119 = reflect (lastStep 119) (coordinates (parent 119)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_120 : (120 : Root) ≠ 0 → coordinates 120 = reflect (lastStep 120) (coordinates (parent 120)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_121 : (121 : Root) ≠ 0 → coordinates 121 = reflect (lastStep 121) (coordinates (parent 121)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_122 : (122 : Root) ≠ 0 → coordinates 122 = reflect (lastStep 122) (coordinates (parent 122)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_123 : (123 : Root) ≠ 0 → coordinates 123 = reflect (lastStep 123) (coordinates (parent 123)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_124 : (124 : Root) ≠ 0 → coordinates 124 = reflect (lastStep 124) (coordinates (parent 124)) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem parent_coordinates_125 : (125 : Root) ≠ 0 → coordinates 125 = reflect (lastStep 125) (coordinates (parent 125)) := by decide +kernel
theorem parent_coordinates : ∀ a : Root, a ≠ 0 → coordinates a = reflect (lastStep a) (coordinates (parent a)) := by
  intro a
  fin_cases a
  · exact parent_coordinates_0
  · exact parent_coordinates_1
  · exact parent_coordinates_2
  · exact parent_coordinates_3
  · exact parent_coordinates_4
  · exact parent_coordinates_5
  · exact parent_coordinates_6
  · exact parent_coordinates_7
  · exact parent_coordinates_8
  · exact parent_coordinates_9
  · exact parent_coordinates_10
  · exact parent_coordinates_11
  · exact parent_coordinates_12
  · exact parent_coordinates_13
  · exact parent_coordinates_14
  · exact parent_coordinates_15
  · exact parent_coordinates_16
  · exact parent_coordinates_17
  · exact parent_coordinates_18
  · exact parent_coordinates_19
  · exact parent_coordinates_20
  · exact parent_coordinates_21
  · exact parent_coordinates_22
  · exact parent_coordinates_23
  · exact parent_coordinates_24
  · exact parent_coordinates_25
  · exact parent_coordinates_26
  · exact parent_coordinates_27
  · exact parent_coordinates_28
  · exact parent_coordinates_29
  · exact parent_coordinates_30
  · exact parent_coordinates_31
  · exact parent_coordinates_32
  · exact parent_coordinates_33
  · exact parent_coordinates_34
  · exact parent_coordinates_35
  · exact parent_coordinates_36
  · exact parent_coordinates_37
  · exact parent_coordinates_38
  · exact parent_coordinates_39
  · exact parent_coordinates_40
  · exact parent_coordinates_41
  · exact parent_coordinates_42
  · exact parent_coordinates_43
  · exact parent_coordinates_44
  · exact parent_coordinates_45
  · exact parent_coordinates_46
  · exact parent_coordinates_47
  · exact parent_coordinates_48
  · exact parent_coordinates_49
  · exact parent_coordinates_50
  · exact parent_coordinates_51
  · exact parent_coordinates_52
  · exact parent_coordinates_53
  · exact parent_coordinates_54
  · exact parent_coordinates_55
  · exact parent_coordinates_56
  · exact parent_coordinates_57
  · exact parent_coordinates_58
  · exact parent_coordinates_59
  · exact parent_coordinates_60
  · exact parent_coordinates_61
  · exact parent_coordinates_62
  · exact parent_coordinates_63
  · exact parent_coordinates_64
  · exact parent_coordinates_65
  · exact parent_coordinates_66
  · exact parent_coordinates_67
  · exact parent_coordinates_68
  · exact parent_coordinates_69
  · exact parent_coordinates_70
  · exact parent_coordinates_71
  · exact parent_coordinates_72
  · exact parent_coordinates_73
  · exact parent_coordinates_74
  · exact parent_coordinates_75
  · exact parent_coordinates_76
  · exact parent_coordinates_77
  · exact parent_coordinates_78
  · exact parent_coordinates_79
  · exact parent_coordinates_80
  · exact parent_coordinates_81
  · exact parent_coordinates_82
  · exact parent_coordinates_83
  · exact parent_coordinates_84
  · exact parent_coordinates_85
  · exact parent_coordinates_86
  · exact parent_coordinates_87
  · exact parent_coordinates_88
  · exact parent_coordinates_89
  · exact parent_coordinates_90
  · exact parent_coordinates_91
  · exact parent_coordinates_92
  · exact parent_coordinates_93
  · exact parent_coordinates_94
  · exact parent_coordinates_95
  · exact parent_coordinates_96
  · exact parent_coordinates_97
  · exact parent_coordinates_98
  · exact parent_coordinates_99
  · exact parent_coordinates_100
  · exact parent_coordinates_101
  · exact parent_coordinates_102
  · exact parent_coordinates_103
  · exact parent_coordinates_104
  · exact parent_coordinates_105
  · exact parent_coordinates_106
  · exact parent_coordinates_107
  · exact parent_coordinates_108
  · exact parent_coordinates_109
  · exact parent_coordinates_110
  · exact parent_coordinates_111
  · exact parent_coordinates_112
  · exact parent_coordinates_113
  · exact parent_coordinates_114
  · exact parent_coordinates_115
  · exact parent_coordinates_116
  · exact parent_coordinates_117
  · exact parent_coordinates_118
  · exact parent_coordinates_119
  · exact parent_coordinates_120
  · exact parent_coordinates_121
  · exact parent_coordinates_122
  · exact parent_coordinates_123
  · exact parent_coordinates_124
  · exact parent_coordinates_125
#check parent_coordinates
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_0 : (0 : Root) ≠ 0 → rootWord 0 = rootWord (parent 0) ++ [lastStep 0] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_1 : (1 : Root) ≠ 0 → rootWord 1 = rootWord (parent 1) ++ [lastStep 1] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_2 : (2 : Root) ≠ 0 → rootWord 2 = rootWord (parent 2) ++ [lastStep 2] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_3 : (3 : Root) ≠ 0 → rootWord 3 = rootWord (parent 3) ++ [lastStep 3] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_4 : (4 : Root) ≠ 0 → rootWord 4 = rootWord (parent 4) ++ [lastStep 4] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_5 : (5 : Root) ≠ 0 → rootWord 5 = rootWord (parent 5) ++ [lastStep 5] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_6 : (6 : Root) ≠ 0 → rootWord 6 = rootWord (parent 6) ++ [lastStep 6] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_7 : (7 : Root) ≠ 0 → rootWord 7 = rootWord (parent 7) ++ [lastStep 7] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_8 : (8 : Root) ≠ 0 → rootWord 8 = rootWord (parent 8) ++ [lastStep 8] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_9 : (9 : Root) ≠ 0 → rootWord 9 = rootWord (parent 9) ++ [lastStep 9] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_10 : (10 : Root) ≠ 0 → rootWord 10 = rootWord (parent 10) ++ [lastStep 10] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_11 : (11 : Root) ≠ 0 → rootWord 11 = rootWord (parent 11) ++ [lastStep 11] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_12 : (12 : Root) ≠ 0 → rootWord 12 = rootWord (parent 12) ++ [lastStep 12] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_13 : (13 : Root) ≠ 0 → rootWord 13 = rootWord (parent 13) ++ [lastStep 13] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_14 : (14 : Root) ≠ 0 → rootWord 14 = rootWord (parent 14) ++ [lastStep 14] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_15 : (15 : Root) ≠ 0 → rootWord 15 = rootWord (parent 15) ++ [lastStep 15] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_16 : (16 : Root) ≠ 0 → rootWord 16 = rootWord (parent 16) ++ [lastStep 16] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_17 : (17 : Root) ≠ 0 → rootWord 17 = rootWord (parent 17) ++ [lastStep 17] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_18 : (18 : Root) ≠ 0 → rootWord 18 = rootWord (parent 18) ++ [lastStep 18] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_19 : (19 : Root) ≠ 0 → rootWord 19 = rootWord (parent 19) ++ [lastStep 19] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_20 : (20 : Root) ≠ 0 → rootWord 20 = rootWord (parent 20) ++ [lastStep 20] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_21 : (21 : Root) ≠ 0 → rootWord 21 = rootWord (parent 21) ++ [lastStep 21] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_22 : (22 : Root) ≠ 0 → rootWord 22 = rootWord (parent 22) ++ [lastStep 22] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_23 : (23 : Root) ≠ 0 → rootWord 23 = rootWord (parent 23) ++ [lastStep 23] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_24 : (24 : Root) ≠ 0 → rootWord 24 = rootWord (parent 24) ++ [lastStep 24] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_25 : (25 : Root) ≠ 0 → rootWord 25 = rootWord (parent 25) ++ [lastStep 25] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_26 : (26 : Root) ≠ 0 → rootWord 26 = rootWord (parent 26) ++ [lastStep 26] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_27 : (27 : Root) ≠ 0 → rootWord 27 = rootWord (parent 27) ++ [lastStep 27] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_28 : (28 : Root) ≠ 0 → rootWord 28 = rootWord (parent 28) ++ [lastStep 28] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_29 : (29 : Root) ≠ 0 → rootWord 29 = rootWord (parent 29) ++ [lastStep 29] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_30 : (30 : Root) ≠ 0 → rootWord 30 = rootWord (parent 30) ++ [lastStep 30] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_31 : (31 : Root) ≠ 0 → rootWord 31 = rootWord (parent 31) ++ [lastStep 31] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_32 : (32 : Root) ≠ 0 → rootWord 32 = rootWord (parent 32) ++ [lastStep 32] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_33 : (33 : Root) ≠ 0 → rootWord 33 = rootWord (parent 33) ++ [lastStep 33] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_34 : (34 : Root) ≠ 0 → rootWord 34 = rootWord (parent 34) ++ [lastStep 34] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_35 : (35 : Root) ≠ 0 → rootWord 35 = rootWord (parent 35) ++ [lastStep 35] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_36 : (36 : Root) ≠ 0 → rootWord 36 = rootWord (parent 36) ++ [lastStep 36] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_37 : (37 : Root) ≠ 0 → rootWord 37 = rootWord (parent 37) ++ [lastStep 37] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_38 : (38 : Root) ≠ 0 → rootWord 38 = rootWord (parent 38) ++ [lastStep 38] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_39 : (39 : Root) ≠ 0 → rootWord 39 = rootWord (parent 39) ++ [lastStep 39] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_40 : (40 : Root) ≠ 0 → rootWord 40 = rootWord (parent 40) ++ [lastStep 40] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_41 : (41 : Root) ≠ 0 → rootWord 41 = rootWord (parent 41) ++ [lastStep 41] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_42 : (42 : Root) ≠ 0 → rootWord 42 = rootWord (parent 42) ++ [lastStep 42] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_43 : (43 : Root) ≠ 0 → rootWord 43 = rootWord (parent 43) ++ [lastStep 43] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_44 : (44 : Root) ≠ 0 → rootWord 44 = rootWord (parent 44) ++ [lastStep 44] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_45 : (45 : Root) ≠ 0 → rootWord 45 = rootWord (parent 45) ++ [lastStep 45] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_46 : (46 : Root) ≠ 0 → rootWord 46 = rootWord (parent 46) ++ [lastStep 46] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_47 : (47 : Root) ≠ 0 → rootWord 47 = rootWord (parent 47) ++ [lastStep 47] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_48 : (48 : Root) ≠ 0 → rootWord 48 = rootWord (parent 48) ++ [lastStep 48] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_49 : (49 : Root) ≠ 0 → rootWord 49 = rootWord (parent 49) ++ [lastStep 49] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_50 : (50 : Root) ≠ 0 → rootWord 50 = rootWord (parent 50) ++ [lastStep 50] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_51 : (51 : Root) ≠ 0 → rootWord 51 = rootWord (parent 51) ++ [lastStep 51] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_52 : (52 : Root) ≠ 0 → rootWord 52 = rootWord (parent 52) ++ [lastStep 52] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_53 : (53 : Root) ≠ 0 → rootWord 53 = rootWord (parent 53) ++ [lastStep 53] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_54 : (54 : Root) ≠ 0 → rootWord 54 = rootWord (parent 54) ++ [lastStep 54] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_55 : (55 : Root) ≠ 0 → rootWord 55 = rootWord (parent 55) ++ [lastStep 55] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_56 : (56 : Root) ≠ 0 → rootWord 56 = rootWord (parent 56) ++ [lastStep 56] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_57 : (57 : Root) ≠ 0 → rootWord 57 = rootWord (parent 57) ++ [lastStep 57] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_58 : (58 : Root) ≠ 0 → rootWord 58 = rootWord (parent 58) ++ [lastStep 58] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_59 : (59 : Root) ≠ 0 → rootWord 59 = rootWord (parent 59) ++ [lastStep 59] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_60 : (60 : Root) ≠ 0 → rootWord 60 = rootWord (parent 60) ++ [lastStep 60] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_61 : (61 : Root) ≠ 0 → rootWord 61 = rootWord (parent 61) ++ [lastStep 61] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_62 : (62 : Root) ≠ 0 → rootWord 62 = rootWord (parent 62) ++ [lastStep 62] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_63 : (63 : Root) ≠ 0 → rootWord 63 = rootWord (parent 63) ++ [lastStep 63] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_64 : (64 : Root) ≠ 0 → rootWord 64 = rootWord (parent 64) ++ [lastStep 64] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_65 : (65 : Root) ≠ 0 → rootWord 65 = rootWord (parent 65) ++ [lastStep 65] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_66 : (66 : Root) ≠ 0 → rootWord 66 = rootWord (parent 66) ++ [lastStep 66] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_67 : (67 : Root) ≠ 0 → rootWord 67 = rootWord (parent 67) ++ [lastStep 67] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_68 : (68 : Root) ≠ 0 → rootWord 68 = rootWord (parent 68) ++ [lastStep 68] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_69 : (69 : Root) ≠ 0 → rootWord 69 = rootWord (parent 69) ++ [lastStep 69] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_70 : (70 : Root) ≠ 0 → rootWord 70 = rootWord (parent 70) ++ [lastStep 70] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_71 : (71 : Root) ≠ 0 → rootWord 71 = rootWord (parent 71) ++ [lastStep 71] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_72 : (72 : Root) ≠ 0 → rootWord 72 = rootWord (parent 72) ++ [lastStep 72] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_73 : (73 : Root) ≠ 0 → rootWord 73 = rootWord (parent 73) ++ [lastStep 73] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_74 : (74 : Root) ≠ 0 → rootWord 74 = rootWord (parent 74) ++ [lastStep 74] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_75 : (75 : Root) ≠ 0 → rootWord 75 = rootWord (parent 75) ++ [lastStep 75] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_76 : (76 : Root) ≠ 0 → rootWord 76 = rootWord (parent 76) ++ [lastStep 76] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_77 : (77 : Root) ≠ 0 → rootWord 77 = rootWord (parent 77) ++ [lastStep 77] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_78 : (78 : Root) ≠ 0 → rootWord 78 = rootWord (parent 78) ++ [lastStep 78] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_79 : (79 : Root) ≠ 0 → rootWord 79 = rootWord (parent 79) ++ [lastStep 79] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_80 : (80 : Root) ≠ 0 → rootWord 80 = rootWord (parent 80) ++ [lastStep 80] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_81 : (81 : Root) ≠ 0 → rootWord 81 = rootWord (parent 81) ++ [lastStep 81] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_82 : (82 : Root) ≠ 0 → rootWord 82 = rootWord (parent 82) ++ [lastStep 82] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_83 : (83 : Root) ≠ 0 → rootWord 83 = rootWord (parent 83) ++ [lastStep 83] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_84 : (84 : Root) ≠ 0 → rootWord 84 = rootWord (parent 84) ++ [lastStep 84] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_85 : (85 : Root) ≠ 0 → rootWord 85 = rootWord (parent 85) ++ [lastStep 85] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_86 : (86 : Root) ≠ 0 → rootWord 86 = rootWord (parent 86) ++ [lastStep 86] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_87 : (87 : Root) ≠ 0 → rootWord 87 = rootWord (parent 87) ++ [lastStep 87] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_88 : (88 : Root) ≠ 0 → rootWord 88 = rootWord (parent 88) ++ [lastStep 88] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_89 : (89 : Root) ≠ 0 → rootWord 89 = rootWord (parent 89) ++ [lastStep 89] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_90 : (90 : Root) ≠ 0 → rootWord 90 = rootWord (parent 90) ++ [lastStep 90] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_91 : (91 : Root) ≠ 0 → rootWord 91 = rootWord (parent 91) ++ [lastStep 91] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_92 : (92 : Root) ≠ 0 → rootWord 92 = rootWord (parent 92) ++ [lastStep 92] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_93 : (93 : Root) ≠ 0 → rootWord 93 = rootWord (parent 93) ++ [lastStep 93] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_94 : (94 : Root) ≠ 0 → rootWord 94 = rootWord (parent 94) ++ [lastStep 94] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_95 : (95 : Root) ≠ 0 → rootWord 95 = rootWord (parent 95) ++ [lastStep 95] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_96 : (96 : Root) ≠ 0 → rootWord 96 = rootWord (parent 96) ++ [lastStep 96] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_97 : (97 : Root) ≠ 0 → rootWord 97 = rootWord (parent 97) ++ [lastStep 97] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_98 : (98 : Root) ≠ 0 → rootWord 98 = rootWord (parent 98) ++ [lastStep 98] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_99 : (99 : Root) ≠ 0 → rootWord 99 = rootWord (parent 99) ++ [lastStep 99] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_100 : (100 : Root) ≠ 0 → rootWord 100 = rootWord (parent 100) ++ [lastStep 100] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_101 : (101 : Root) ≠ 0 → rootWord 101 = rootWord (parent 101) ++ [lastStep 101] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_102 : (102 : Root) ≠ 0 → rootWord 102 = rootWord (parent 102) ++ [lastStep 102] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_103 : (103 : Root) ≠ 0 → rootWord 103 = rootWord (parent 103) ++ [lastStep 103] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_104 : (104 : Root) ≠ 0 → rootWord 104 = rootWord (parent 104) ++ [lastStep 104] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_105 : (105 : Root) ≠ 0 → rootWord 105 = rootWord (parent 105) ++ [lastStep 105] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_106 : (106 : Root) ≠ 0 → rootWord 106 = rootWord (parent 106) ++ [lastStep 106] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_107 : (107 : Root) ≠ 0 → rootWord 107 = rootWord (parent 107) ++ [lastStep 107] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_108 : (108 : Root) ≠ 0 → rootWord 108 = rootWord (parent 108) ++ [lastStep 108] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_109 : (109 : Root) ≠ 0 → rootWord 109 = rootWord (parent 109) ++ [lastStep 109] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_110 : (110 : Root) ≠ 0 → rootWord 110 = rootWord (parent 110) ++ [lastStep 110] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_111 : (111 : Root) ≠ 0 → rootWord 111 = rootWord (parent 111) ++ [lastStep 111] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_112 : (112 : Root) ≠ 0 → rootWord 112 = rootWord (parent 112) ++ [lastStep 112] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_113 : (113 : Root) ≠ 0 → rootWord 113 = rootWord (parent 113) ++ [lastStep 113] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_114 : (114 : Root) ≠ 0 → rootWord 114 = rootWord (parent 114) ++ [lastStep 114] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_115 : (115 : Root) ≠ 0 → rootWord 115 = rootWord (parent 115) ++ [lastStep 115] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_116 : (116 : Root) ≠ 0 → rootWord 116 = rootWord (parent 116) ++ [lastStep 116] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_117 : (117 : Root) ≠ 0 → rootWord 117 = rootWord (parent 117) ++ [lastStep 117] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_118 : (118 : Root) ≠ 0 → rootWord 118 = rootWord (parent 118) ++ [lastStep 118] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_119 : (119 : Root) ≠ 0 → rootWord 119 = rootWord (parent 119) ++ [lastStep 119] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_120 : (120 : Root) ≠ 0 → rootWord 120 = rootWord (parent 120) ++ [lastStep 120] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_121 : (121 : Root) ≠ 0 → rootWord 121 = rootWord (parent 121) ++ [lastStep 121] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_122 : (122 : Root) ≠ 0 → rootWord 122 = rootWord (parent 122) ++ [lastStep 122] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_123 : (123 : Root) ≠ 0 → rootWord 123 = rootWord (parent 123) ++ [lastStep 123] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_124 : (124 : Root) ≠ 0 → rootWord 124 = rootWord (parent 124) ++ [lastStep 124] := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem root_word_step_125 : (125 : Root) ≠ 0 → rootWord 125 = rootWord (parent 125) ++ [lastStep 125] := by decide +kernel
theorem root_word_step : ∀ a : Root, a ≠ 0 → rootWord a = rootWord (parent a) ++ [lastStep a] := by
  intro a
  fin_cases a
  · exact root_word_step_0
  · exact root_word_step_1
  · exact root_word_step_2
  · exact root_word_step_3
  · exact root_word_step_4
  · exact root_word_step_5
  · exact root_word_step_6
  · exact root_word_step_7
  · exact root_word_step_8
  · exact root_word_step_9
  · exact root_word_step_10
  · exact root_word_step_11
  · exact root_word_step_12
  · exact root_word_step_13
  · exact root_word_step_14
  · exact root_word_step_15
  · exact root_word_step_16
  · exact root_word_step_17
  · exact root_word_step_18
  · exact root_word_step_19
  · exact root_word_step_20
  · exact root_word_step_21
  · exact root_word_step_22
  · exact root_word_step_23
  · exact root_word_step_24
  · exact root_word_step_25
  · exact root_word_step_26
  · exact root_word_step_27
  · exact root_word_step_28
  · exact root_word_step_29
  · exact root_word_step_30
  · exact root_word_step_31
  · exact root_word_step_32
  · exact root_word_step_33
  · exact root_word_step_34
  · exact root_word_step_35
  · exact root_word_step_36
  · exact root_word_step_37
  · exact root_word_step_38
  · exact root_word_step_39
  · exact root_word_step_40
  · exact root_word_step_41
  · exact root_word_step_42
  · exact root_word_step_43
  · exact root_word_step_44
  · exact root_word_step_45
  · exact root_word_step_46
  · exact root_word_step_47
  · exact root_word_step_48
  · exact root_word_step_49
  · exact root_word_step_50
  · exact root_word_step_51
  · exact root_word_step_52
  · exact root_word_step_53
  · exact root_word_step_54
  · exact root_word_step_55
  · exact root_word_step_56
  · exact root_word_step_57
  · exact root_word_step_58
  · exact root_word_step_59
  · exact root_word_step_60
  · exact root_word_step_61
  · exact root_word_step_62
  · exact root_word_step_63
  · exact root_word_step_64
  · exact root_word_step_65
  · exact root_word_step_66
  · exact root_word_step_67
  · exact root_word_step_68
  · exact root_word_step_69
  · exact root_word_step_70
  · exact root_word_step_71
  · exact root_word_step_72
  · exact root_word_step_73
  · exact root_word_step_74
  · exact root_word_step_75
  · exact root_word_step_76
  · exact root_word_step_77
  · exact root_word_step_78
  · exact root_word_step_79
  · exact root_word_step_80
  · exact root_word_step_81
  · exact root_word_step_82
  · exact root_word_step_83
  · exact root_word_step_84
  · exact root_word_step_85
  · exact root_word_step_86
  · exact root_word_step_87
  · exact root_word_step_88
  · exact root_word_step_89
  · exact root_word_step_90
  · exact root_word_step_91
  · exact root_word_step_92
  · exact root_word_step_93
  · exact root_word_step_94
  · exact root_word_step_95
  · exact root_word_step_96
  · exact root_word_step_97
  · exact root_word_step_98
  · exact root_word_step_99
  · exact root_word_step_100
  · exact root_word_step_101
  · exact root_word_step_102
  · exact root_word_step_103
  · exact root_word_step_104
  · exact root_word_step_105
  · exact root_word_step_106
  · exact root_word_step_107
  · exact root_word_step_108
  · exact root_word_step_109
  · exact root_word_step_110
  · exact root_word_step_111
  · exact root_word_step_112
  · exact root_word_step_113
  · exact root_word_step_114
  · exact root_word_step_115
  · exact root_word_step_116
  · exact root_word_step_117
  · exact root_word_step_118
  · exact root_word_step_119
  · exact root_word_step_120
  · exact root_word_step_121
  · exact root_word_step_122
  · exact root_word_step_123
  · exact root_word_step_124
  · exact root_word_step_125
#check root_word_step
theorem root_word_coordinates (a : Root) :
    wordAction (rootWord a) (Pi.single 0 1) = coordinates a := by
  induction a using Fin.strong_induction_on with
  | h a ih =>
    by_cases hz : a = 0
    · subst a; decide
    · rw [root_word_step a hz, wordAction_append, ih (parent a) (parent_lt a hz)]
      exact (parent_coordinates a hz).symm
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_0 : (∀ i, 0 ≤ coordinates 0 i) ∨ (∀ i, coordinates 0 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_1 : (∀ i, 0 ≤ coordinates 1 i) ∨ (∀ i, coordinates 1 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_2 : (∀ i, 0 ≤ coordinates 2 i) ∨ (∀ i, coordinates 2 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_3 : (∀ i, 0 ≤ coordinates 3 i) ∨ (∀ i, coordinates 3 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_4 : (∀ i, 0 ≤ coordinates 4 i) ∨ (∀ i, coordinates 4 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_5 : (∀ i, 0 ≤ coordinates 5 i) ∨ (∀ i, coordinates 5 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_6 : (∀ i, 0 ≤ coordinates 6 i) ∨ (∀ i, coordinates 6 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_7 : (∀ i, 0 ≤ coordinates 7 i) ∨ (∀ i, coordinates 7 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_8 : (∀ i, 0 ≤ coordinates 8 i) ∨ (∀ i, coordinates 8 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_9 : (∀ i, 0 ≤ coordinates 9 i) ∨ (∀ i, coordinates 9 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_10 : (∀ i, 0 ≤ coordinates 10 i) ∨ (∀ i, coordinates 10 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_11 : (∀ i, 0 ≤ coordinates 11 i) ∨ (∀ i, coordinates 11 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_12 : (∀ i, 0 ≤ coordinates 12 i) ∨ (∀ i, coordinates 12 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_13 : (∀ i, 0 ≤ coordinates 13 i) ∨ (∀ i, coordinates 13 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_14 : (∀ i, 0 ≤ coordinates 14 i) ∨ (∀ i, coordinates 14 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_15 : (∀ i, 0 ≤ coordinates 15 i) ∨ (∀ i, coordinates 15 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_16 : (∀ i, 0 ≤ coordinates 16 i) ∨ (∀ i, coordinates 16 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_17 : (∀ i, 0 ≤ coordinates 17 i) ∨ (∀ i, coordinates 17 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_18 : (∀ i, 0 ≤ coordinates 18 i) ∨ (∀ i, coordinates 18 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_19 : (∀ i, 0 ≤ coordinates 19 i) ∨ (∀ i, coordinates 19 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_20 : (∀ i, 0 ≤ coordinates 20 i) ∨ (∀ i, coordinates 20 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_21 : (∀ i, 0 ≤ coordinates 21 i) ∨ (∀ i, coordinates 21 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_22 : (∀ i, 0 ≤ coordinates 22 i) ∨ (∀ i, coordinates 22 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_23 : (∀ i, 0 ≤ coordinates 23 i) ∨ (∀ i, coordinates 23 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_24 : (∀ i, 0 ≤ coordinates 24 i) ∨ (∀ i, coordinates 24 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_25 : (∀ i, 0 ≤ coordinates 25 i) ∨ (∀ i, coordinates 25 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_26 : (∀ i, 0 ≤ coordinates 26 i) ∨ (∀ i, coordinates 26 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_27 : (∀ i, 0 ≤ coordinates 27 i) ∨ (∀ i, coordinates 27 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_28 : (∀ i, 0 ≤ coordinates 28 i) ∨ (∀ i, coordinates 28 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_29 : (∀ i, 0 ≤ coordinates 29 i) ∨ (∀ i, coordinates 29 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_30 : (∀ i, 0 ≤ coordinates 30 i) ∨ (∀ i, coordinates 30 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_31 : (∀ i, 0 ≤ coordinates 31 i) ∨ (∀ i, coordinates 31 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_32 : (∀ i, 0 ≤ coordinates 32 i) ∨ (∀ i, coordinates 32 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_33 : (∀ i, 0 ≤ coordinates 33 i) ∨ (∀ i, coordinates 33 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_34 : (∀ i, 0 ≤ coordinates 34 i) ∨ (∀ i, coordinates 34 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_35 : (∀ i, 0 ≤ coordinates 35 i) ∨ (∀ i, coordinates 35 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_36 : (∀ i, 0 ≤ coordinates 36 i) ∨ (∀ i, coordinates 36 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_37 : (∀ i, 0 ≤ coordinates 37 i) ∨ (∀ i, coordinates 37 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_38 : (∀ i, 0 ≤ coordinates 38 i) ∨ (∀ i, coordinates 38 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_39 : (∀ i, 0 ≤ coordinates 39 i) ∨ (∀ i, coordinates 39 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_40 : (∀ i, 0 ≤ coordinates 40 i) ∨ (∀ i, coordinates 40 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_41 : (∀ i, 0 ≤ coordinates 41 i) ∨ (∀ i, coordinates 41 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_42 : (∀ i, 0 ≤ coordinates 42 i) ∨ (∀ i, coordinates 42 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_43 : (∀ i, 0 ≤ coordinates 43 i) ∨ (∀ i, coordinates 43 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_44 : (∀ i, 0 ≤ coordinates 44 i) ∨ (∀ i, coordinates 44 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_45 : (∀ i, 0 ≤ coordinates 45 i) ∨ (∀ i, coordinates 45 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_46 : (∀ i, 0 ≤ coordinates 46 i) ∨ (∀ i, coordinates 46 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_47 : (∀ i, 0 ≤ coordinates 47 i) ∨ (∀ i, coordinates 47 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_48 : (∀ i, 0 ≤ coordinates 48 i) ∨ (∀ i, coordinates 48 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_49 : (∀ i, 0 ≤ coordinates 49 i) ∨ (∀ i, coordinates 49 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_50 : (∀ i, 0 ≤ coordinates 50 i) ∨ (∀ i, coordinates 50 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_51 : (∀ i, 0 ≤ coordinates 51 i) ∨ (∀ i, coordinates 51 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_52 : (∀ i, 0 ≤ coordinates 52 i) ∨ (∀ i, coordinates 52 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_53 : (∀ i, 0 ≤ coordinates 53 i) ∨ (∀ i, coordinates 53 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_54 : (∀ i, 0 ≤ coordinates 54 i) ∨ (∀ i, coordinates 54 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_55 : (∀ i, 0 ≤ coordinates 55 i) ∨ (∀ i, coordinates 55 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_56 : (∀ i, 0 ≤ coordinates 56 i) ∨ (∀ i, coordinates 56 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_57 : (∀ i, 0 ≤ coordinates 57 i) ∨ (∀ i, coordinates 57 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_58 : (∀ i, 0 ≤ coordinates 58 i) ∨ (∀ i, coordinates 58 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_59 : (∀ i, 0 ≤ coordinates 59 i) ∨ (∀ i, coordinates 59 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_60 : (∀ i, 0 ≤ coordinates 60 i) ∨ (∀ i, coordinates 60 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_61 : (∀ i, 0 ≤ coordinates 61 i) ∨ (∀ i, coordinates 61 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_62 : (∀ i, 0 ≤ coordinates 62 i) ∨ (∀ i, coordinates 62 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_63 : (∀ i, 0 ≤ coordinates 63 i) ∨ (∀ i, coordinates 63 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_64 : (∀ i, 0 ≤ coordinates 64 i) ∨ (∀ i, coordinates 64 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_65 : (∀ i, 0 ≤ coordinates 65 i) ∨ (∀ i, coordinates 65 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_66 : (∀ i, 0 ≤ coordinates 66 i) ∨ (∀ i, coordinates 66 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_67 : (∀ i, 0 ≤ coordinates 67 i) ∨ (∀ i, coordinates 67 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_68 : (∀ i, 0 ≤ coordinates 68 i) ∨ (∀ i, coordinates 68 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_69 : (∀ i, 0 ≤ coordinates 69 i) ∨ (∀ i, coordinates 69 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_70 : (∀ i, 0 ≤ coordinates 70 i) ∨ (∀ i, coordinates 70 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_71 : (∀ i, 0 ≤ coordinates 71 i) ∨ (∀ i, coordinates 71 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_72 : (∀ i, 0 ≤ coordinates 72 i) ∨ (∀ i, coordinates 72 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_73 : (∀ i, 0 ≤ coordinates 73 i) ∨ (∀ i, coordinates 73 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_74 : (∀ i, 0 ≤ coordinates 74 i) ∨ (∀ i, coordinates 74 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_75 : (∀ i, 0 ≤ coordinates 75 i) ∨ (∀ i, coordinates 75 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_76 : (∀ i, 0 ≤ coordinates 76 i) ∨ (∀ i, coordinates 76 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_77 : (∀ i, 0 ≤ coordinates 77 i) ∨ (∀ i, coordinates 77 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_78 : (∀ i, 0 ≤ coordinates 78 i) ∨ (∀ i, coordinates 78 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_79 : (∀ i, 0 ≤ coordinates 79 i) ∨ (∀ i, coordinates 79 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_80 : (∀ i, 0 ≤ coordinates 80 i) ∨ (∀ i, coordinates 80 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_81 : (∀ i, 0 ≤ coordinates 81 i) ∨ (∀ i, coordinates 81 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_82 : (∀ i, 0 ≤ coordinates 82 i) ∨ (∀ i, coordinates 82 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_83 : (∀ i, 0 ≤ coordinates 83 i) ∨ (∀ i, coordinates 83 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_84 : (∀ i, 0 ≤ coordinates 84 i) ∨ (∀ i, coordinates 84 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_85 : (∀ i, 0 ≤ coordinates 85 i) ∨ (∀ i, coordinates 85 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_86 : (∀ i, 0 ≤ coordinates 86 i) ∨ (∀ i, coordinates 86 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_87 : (∀ i, 0 ≤ coordinates 87 i) ∨ (∀ i, coordinates 87 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_88 : (∀ i, 0 ≤ coordinates 88 i) ∨ (∀ i, coordinates 88 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_89 : (∀ i, 0 ≤ coordinates 89 i) ∨ (∀ i, coordinates 89 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_90 : (∀ i, 0 ≤ coordinates 90 i) ∨ (∀ i, coordinates 90 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_91 : (∀ i, 0 ≤ coordinates 91 i) ∨ (∀ i, coordinates 91 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_92 : (∀ i, 0 ≤ coordinates 92 i) ∨ (∀ i, coordinates 92 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_93 : (∀ i, 0 ≤ coordinates 93 i) ∨ (∀ i, coordinates 93 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_94 : (∀ i, 0 ≤ coordinates 94 i) ∨ (∀ i, coordinates 94 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_95 : (∀ i, 0 ≤ coordinates 95 i) ∨ (∀ i, coordinates 95 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_96 : (∀ i, 0 ≤ coordinates 96 i) ∨ (∀ i, coordinates 96 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_97 : (∀ i, 0 ≤ coordinates 97 i) ∨ (∀ i, coordinates 97 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_98 : (∀ i, 0 ≤ coordinates 98 i) ∨ (∀ i, coordinates 98 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_99 : (∀ i, 0 ≤ coordinates 99 i) ∨ (∀ i, coordinates 99 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_100 : (∀ i, 0 ≤ coordinates 100 i) ∨ (∀ i, coordinates 100 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_101 : (∀ i, 0 ≤ coordinates 101 i) ∨ (∀ i, coordinates 101 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_102 : (∀ i, 0 ≤ coordinates 102 i) ∨ (∀ i, coordinates 102 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_103 : (∀ i, 0 ≤ coordinates 103 i) ∨ (∀ i, coordinates 103 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_104 : (∀ i, 0 ≤ coordinates 104 i) ∨ (∀ i, coordinates 104 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_105 : (∀ i, 0 ≤ coordinates 105 i) ∨ (∀ i, coordinates 105 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_106 : (∀ i, 0 ≤ coordinates 106 i) ∨ (∀ i, coordinates 106 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_107 : (∀ i, 0 ≤ coordinates 107 i) ∨ (∀ i, coordinates 107 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_108 : (∀ i, 0 ≤ coordinates 108 i) ∨ (∀ i, coordinates 108 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_109 : (∀ i, 0 ≤ coordinates 109 i) ∨ (∀ i, coordinates 109 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_110 : (∀ i, 0 ≤ coordinates 110 i) ∨ (∀ i, coordinates 110 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_111 : (∀ i, 0 ≤ coordinates 111 i) ∨ (∀ i, coordinates 111 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_112 : (∀ i, 0 ≤ coordinates 112 i) ∨ (∀ i, coordinates 112 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_113 : (∀ i, 0 ≤ coordinates 113 i) ∨ (∀ i, coordinates 113 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_114 : (∀ i, 0 ≤ coordinates 114 i) ∨ (∀ i, coordinates 114 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_115 : (∀ i, 0 ≤ coordinates 115 i) ∨ (∀ i, coordinates 115 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_116 : (∀ i, 0 ≤ coordinates 116 i) ∨ (∀ i, coordinates 116 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_117 : (∀ i, 0 ≤ coordinates 117 i) ∨ (∀ i, coordinates 117 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_118 : (∀ i, 0 ≤ coordinates 118 i) ∨ (∀ i, coordinates 118 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_119 : (∀ i, 0 ≤ coordinates 119 i) ∨ (∀ i, coordinates 119 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_120 : (∀ i, 0 ≤ coordinates 120 i) ∨ (∀ i, coordinates 120 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_121 : (∀ i, 0 ≤ coordinates 121 i) ∨ (∀ i, coordinates 121 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_122 : (∀ i, 0 ≤ coordinates 122 i) ∨ (∀ i, coordinates 122 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_123 : (∀ i, 0 ≤ coordinates 123 i) ∨ (∀ i, coordinates 123 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_124 : (∀ i, 0 ≤ coordinates 124 i) ∨ (∀ i, coordinates 124 i ≤ 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem sign_coherent_125 : (∀ i, 0 ≤ coordinates 125 i) ∨ (∀ i, coordinates 125 i ≤ 0) := by decide +kernel
theorem sign_coherent : ∀ a : Root, (∀ i, 0 ≤ coordinates a i) ∨ (∀ i, coordinates a i ≤ 0) := by
  intro a
  fin_cases a
  · exact sign_coherent_0
  · exact sign_coherent_1
  · exact sign_coherent_2
  · exact sign_coherent_3
  · exact sign_coherent_4
  · exact sign_coherent_5
  · exact sign_coherent_6
  · exact sign_coherent_7
  · exact sign_coherent_8
  · exact sign_coherent_9
  · exact sign_coherent_10
  · exact sign_coherent_11
  · exact sign_coherent_12
  · exact sign_coherent_13
  · exact sign_coherent_14
  · exact sign_coherent_15
  · exact sign_coherent_16
  · exact sign_coherent_17
  · exact sign_coherent_18
  · exact sign_coherent_19
  · exact sign_coherent_20
  · exact sign_coherent_21
  · exact sign_coherent_22
  · exact sign_coherent_23
  · exact sign_coherent_24
  · exact sign_coherent_25
  · exact sign_coherent_26
  · exact sign_coherent_27
  · exact sign_coherent_28
  · exact sign_coherent_29
  · exact sign_coherent_30
  · exact sign_coherent_31
  · exact sign_coherent_32
  · exact sign_coherent_33
  · exact sign_coherent_34
  · exact sign_coherent_35
  · exact sign_coherent_36
  · exact sign_coherent_37
  · exact sign_coherent_38
  · exact sign_coherent_39
  · exact sign_coherent_40
  · exact sign_coherent_41
  · exact sign_coherent_42
  · exact sign_coherent_43
  · exact sign_coherent_44
  · exact sign_coherent_45
  · exact sign_coherent_46
  · exact sign_coherent_47
  · exact sign_coherent_48
  · exact sign_coherent_49
  · exact sign_coherent_50
  · exact sign_coherent_51
  · exact sign_coherent_52
  · exact sign_coherent_53
  · exact sign_coherent_54
  · exact sign_coherent_55
  · exact sign_coherent_56
  · exact sign_coherent_57
  · exact sign_coherent_58
  · exact sign_coherent_59
  · exact sign_coherent_60
  · exact sign_coherent_61
  · exact sign_coherent_62
  · exact sign_coherent_63
  · exact sign_coherent_64
  · exact sign_coherent_65
  · exact sign_coherent_66
  · exact sign_coherent_67
  · exact sign_coherent_68
  · exact sign_coherent_69
  · exact sign_coherent_70
  · exact sign_coherent_71
  · exact sign_coherent_72
  · exact sign_coherent_73
  · exact sign_coherent_74
  · exact sign_coherent_75
  · exact sign_coherent_76
  · exact sign_coherent_77
  · exact sign_coherent_78
  · exact sign_coherent_79
  · exact sign_coherent_80
  · exact sign_coherent_81
  · exact sign_coherent_82
  · exact sign_coherent_83
  · exact sign_coherent_84
  · exact sign_coherent_85
  · exact sign_coherent_86
  · exact sign_coherent_87
  · exact sign_coherent_88
  · exact sign_coherent_89
  · exact sign_coherent_90
  · exact sign_coherent_91
  · exact sign_coherent_92
  · exact sign_coherent_93
  · exact sign_coherent_94
  · exact sign_coherent_95
  · exact sign_coherent_96
  · exact sign_coherent_97
  · exact sign_coherent_98
  · exact sign_coherent_99
  · exact sign_coherent_100
  · exact sign_coherent_101
  · exact sign_coherent_102
  · exact sign_coherent_103
  · exact sign_coherent_104
  · exact sign_coherent_105
  · exact sign_coherent_106
  · exact sign_coherent_107
  · exact sign_coherent_108
  · exact sign_coherent_109
  · exact sign_coherent_110
  · exact sign_coherent_111
  · exact sign_coherent_112
  · exact sign_coherent_113
  · exact sign_coherent_114
  · exact sign_coherent_115
  · exact sign_coherent_116
  · exact sign_coherent_117
  · exact sign_coherent_118
  · exact sign_coherent_119
  · exact sign_coherent_120
  · exact sign_coherent_121
  · exact sign_coherent_122
  · exact sign_coherent_123
  · exact sign_coherent_124
  · exact sign_coherent_125
#check sign_coherent
end Atlas.Chevalley.E7Table
