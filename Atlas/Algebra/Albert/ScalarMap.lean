import Atlas.Algebra.Albert.Cubic

namespace Atlas.Albert
variable {R S : Type*} [CommRing R] [CommRing S]

def map (f : R →+* S) (x : Carrier R) : Carrier S :=
  (fun i => f (x.1 i), fun i j => f (x.2 i j))

theorem norm_map (f : R →+* S) (x : Carrier R) : norm (map f x) = f (norm x) := by
  simp [norm, map, SplitOctonion.norm, SplitOctonion.trace, SplitOctonion.mul]

theorem trace_map (f : R →+* S) (x : Carrier R) : trace (map f x) = f (trace x) := by
  simp [trace, map]

theorem quadraticTrace_map (f : R →+* S) (x : Carrier R) :
    quadraticTrace (map f x) = f (quadraticTrace x) := by
  simp [quadraticTrace, map, SplitOctonion.norm]

theorem map_add (f : R →+* S) (x y : Carrier R) : map f (x+y) = map f x + map f y := by
  apply Prod.ext
  · funext i; exact f.map_add _ _
  · funext i j; exact f.map_add _ _

theorem map_unit (f : R →+* S) : map f unit = unit := by
  apply Prod.ext
  · funext i; exact f.map_one
  · funext i j; exact f.map_zero

end Atlas.Albert
