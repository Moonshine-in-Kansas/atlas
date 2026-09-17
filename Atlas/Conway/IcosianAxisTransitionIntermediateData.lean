import Atlas.Conway.IcosianAxisTransitionWords
import Atlas.Conway.IcosianEightAxisNeighbors

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianAxisTransitionTargetIndex : Fin 4 → Fin 3 → Fin 8 :=
  ![![0,1,6],![0,2,5],![0,3,4],![0,7,0]]

def icosianAxisTransitionTarget (k : Fin 4) (i : Fin 3) : IcosianRoot :=
  if i=0 then icosianAxisRoot (0,1)
  else icosianEightNeighborRoot (icosianAxisTransitionTargetIndex k i)

def icosianAxisTransitionTargetRaw (k : Fin 4) (i : Fin 3) :
    IcosianRationalCoordinates :=
  if i=0 then Pi.single 0 2 else fun j =>
    if j=0 then 0 else if j=1 then icosianCoordinatesQuaternion (icosianEightNeighborData 0)
    else icosianCoordinatesQuaternion (icosianEightNeighborData (icosianAxisTransitionTargetIndex k i))

/-- Twelve explicit right scalar multipliers, used only to certify the twelve
local images of coordinate root vectors. -/
def icosianAxisTransitionScalarData : Fin 4 → Fin 3 → IcosianIntegerCoordinates := ![
  ![![0,0,1,0,1,-1,0,-1],![-2,0,0,0,0,0,0,0],![0,0,2,0,0,0,0,0]],
  ![![0,0,-1,1,0,-1,1,0],![-1,0,1,0,1,0,1,0],![-1,0,1,0,-1,0,-1,0]],
  ![![0,0,0,-1,-1,0,1,-1],![-1,0,1,0,1,0,-1,0],![-1,0,1,0,-1,0,1,0]],
  ![![1,0,0,0,0,-1,-1,1],![0,0,-2,0,0,0,0,0],![-2,0,0,0,0,0,0,0]]]

def icosianAxisTransitionScalar (k : Fin 4) (i : Fin 3) : IcosianQuaternion :=
  icosianCoordinatesQuaternion (icosianAxisTransitionScalarData k i)

def icosianAxisFirstData : Fin 3 → Fin 3 → IcosianIntegerCoordinates :=
  ![![![0,0,0,0,0,0,0,0],![-1,0,1,0,-1,0,-1,2],![-1,0,1,0,-1,0,-1,2]],![![-1,0,-1,0,1,0,1,-2],![2,0,0,0,0,0,0,0],![-2,0,0,0,0,0,0,0]],![![-1,0,-1,0,1,0,1,-2],![-2,0,0,0,0,0,0,0],![2,0,0,0,0,0,0,0]]]

def icosianAxisMiddleData : Fin 3 → Fin 3 → Fin 3 → IcosianIntegerCoordinates :=
  ![![![![0,0,0,0,0,0,0,0],![1,0,1,0,-1,2,1,0],![1,0,1,0,-1,2,1,0]],![![-1,0,-1,0,1,0,1,-2],![0,0,2,0,0,0,0,0],![0,0,-2,0,0,0,0,0]],![![-1,0,-1,0,1,0,1,-2],![0,0,-2,0,0,0,0,0],![0,0,2,0,0,0,0,0]]],![![![0,0,0,0,0,0,0,0],![1,-2,1,0,1,0,-1,0],![1,-2,1,0,1,0,-1,0]],![![-1,0,-1,0,1,0,1,-2],![0,0,0,0,0,0,-2,0],![0,0,0,0,0,0,2,0]],![![-1,0,-1,0,1,0,1,-2],![0,0,0,0,0,0,2,0],![0,0,0,0,0,0,-2,0]]],![![![0,0,0,0,0,0,0,0],![1,0,-1,2,-1,0,-1,0],![1,0,-1,2,-1,0,-1,0]],![![-1,0,-1,0,1,0,1,-2],![0,0,0,0,-2,0,0,0],![0,0,0,0,2,0,0,0]],![![-1,0,-1,0,1,0,1,-2],![0,0,0,0,2,0,0,0],![0,0,0,0,-2,0,0,0]]]]

def icosianAxisFirstVector (i : Fin 3) : IcosianRationalCoordinates :=
  fun j => icosianCoordinatesQuaternion (icosianAxisFirstData i j)

def icosianAxisMiddleVector (k i : Fin 3) : IcosianRationalCoordinates :=
  fun j => icosianCoordinatesQuaternion (icosianAxisMiddleData k i j)

end Atlas.Conway
