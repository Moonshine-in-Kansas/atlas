import Atlas.Conway.IcosianCentralizer

namespace Atlas.Conway

instance icosianHermitianGroup_finite : Finite icosianHermitianGroup :=
  Finite.of_injective icosianHermitianToCo0 icosianHermitianToCo0_injective

end Atlas.Conway
