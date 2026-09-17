import Atlas.Sporadic.Mathieu22
import Atlas.Mathieu.Mathieu22Simplicity

namespace Atlas.Sporadic.Mathieu22

theorem isSimpleGroup (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    IsSimpleGroup (Model a b) := Atlas.Codes.mathieu22_simple a b

end Atlas.Sporadic.Mathieu22
