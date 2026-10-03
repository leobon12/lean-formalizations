import LQGMetric.Field.ExistGFF
import LQGMetric.Papers.GM.S1.Defs

/-!
# `GM.ExistsNormalizedGFF` (blueprint M1 row 4 / §5, field layer `F.GFF-exist`; obligation N1)

Proved by `GFFExist.exists_normalizedWPGFF` (task P2-EXIST).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace GM

/-- **N1**: a normalized whole-plane GFF exists (`GM.ExistsNormalizedGFF`). -/
theorem existsNormalizedGFF : ExistsNormalizedGFF := GFFExist.exists_normalizedWPGFF

end GM
end LQGMetric
