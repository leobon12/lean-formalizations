import LQGMetric.Papers.GM.S5.Geom56P3
import LQGMetric.Papers.GM.S5.Geom56CFin

/-!
# GM Lemma 5.6: the deterministic geometry `L56GeomN` (task P2-M2L56c)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, l. 2963–2989:
`l56Paths` (the paths `π±`, Geom56P3.lean) with `l56ConstrN_of_paths`, `l56GeomN_of_paths`
(Geom56CFin.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric.GM

/-- the deterministic part of GM Lemma 5.6 -/
theorem l56GeomN : L56GeomN := l56GeomN_of_paths l56Paths

end LQGMetric.GM
