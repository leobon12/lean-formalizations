import GaussianLQG.Uniform.RSW.Law
import GaussianLQG.Uniform.RSW.P10
import GaussianLQG.Uniform.RSW.Phi
import GaussianLQG.Uniform.RSW.Psi

/-!
# DDDF Prop 10 and the RSW estimates with constants uniform in `ξ` (Route U, items U3–U4)

Phase B, packet PB-RSW. Root module of `GaussianLQG/Uniform/RSW/`. Mathematical source: the
uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex` (U1, U3, U4, §OP-3) and the
feasibility study `planning/audits/B1-S6-feasibility.md` (§3b rows 14–17, §4 U3–U4). The
fixed-`ξ` templates are in `LQGMetric/Papers/DDDF/` (`P10Core`, `P10Main`, `RSWLow`, `RSWHigh`,
`RSWUnif`, `RSWUnifQ`, `C8`, `C8High`, `RSWUncond`); none of them is edited.

Every result comes in two forms.

* The ledger's U-form (OP-3, option (b)): a fixed white noise `hW : IsWhiteNoise P W`, then the
  constants, then `∀ ξ ∈ Ioc 0 ξs`. Names: `Prop10U ξs P W`, `prop10_unif`, `rsw_low_xi`,
  `rsw_high_xi`, `rsw_low_unif_xi`, `rsw_high_unif_xi`, `rsw_low_quantile_unif`,
  `rsw_high_quantile_unif`, `psi_rsw_low_quantile_unif`, `psi_rsw_high_quantile_unif`.
* A stronger form with the constants chosen before the probability space (suffix `_all`,
  `Prop10UAll`), from which the U-form follows by instantiation. It is obtained from a
  reference white noise on `(ℕ → ℝ, stdP)` and the law invariance of crossing lengths
  (`measure_crossLenIn_le_eq`) and of `X_{a,b}` (`RSW/Law.lean`).

Contents:

* `RSW/Law.lean`: the law of `(W (F i))_i` does not depend on the white noise (`map_wn_eq`); the
  law of `X_{a,b}` on a translated box does not depend on it (`map_XAB_shift_eq`); hence the
  Prop 5 constants before `Ω` (`dddf_prop5_XAB_W`, `exists_tail_XAB_unif_W`,
  `expMoment_XAB_shift_W`).
* `RSW/P10.lean`: `p10_core_unif` (Lemma 6 constants before `ξ`), `prop10_unif_all`,
  `prop10_unif` (U3).
* `RSW/Phi.lean`: DDDF Prop 14 / Prop 7 and (3.36)–(3.37) for `φ` (U4).
* `RSW/Psi.lean`: DDDF Cor 8, (3.38)–(3.39) for `ψ` (U4), with `|ξ| ≤ ξs` in the constants.

Every constant exported here satisfies `C ≥ 1` (ledger Finding fd:C1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace GaussianLQG
end GaussianLQG
