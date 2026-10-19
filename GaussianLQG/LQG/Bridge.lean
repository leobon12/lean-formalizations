import GaussianLQG.LQG.Bridge.Defs
import GaussianLQG.LQG.Bridge.Basic
import GaussianLQG.LQG.Bridge.RotNormalized
import GaussianLQG.LQG.Bridge.LFPPRotBdd
import GaussianLQG.LQG.Bridge.RotMetric
import GaussianLQG.LQG.Bridge.Affine
import GaussianLQG.LQG.Bridge.Median
import GaussianLQG.LQG.Bridge.Exists

/-!
# The LQG-metric bridge

Facts about the canonical γ-LQG metric of Gwynne–Miller (arXiv:1905.00383v3), Theorems 1.1–1.2,
as formalized in `LQGMetric`, used by blueprint Definition `def:metric`, Proposition
`prop:metric-facts` and Proposition `prop:S2-S5`. Throughout, `D` is a canonical γ-LQG metric
(`GaussianLQG.IsCanonicalLQGMetric γ D`, `Bridge/Defs.lean`), which exists for `γ ∈ (0,2)`
(`GaussianLQG.exists_isCanonicalLQGMetric`, `Bridge/Exists.lean`) and is almost surely unique
(`GaussianLQG.IsCanonicalLQGMetric.ae_eq`).

* Measurability, (F1) and (S2) (first clause), `Bridge/Basic.lean`:
  `IsCanonicalLQGMetric.measurable_dist` (`ω ↦ D_{h(ω)}(u, v)`) and
  `IsCanonicalLQGMetric.measurable_coe` (`ω ↦ D_{h(ω)} ∈ C(ℂ × ℂ, ℝ)`).
* Rotation invariance of the normalized whole-plane GFF, `Bridge/RotNormalized.lean`:
  `GaussianLQG.isNormalizedWPGFF_rotDist` and `GaussianLQG.map_rotDist_eq` (`h(a·) =ᵈ h` for
  `|a| = 1`).
* (F3), rotation case, `Bridge/RotMetric.lean`: `IsCanonicalLQGMetric.ae_rotDist`
  (`D_{h(a·)}(u, v) = D_h(a u, a v)` a.s. for `|a| = 1` and a whole-plane GFF `h`) and
  `IsCanonicalLQGMetric.ae_rotDist_of_isGFFPlusBddCont` (for a whole-plane GFF plus a bounded
  continuous function), from the exact rotation covariance of LFPP
  (`GaussianLQG.ae_lfppDistE_rotDist`, extended in `Bridge/LFPPRotBdd.lean`) and the a.s.
  uniqueness of limits in probability (`GaussianLQG.ae_eq_comp_of_tendstoInProbLU`).
* (F3) for complex `a` and (S4), `Bridge/Affine.lean`: `IsCanonicalLQGMetric.ae_coord`,
  `IsCanonicalLQGMetric.ae_affine_eq`, and the affine covariance in law
  `IsCanonicalLQGMetric.map_affine_eq` (equality of laws on `C(ℂ × ℂ, ℝ)`) with its
  finite-dimensional form `IsCanonicalLQGMetric.map_affine_eval_eq`.
* (F4) = (S5), `Bridge/Median.lean`: `IsCanonicalLQGMetric.isMedian_crossFn`,
  `IsCanonicalLQGMetric.isMedian_iInf`, `IsCanonicalLQGMetric.half_le_prob_crossFn`, with
  `GaussianLQG.crossFn_eq_iInf` (`crossFn d = inf_{s,t ∈ [0,1]} d(is, 1 + it)`) and
  `IsCanonicalLQGMetric.measurable_crossFn`.
-/
