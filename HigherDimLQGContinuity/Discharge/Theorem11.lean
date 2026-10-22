import HigherDimLQGContinuity.Discharge.Estimates
import HigherDimLQGContinuity.Final.Metric
import HigherDimLQGContinuity.Final.Gamma
import HigherDimLQGContinuity.Final.Xi
import HigherDimLQGContinuity.Version.Glue
import HigherDimLQGContinuity.Endpoint.Main
import HigherDimLQGContinuity.MetricVersion.Main
import HigherDimLQGContinuity.Param.Prop18
import HigherDimLQGContinuity.Seed.Prop37
import HigherDimLQGContinuity.Improve.Prop35

/-!
# Theorem 1.1 from `Prop37Shape` (orchestrator assembly, step 4)

The three forms of [C] Theorem 1.1 (`Theorem11XiStmt`, `Theorem11Stmt`, `Theorem11MetricStmt`, the statements of the
frozen anchors `theorem11Xi`, `theorem11`, `theorem11_metric`) follow from the landed packets with one remaining input,
`Prop37Shape d` (Part C `c:lem-p37`; producer P8b from Proposition 3.5 = Q11 and Lemma 2.1). Everything else is
discharged: the parametrization (PAR), the windows (PARX), the positive-parameter version (E1a, E1b), the Euclidean
endpoint (E3) with Lemma 5.1 (`marginalEuclid_holds`), the metric strengthening (E5) with the frame (N3), and the final
composition (E4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- `theorem11_metric`'s statement from `Prop37Shape`. -/
theorem theorem11Metric_of_prop37 (hP37 : ∀ d : ℕ, 3 ≤ d → Prop37Shape d) : Theorem11MetricStmt :=
  theorem11_metric_of_parts (fun d hd => by
    obtain ⟨X, hX⟩ := posVersion_of d hd (hP37 d hd)
    exact ⟨subcritLocal_holds (by omega), X, hX, endpoint_of hd (hP37 d hd) (marginalEuclid_holds hd) hX,
      metricVersion_of hd (Classical.choice (exists_pairingFrame hd)) hX⟩) prop18_holds

/-- `theorem11Xi`'s statement from `Prop37Shape`. -/
theorem theorem11Xi_of_prop37 (hP37 : ∀ d : ℕ, 3 ≤ d → Prop37Shape d) : Theorem11XiStmt :=
  theorem11Xi_of_parts fun d hd => by
    obtain ⟨X, hX⟩ := posVersion_of d hd (hP37 d hd)
    exact ⟨subcritLocal_holds (by omega), X, hX, endpoint_of hd (hP37 d hd) (marginalEuclid_holds hd) hX⟩

/-- `theorem11`'s statement from `Prop37Shape`. -/
theorem theorem11_of_prop37 (hP37 : ∀ d : ℕ, 3 ≤ d → Prop37Shape d) : Theorem11Stmt :=
  theorem11_of (theorem11Xi_of_prop37 hP37) prop18_holds

/-- `Prop37Shape` from Proposition 3.5 (P8b's `prop37Shape_of`, with Lemma 2.1 = `uniformEstimates_holds`). -/
theorem prop37Shape_of_prop35 {d : ℕ} (hd : 3 ≤ d)
    (h35 : ∀ ξbar : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar → Prop35Shape d ξbar) : Prop37Shape d :=
  prop37Shape_of hd h35 fun _ξbar h0 hsub _s hs1 hs10 => uniformEstimates_holds hd ⟨h0, hsub⟩ hs1 hs10

/-- `theorem11_metric`'s statement from Proposition 3.5 (the only remaining input; producer Q11). -/
theorem theorem11Metric_of_prop35
    (h35 : ∀ d : ℕ, 3 ≤ d → ∀ ξbar : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar → Prop35Shape d ξbar) :
    Theorem11MetricStmt :=
  theorem11Metric_of_prop37 fun d hd => prop37Shape_of_prop35 hd (h35 d hd)

/-- `theorem11_metric`'s statement from the site certificate alone (Prop 3.5 = Q11's `prop35_of`). -/
theorem theorem11Metric_of_siteCert (hcert : ∀ d : ℕ, 3 ≤ d → SiteCertOfLabel d) : Theorem11MetricStmt :=
  theorem11Metric_of_prop35 fun d hd _ξbar h0 hsub => prop35_of hd ⟨h0, hsub⟩ (hcert d hd)

/-- `theorem11Xi`'s statement from the site certificate alone. -/
theorem theorem11Xi_of_siteCert (hcert : ∀ d : ℕ, 3 ≤ d → SiteCertOfLabel d) : Theorem11XiStmt :=
  theorem11Xi_of_prop37 fun d hd => prop37Shape_of_prop35 hd fun _ξbar h0 hsub => prop35_of hd ⟨h0, hsub⟩ (hcert d hd)

/-- `theorem11`'s statement from the site certificate alone. -/
theorem theorem11_of_siteCert (hcert : ∀ d : ℕ, 3 ≤ d → SiteCertOfLabel d) : Theorem11Stmt :=
  theorem11_of (theorem11Xi_of_siteCert hcert) prop18_holds

end HigherDimLQGContinuity
