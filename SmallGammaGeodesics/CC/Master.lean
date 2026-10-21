import SmallGammaGeodesics.CC.Reversal
import SmallGammaGeodesics.Core.Setup
import LQGMetric.Papers.GM.S1.StrongWeak

/-!
# The master keystones of track CC: two-sided and strong forms (packet CC11, T2 and T3)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D16** ("Strong
metrics"), rulings G17 and G19.

* **T2** `masterCC_of_masterCCLE : MasterCCLE → MasterCC`: a canonical γ-LQG metric is strong
  (`IsCanonicalLQGMetric γ D` is `IsStrongLQGMetric γ D ∧ …`), so T1 (`reversal_holds`) turns the
  one-sided form into the two-sided one.
* **T3** `masterCCStrong_of_masterCC : MasterCC → MasterCCStrong`: by GM Theorem 1.2
  (`theorem12_proved`, packaged as `exists_canonical_smul` in `Core/Setup.lean`) every strong
  γ-LQG metric `D` is a.s. a deterministic multiple `C · D'` of a canonical one, for every
  whole-plane GFF plus a continuous function. Apply this to `h` and to `h̄ + f`; internal metrics scale by `C`
  (`ContMetric.internal_smulPos`), so `ConfCov γ D'` gives `ConfCov γ D`
  (`confCov_of_eq_smul`).
* Corollaries: `masterCCStrong_of_masterCCLE` and the one-sided strong form
  `confCovLE_of_masterCCLE`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## Internal metrics of a constant multiple -/

/-- If `D₁ = C · D₂` pointwise with `C > 0`, then `D₁(·,·;U) = C · D₂(·,·;U)` for every `U`. -/
theorem internal_eq_of_dist_eq_mul {D₁ D₂ : ContMetric} {C : ℝ} (hC : 0 < C)
    (h : ∀ u v : ℂ, D₁.1 (u, v) = C * D₂.1 (u, v)) (U : Set ℂ) (z w : ℂ) :
    D₁.internal U z w = ENNReal.ofReal C * D₂.internal U z w := by
  have hD : D₁ = D₂.smulPos C hC := by
    refine Subtype.ext (ContinuousMap.ext fun p => ?_)
    rw [show (D₂.smulPos C hC).1 p = C * D₂.1 p from ContMetric.smulPos_apply C hC D₂ p]
    exact h p.1 p.2
  rw [hD, ContMetric.internal_smulPos]

/-- **`ConfCov` is invariant under constant multiples**: if a.s. `D_g = C · D'_g` for every
whole-plane GFF plus a continuous function `g` (with one deterministic `C > 0`), then
`ConfCov γ D'` implies `ConfCov γ D`. -/
theorem confCov_of_eq_smul {γ : ℝ} {D D' : DistC → ContMetric} {C : ℝ} (hC : 0 < C)
    (hDD : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = C * (D' (h ω)).1 (u, v))
    (hCC : ConfCov γ D') : ConfCov γ D := by
  intro ϕ W V hϕ Ω _ P _ h hbar f hh hhb hf hc
  filter_upwards [hCC ϕ W V hϕ P h hbar f hh hhb hf hc, hDD P h (isGFFPlusCont_of_wp hh),
    hDD P (fun ω => addFun (hbar ω) (f ω)) (isGFFPlusCont_addFun_of_wp hhb hf)]
    with ω hω h1 h2 z hz w hw
  rw [confMetric_def, internal_eq_of_dist_eq_mul hC h1, internal_eq_of_dist_eq_mul hC h2,
    hω z hz w hw, confMetric_def]

/-! ## The master keystones -/

/-- **T2**: the one-sided master keystone gives the two-sided one (T1 for canonical metrics). -/
theorem masterCC_of_masterCCLE (hM : MasterCCLE) : MasterCC := fun γ hγ hγ2 D hD =>
  reversal_holds hD.1 (hM γ hγ hγ2 D hD)

/-- **T3**: the two-sided master keystone for canonical metrics gives it for every strong γ-LQG
metric (GM Theorem 1.2 uniqueness; internal metrics scale by the constant). -/
theorem masterCCStrong_of_masterCC (hM : MasterCC) : MasterCCStrong := by
  intro γ hγ hγ2 D hD
  obtain ⟨D', hD', C, hC, hDC⟩ := exists_canonical_smul hγ hγ2 hD
  exact confCov_of_eq_smul hC hDC (hM γ hγ hγ2 D' hD')

/-- `MasterCCLE` gives the two-sided conformal covariance of every strong γ-LQG metric. -/
theorem masterCCStrong_of_masterCCLE (hM : MasterCCLE) : MasterCCStrong :=
  masterCCStrong_of_masterCC (masterCC_of_masterCCLE hM)

/-- `MasterCCLE` gives the one-sided conformal covariance of every strong γ-LQG metric (the
form consumed by §5, GA2's `[CC≥]`). -/
theorem confCovLE_of_masterCCLE (hM : MasterCCLE) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) : ConfCovLE γ D :=
  confCovLE_of_confCov (masterCCStrong_of_masterCCLE hM γ hγ hγ2 D hD)

end SmallGammaGeodesics.CC
