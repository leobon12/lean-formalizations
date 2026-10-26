import SupercriticalConformalCovariance.BiLip.WeylCmp
import SupercriticalConformalCovariance.BiLip.Port.LocalFunctional
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.CostMeas
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal

/-!
# Lemma 2.1, step 4 tools: the annulus functionals are measurable, local and scale-covariant

For whole-plane lower semicontinuous metrics:
* `acr_eq_mul_of_dist_scale`, `around_eq_mul_of_dist_scale`: under `E = c · D` (`c ∈ (0, ∞)`) the
  closed-annulus crossing cost and the path-hit around cost scale by `c` (as SLU's `aroundDist`);
* `acr_eq_of_internal_eq`: the closed-annulus crossing cost is determined by the internal metric on any
  set containing the closed annulus (through SLU's `internal_eq_of_internal_eq`; no barrier is needed);
* `isPathwiseLocal_*`: for a strong LQG metric, `g ↦ aroundDist (D g) A`, `g ↦ acr (D g) w a b` and
  `g ↦ around (D g) w a b` are pathwise local (`IsPathwiseLocal`) on every open set containing the
  respective annulus, and they are Borel.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric aroundDist EuclideanAnnulus IsStrongLQGMetric)
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr around cann ann)
open LQGMetric (DistC restrictTo IsGFFPlusCont)
open SupercriticalConformalCovariance.BiLip.PortTan (IsPathwiseLocal)

/-- `acr (c · D) = c · acr D` -/
theorem acr_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (w : ℂ) (a b : ℝ) :
    acr E w a b = c * acr D w a b := by
  unfold acr
  simp only [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale D E c
      hc0 hcTop hscale,
    SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

/-- `around (c · D) = c · around D` -/
theorem around_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (w : ℂ) (a b : ℝ) :
    around E w a b = c * around D w a b := by
  unfold around
  simp only [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale D E c
      hc0 hcTop hscale,
    SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

/-- The closed-annulus crossing cost through the internal metric of the closed annulus. -/
theorem acr_eq_iInf_internal (D : LSCMetric) (w : ℂ) (a b : ℝ) :
    acr D w a b = ⨅ (x : cann w a b) (y : cann w a b) (_ : (x : ℂ) ∈ sphere w a)
      (_ : (y : ℂ) ∈ sphere w b), D.internal (cann w a b) (x, y) := by
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun y => le_iInf fun hx => le_iInf fun hy => ?_
    unfold LSCMetric.internal acr
    refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPK =>
      le_iInf fun hs => le_iInf fun ht => ?_
    refine iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hP <|
      iInf_le_of_le ?_ <| iInf_le_of_le (hs ▸ hx) <| iInf_le_of_le (ht ▸ hy) le_rfl
    rintro _ ⟨u, hu, rfl⟩
    exact hPK u hu
  · unfold acr
    refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPK =>
      le_iInf fun hs => le_iInf fun ht => ?_
    have hK : ∀ u ∈ Icc s t, P u ∈ cann w a b := fun u hu => hPK ⟨u, hu, rfl⟩
    refine iInf_le_of_le ⟨P s, hK s ⟨le_rfl, hP.1⟩⟩ <| iInf_le_of_le ⟨P t, hK t ⟨hP.1, le_rfl⟩⟩ <|
      iInf_le_of_le hs <| iInf_le_of_le ht ?_
    exact SupercriticalLQGUniqueness.B2.PfeLocal.internal_le_len D _ P s t hP hK

/-- **Locality of `acr`**: equal internal metrics on a set containing the closed annulus give equal
closed-annulus crossing costs. -/
theorem acr_eq_of_internal_eq (D₁ D₂ : LSCMetric) {W : Set ℂ} (hint : D₁.internal W = D₂.internal W)
    (w : ℂ) (a b : ℝ) (hK : cann w a b ⊆ W) : acr D₁ w a b = acr D₂ w a b := by
  have h := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq
    D₁ D₂ hK hint
  rw [acr_eq_iInf_internal, acr_eq_iInf_internal, h]

/-- **Locality of `around`** (open annulus). -/
theorem around_eq_of_internal_eq (D₁ D₂ : LSCMetric) {W : Set ℂ}
    (hint : D₁.internal W = D₂.internal W) (w : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hA : ann w a b ⊆ W) : around D₁ w a b = around D₂ w a b := by
  rw [SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.around_eq_aroundDist D₁ w a b
      ha hab,
    SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.around_eq_aroundDist D₂ w a b
      ha hab]
  refine SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq
    D₁ D₂ W hint _ fun x hx => hA ?_
  rw [annulus_toSet_mem ha hab, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hx
  exact ⟨hx.2, hx.1⟩

section Pathwise

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem isPathwiseLocal_of_internal (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ)
    {L : Type*} (Θ : DistC → L)
    (hΘ : ∀ g₁ g₂ : DistC, (D g₁).internal (W : Set ℂ) = (D g₂).internal (W : Set ℂ) →
      Θ g₁ = Θ g₂) : IsPathwiseLocal W Θ := by
  intro Ω _ P _ g₁ g₂ h₁ h₂ hW
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_internal_eq_of_ae_restrictTo_eq_lsc hD h₁ h₂ W hW] with ω hω
  exact hΘ _ _ hω

theorem isPathwiseLocal_aroundDist (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ)
    (A : EuclideanAnnulus) (hA : A.toSet ⊆ W) :
    IsPathwiseLocal W (fun g => aroundDist (D g) A) :=
  isPathwiseLocal_of_internal hD W _ fun _ _ h =>
    SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq
      _ _ _ h A hA

theorem isPathwiseLocal_acr (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ)
    (w : ℂ) (a b : ℝ) (hK : cann w a b ⊆ W) :
    IsPathwiseLocal W (fun g => acr (D g) w a b) :=
  isPathwiseLocal_of_internal hD W _ fun _ _ h => acr_eq_of_internal_eq _ _ h w a b hK

theorem isPathwiseLocal_around (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ)
    (w : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hA : ann w a b ⊆ W) :
    IsPathwiseLocal W (fun g => around (D g) w a b) :=
  isPathwiseLocal_of_internal hD W _ fun _ _ h => around_eq_of_internal_eq _ _ h w ha hab hA

theorem measurable_aroundDist_comp (hD : IsStrongLQGMetric ξ Q D) (A : EuclideanAnnulus) :
    Measurable (fun g => aroundDist (D g) A) :=
  (SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.aroundBoundedAnnulus_borel A).comp hD.1

theorem measurable_acr_comp (hD : IsStrongLQGMetric ξ Q D) (w : ℂ) (a b : ℝ) :
    Measurable (fun g => acr (D g) w a b) :=
  (SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.measurable_acr w a b).comp hD.1

theorem measurable_around_comp (hD : IsStrongLQGMetric ξ Q D) (w : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) : Measurable (fun g => around (D g) w a b) := by
  have h := measurable_aroundDist_comp hD (⟨(w, a, b), ha, hab⟩ : EuclideanAnnulus)
  have e : (fun g => around (D g) w a b) =
      fun g => aroundDist (D g) (⟨(w, a, b), ha, hab⟩ : EuclideanAnnulus) := by
    funext g
    exact SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.around_eq_aroundDist
      (D g) w a b ha hab
  rw [e]; exact h

end Pathwise

end SupercriticalConformalCovariance.BiLip
