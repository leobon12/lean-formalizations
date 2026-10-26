import SupercriticalConformalCovariance.Small.DyadicSchedule

set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-- A persistent sequence of confined regular failures contradicts deterministic
recovery.  This is the pathwise step after Skorokhod representation. -/
theorem no_persistent_source_failure
    (D E : ℕ → LSCMetric) (d : LSCMetric)
    (hD : Tendsto D atTop (𝓝 d)) (hE : Tendsto E atTop (𝓝 d))
    (c : NNReal) (hc : 0 < c)
    (hDlen : ∀ n, (D n).IsLengthSpace)
    (hElen : ∀ n, (E n).IsLengthSpace)
    (hDreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (D n).IsCurve P a b → (D n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (E n).IsCurve P a b → (E n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      D n (x,y) ≤ (c : ℝ≥0∞) * E n (x,y) ∧
      E n (x,y) ≤ (c : ℝ≥0∞) * D n (x,y))
    (u v : ℕ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hKend : ∀ n, u n ∈ K ∧ v n ∈ K)
    (α θ m : ℝ) (hα : α < 1) (hθ : 0 < θ)
    (M : NNReal) (η : ℝ) (hη : 0 < η)
    (hbad : ∀ n, SupercriticalConformalCovariance.Regular.SourceFailure (D n) (E n)
      0 (u n) (v n) 1 α θ m (M : ℝ) (1 - α) η) : False := by
  obtain ⟨J, hJ⟩ := exists_small_dyadic_offset hα
  let s : ℕ → ℝ := fun j => SupercriticalConformalCovariance.Regular.dyadic (j + J)
  have hs : Tendsto s atTop (𝓝 0) :=
    dyadic_tendsto_zero.comp (tendsto_add_atTop_nat J)
  have hspos : ∀ j, 0 < s j := fun j => (hJ j).1
  have hsone : ∀ j, s j < 1 := fun j => (hJ j).2.2
  have hcost : ∀ j n,
      setDist (D n) {u n} (Metric.sphere (u n) (s j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      setDist (D n) {v n} (Metric.sphere (v n) (s j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      aroundDist (D n)
        (SupercriticalConformalCovariance.Recovery.shortAnnulus (u n) (s j) (hspos j) (hsone j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      aroundDist (D n)
        (SupercriticalConformalCovariance.Recovery.shortAnnulus (v n) (s j) (hspos j) (hsone j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) := by
    intro j n
    exact sourceRegularPair_recovery_costs (D n) (u n) (v n)
      α θ m (M : ℝ) (s j) (hbad n).1 (hbad n).2.1
      ⟨j + J, rfl, (hJ j).1, (hJ j).2.1⟩
      (hspos j) (hsone j) M.coe_nonneg
  have hno := SupercriticalConformalCovariance.Recovery.deterministic_recovery D E d hD hE c hc
    hDlen hElen hDreg hEreg hcomp u v K hK hKend
    (1 - α) (sub_pos.mpr hα)
    (fun n => (hbad n).2.2.1)
    M (fun n => by simpa only [ENNReal.ofReal_coe_nnreal] using (hbad n).2.1)
    θ hθ s hs hspos hsone
    (fun j => Filter.Eventually.of_forall fun n => ⟨(hcost j n).1, (hcost j n).2.1⟩)
    (fun j => Filter.Eventually.of_forall fun n => ⟨(hcost j n).2.2.1, (hcost j n).2.2.2⟩)
    η hη
  apply hno
  refine ⟨id, strictMono_id, ?_⟩
  intro n
  exact (hbad n).2.2.2

end SupercriticalConformalCovariance.Small
