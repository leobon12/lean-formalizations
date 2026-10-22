import HigherDimLQGMetric.DGZ.NondegLocalMeas
import LQGMetric.Papers.DFGPS.L2_17Ind
import HigherDimLFPP.Field.FiniteRange

/-!
# Independence of separated local metrics

The finite range of the band field gives independence of local internal metrics
on well separated domains. The statement includes its exact geometric separation
condition, so it can be applied at each grid scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- A local internal metric is a measurable function of its band field on `U`. -/
theorem nd_measurable_jointLocal_comap {κ : Rd d → ℝ} {ξ Q : ℝ}
    (_h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (q : ℝ≥0∞)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r) (m : ℕ) :
    Measurable[MeasurableSpace.comap
      (fun ω (z : nd_domain r i) => H n z.1 ω - H m z.1 ω) MeasurableSpace.pi]
      (fun ω => (nd_jointSample P H ξ q r n ω).2 (i, m)) := by
  change Measurable[MeasurableSpace.comap
    (fun ω (z : nd_domain r i) => H n z.1 ω - H m z.1 ω) MeasurableSpace.pi]
      (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω)
        (nd_domain r i) (aQ P H ξ n q))
  exact nd_measurable_internalMetricC_comap
    (fun ω => ((hH.band n).continuous ω).sub ((hH.band m).continuous ω))
    (nd_isOpen_domain r i) (nd_isConnected_domain r i).isPreconnected ξ _

/-- Prelimit independence of two local coordinates, for a separation exceeding
the correlation range of the band `H n - H m`. -/
theorem nd_indepFun_jointLocal {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (q : ℝ≥0∞)
    (r : ℝ) (n m : ℕ) (hmn : m ≤ n)
    (i₁ i₂ : nd_DomainIndex d r) (ρ : ℝ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0)
    (hsep : ∀ z ∈ nd_domain r i₁, ∀ w ∈ nd_domain r i₂,
      2 * ρ * ((2 : ℝ)⁻¹ ^ m) < ‖z - w‖) :
    IndepFun
      (fun ω => (nd_jointSample P H ξ q r n ω).2 (i₁, m))
      (fun ω => (nd_jointSample P H ξ q r n ω).2 (i₂, m)) P := by
  let F₁ : Ω → nd_domain r i₁ → ℝ :=
    fun ω z => H n z.1 ω - H m z.1 ω
  let F₂ : Ω → nd_domain r i₂ → ℝ :=
    fun ω z => H n z.1 ω - H m z.1 ω
  have hband := isBandVersion_sub_of_realization h.kernel hH hmn
  have hind : IndepFun F₁ F₂ P :=
    hband.indepFun_restrict_of_two_mul_lt hH.whiteNoise h.kernel hρ hband
      (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
      (by simpa only [max_self] using hsep)
  have hm₁ := nd_measurable_jointLocal_comap h hH q r n i₁ m
  have hm₂ := nd_measurable_jointLocal_comap h hH q r n i₂ m
  apply (IndepFun_iff _ _ _).2
  intro A B hA hB
  apply (IndepFun_iff F₁ F₂ P).1 hind A B
  · exact (MeasurableSpace.le_def.mp (Measurable.comap_le hm₁)) A hA
  · exact (MeasurableSpace.le_def.mp (Measurable.comap_le hm₂)) B hB

/-- Independence of separated local coordinates survives convergence of the joint laws. -/
theorem nd_indepFun_jointLimit {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (q : ℝ≥0∞)
    (r : ℝ) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (m : ℕ) (i₁ i₂ : nd_DomainIndex d r) (ρ : ℝ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0)
    (hsep : ∀ z ∈ nd_domain r i₁, ∀ w ∈ nd_domain r i₂,
      2 * ρ * ((2 : ℝ)⁻¹ ^ m) < ‖z - w‖) :
    IndepFun (fun x : nd_Joint d r => x.2 (i₁, m))
      (fun x : nd_Joint d r => x.2 (i₂, m)) (μ : Measure (nd_Joint d r)) := by
  letI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  obtain ⟨N, hN⟩ := (hns.eventually (eventually_ge_atTop m)).exists_forall_of_atTop
  let f : nd_Joint d r →
      C(nd_domain r i₁ × nd_domain r i₁, ℝ) ×
        C(nd_domain r i₂ × nd_domain r i₂, ℝ) :=
    fun x => (x.2 (i₁, m), x.2 (i₂, m))
  have hf : Continuous f :=
    ((continuous_apply (i₁, m)).comp continuous_snd).prodMk
      ((continuous_apply (i₂, m)).comp continuous_snd)
  let ν : ℕ → ProbabilityMeasure (nd_Joint d r) :=
    fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns (k + N))
  let ρn : ℕ → ProbabilityMeasure
      (C(nd_domain r i₁ × nd_domain r i₁, ℝ) ×
        C(nd_domain r i₂ × nd_domain r i₂, ℝ)) := fun k => (ν k).map f
  let ρ₀ : ProbabilityMeasure
      (C(nd_domain r i₁ × nd_domain r i₁, ℝ) ×
        C(nd_domain r i₂ × nd_domain r i₂, ℝ)) := μ.map f
  have hν : Tendsto ν atTop (𝓝 μ) := hlim.comp (tendsto_add_atTop_nat N)
  have hconv : Tendsto ρn atTop (𝓝 ρ₀) :=
    (ProbabilityMeasure.continuous_map hf).tendsto μ |>.comp hν
  apply LQGMetric.DFGPS.L217.indepFun_of_tendsto_law
    (P := P) (P' := (μ : Measure (nd_Joint d r)))
    (Xn := fun k ω => (nd_jointSample P H ξ q r (ns (k + N)) ω).2 (i₁, m))
    (Yn := fun k ω => (nd_jointSample P H ξ q r (ns (k + N)) ω).2 (i₂, m))
    (ρ := ρn) (ρ₀ := ρ₀)
  · intro k
    exact ((measurable_pi_apply (i₁, m)).comp measurable_snd |>.comp
      (nd_measurable_jointSample hH ξ q r (ns (k + N)))).aemeasurable
  · intro k
    exact ((measurable_pi_apply (i₂, m)).comp measurable_snd |>.comp
      (nd_measurable_jointSample hH ξ q r (ns (k + N)))).aemeasurable
  · exact ((measurable_pi_apply (i₁, m)).comp measurable_snd).aemeasurable
  · exact ((measurable_pi_apply (i₂, m)).comp measurable_snd).aemeasurable
  · intro k
    exact nd_indepFun_jointLocal h hH q r (ns (k + N)) m
      (hN (k + N) (by omega))
      i₁ i₂ ρ hρ hsep
  · intro k
    change ((P.map (nd_jointSample P H ξ q r (ns (k + N)))).map f) = _
    rw [Measure.map_map hf.measurable (nd_measurable_jointSample hH ξ q r (ns (k + N)))]
    rfl
  · rfl
  · exact hconv

end HigherDimLQGMetric.DGZ
