import HigherDimLQGMetric.Markov.StochEq

/-! Measurability and pairings of a locally continuous function viewed as a distribution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- Integrating an open-set continuous random function against a supported test is measurable. -/
theorem markov_measurable_integral_localVersion (O : Opens (Rd d))
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) O)
    (hYm : Measurable Y) (ψ : TestOn O) :
    Measurable fun ω => ∫ x, (testIncl O ψ) x * Y ω x := by
  classical
  let w : Rd d → ℝ := testIncl O ψ
  have hwc : Continuous w := (testIncl O ψ).continuous
  have hws : HasCompactSupport w := (testIncl O ψ).hasCompactSupport
  have hwo : tsupport w ⊆ O := by
    change tsupport ((testIncl O ψ : TestRd d) : Rd d → ℝ) ⊆ O
    rw [coe_testIncl]
    exact ψ.tsupport_subset
  obtain ⟨η, hηc, hηs, _, hη1⟩ := markov_exists_weightCutoff O hws hwo
  have hηw (x : Rd d) : η x * w x = w x := by
    by_cases hx : x ∈ tsupport w
    · rw [hη1 x hx, one_mul]
    · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hw0]
  let Yw : Rd d → Ω → ℝ := fun x ω => w x * Y ω x
  have hYwc (ω : Ω) : Continuous fun x => Yw x ω := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ O
    · exact hwc.continuousAt.mul ((hYc ω).continuousAt (O.isOpen.mem_nhds hx))
    · have hnot : x ∉ tsupport w := fun ht => hx (hwo ht)
      have heq : (fun y => Yw y ω) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [Yw, hy]
      exact continuousAt_const.congr_of_eventuallyEq heq
  have hYwm (x : Rd d) : Measurable (Yw x) :=
    measurable_const.mul ((measurable_pi_iff.mp hYm) x)
  have hJoint : Measurable fun p : Ω × Rd d => Yw p.2 p.1 :=
    markov_measurable_Y₂ hYwc hYwm
  have hIntegral : Measurable fun ω => ∫ x, η x * Yw x ω :=
    (((hηc.measurable.comp measurable_snd).mul hJoint).stronglyMeasurable.integral_prod_right'
      (ν := volume)).measurable
  have heq : (fun ω => ∫ x, w x * Y ω x) =
      (fun ω => ∫ x, η x * Yw x ω) := by
    funext ω
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    dsimp [Yw]
    rw [← mul_assoc, hηw]
  rw [heq]
  exact hIntegral

/-- A continuous exterior version defines a measurable random distribution. -/
theorem markov_measurable_ofFunOn (O : Opens (Rd d))
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) O)
    (hYm : Measurable Y) :
    Measurable fun ω => ofFunOn O (Y ω) := by
  refine measurable_distOn_iff.mpr fun ψ => ?_
  have hm := markov_measurable_integral_localVersion O Y hYc hYm ψ
  have heq (ω : Ω) : ofFunOn O (Y ω) ψ =
      ∫ x, (testIncl O ψ) x * Y ω x := by
    rw [ofFunOn, Distribution.ofFun_apply ((hYc ω).locallyIntegrableOn O.isOpen.measurableSet)]
    simp only [coe_testIncl, smul_eq_mul]
  convert hm using 1
  funext ω
  exact heq ω

end HigherDimLQGMetric
