import HigherDimLQGMetric.Markov.Version

/-! Bochner integration of the exterior point Riesz vectors against compact test functions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped Topology RealInnerProductSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- Zero extension of the exterior point vector, used only under test functions supported in
the exterior open set. -/
def markovExteriorVec (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V) (x : Rd d) : Lp ℝ 2 P :=
  by
    classical
    exact if hx : x ∈ extOpen V then markovPointVec hd hh V hVb hρ hρV x hx else 0

theorem markovExteriorVec_eq (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    {x : Rd d} (hx : x ∈ extOpen V) :
    markovExteriorVec hd hh V hVb hρ hρV x =
      markovPointVec hd hh V hVb hρ hρV x hx := by
  simp only [markovExteriorVec, dite_eq_left hx]

theorem markovExteriorVec_continuousOn (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V) :
    ContinuousOn (markovExteriorVec hd hh V hVb hρ hρV) (extOpen V) := by
  let E := markovExteriorVec hd hh V hVb hρ hρV
  apply continuousOn_of_locally_continuousOn
  intro x hx
  obtain ⟨r, C, hr, hC, hball, hLip⟩ :=
    markovPointVec_local_lipschitz hd hh V hVb hρ hρV x hx
  let U : Set (Rd d) := ball x r
  have hEL : LipschitzOnWith (Real.toNNReal C) E U :=
    LipschitzOnWith.of_dist_le' (K := C) (fun y hy z hz => by
      have hyo : y ∈ extOpen V := hball hy
      have hzo : z ∈ extOpen V := hball hz
      have hbound := hLip z hzo y hyo
        (ball_subset_closedBall hz) (ball_subset_closedBall hy)
      simpa only [dist_eq_norm, E, markovExteriorVec_eq hd hh V hVb hρ hρV hyo,
        markovExteriorVec_eq hd hh V hVb hρ hρV hzo] using hbound)
  refine ⟨U, isOpen_ball, mem_ball_self hr, ?_⟩
  exact hEL.continuousOn.mono inter_subset_right

theorem markov_integrable_weightedExteriorVec (hd : 1 ≤ d)
    (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (ψ : TestOn (extOpen V)) :
    Integrable (fun x : Rd d => (testIncl (extOpen V) ψ) x •
      markovExteriorVec hd hh V hVb hρ hρV x) := by
  let w : Rd d → ℝ := testIncl (extOpen V) ψ
  let E := markovExteriorVec hd hh V hVb hρ hρV
  have hwc : Continuous w := (testIncl (extOpen V) ψ).continuous
  have hws : HasCompactSupport w := (testIncl (extOpen V) ψ).hasCompactSupport
  have hwo : tsupport w ⊆ extOpen V := by
    change tsupport ((testIncl (extOpen V) ψ : TestRd d) : Rd d → ℝ) ⊆ extOpen V
    rw [coe_testIncl]
    exact ψ.tsupport_subset
  have hEc : ContinuousOn E (extOpen V) :=
    markovExteriorVec_continuousOn hd hh V hVb hρ hρV
  have hcont : Continuous fun x : Rd d => w x • E x := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ extOpen V
    · have hEca : ContinuousAt E x :=
        hEc.continuousAt ((extOpen V).isOpen.mem_nhds hx)
      exact hwc.continuousAt.smul hEca
    · have hnot : x ∉ tsupport w := fun ht => hx (hwo ht)
      have heq : (fun y : Rd d => w y • E y) =ᶠ[𝓝 x]
          (fun _ => (0 : Lp ℝ 2 P)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [hy]
      exact continuousAt_const.congr_of_eventuallyEq heq
  exact hcont.integrable_of_hasCompactSupport hws.smul_right

end HigherDimLQGMetric
