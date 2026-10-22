import HigherDimLQGMetric.Markov.SFub

/-! Stochastic integration of the continuous exterior projection process. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- A compactly supported weight inside an open set has a compactly supported continuous
cutoff equal to one on its support. -/
theorem markov_exists_weightCutoff (O : Opens (Rd d)) {w : Rd d → ℝ}
    (hws : HasCompactSupport w) (hwo : tsupport w ⊆ O) :
    ∃ η : Rd d → ℝ, Continuous η ∧ HasCompactSupport η ∧
      tsupport η ⊆ O ∧ (∀ x ∈ tsupport w, η x = 1) := by
  let K : Set (Rd d) := tsupport w
  have hKc : IsCompact K := hws
  obtain ⟨R, hR, hKR⟩ := hKc.isBounded.exists_pos_norm_lt
  let U : Set (Rd d) := ball 0 R ∩ O
  have hUo : IsOpen U := isOpen_ball.inter O.isOpen
  have hKU : K ⊆ U := by
    intro x hx
    exact ⟨by simpa only [mem_ball, dist_zero_right] using hKR x hx, hwo hx⟩
  have hUc : IsCompact (closure U) :=
    (isCompact_closedBall (0 : Rd d) R).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ball_subset_closedBall hx.1) isClosed_closedBall)
  obtain ⟨η, hηs, hη1, _⟩ := exists_tsupport_one_of_isOpen_isClosed
    hUo hUc (isClosed_tsupport w) hKU
  refine ⟨η, η.continuous, ?_, hηs.trans inter_subset_right, fun x hx => hη1 hx⟩
  exact hUc.of_isClosed_subset (isClosed_tsupport η)
    (hηs.trans subset_closure)

/-- Multiplying a locally continuous exterior version by a test supported in the exterior
produces a global continuous `L²` process with uniformly bounded second moments. -/
theorem markov_weighted_version (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (Y : Ω → Rd d → ℝ) (hYc : ∀ ω, ContinuousOn (Y ω) (extOpen V))
    (hYm : Measurable Y)
    (hYae : ∀ x (hx : x ∈ extOpen V),
      (fun ω => Y ω x) =ᵐ[P]
        (markovPointVec hd hh V hVb hρ hρV x hx : Ω → ℝ))
    (ψ : TestOn (extOpen V)) :
    let w : Rd d → ℝ := testIncl (extOpen V) ψ
    let E : Rd d → Lp ℝ 2 P := markovExteriorVec hd hh V hVb hρ hρV
    (∀ ω, Continuous fun x => w x * Y ω x) ∧
    (∀ x, Measurable fun ω => w x * Y ω x) ∧
    (∀ x, (fun ω => w x * Y ω x) =ᵐ[P]
      (fun ω => w x * (E x : Ω → ℝ) ω)) ∧
    (∀ x, MemLp (fun ω => w x * Y ω x) 2 P) ∧
    (∃ C : ℝ, ∀ x, ∫ ω, (w x * Y ω x) ^ 2 ∂P ≤ C) := by
  classical
  dsimp
  let w : Rd d → ℝ := testIncl (extOpen V) ψ
  let E : Rd d → Lp ℝ 2 P := markovExteriorVec hd hh V hVb hρ hρV
  let F : Rd d → Lp ℝ 2 P := fun x => w x • E x
  have hwc : Continuous w := (testIncl (extOpen V) ψ).continuous
  have hws : HasCompactSupport w := (testIncl (extOpen V) ψ).hasCompactSupport
  have hwo : tsupport w ⊆ extOpen V := by
    change tsupport ((testIncl (extOpen V) ψ : TestRd d) : Rd d → ℝ) ⊆ extOpen V
    rw [coe_testIncl]
    exact ψ.tsupport_subset
  have hEc : ContinuousOn E (extOpen V) :=
    markovExteriorVec_continuousOn hd hh V hVb hρ hρV
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ extOpen V
    · exact hwc.continuousAt.smul
        (hEc.continuousAt ((extOpen V).isOpen.mem_nhds hx))
    · have hnot : x ∉ tsupport w := fun ht => hx (hwo ht)
      have heq : F =ᶠ[𝓝 x] (fun _ => (0 : Lp ℝ 2 P)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [F, hy]
      exact continuousAt_const.congr_of_eventuallyEq heq
  have hFs : HasCompactSupport F := hws.smul_right
  have hYwc (ω : Ω) : Continuous fun x => w x * Y ω x := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ extOpen V
    · exact hwc.continuousAt.mul
        ((hYc ω).continuousAt ((extOpen V).isOpen.mem_nhds hx))
    · have hnot : x ∉ tsupport w := fun ht => hx (hwo ht)
      have heq : (fun y => w y * Y ω y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
        simp [hy]
      exact continuousAt_const.congr_of_eventuallyEq heq
  have hYwm (x : Rd d) : Measurable fun ω => w x * Y ω x :=
    measurable_const.mul ((measurable_pi_iff.mp hYm) x)
  have hYwF (x : Rd d) : (fun ω => w x * Y ω x) =ᵐ[P] (F x : Ω → ℝ) := by
    by_cases hx : x ∈ extOpen V
    · filter_upwards [hYae x hx, Lp.coeFn_smul (w x) (E x)] with ω hy hsm
      rw [hy]
      simpa only [F, E, markovExteriorVec_eq hd hh V hVb hρ hρV hx,
        Pi.smul_apply, smul_eq_mul] using hsm.symm
    · have hw0 : w x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hx (hwo ht))
      filter_upwards [] with ω
      simp [F, hw0]
  have hYwL2 (x : Rd d) : MemLp (fun ω => w x * Y ω x) 2 P :=
    (Lp.memLp (F x)).ae_eq (hYwF x).symm
  obtain ⟨M, hM⟩ := hFs.exists_bound_of_continuous hFc
  have hYwsq (x : Rd d) : ∫ ω, (w x * Y ω x) ^ 2 ∂P = ‖F x‖ ^ 2 := by
    calc
      _ = ∫ ω, ((F x : Ω → ℝ) ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hYwF x] with ω hω
        rw [hω]
      _ = ‖F x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq (F x), L2.inner_def]
        congr 1
        funext ω
        simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  refine ⟨hYwc, hYwm, ?_, hYwL2, ?_⟩
  · intro x
    filter_upwards [hYwF x, Lp.coeFn_smul (w x) (E x)] with ω hω hsm
    rw [hω, hsm]
    rfl
  · refine ⟨M ^ 2, fun x => ?_⟩
    rw [hYwsq]
    nlinarith [hM x, norm_nonneg (F x)]

end HigherDimLQGMetric
