/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk4

/-!
# The restarted walk: retained data and launch records

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). Under the hypotheses of `statePhys_restart`, the
restarted run has the retained data of the first run at every instruction, and each of its later launches is a launch
of the first run in a chart equal on `ℍ` (**`restart_retained_launches`**). A chart transport only sees the chart on
`ℍ` (**`isChartTransport_of_chartEqH`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **A chart transport only sees the chart on `ℍ`.** -/
theorem isChartTransport_of_chartEqH {c c' : Chart} (hc : ChartEqH c c') {σ a k : ℝ}
    {f g : DistOn upperHalfPlaneOpens} (hT : IsChartTransport c σ a k f g) : IsChartTransport c' σ a k f g := by
  have himg : c.2.1 '' H = c'.2.1 '' H := Set.image_congr hc.2.2
  intro φ φ' hsupp hφ
  rw [← himg] at hsupp
  have h1 := hT φ φ' hsupp (by
    intro z hz
    rw [hc.1]
    exact hφ z (himg ▸ hz))
  rw [h1]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ H
  · show c.2.2 (c.2.1 w) * φ' w = c'.2.2 (c'.2.1 w) * φ' w
    rw [hc.2.2 hw, hc.2.1]
  · have : φ' w = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (φ'.tsupport_subset h)
    simp [this]

section Restart

variable {κ : ℝ} {B : ℝ → ℝ} {JB : Finset ℝ} (prog : List Instr) (h0 : prog[0]? = some (.inl (-(Real.pi / 2), ⊤)))
  (h1 : prog[1]? = some (.inr (.inl true))) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h0 in
theorem retained_run_one (x₀ : ℝ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d) (hreg : IsRegularDriver d) (hz : d.2 = 0) :
    (ExplState.run κ B JB (x₀, false, prog) D 1).2.2.1 =
      Function.update (fun _ : ℕ => ((fun _ : ℝ≥0 => (0 : ℝ)), (0 : ℝ≥0∞), false)) 0
        ((fun _ : ℝ≥0 => (0 : ℝ)), (0 : ℝ≥0∞), true) := by
  rw [run_succ, show (x₀, false, prog).2.2[0]? = some (.inl (-(Real.pi / 2), ⊤)) from h0]
  show (ExplState.flowStep κ B false (ExplState.init x₀) 0 (D 0) (-(Real.pi / 2)) ⊤).2.2.1 = _
  rw [hD]
  exact (launch_init_zero_components x₀ hreg hz).2.2.1

include h0 h1 in
/-- **The restarted run has the retained data of the first run, and its later launches are launches of the first run
in charts equal on `ℍ`.** -/
theorem restart_retained_launches {x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂) {d d' : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d)
    (hD' : D' 0 = d') (hreg : IsRegularDriver d) (hreg' : IsRegularDriver d') (hz : d.2 = 0) (hz' : d'.2 = 0)
    (hlow₁ : rightLim B x₁ - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow₂ : rightLim B x₂ - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hmid : ∀ y ∈ jumpSet B JB, x₁ < y → y ≤ x₂ → ¬ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ)
    (hregD : ∀ j, IsRegularDriver (D j)) (hDD : ∀ j, 2 ≤ j → D' j = D j)
    (hstep : ∀ j, 2 ≤ j → ∀ θ t, (x₁, false, prog).2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ B false (ExplState.run κ B JB (x₁, false, prog) D j) j (D j) θ t =
        ExplState.launch (ExplState.run κ B JB (x₁, false, prog) D j) j (D j) θ t →
      (min t (D j).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j)))) ∧
        RightExit (ExplState.run κ B JB (x₁, false, prog) D j) t (D j)) :
    (∀ k, (ExplState.run κ B JB (x₂, false, prog) D' k).2.2.1 = (ExplState.run κ B JB (x₁, false, prog) D k).2.2.1) ∧
      ∀ k, 1 ≤ k → ∀ (c₂ : Chart) (θ : ℝ),
        (ExplState.run κ B JB (x₂, false, prog) D' (k + 1)).2.2.2.1 k = some (c₂, θ) →
        ∃ c₁ : Chart, (ExplState.run κ B JB (x₁, false, prog) D (k + 1)).2.2.2.1 k = some (c₁, θ) ∧
          ChartEqH c₁ c₂ := by
  obtain ⟨-, -, r1, l1⟩ := launch_init_zero_components x₁ hreg hz
  obtain ⟨-, -, r2, l2⟩ := launch_init_zero_components x₂ hreg' hz'
  have hret01 : ∀ k, k ≤ 1 → (ExplState.run κ B JB (x₂, false, prog) D' k).2.2.1 =
      (ExplState.run κ B JB (x₁, false, prog) D k).2.2.1 := by
    intro k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · rfl
    · rw [retained_run_one prog h0 x₂ hD' hreg' hz', retained_run_one prog h0 x₁ hD hreg hz]
  by_cases hC : (walkFilter κ B JB x₂).Nonempty
  · have hrel := restartRel_run (spec₁ := (x₁, false, prog)) (spec₂ := (x₂, false, prog)) rfl rfl hregD
      (n := 2) hDD (restartRel_two prog h0 h1 h12 hD hD' hreg hreg' hz hz' hlow₁ hlow₂ hmid hC) hstep
    refine ⟨fun k => ?_, fun k hk c₂ θ hl => ?_⟩
    · rcases le_or_gt k 1 with hk | hk
      · exact hret01 k hk
      · exact (hrel k hk).2.2.1.symm
    · have hL := (hrel (k + 1) (by omega)).2.2.2.1 k (by omega)
      rw [hl] at hL
      rcases h : (ExplState.run κ B JB (x₁, false, prog) D (k + 1)).2.2.2.1 k with _ | ⟨c₁, θ₁⟩
      · rw [h] at hL; exact hL.elim
      · rw [h] at hL
        obtain ⟨hc, hθ⟩ := hL
        exact ⟨c₁, by rw [show θ₁ = θ from hθ], hc⟩
  · have hF := walkFilter_eq (κ := κ) (B := B) (JB := JB) h12 hmid
    have hC₁ : ¬ (walkFilter κ B JB x₁).Nonempty := hF ▸ hC
    have e2A := run_two_done prog h0 h1 x₁ hD hreg hz hlow₁ hC₁
    have e2B := run_two_done prog h0 h1 x₂ hD' hreg' hz' hlow₂ hC
    have hdA : stStatus (ExplState.run κ B JB (x₁, false, prog) D 2) = stDone := by
      rw [e2A]; obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := ExplState.launch (ExplState.init x₁) 0 d (-(Real.pi / 2)) ⊤
      rfl
    have hdB : stStatus (ExplState.run κ B JB (x₂, false, prog) D' 2) = stDone := by
      rw [e2B]; obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := ExplState.launch (ExplState.init x₂) 0 d' (-(Real.pi / 2)) ⊤
      rfl
    have hmE : ∀ s : ExplState, (ExplState.moveToEnd s true).2.2.1 = s.2.2.1 ∧
        (ExplState.moveToEnd s true).2.2.2.1 = s.2.2.2.1 := fun s => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; exact ⟨rfl, rfl⟩
    refine ⟨fun k => ?_, fun k hk c₂ θ hl => ?_⟩
    · rcases le_or_gt k 1 with hk | hk
      · exact hret01 k hk
      · rw [run_eq_of_done _ _ hdA k (by omega), run_eq_of_done _ _ hdB k (by omega), e2A, e2B, (hmE _).1,
          (hmE _).1, r1, r2]
    · rw [run_eq_of_done _ _ hdB (k + 1) (by omega), e2B, (hmE _).2, l2,
        Function.update_of_ne (show k ≠ 0 by omega)] at hl
      exact ((Option.some_ne_none _).symm hl).elim

end Restart

end InteractingSLE.Theorem14.SB.Lf
