/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwInv
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW2ScheduleRun
import InteractingSLE.Spec.Supplement.SB2JLower

/-!
# SB2(2)'s word: the conditional word at every launch of the upper schedule

Packet PROVE-T14-SB2LOW (ruling R99). The staged conditional law (PROVE-STAGEDLAW) is proved one launch at a time;
GW1W's `isStageWitness_succ_expl` exports the word of the witness at a launch `k`: the stop word of the previous piece
(`stopWord κ (β_ℓ, θ_ℓ, record_ℓ)`, recentred). For the upper schedule program `⟨u, true, scheduleProgram 0 l⟩` the
previous launch is `k − 1`, its piece stopped strictly before its lifetime (GW2's run), and the recentring is `0`.
Hence:

* **`exists_witness_upper`**: at every instruction `k` the staged law has a witness whose word satisfies SB2(2)'s
  upper invariant `UInv` at every sample where `k` launches (the mirror of `GW1W.exists_witness_right`; no
  probabilistic stage facts are needed: the pieces stop at interior tips, whose records are good at every sample);
* **`ae_eq_fn_of_witness`**: the data `b'` of every launch witness of the frozen `IsStagedHistory` agree with the word
  of the witness off a finite set (GFF data uniqueness), almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart GW1W

/-- Recentring by `0` changes nothing. -/
theorem shiftW_zero (c : BoundaryWord) : BoundaryWord.shiftW 0 c = c := by
  unfold BoundaryWord.shiftW
  simp only [sub_zero]

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₀ : ℝ} {l : List (ℝ × ℝ≥0)} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Before a later launch of the upper schedule** the previous instruction launched a piece, with a finite own
time strictly before its lifetime (GW2's run: piece `k` launches exactly when every earlier piece succeeded). -/
theorem upper_launch_prev {k : ℕ} (hk : 0 < k)
    (hl : (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (k + 1)).2.2.2.1 k ≠ none) :
    (ExplState.run κ b jumps (Lu.upperSpec x₀ l) D (k - 1 + 1)).2.2.2.1 (k - 1) ≠ none ∧
      instrTime (Lu.upperSpec x₀ l) (k - 1) ≠ ⊤ ∧ instrTime (Lu.upperSpec x₀ l) (k - 1) < (D (k - 1)).2 := by
  have hgw : (Lu.upperSpec x₀ l).2.1 = true := rfl
  have hprog : GW2Schedule.IsFlowProg (Lu.upperSpec x₀ l).2.2 (GW2Schedule.schedAngle l)
      (GW2Schedule.schedDelta 0 l) := GW2Schedule.isFlowProg_scheduleProgram 0 l
  have hΔ := GW2Schedule.schedDelta_ne_top 0 l
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨hspec, -, -⟩ := eq_launch_of_launches _ _ hcθ
  have hklen : k < (Lu.upperSpec x₀ l).2.2.length := by
    by_contra hk'
    push Not at hk'
    rw [List.getElem?_eq_none hk'] at hspec
    exact absurd hspec (by simp)
  have hall : GW2Schedule.AllSucc (GW2Schedule.schedDelta 0 l) D k := by
    by_contra hns
    exact hl ((GW2Schedule.launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ D hklen).2 hns)
  have hk1 : k - 1 < (Lu.upperSpec x₀ l).2.2.length := by omega
  have hall1 := hall.mono (Nat.sub_le k 1)
  have hinstr : instrTime (Lu.upperSpec x₀ l) (k - 1) = GW2Schedule.schedDelta 0 l (k - 1) := by
    unfold instrTime
    rw [hprog (k - 1) hk1]
  refine ⟨?_, by rw [hinstr]; exact hΔ _, by rw [hinstr]; exact hall (k - 1) (by omega)⟩
  rw [(GW2Schedule.launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ D hk1).1 hall1]
  simp

end Run

section Witness

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s upper invariant at every launch of the upper schedule**: for a staged upper history with measurable
drivers regular at every sample, at every instruction `k` the staged conditional law has a witness whose word satisfies
`UInv` at every sample where `k` launches (GW1's ambient bound `b − (π/2)χ < λ` left of `0`). -/
theorem exists_witness_upper (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {x₀ : ℝ} {l : List (ℝ × ℝ≥0)} (hx₀ : x₀ ≤ 0)
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (Lu.upperSpec x₀ l) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ x, x < 0 → x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (Lu.upperSpec x₀ l) E k β Y ∧
      ∀ ω, (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        UInv κ b jumps x₀ l (β ω) (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E j ω) k) := by
  set spec := Lu.upperSpec x₀ l with hspec
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω),
        isStageWitness_zero hh hc₀J hc₀, fun ω _ => ?_⟩
      exact uInv_init hx₀ hamb hc₀J hc₀
    have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧
        ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          UInv κ b jumps x₀ l (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, hW, hI⟩ := ih ℓ hℓ
        exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose β Y hWI using H
    obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
      hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
    refine ⟨βk, Yk, hWk, fun ω hlk => ?_⟩
    obtain ⟨hl, htop, hlt⟩ := upper_launch_prev (D := fun j => E j ω) hk hlk
    have hℓk : k - 1 < k := by omega
    have hk' : k - 1 + 1 = k := by omega
    have hn : ∀ j, k - 1 < j → j < k →
        (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none := by
      intro j h1 h2
      omega
    have hβ := hexpl (k - 1) ω hℓk hlk hl hn
    obtain ⟨⟨c', θ'⟩, hcθ'⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨hsp, hrun, -⟩ := eq_launch_of_launches spec _ hcθ'
    have hθ' : instrAngle spec (k - 1) = θ' := by unfold instrAngle; rw [hsp]
    rw [hθ', pastMap_last_of_launch hl] at hβ
    have ha : ((ExplState.run κ b jumps spec (fun j => E j ω) (k - 1 + 1)).2.2.2.2.1.1 0 -
        (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 0).re = 0 := by
      rw [hk', sub_self, Complex.zero_re]
    rw [ha, shiftW_zero] at hβ
    have hrun' : ExplState.run κ b jumps spec (fun j => E j ω) k =
        ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω) (k - 1)) (k - 1) (E (k - 1) ω) θ'
          (instrTime spec (k - 1)) := by
      rw [← hrun, hk']
    rw [hβ, hrun']
    obtain ⟨p, hp, hpθ⟩ := Lu.exists_mem_of_scheduleProgram_getElem? 0 l (k - 1) hsp
    have hθ : -(Real.pi / 2) < θ' := by rw [hpθ]; exact (hlθ p hp).1
    exact uInv_launch hκ hκ4 hb ((hWI (k - 1) hℓk).2 ω hl) (k - 1) ⟨p, hp, hpθ⟩ hθ (hreg (k - 1) ω) htop hlt

/-- **The launch witness's data are the word of the stage witness** off a finite set, almost surely (the field read in
the launch chart is the witness's field, GFF data uniqueness). -/
theorem ae_eq_fn_of_witness (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData b' jumps' → (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' b' jumps' →
        ∀ y ∉ jumps' ∪ (β ω₀).jumps, b' y = (β ω₀).fn y := by
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hE.2.1 k
  filter_upwards [hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hW.2.2.1,
    ae_ae_run_eq runMeasStatement hb spec (k := k) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)]
    with ω₀ hp₀ hk₀ hpK hrunK
  intro c θ hcθ b' J' h' hb' hT' hG'
  have hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by rw [hcθ]; simp
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hgT : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) :=
    fun ω => Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _
      (h ω)
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) :=
    funext fun ω => (hT' ω).unique hconf (hgT ω)
  have hh'm : Measurable h' := by
    rw [hh'e]
    exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYe : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), Y ω = h' ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact hT.unique hconf (hT' ω)
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn
      (β ω₀).jumps := isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm hYe
  exact Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb' (β ω₀).isPiecewiseConstantBoundaryData hG' hG

end Witness

end InteractingSLE.Theorem14.SB.Lh
