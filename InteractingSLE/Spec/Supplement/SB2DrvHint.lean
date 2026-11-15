/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEntrance
import InteractingSLE.Spec.Supplement.SB2LwStop
import InteractingSLE.Spec.Supplement.BW1LifeWord
import InteractingSLE.Spec.Supplement.BW1InIntGauss
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# The launch words have uniformly bounded heights; K2's integrability for SB2(1)

Packet PROVE-T14-SB2DRV (round 2), clause (E4) of `SB2EntranceK2Statement`. The conditional word at a launch of a
finite staged history is, almost surely, an explicit iterated stop word (`GW1W.isStageWitness_succ_expl`); every value
of a stop word is a value of the word it was launched with or one of the two new side heights `∓λ − θχ`
(`Lh.stopWord_fn_neg_mem`, `stopWord_fn_pos_mem`). So one constant bounds the heights of the conditional words at a
given stage for almost every sample (`exists_stageWitness_bounded`), and by the maximum principle for piecewise-constant
data and the Gaussian law of the centred pairing (`BW1In.lintegral_enorm_apply_le_of_isGFF`) the chart pairings of the
field are integrable on the launch event (`integrableOn_chartPairing`, disintegration over the retained past as in
`BW1In.integrableOn_bwRelField`).

* `stopWord_fn_pos_mem`: right of the tip every value of a stop word is `λ − θχ` or a value of the launch word at a
  positive non-jump point (mirror of `Lh.stopWord_fn_neg_mem`);
* `abs_stopWord_fn_le`, `abs_shiftW_fn_le`;
* **`exists_stageWitness_bounded`**;
* **`integrableOn_chartPairing`**: for every SB2(1) problem and chart record, every pairing of the flow-rule field read
  in the recentred version chart is integrable on the launch event;
* `SB2EntranceK2NStatement`, `SB2LaunchK2NStatement` (the two named inputs without their integrability clause) and
  `sb2DriverLinkAmbStatement_of_entranceK2N`, `sb2DriverLinkAmbStatement_of_launchK2N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal

/-! ### Values of stop words -/

section StopWord

variable {κ : ℝ}

/-- **Right of the tip**, every value of the stop word is the new right-side height `λ − θχ` or a value of the
launch word at a positive point off its jumps (the right partial sums of the flow-line word are the original right
heights). -/
theorem stopWord_fn_pos_mem (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy : 0 < y) :
    (stopWord κ (c, θ, r)).fn y = sleLambda κ - θ * chiC κ ∨
      ∃ x > 0, x ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn y = c.fn x := by
  obtain ⟨m, hm, he⟩ := exists_fn_forceWord_of_pos (κ := κ) (nL := flowLineNL c.fn c.jumps 0)
    (nR := flowLineNR c.fn c.jumps 0)
    (pL := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (pR := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
    (ρL := (padFL κ θ c.fn c.jumps).2.1) (ρR := (padFL κ θ c.fn c.jumps).2.2) (s := θ * chiC κ)
    (isMarkOrder_stopWord c r).2.1 hy
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hW : stopWord κ (c, θ, r) = forceWord κ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)
      (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
      (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) := rfl
  rw [hW, he]
  change (sleLambda κ * (1 + ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.2 i) - θ * chiC κ =
      sleLambda κ - θ * chiC κ) ∨ ∃ x > 0, x ∉ c.jumps ∧
      sleLambda κ * (1 + ∑ i ∈ Finset.range m, (padFL κ θ c.fn c.jumps).2.2 i) - θ * chiC κ = c.fn x
  rcases m with _ | j
  · left
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
  · right
    have hj : j < flowLineNR c.fn c.jumps 0 := by omega
    rw [sum_range_padFL_right κ θ c hj]
    have hsum : ∑ l ∈ Finset.univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNR c.fn c.jumps 0))),
          flowLineRhoR κ c.fn c.jumps 0 θ l =
        ∑ l ∈ Finset.univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNR c.fn c.jumps 0))),
          flowLineRhoR κ c.fn c.jumps 0 0 l + θ * chiC κ / sleLambda κ := by
      rw [Finset.sum_congr rfl (fun l _ => flowLineRhoR_theta κ c.fn c.jumps θ l), Finset.sum_add_distrib,
        sum_filter_le_ite_val_eq_zero _ ⟨j, hj⟩ ⟨0, by unfold flowLineNR; omega⟩ rfl]
    rw [hsum, GW3Word.filter_le_eq_filter_flowLineXR_le]
    obtain ⟨y', hy', hy'J, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoR_eq hκ
      c.isPiecewiseConstantBoundaryData (GW3Word.flowLineXR_nonneg c.fn c.jumps ⟨j, hj⟩)
    refine ⟨y', lt_of_le_of_lt (GW3Word.flowLineXR_nonneg c.fn c.jumps ⟨j, hj⟩) hy', hy'J, ?_⟩
    rw [hS, Sec4.cumWeightRight]
    field_simp
    ring

/-- **A uniform bound for a stop word**: if the launch word is bounded by `M` off its jumps, the stop word is bounded
by `max M (λ + |θχ|)` off its jumps. -/
theorem abs_stopWord_fn_le (hκ : 0 < κ) {c : BoundaryWord} {M : ℝ} (hc : ∀ x ∉ c.jumps, |c.fn x| ≤ M)
    (θ : ℝ) (r : RecData) {y : ℝ} (hy : y ∉ (stopWord κ (c, θ, r)).jumps) :
    |(stopWord κ (c, θ, r)).fn y| ≤ max M (sleLambda κ + |θ * chiC κ|) := by
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hside : ∀ s : ℝ, s = sleLambda κ ∨ s = -sleLambda κ →
      |s - θ * chiC κ| ≤ max M (sleLambda κ + |θ * chiC κ|) := by
    intro s hs
    refine le_max_of_le_right ((abs_sub _ _).trans ?_)
    rcases hs with rfl | rfl
    · rw [abs_of_pos hl]
    · rw [abs_neg, abs_of_pos hl]
  have hneg : ∀ z < 0, |(stopWord κ (c, θ, r)).fn z| ≤ max M (sleLambda κ + |θ * chiC κ|) := by
    intro z hz
    rcases Lh.stopWord_fn_neg_mem hκ c θ r hz with he | ⟨x, -, hxJ, he⟩
    · rw [he, show -sleLambda κ - θ * chiC κ = -sleLambda κ - θ * chiC κ from rfl]
      exact hside _ (Or.inr rfl)
    · rw [he]
      exact le_max_of_le_left (hc x hxJ)
  rcases lt_trichotomy y 0 with hy0 | rfl | hy0
  · exact hneg y hy0
  · obtain ⟨z, hz, hz0⟩ := ((BoundaryWord.eventually_index_eq hy).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Iio (0 : ℝ) ∈ 𝓝[<] 0) |>.exists
    have he : (stopWord κ (c, θ, r)).fn z = (stopWord κ (c, θ, r)).fn 0 := by
      unfold BoundaryWord.fn
      rw [hz]
    rw [← he]
    exact hneg z hz0
  · rcases stopWord_fn_pos_mem hκ c θ r hy0 with he | ⟨x, -, hxJ, he⟩
    · rw [he]
      exact hside _ (Or.inl rfl)
    · rw [he]
      exact le_max_of_le_left (hc x hxJ)

/-- A recentring keeps a uniform bound off the jumps. -/
theorem abs_shiftW_fn_le {c : BoundaryWord} {M : ℝ} (hc : ∀ x ∉ c.jumps, |c.fn x| ≤ M) (a : ℝ) :
    ∀ y ∉ (BoundaryWord.shiftW a c).jumps, |(BoundaryWord.shiftW a c).fn y| ≤ M := by
  intro y hy
  rw [BoundaryWord.fn_shiftW]
  refine hc _ fun hmem => hy ?_
  rw [BoundaryWord.jumps_shiftW]
  exact Finset.mem_image.2 ⟨y + a, hmem, by ring⟩

/-- Every word is bounded by the sum of the absolute values of its heights. -/
theorem abs_fn_le_sum (c : BoundaryWord) (y : ℝ) :
    |c.fn y| ≤ ∑ i ∈ Finset.range (c.1 + 1), |c.2.2 i| := by
  unfold BoundaryWord.fn
  exact Finset.single_le_sum (f := fun i => |c.2.2 i|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (BoundaryWord.index_le c y)))

end StopWord

/-! ### Uniformly bounded stage witnesses -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The conditional words of a finite staged history have uniformly bounded heights**: at every stage there is a
witness of the staged law and one constant bounding its word off the jumps at almost every launch sample (strong
induction on the stage through the explicit stop-word witness `GW1W.isStageWitness_succ_expl`, as for the countable
profiles of `exists_stageWitness_countable_profiles`). -/
theorem exists_stageWitness_bounded (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
      IsStageWitness κ b jumps P h spec E k β Y ∧ 0 ≤ M ∧
        ∀ᵐ ω ∂P,
          (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
            ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀,
        fun ω => Exist.flowField spec.1 0 (h ω), ∑ i ∈ Finset.range (c₀.1 + 1), |c₀.2.2 i|,
        GW1W.isStageWitness_zero hh hc₀J hc₀,
        Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
      exact Eventually.of_forall fun _ _ =>
        abs_shiftW_fn_le (fun x _ => abs_fn_le_sum c₀ x) spec.1
    have Hprev : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧ 0 ≤ M ∧
          ∀ᵐ ω ∂P,
            (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
              ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, M, hW, hM0, hM⟩ := ih ℓ hℓ
        exact ⟨β, Y, M, fun _ => ⟨hW, hM0, hM⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, 0, fun h' => absurd h' hℓ⟩
    choose β Y M hprev using Hprev
    obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
      (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
      (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
      β Y (fun ℓ hℓ => (hprev ℓ hℓ).1)
    set Mk : ℝ := ∑ ℓ ∈ Finset.range k, (M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|)) with hMk
    have hterm : ∀ ℓ ∈ Finset.range k, 0 ≤ M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|) :=
      fun ℓ hℓ => add_nonneg (hprev ℓ (Finset.mem_range.1 hℓ)).2.1
        (add_nonneg hl.le (abs_nonneg _))
    have hle : ∀ ℓ < k, max (M ℓ) (sleLambda κ + |instrAngle spec ℓ * chiC κ|) ≤ Mk := by
      intro ℓ hℓ
      have hM0 := (hprev ℓ hℓ).2.1
      refine (max_le_add_of_nonneg hM0 (add_nonneg hl.le (abs_nonneg _))).trans ?_
      exact Finset.single_le_sum (f := fun ℓ => M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|))
        hterm (Finset.mem_range.2 hℓ)
    refine ⟨βk, Yk, Mk, hWk, Finset.sum_nonneg hterm, ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          ∀ y ∉ (β ℓ ω).jumps, |(β ℓ ω).fn y| ≤ M ℓ := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · exact (hprev ℓ hℓ).2.2.mono fun _ hω _ => hω
      · exact Eventually.of_forall fun _ h' => absurd h' hℓ
    filter_upwards [hall] with ω hω hlk
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ :=
      exists_last_launch spec (fun j => E j ω) hk hcθ
    have hlℓ : (ExplState.run κ b jumps spec (fun j => E j ω)
        (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hl']
      exact Option.some_ne_none _
    rw [hexpl ℓ ω hℓk hlk hlℓ hn]
    intro y hy
    exact (abs_shiftW_fn_le (fun x hx => abs_stopWord_fn_le hκ (hω ℓ hℓk hlℓ) _ _ hx) _ y hy).trans
      (hle ℓ hℓk)

end Stage

/-! ### The bounded conditional chart field and the integrability of its pairings -/

section Chart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The field read in the recentred version chart is conditionally a GFF with uniformly bounded data**: one
constant `M` such that, at almost every launch sample, conditionally on the retained past the field read in the
version chart recentred at any entry `m` is the GFF of a word bounded by `M` off its jumps (the bounded witness of
`exists_stageWitness_bounded`, transported as in `exists_k2Word_countable_types`). -/
theorem exists_bound_condChartField (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) (m : Ω → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∃ (c' : BoundaryWord) (h' : Ω → DistOn upperHalfPlaneOpens),
        (∀ y ∉ c'.jumps, |c'.fn y| ≤ M) ∧
        (∀ ω, IsChartTransport ((verChart κ b jumps spec E k ω₀).recenter (m ω₀))
          1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
          h' c'.fn c'.jumps := by
  obtain ⟨β, Y, M, hW, hM0, hbd⟩ := exists_stageWitness_bounded hκ hb hh hE hreg k
  refine ⟨M, hM0, ?_⟩
  have hG := ae_condChartField_of_stageWitness k hreg (hE.2.1 k) hW hh.1
  filter_upwards [hG, ae_verChart_eq_runChart hR hreg k, hW.2.2.1, hbd]
    with ω₀ hG₀ hver hp hbd₀ hlaunch
  obtain ⟨h', hct, hgff⟩ := hG₀ hlaunch
  obtain ⟨hc, hlc, -⟩ := hp hlaunch
  have hc' := hc.recenter (m ω₀)
  have hT' : ∀ ω, IsChartTransport ((Cond.runChart κ b jumps spec E k ω₀).recenter (m ω₀))
      1 0 (chiC κ) (h ω) (Chart.chartTransport hc' 1 0 (chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hc'
      (Chart.locallyIntegrableOn_of_continuousOn (Chart.continuousOn_recenter_lift hlc))
      1 0 (chiC κ) (h ω)
  have he : (fun ω => Chart.chartTransport hc' 1 0 (chiC κ) (h ω)) =
      fun ω => Exist.flowField (m ω₀) 0 (h' ω) :=
    funext fun ω => eq_flowField_of_recenter hc hlc (hct ω) (hT' ω)
  refine ⟨BoundaryWord.shiftW (m ω₀) (β ω₀), fun ω => Chart.chartTransport hc' 1 0 (chiC κ) (h ω),
    abs_shiftW_fn_le (hbd₀ hlaunch) (m ω₀), ?_, ?_⟩
  · rw [hver]
    exact hT'
  · rw [he, BoundaryWord.jumps_shiftW,
      show (BoundaryWord.shiftW (m ω₀) (β ω₀)).fn =
        fun y => (β ω₀).fn (y + m ω₀) from funext (BoundaryWord.fn_shiftW _ _)]
    exact Supp9.IsGFFWithBoundaryData.recenter (β ω₀).isPiecewiseConstantBoundaryData
      (m ω₀) hgff

end Chart

/-- **K2's integrability clause for SB2(1), PROVED** (clause (E4) of `SB2EntranceK2Statement`): for every SB2(1)
launch problem and chart record, every pairing of the flow-rule field read in the recentred version chart is
integrable on the launch event. Conditionally on the retained past the field read in that chart is a GFF with data
bounded by one constant (`exists_bound_condChartField`), so the conditional first moment of the pairing is bounded
uniformly (`BW1In.lintegral_enorm_apply_le_of_isGFF`, plus the constant `ψχ ∫ φ`); disintegrate over the retained
past. -/
theorem integrableOn_chartPairing {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (φ : TestOn upperHalfPlaneOpens) :
    IntegrableOn (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ)
      (launchSet κ b jumps E (k + 1)) P := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS : IsStagedHistory κ b jumps P h w (E w) := H.staged w hprog
  have hR : StagedPiecesRegular κ b jumps P w (E w) := H.pieces_regular w hprog
  have h𝒢 : pastSigma κ b jumps w (E w) (k + 1) ≤ mΩ := hS.2.1 (k + 1)
  have hF𝒢 : MeasurableSet[pastSigma κ b jumps w (E w) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma H.boundary hS.1 (H.drivers_regular w) (k + 1)
  have hF : MeasurableSet (launchSet κ b jumps E (k + 1)) := h𝒢 _ hF𝒢
  obtain ⟨M, hM0, hbd⟩ := exists_bound_condChartField H.kappa_pos H.boundary H.field hS hR
    (H.drivers_regular w) (k + 1) I.entry
  have hcm := I.chart_measurable.mono h𝒢
  have hXm : Measurable fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ :=
    (LQGMetric.measurable_distOn_apply φ).comp
      (Chart.measurable_chartTransport_random' I.chart_measurable.1 hcm.2.2.2.1 hcm.2.2.2.2.1
        hcm.2.2.2.2.2.2 I.chart_measurable.2.1 H.field.1 1 (ψ * chiC κ) (chiC κ))
  set K : ℝ≥0∞ := ‖ψ * chiC κ * Chart.oneDist φ‖ₑ with hK
  set C : ℝ≥0∞ := ENNReal.ofReal (M * ∫ z, |φ z|) +
    ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal) + K
    with hC
  have hCtop : C < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    BW1In.lintegral_enorm_gaussianReal_lt_top _⟩, enorm_lt_top⟩
  set f : Ω → ℝ≥0∞ := (launchSet κ b jumps E (k + 1)).indicator fun ω =>
    ‖Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ‖ₑ with hfdef
  have hfm : Measurable f := hXm.enorm.indicator hF
  have hbound : ∀ᵐ ω₀ ∂P, ∫⁻ ω, f ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) ≤ C := by
    filter_upwards [KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hF𝒢, hbd, I.frozen] with ω₀ hc hb₀ hfz
    by_cases hω₀ : ω₀ ∈ launchSet κ b jumps E (k + 1)
    · obtain ⟨c', h', hc'M, hct, hgff⟩ := hb₀ hω₀
      have hY : ∀ ω, h' ω = Chart.chartTransport (I.chart_measurable.1 ω₀) 1 0 (chiC κ) (h ω) := fun ω =>
        IsChartTransport.unique (I.chart_measurable.1 ω₀) (hct ω)
          (CondDriverBridge.isChartTransport_chartTransport_of_continuousOn (I.chart_measurable.1 ω₀)
            (I.chart_measurable.2.1 ω₀) 1 0 (chiC κ) (h ω))
      have hpt : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀),
          f ω ≤ ‖h' ω φ‖ₑ + K := by
        filter_upwards [hfz] with ω hω
        have he := CondDriverBridge.chartTransport_congr_chart (I.chart_measurable.1 ω)
          (I.chart_measurable.1 ω₀) hω 1 (ψ * chiC κ) (chiC κ) (h ω)
        refine (indicator_le_self _ _ ω).trans ?_
        change ‖Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ‖ₑ ≤ _
        rw [he, hY ω]
        have hsplit : Chart.chartTransport (I.chart_measurable.1 ω₀) 1 (ψ * chiC κ) (chiC κ) (h ω) φ =
            Chart.chartTransport (I.chart_measurable.1 ω₀) 1 0 (chiC κ) (h ω) φ +
              ψ * chiC κ * Chart.oneDist φ := by
          rw [Chart.chartTransport_apply', Chart.chartTransport_apply']
          ring
        rw [hsplit]
        exact enorm_add_le _ _
      calc ∫⁻ ω, f ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀)
          ≤ ∫⁻ ω, (‖h' ω φ‖ₑ + K) ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) :=
            lintegral_mono_ae hpt
        _ = ∫⁻ ω, ‖h' ω φ‖ₑ ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) + K := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ C := add_le_add_left
            (BW1In.lintegral_enorm_apply_le_of_isGFF c'.isPiecewiseConstantBoundaryData hgff hM0 hc'M φ) K
    · have h0 : condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀ (launchSet κ b jumps E (k + 1)) = 0 :=
        hc.2 hω₀
      rw [hfdef, lintegral_indicator hF, setLIntegral_measure_zero _ _ h0]
      exact zero_le
  refine ⟨hXm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [← lintegral_indicator hF]
  change ∫⁻ ω, f ω ∂P < ⊤
  rw [← KernelTower.lintegral_lintegral_condExpKernel h𝒢 hfm]
  calc ∫⁻ ω₀, ∫⁻ ω, f ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) ∂P ≤ ∫⁻ _, C ∂P :=
        lintegral_mono_ae hbound
    _ = C := by rw [lintegral_const, measure_univ, mul_one]
    _ < ⊤ := hCtop

/-! ### The named inputs without their integrability clause -/

/-- **Named input, route A, without (E4)**: `SB2EntranceK2Statement` with its integrability clause dropped (it is
proved, `integrableOn_chartPairing`). -/
def SB2EntranceK2NStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∃ (𝒢' : {m : MeasurableSpace Ω // m ≤ mΩ}) (F' : Set Ω) (𝓗 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ),
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ 𝒢'.1 ∧
      𝒢'.1 ≤ 𝓗 0 ∧ MeasurableSet[𝒢'.1] F' ∧ F' ⊆ launchSet κ b jumps E (k + 1) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω → ω ∈ F') ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ F' → ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (I.chart ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢'.1 ω₀) h' (I.word ω₀).fn (I.word ω₀).jumps) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      (∀ w ∈ I.types,
        HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ ψ I.word F' w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P 𝓗 (seedCell κ ψ I.word F' w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))) ∧
      ∃ Vg : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
            IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
              (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
              (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)) ∧
        ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          ω ∈ wordTypeCell κ ψ I.word F' w →
          Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- **Named input, route B, without (E4)**: `SB2LaunchK2Statement` with its integrability clause dropped. -/
def SB2LaunchK2NStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ),
      pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ 𝓗 0 ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓗 W ∧
      (∀ w ∈ I.types,
        HasSafeLaw κ (typedRhoL w) (typedRhoR w) P 𝓗 (seedCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P 𝓗 (seedCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w)
          (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) W
          (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))) ∧
      ∃ Vg : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
            IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
              (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
              (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)) ∧
        ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
          ω ∈ wordTypeCell κ ψ I.word (launchSet κ b jumps E (k + 1)) w →
          Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- Route A without (E4) gives route A: the integrability clause on `F' ⊆ launchSet` from
`integrableOn_chartPairing`. -/
theorem sb2EntranceK2Statement_of_N (hN : SB2EntranceK2NStatement.{u}) : SB2EntranceK2Statement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ H I
  obtain ⟨G', F', 𝓗, W, Γ, h1, h2, h3, h4, h5, h6, hW0, hWc, hWa, hK2, Vg, hl, hlf⟩ :=
    hN κ b jumps P h E k u ψ η ζ H I
  exact ⟨G', F', 𝓗, W, Γ, h1, h2, h3, h4, h5, h6, hW0, hWc, hWa,
    fun φ => (integrableOn_chartPairing H I φ).mono_set h4, hK2, Vg, hl, hlf⟩

/-- Route B without (E4) gives route B. -/
theorem sb2LaunchK2Statement_of_N (hN : SB2LaunchK2NStatement.{u}) : SB2LaunchK2Statement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ H I
  obtain ⟨𝓗, W, Γ, h0, hW0, hWc, hWa, hK2, Vg, hl, hlf⟩ := hN κ b jumps P h E k u ψ η ζ H I
  exact ⟨𝓗, W, Γ, h0, hW0, hWc, hWa, fun φ => integrableOn_chartPairing H I φ, hK2, Vg, hl, hlf⟩

/-- **SB2(1)'s clauses (1) and (3) at the launches after the first from Theorems 1.2–1.3 and route A without
(E4).** -/
theorem sb2DriverLinkAmbStatement_of_entranceK2N (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hN : SB2EntranceK2NStatement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_entranceK2 h12p h13 (sb2EntranceK2Statement_of_N hN)

/-- **The same from route B without (E4).** -/
theorem sb2DriverLinkAmbStatement_of_launchK2N (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hN : SB2LaunchK2NStatement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_launchK2 h12p h13 (sb2LaunchK2Statement_of_N hN)

end InteractingSLE.Theorem14.SB.Lv
