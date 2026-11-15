/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PathWitness
import InteractingSLE.Spec.Supplement.BR6ProofArc
import InteractingSLE.Spec.Supplement.GW4IdentLaw

/-!
# GW1's retargeting inside the conditional pair (right walk)

Packet PROVE-GW1-PATH. Astra follow-up 5 §4.4: "Apply the adopted boundary-hitting result inside the complete
conditional law of Proposition 4.2 […] Only now apply finite retargeting, inside the already identified conditional
law". For the right walk at a next launch `2(n+1)`, under the regular conditional law `μ` given the retained past
`pastSigma (2n+1)`:

* `launchChart_next_eq`: the next launch chart is the post-piece chart `d` recentred at `v = postShift`;
* `ae_visit_of_low`: BR6 sufficiency (proved from Theorem 1.3, `GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`)
  makes a centred counterflow visit every point `v > 0` below which its word is low (every rational point of `(0, v)`
  is a low-arc root; the completed range is closed);
* `IsRegCf`, `IsRetargetOf`: a regular counterflow driver path; `U` is `Q` retargeted at `v` (Corollary BR4a's
  pathwise conclusion for one path: transient trace of `U`, clock onto `[0, T_v)`, tip identification);
* **`ae_kernel_retarget_right`**: for almost every `ω₀` at a next launch, `v > 0` and, `μ`-almost surely, the terminal
  relative driver `Q` visits `v` and the next-launch driver `U` is `Q` retargeted at `v` (`IsRetargetOf`). This is
  Corollary BR4a applied under `μ` to the post-piece field, with the retargeted driver identified with `U` by
  Theorem 1.2's determination (`GW4Ident.ae_eq_of_isCenteredCounterflowDriver`).

Inputs: `BR4a.BR4aStatement` (an existing Theorem 1.4 leaf), Theorems 1.2 (R44 form) and 1.3. What this does **not**
give is the `P`-almost sure (pathwise) form required by `GW1Laws.RetargetPathStatement`: the clock depends on the
conditional law, and the tip relation is not a measurable event (ruling R51); see `GW1PathReduce`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Path

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1W GW1WalkExit GW1Laws
  GW1RestartPair

section Chart

variable {κ θ₀ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The next launch chart is the post-piece chart recentred at `postShift`.** -/
theorem launchChart_next_eq {n : ℕ} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ₀ right) D (2 * n + 1)).2.2.2.1 (2 * n) ≠ none)
    (hcθ : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ₀ right) D (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) = some (c, θ)) :
    c = (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ₀ right) D (2 * n + 1))).recenter
      (postShift κ b jumps (boundaryWalkSpec b jumps θ₀ right) D n) := by
  set spec := boundaryWalkSpec b jumps θ₀ right with hspec
  have hc := (eq_launch_of_launches spec D hcθ).2.2
  obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, a, hchart⟩ := exists_last_launch spec D (by omega : 0 < 2 * (n + 1)) hcθ
  have hℓ : ℓ = 2 * n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hl (hn (2 * n) hlt (by omega))
    · have h1 : ℓ = 2 * n + 1 := by omega
      subst h1
      have h2 := GW1RestartPair.noLaunch_walk_odd (κ := κ) (b := b) (jumps := jumps) (θ := θ₀) (right := right) D n
      rw [h2] at hl'
      exact absurd hl' (by simp)
  subst hℓ
  have hx : postShift κ b jumps spec D n = a := by
    unfold postShift
    rw [hchart]
    simp [InteractingSLE.Chart.recenter]
  rw [hc, hchart, hx]

end Chart

section Visit

/-- **A centred counterflow visits every `v > 0` below which its word is low** (BR6 sufficiency at the rational points
of `(0, v)`, proved from Theorem 1.3, and closedness of the completed range). -/
theorem ae_visit_of_low (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {γ : BoundaryWord} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData μ h γ.fn γ.jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ μ h W ζ) (hζ : ∀ᵐ ω ∂μ, ζ ω = ⊤)
    {v : ℝ} (hv0 : 0 < v)
    (hlow : ∀ y, 0 < y → y < v → y ∉ γ.jumps → γ.fn y + -(Real.pi / 2) * chiC κ ≤ -sleLambda κ) :
    ∀ᵐ ω ∂μ, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W t ω) ⊤ := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  have hrat : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < v →
      (((q : ℝ) : ℂ)) ∈ counterflowCompletedRange (fun t => W t ω) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < v
    · filter_upwards [GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 hT13 hGW0 hκ hκ4
        γ.isPiecewiseConstantBoundaryData hh hcf hζ (mem_lowerArcRoots_of_fn_low hlow q hq.1 hq.2) hq.1 le_rfl]
        with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hq
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  filter_upwards [hrat, hγ, hζ, hdrv] with ω hq hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hclosed := CounterflowRange.isClosed_counterflowCompletedRange hγω.1 hWc hdω.1 (hγω.2 rfl)
  have hmem : (v : ℂ) ∈ counterflowCompletedRange (fun t => W t ω) := by
    rw [← hclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (v - ε) (v / 2) < v from
      max_lt (by linarith) (by linarith))
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_right _ _) hq1)
    refine ⟨((q : ℝ) : ℂ), hq q hq0 hq2, ?_⟩
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith [le_max_left (v - ε) (v / 2)]
  rcases hmem with h1 | h1
  · exact h1
  · exfalso
    rw [mem_singleton_iff, Complex.ofReal_eq_zero] at h1
    exact hv0.ne' h1

end Visit

section Defs

/-- **A regular counterflow driver path**: continuous from `0`, with a transient continuous generating trace on
`[0, ∞)`. -/
def IsRegCf (Q : ℝ≥0 → ℝ) : Prop :=
  Continuous Q ∧ Q 0 = 0 ∧ ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace Q ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop

/-- **`U` is `Q` retargeted at the real point `v`**, in a fixed counterflow coordinate (the conclusion of Corollary
BR4a for one path): `U` has a transient continuous generating trace, and a continuous strictly increasing clock maps
`[0, ∞)` onto `[0, T_v)`, `T_v` the first visit of `v` by `Q`, so that the tips of `U` read through `id.recenter v`
and the inversion are the tips of `Q` (read through the inversion) at the clock times. -/
def IsRetargetOf (U Q : ℝ≥0 → ℝ) (v : ℝ) : Prop :=
  (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace U ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
  ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧
    range ℓ = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart Q {(v : ℂ)}} ∧
    ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.recenter v).trans infinitySourceChart).tipAt U r z ↔
      infinitySourceChart.tipAt Q (ℓ r) z

end Defs

section Retarget

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Retargeting inside the conditional pair (right walk).** For almost every `ω₀` at a next launch, the recentring
amount `v = postShift ω₀` is positive and, under the regular conditional law given `pastSigma (2n+1)`, almost surely
the terminal relative driver `Q` visits `v` and the next-launch driver `U` is `Q` retargeted at `v` (Corollary BR4a
under the conditional law, the retargeted driver identified with `U` by Theorem 1.2's determination). -/
theorem ae_kernel_retarget_right (hBR4a : BR4a.BR4aStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E true n V ζV ℓ)
    {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞} {β : Ω → ℝ≥0 → ℝ≥0}
    (hQ : IsTerminalRestart κ b jumps P h true (E (GW1Z.walkSpec b jumps true)) n V Q ζQ β)
    {U : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hU : IsForcedRetargetCond κ b jumps P h true (E (GW1Z.walkSpec b jumps true)) n U ζ) :
    ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω₀)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      0 < postShift κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n ∧
      ∀ᵐ ω ∂(condExpKernel P
          (pastSigma κ b jumps (GW1Z.walkSpec b jumps true) (E (GW1Z.walkSpec b jumps true)) (2 * n + 1)) ω₀),
        ((postShift κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n : ℝ) :
            ℂ) ∈ infinitySourceChart.tipSet (fun t => Q t ω) ⊤ ∧
        IsRetargetOf (fun s => U s ω) (fun s => Q s ω)
          (postShift κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n) := by
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hh := hdata.field
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc true) true
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps true)
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hdata.counterflow hdata.complete
  obtain ⟨βk, Yk, hW, hgood⟩ := exists_post_witness_right_prof hκ hb hh hE hreg hambL hambR n
  have hstages : ∀ᵐ ω ∂P, WalkStageData κ b jumps (-(Real.pi / 2)) true
      (fun j => E (GW1Z.walkSpec b jumps true) j ω) := by
    filter_upwards [hdata.stages] with ω hω
    simpa only [↓reduceIte] using hω
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hstages, hdata.pieces _ hprog] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  have hgood' : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true) (fun j => E (GW1Z.walkSpec b jumps true) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
        βk ω = BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps true)
          (fun j => E (GW1Z.walkSpec b jumps true) j ω) n) γ := by
    filter_upwards [hgood] with ω hω hlk hl
    obtain ⟨γ, hγ, hβ, -, -⟩ := hω hlk hl
    exact ⟨γ, hγ, hβ⟩
  have hK := ae_terminal_kernel hb hE hreg hW hgood' hprev
  have hLow := ae_post_low_right (P := P) hb hreg hstages n hgood hprev
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps true)
        (E (GW1Z.walkSpec b jumps true)) (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps true)
        (E (GW1Z.walkSpec b jumps true)) (2 * n + 1)) ω :=
    condExpKernel_walk_connector (κ := κ) (b := b) (jumps := jumps) (θ := -(Real.pi / 2)) (right := true) P _ n
  filter_upwards [hK, hLow, hQ.conditional, hU.2, hprev] with ω₀ hk hlow hq hu hpv hlk
  obtain ⟨hgw, hgff, -, hconf, hlift, htrans⟩ := hk hlk
  obtain ⟨hv0, hlowv⟩ := hlow hlk
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
  -- the field read in the post-piece chart, exactly
  have hh' : ∀ ω, IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true)
      (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) (2 * n + 1))) 1 0 (chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'm : Measurable fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) :=
    (Chart.measurable_chartTransport _ _ _ _).comp hh.1
  have hgffμ := isGFFWithBoundaryData_congr_ae hgff hh'm (htrans _ hh')
  rw [hker ω₀] at hgffμ
  obtain ⟨hQcf, hQζ⟩ := hq hlk _ hh'
  have hvis := ae_visit_of_low hT13 hT13₀ hκ hκ4 hgffμ hQcf hQζ hv0 hlowv
  obtain ⟨hv, Wv, ζv, ℓv, hvtr, hvcf, -, hvae⟩ :=
    hBR4a κ hκ hκ4 _ _ (postWord κ b jumps (GW1Z.walkSpec b jumps true) (E (GW1Z.walkSpec b jumps true)) n βk
      ω₀).isPiecewiseConstantBoundaryData _ _ hgffμ Q ζQ hQcf hQζ _ hv0.ne' hvis
  -- the next launch chart is the post-piece chart recentred at `v`
  have hc := launchChart_next_eq (hpv hlk) hcθ
  have htrc : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hv ω) := by
    intro ω
    have h1 := IsChartTransport.trans hconf (isConformal_shiftChart _) hlift (continuousOn_shiftChart_lift _)
      (hh' ω) (hvtr ω)
    rw [hc, Chart.recenter_eq_trans]
    exact h1
  obtain ⟨hUcf, hUζ⟩ := hu c θ hcθ hv htrc
  -- determination: `U` is the retargeted driver
  have hvgff : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps true)
      (E (GW1Z.walkSpec b jumps true)) (2 * n + 1)) ω₀) hv
      (BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps true)
        (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n)
        (postWord κ b jumps (GW1Z.walkSpec b jumps true) (E (GW1Z.walkSpec b jumps true)) n βk ω₀)).fn
      (BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps true)
        (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n)
        (postWord κ b jumps (GW1Z.walkSpec b jumps true) (E (GW1Z.walkSpec b jumps true)) n βk ω₀)).jumps := by
    have h1 := isGFFWithBoundaryData_shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps true)
      (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n) hgffμ
    have e : (fun ω => flowField (postShift κ b jumps (GW1Z.walkSpec b jumps true)
        (fun j => E (GW1Z.walkSpec b jumps true) j ω₀) n) 0
          (Chart.chartTransport hconf 1 0 (chiC κ) (h ω))) = hv :=
      funext fun ω => (isChartTransport_shiftChart _ (chiC κ) _).unique (isConformal_shiftChart _) (hvtr ω)
    rw [e] at h1
    exact h1
  have hdet := GW4Ident.ae_eq_of_isCenteredCounterflowDriver h12p hT13 hκ
    (BoundaryWord.isPiecewiseConstantBoundaryData _) hvgff hUcf hUζ hvcf (hvae.mono fun ω hω => hω.1)
  -- the retargeted driver has a transient trace (Theorem 1.3)
  obtain ⟨bv, Jv, hv'', -, -, hvfl⟩ := hvcf
  have hvtrace := GW2aSingle.ae_chosenTrace hT13 (show (0 : ℝ) < 16 / κ by positivity) hvfl
  refine ⟨hv0, ?_⟩
  filter_upwards [hvis, hvae, hdet, hvtrace] with ω hvisω hvω hdω htω
  obtain ⟨hζv, hc1, hc2, hc3, hc4⟩ := hvω
  rw [hζv] at htω
  refine ⟨hvisω, ⟨GW2aSingle.chosenTrace Wv ζv ω, ?_, ?_⟩, ℓv ω, hc1, hc2, hc3, fun r z => ?_⟩
  · rw [hdω]
    exact htω.1
  · exact htω.2 rfl
  · rw [hdω]
    exact hc4 r z

end Retarget

end InteractingSLE.Theorem14.GW1Path
