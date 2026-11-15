/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aPiece
import InteractingSLE.Spec.Supplement.GW1PieceChart
import InteractingSLE.Spec.Supplement.GW2aMulti

/-!
# GW2a's step in a launch chart: from the conditional pair to the original physical range

Packet PROVE-T14-BR5. GW2a (supplement p. 623): "In the already established complete conditional counterflow pair
targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary piece […] Its raw range is in the earlier
counterflow prefix"; GW1 (p. 619): "Apply GB6, within the independently established complete conditional pair in
item 2, to every available interior-tip prefix of `β_j`. It lies in `η[0, T_{w_j}]` in reverse first-visit order.
Continuity gives the same inclusion at a finite endpoint."

A piece launched at stage `k` is read through the launch chart `c` (the chart of the current unbounded domain). In
the coordinates of `c` the piece and the conditional counterflow are a flow line and the centred counterflow of the
conditional field, so `GW2aPiece.ae_tipSet_subset_of_pair` places the piece in the conditional counterflow range in
these coordinates. This file carries the inclusion through the chart, also at the times at which the piece touches
the boundary of its domain (where `c⁻¹` is not continuous on `ℂ`): it uses the boundary limits `f` of `c⁻¹` from inside
`ℍ` (`GW1P.HasProperBdryExt`, proved for every chart of a run with regular pieces in `GW1PieceRun`) and the tip
identification of the conditional counterflow with the original one (the clock part of the pair, as in
`BR4a.BR4aStatement` and `BW1.BW1Statement`).

* `trace_mem_Hbar`, `neg_inv_mem_H`, `neg_inv_mem_Hbar`, `mem_Hbar_of_mem_counterflowCompletedRange`;
* `tipAt_trans_of_ne_zero`: the conditional counterflow's tip at `r`, read through `c` and the inversion, is
  `f(−1/γ(r))`;
* **`tipSet_subset_of_chart`** (pathwise): if the piece's chart-coordinate points lie in the conditional counterflow's
  completed range, every conditional tip read through `c` lies in a closed set `R`, and the conditional counterflow is
  transient, then the piece's physical points (read through `c`) lie in `R` — its terminal point `0` by continuity of
  `f` at `0` along the transient trace;
* **`ae_tipSet_subset_of_chart_pair`**: under one probability law (in the application, the conditional law given the
  retained past), GW2a's step for a piece read through a launch chart with boundary limits.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aPiece

open CounterflowRange

/-! ### Points of the closed half-plane -/

/-- `z ↦ −1/z` maps `ℍ` into `ℍ`. -/
theorem neg_inv_mem_H {w : ℂ} (hw : w ∈ H) : -w⁻¹ ∈ H := by
  have hw' : 0 < w.im := hw
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw'; exact lt_irrefl _ hw'
  change 0 < (-w⁻¹).im
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hw' (Complex.normSq_pos.2 hw0)

/-- `z ↦ −1/z` maps `ℍ̄` into `ℍ̄` (with `−1/0 = 0`). -/
theorem neg_inv_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : -z⁻¹ ∈ Hbar := by
  have hz' : 0 ≤ z.im := hz
  change 0 ≤ (-z⁻¹).im
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_nonneg hz' (Complex.normSq_nonneg z)

/-- The points of a continuous generating trace on `[0, ∞)` of a continuous driver lie in `ℍ̄`. -/
theorem trace_mem_Hbar {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W)
    (hW0 : W 0 = 0) (r : ℝ≥0) : γ r ∈ Hbar := by
  have hU : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
  have hU0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
  have hF := hγ.tendsto_fwdMapInv_mul_I hW.continuousOn hW0 (ENNReal.coe_lt_top (r := r))
  refine QuantumZipper.isClosed_Hbar.mem_of_tendsto hF ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyH : (y : ℂ) * Complex.I ∈ H := by
    show 0 < ((y : ℂ) * Complex.I).im
    simpa using hy
  exact (show 0 < (fwdMapInv (fun s : ℝ => W s.toNNReal) r ((y : ℂ) * Complex.I)).im from
    QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg r) hyH).le

/-- The completed range of a counterflow with a continuous generating trace lies in `ℍ̄`. -/
theorem mem_Hbar_of_mem_counterflowCompletedRange {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) {p : ℂ}
    (hp : p ∈ counterflowCompletedRange W) : p ∈ Hbar := by
  rcases hp with hp | hp0
  · rw [tipSet_infinitySourceChart_top hγ hW hW0] at hp
    obtain ⟨r, -, rfl⟩ := hp
    exact neg_inv_mem_Hbar (trace_mem_Hbar hγ hW hW0 r)
  · rw [mem_singleton_iff.1 hp0]
    show (0 : ℝ) ≤ (0 : ℂ).im
    simp

/-! ### Through the launch chart -/

/-- **The conditional counterflow's tip at `r`, read through the chart `c` and the inversion**, is `f(−1/γ(r))`, where
`f` is the boundary-limit map of `c⁻¹` from inside `ℍ`. -/
theorem tipAt_trans_of_ne_zero {c : Chart} {f : ℂ → ℂ} (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ≥0}
    (hr : γ r ≠ 0) : (c.trans infinitySourceChart).tipAt W r (f (-(γ r)⁻¹)) := by
  have hU : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
  have hU0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
  have hF := hγ.tendsto_fwdMapInv_mul_I hW.continuousOn hW0 (ENNReal.coe_lt_top (r := r))
  have hinv : Tendsto (fun y : ℝ => -(fwdMapInv (fun s : ℝ => W s.toNNReal) r ((y : ℂ) * Complex.I))⁻¹)
      (𝓝[>] 0) (𝓝 (-(γ r)⁻¹)) := (hF.inv₀ hr).neg
  have hH : ∀ᶠ y : ℝ in 𝓝[>] 0, -(fwdMapInv (fun s : ℝ => W s.toNNReal) r ((y : ℂ) * Complex.I))⁻¹ ∈ H := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := by
      show 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    exact neg_inv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg r) hyH)
  exact (hc _ (neg_inv_mem_Hbar (trace_mem_Hbar hγ hW hW0 r))).comp (tendsto_nhdsWithin_iff.2 ⟨hinv, hH⟩)

/-- **GW2a's step through a launch chart, pathwise.** Let `c` be a chart whose inverse has the boundary limits `f` from
inside `ℍ` at every point of `ℍ̄`, `α` a continuous generating trace of the piece's driver `Wα` up to its stop `S`, and
`γ` a transient continuous generating trace of the conditional counterflow's driver `W`. If the piece's
chart-coordinate points lie in the completed range of `W`, and every tip of `W` read through `c` and the inversion lies
in a closed set `R`, then the piece's physical points, read through `c`, lie in `R`. -/
theorem tipSet_subset_of_chart {c : Chart} {f : ℂ → ℂ} (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {Wα : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace Wα S α)
    (hWα : ContinuousOn Wα {t | (t : ℝ≥0∞) ≤ S}) (hWα0 : Wα 0 = 0) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun r => ‖γ r‖) atTop atTop)
    (hin : (Chart.id.recenter 0).tipSet (fun r : ℝ≥0 => Wα (min (r : ℝ≥0∞) S).toNNReal) S ⊆
      counterflowCompletedRange W)
    {R : Set ℂ} (hR : IsClosed R)
    (hid : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt W r z → z ∈ R) :
    c.tipSet (fun r : ℝ≥0 => Wα (min (r : ℝ≥0∞) S).toNNReal) S ⊆ R := by
  have hin' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ counterflowCompletedRange W := by
    intro t ht
    apply hin
    rw [tipSet_stopped_eq (continuous_recenter_id_inv 0) hα hWα hWα0]
    refine ⟨α t, ⟨t, ht, rfl⟩, ?_⟩
    rw [recenter_id_inv]
    simp
  have hpt : ∀ r : ℝ≥0, γ r ≠ 0 → f (-(γ r)⁻¹) ∈ R := fun r hr =>
    hid r _ (tipAt_trans_of_ne_zero hc hγ hW hW0 hr)
  have hf0 : f 0 ∈ R := by
    have hfc := GW1P.continuousOn_of_tendsto hc
    have h0 : Tendsto (fun r => -(γ r)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun r => ‖γ r‖⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp htr
      simpa only [norm_neg, norm_inv] using h1
    have hne : ∀ᶠ r in atTop, γ r ≠ 0 :=
      (htr.eventually (eventually_gt_atTop 0)).mono fun r hr => norm_pos_iff.1 hr
    have hmem : ∀ᶠ r in atTop, -(γ r)⁻¹ ∈ Hbar :=
      Eventually.of_forall fun r => neg_inv_mem_Hbar (trace_mem_Hbar hγ hW hW0 r)
    have h00 : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
    have hlim : Tendsto (fun r => f (-(γ r)⁻¹)) atTop (𝓝 (f 0)) :=
      (hfc 0 h00).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h0, hmem⟩)
    exact hR.mem_of_tendsto hlim (hne.mono fun r hr => hpt r hr)
  have hHbar : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    mem_Hbar_of_mem_counterflowCompletedRange hγ hW hW0 (hin' t ht)
  rw [tipSet_stopped_eq_of_tendsto hα hWα hWα0 fun t ht => hc (α t) (hHbar t ht)]
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  rcases hin' t ht with hp | hp0
  · rw [tipSet_infinitySourceChart_top hγ hW hW0] at hp
    obtain ⟨r, hr, hreq⟩ := hp
    rw [hreq]
    exact hpt r hr
  · rw [mem_singleton_iff.1 hp0]
    exact hf0


/-- **GW2a's step for a piece read through a launch chart, in one complete pair** (conditional on GB6's
conditional-law half, Lemma GW0's forward implication and Theorem 1.3). Under a probability law `Q` (in GW2a's
induction: the conditional law given the retained past, with the launch chart frozen), let `h` be a GFF with
piecewise-constant data, `Wk` its centred counterflow with infinite lifetime, and `Wα` an angle-`θ` flow line of `h`
(`θ ∈ [−π/2, π/2]`) with its recorded continuous limit at the lifetime. Let `c` be a chart whose inverse has boundary
limits `f` from inside `ℍ` (`GW1P.HasProperBdryExt`), and suppose that almost surely `R ω` is closed and every tip of
`Wk` read through `c` and the inversion lies in `R ω`. Then almost surely the piece run for own time `t`, read through
`c`, lies in `R ω`. -/
theorem ae_tipSet_subset_of_chart_pair (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h b jumps)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hWk : IsCenteredCounterflowDriver κ Q h Wk ζk)
    (hζk : ∀ᵐ ω ∂Q, ζk ω = ⊤) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b jumps θ Q h Wα ζα)
    (hrec : ∀ᵐ ω ∂Q, ζα ω ≠ ⊤ → 0 < ζα ω → ∀ c : ℝ,
      Tendsto (fun s => Wα s ω) (𝓝[<] (ζα ω).toNNReal) (𝓝 c) → Wα (ζα ω).toNNReal ω = c) (t : ℝ≥0∞)
    {c : Chart} {f : ℂ → ℂ} (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {R : Ω → Set ℂ} (hR : ∀ᵐ ω ∂Q, IsClosed (R ω))
    (hid : ∀ᵐ ω ∂Q, ∀ (r : ℝ≥0) (z : ℂ),
      (c.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z → z ∈ R ω) :
    ∀ᵐ ω ∂Q, c.tipSet (fun r : ℝ≥0 => Wα (min (r : ℝ≥0∞) (min t (ζα ω))).toNNReal ω) (min t (ζα ω)) ⊆
      R ω := by
  have hin := ae_tipSet_subset_of_pair hGB6 hGW0 hT13 hκ hκ4 hb hh hWk hζk hθ hfl hrec t
  obtain ⟨b', J', h', -, -, hcf⟩ := hWk
  have hκ' : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hcf
  have hα := GW2aSingle.ae_chosenTrace hT13 hκ hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hcfd := Supp8.GB6.ae_driver_zero_continuousOn hcf
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hthr := hC.1.ae_tendsto_threshold hκ
  filter_upwards [hin, hγ, hα, hdrv, hcfd, hthr, hrec, hζk, hR, hid] with ω hinω hγω hαω hdω hcfω hthω hrecω
    hζω hRω hidω
  rw [hζω] at hγω hcfω
  have hWc : Continuous fun s => Wk s ω := by
    have hc' := hcfω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  -- the driver is continuous up to the stop
  have hend : ζα ω ≠ ⊤ → 0 < ζα ω →
      Tendsto (fun s => Wα s ω) (𝓝[<] (ζα ω).toNNReal) (𝓝 (Wα (ζα ω).toNNReal ω)) := by
    intro hne hpos
    have hT : (((ζα ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζα ω := ENNReal.coe_toNNReal hne
    have hTpos : 0 < (ζα ω).toNNReal := ENNReal.toNNReal_pos hpos.ne' hne
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthω _ hTpos hT
    have h1 : Tendsto (fun s => Wα s ω) (𝓝[<] (ζα ω).toNNReal) (𝓝 w₀) :=
      (continuous_fst.tendsto _).comp hlim
    rw [hrecω hne hpos w₀ h1]
    exact h1
  exact tipSet_subset_of_chart hc (hαω.1.mono_horizon (min_le_right _ _)) (continuousOn_le_min t hdω.2 hend)
    hdω.1 hγω.1 hWc hcfω.1 (hγω.2 rfl) hinω hRω hidω


/-! ### The per-piece step under the conditional law at a launch point -/

/-- **The field of a flow-line coupling is a GFF with the word's data** (any angle `θ`): the coupling field
`h + θχ` has the force-word data of the flow-line word, which is `b + θχ` (PROVE-FLOWEXIST's
`eqOn_flowLine_harmonicExtension`), so `h` has the data `b`. -/
theorem isGFFWithBoundaryData_of_isFlowLineDriver {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ Q h W ζ) : IsGFFWithBoundaryData Q h b J := by
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hshift : ∀ ω φ, h'' ω φ = h ω φ + θ * QuantumZipper.chiC κ * ∫ z, φ z := fun ω φ =>
    htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
  refine ⟨LQGMetric.measurable_distOn_iff.2 fun φ => ?_, fun u₀ hu₀ => ?_⟩
  · have h1 : Measurable fun ω => h'' ω φ := (LQGMetric.measurable_distOn_apply φ).comp hC.2.1
    have e : (fun ω => h ω φ) = fun ω => h'' ω φ - θ * QuantumZipper.chiC κ * ∫ z, φ z :=
      funext fun ω => by rw [hshift]; ring
    rw [e]
    exact h1.sub_const _
  · obtain ⟨uF, huF⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
    have heq := Exist.eqOn_flowLine_harmonicExtension hκ hb 0 θ hu₀ huF
    have key : (fun (φ : LQGMetric.TestOn upperHalfPlaneOpens) ω => h ω φ - ∫ z, u₀ z * φ z) =
        fun φ ω => h'' ω φ - ∫ z, uF z * φ z := by
      funext φ ω
      have hi1 : Integrable fun z => u₀ z * φ z :=
        Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) hu₀.1.continuousOn φ φ.tsupport_subset
      have hi2 : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      have hF : (fun z => uF z * φ z) = fun z => u₀ z * φ z + θ * QuantumZipper.chiC κ * φ z := by
        funext z
        by_cases hz : z ∈ H
        · rw [heq hz]
          simp only [Complex.ofReal_zero, add_zero]
          ring
        · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
          rw [h0]
          ring
      rw [hF, integral_add hi1 (hi2.const_mul _), integral_const_mul, hshift]
      ring
    rw [key]
    exact hC.2.2.1 uF huF

/-- **GW2a's per-piece step under the conditional law at a launch point** (conditional on GB6's conditional-law half,
Lemma GW0's forward implication and Theorem 1.3, and on the **conditional counterflow pair at the launch**, which is
taken here as hypotheses at the fixed point `ω₀`). Let `E` be a staged history and `ω₀` a point at which the
conditional law `ν = condExpKernel P (pastSigma … k) ω₀` makes the piece of instruction `k` the angle-`θ` flow line
`hfl` of the conditional field `h'` (the clause of `IsStagedHistory` at `ω₀`, with data `b'`), and at which, under `ν`,
`(Wk, ζk)` is the centred counterflow of the same `h'` with infinite lifetime whose tips, read through the launch
chart `c` and the inversion, lie in the closed sets `R ω`. If `c⁻¹` has boundary limits from inside `ℍ` and the
recorded continuous limit of the piece holds `ν`-almost surely, then `ν`-almost surely the piece, read through `c`,
lies in `R ω`. -/
theorem ae_condExpKernel_piece_subset (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {b' : ℝ → ℝ} {jumps' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' jumps') {h' : Ω → DistOn upperHalfPlaneOpens}
    (hfl : IsFlowLineDriver κ b' jumps' θ ν h' (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2))
    (hrec : ∀ᵐ ω ∂ν, (E k ω).2 ≠ ⊤ → 0 < (E k ω).2 → ∀ c : ℝ,
      Tendsto (E k ω).1 (𝓝[<] (E k ω).2.toNNReal) (𝓝 c) → (E k ω).1 (E k ω).2.toNNReal = c)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hWk : IsCenteredCounterflowDriver κ ν h' Wk ζk)
    (hζk : ∀ᵐ ω ∂ν, ζk ω = ⊤) {c : Chart} {f : ℂ → ℂ}
    (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {R : Ω → Set ℂ} (hR : ∀ᵐ ω ∂ν, IsClosed (R ω))
    (hid : ∀ᵐ ω ∂ν, ∀ (r : ℝ≥0) (z : ℂ),
      (c.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z → z ∈ R ω) :
    ∀ᵐ ω ∂ν, c.tipSet (GW2aMulti.stoppedDriver spec (fun j => E j ω) k)
        (GW2aMulti.pieceStop spec (fun j => E j ω) k) ⊆ R ω :=
  ae_tipSet_subset_of_chart_pair hGB6 hGW0 hT13 hκ hκ4 hb' (isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl)
    hWk hζk hθ hfl hrec (Exist.StagedLaw.instrTime spec k) hc hR hid

end GW2aPiece

end Theorem14

end InteractingSLE
