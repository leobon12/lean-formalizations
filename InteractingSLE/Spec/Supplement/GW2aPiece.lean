/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Supplement.BR4a
import InteractingSLE.Spec.Supplement.W5CommonSeedShift

/-!
# Theorem 1.4: GW2a for one ordinary piece in a complete counterflow pair; the first piece from a boundary root

Packet PROVE-T14-BR5. Lemma GW2a (supplement p. 623, `source/spec/p577-624.md` L1040–L1060): "In the already
established complete conditional counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next
ordinary piece because its angle is in the displayed interval." Lemma GW2 (p. 621): "For a boundary root `v`, BR6
forces the whole initial arc `[x, v]` and BR4a gives the full conditional pair targeted at `v`. […] GB6 places each
available prefix in this conditional counterflow range in reverse first-visit order. The same conclusion holds at a
finite endpoint by continuity."

* **`ae_tipSet_subset_of_pair`**: the argument of `GW2aSingle.ae_tipSet_first_subset` for an arbitrary complete pair
  (a GFF `h` with piecewise-constant data, its centred counterflow with infinite lifetime, and an angle-`θ` flow line of
  `h` with its recorded continuous limit at the lifetime): almost surely the piece run for own time `t` lies in the
  completed range of the counterflow (GB6's first contacts at rational interior times, then density and the trace
  closure at the stop).
* **`eq_flowField_of_isChartTransport`**: the chart transport by a real translation is the translated field.
* **`IsStagedHistory.isFlowLineDriver_first_root`**: the first piece of a staged history from any root `x` is the
  angle-`θ` flow line of `h(· + x)` with the data `b(· + x)` (GW1Base's `isFlowLineDriver_first` at a general root).
* **`ae_tipSet_first_subset_of_root`**: the first piece of a staged history from a root `v ≠ 0` visited by the
  counterflow lies in its completed range, from BR4a (`BR4a.BR4aStatement`), GB6's conditional-law half, GW0 and
  Theorem 1.3 (the pair of BR4a is the complete counterflow pair targeted at `v`; its range is carried to the
  original range by the tip identification of BR4a, and its terminal point `0` is `v` itself).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aPiece

open CounterflowRange

/-! ### GW2a's single-piece argument in an arbitrary complete pair -/

/-- **One ordinary piece in a complete counterflow pair lies in the completed counterflow range** (GW2a's step, from
GB6). For `0 < κ < 4`, a GFF `h` with piecewise-constant data `b`, its centred counterflow `W'` with almost surely
infinite lifetime, and an angle-`θ` flow line `Wα` of `h` (`θ ∈ [−π/2, π/2]`) whose driver takes its recorded
continuous limit at a finite positive lifetime: almost surely, every physical point of the piece run for own time `t`
(stopped at `min t ζα`) is in `counterflowCompletedRange W'`. Conditional on GB6's conditional-law half, Lemma GW0's
forward implication and Theorem 1.3 (the same named inputs as `GW2aSingle.ae_tipSet_first_subset`, whose proof this
is, with the piece given directly as a flow line). -/
theorem ae_tipSet_subset_of_pair (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hW' : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b jumps θ P h Wα ζα)
    (hrec : ∀ᵐ ω ∂P, ζα ω ≠ ⊤ → 0 < ζα ω → ∀ c : ℝ,
      Tendsto (fun s => Wα s ω) (𝓝[<] (ζα ω).toNNReal) (𝓝 c) → Wα (ζα ω).toNNReal ω = c) (t : ℝ≥0∞) :
    ∀ᵐ ω ∂P, (Chart.id.recenter 0).tipSet
        (fun r : ℝ≥0 => Wα (min (r : ℝ≥0∞) (min t (ζα ω))).toNNReal ω) (min t (ζα ω)) ⊆
      counterflowCompletedRange (fun s => W' s ω) := by
  obtain ⟨b', J', h', hb', htr, hcf⟩ := hW'
  have hκ' : 0 < 16 / κ := by positivity
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hcf hζ'
  set γ := GW2aSingle.chosenTrace W' ζ' with hγdef
  set α := GW2aSingle.chosenTrace Wα ζα with hαdef
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hcf
  have hα := GW2aSingle.ae_chosenTrace hT13 hκ hfl
  have hcomp : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [hγ, hζ'] with ω hω hζ
    rw [hζ] at hω
    exact ⟨hζ, hω.1, hω.2 rfl⟩
  have hFC := Supp8.GB6.gb6FirstContactStatement_of_restart hGB6 κ θ hκ hκ4 hθ.1 hθ.2 Ω _ P
    inferInstance h b jumps W' Wα ζ' ζα γ α b' J' h' hb hh hb' htr
    hcf hadmL hadmR hcomp hfl (hα.mono fun _ hω => hω.1)
  have hall := ae_all_iff.2 fun q : ℚ => hFC (q : ℝ).toNNReal
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hcfd := Supp8.GB6.ae_driver_zero_continuousOn hcf
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hthr := hC.1.ae_tendsto_threshold hκ
  filter_upwards [hcomp, hα, hall, hdrv, hcfd, hthr, hrec] with ω hcω hαω hqω hdω hcfω hthω hrecω
  -- the completed counterflow range is the closure of the physical counterflow
  have hW'c : Continuous fun s => W' s ω := by
    have := hcfω.2
    rw [hcω.1] at this
    simp only [ENNReal.coe_lt_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  rw [counterflowCompletedRange_eq_preimage_closure hcω.2.1 hW'c hcfω.1 hcω.2.2]
  have h0 : ((0 : ℂ) : OnePoint ℂ) ∈ closure (range fun s => Supp8.GB6.sphereInv (γ ω s : OnePoint ℂ)) :=
    mem_closure_of_tendsto (Supp8.GB6.tendsto_sphereInv_of_tendsto_norm hcω.2.2)
      (Eventually.of_forall fun s => ⟨s, rfl⟩)
  have hfc : ∀ q : ℚ, ((q : ℝ).toNNReal : ℝ≥0∞) < ζα ω → α ω (q : ℝ).toNNReal ∈ H →
      ((α ω (q : ℝ).toNNReal : ℂ) : OnePoint ℂ) ∈ range fun s => Supp8.GB6.sphereInv (γ ω s : OnePoint ℂ) := by
    intro q hq hqH
    obtain ⟨T, hT, -⟩ := hqω q hq hqH
    exact ⟨T, hT⟩
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
  rw [tipSet_stopped_eq (continuous_recenter_id_inv 0) (hαω.1.mono_horizon (min_le_right _ _))
    (continuousOn_le_min t hdω.2 hend) hdω.1]
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  rw [recenter_id_inv]
  simp only [Complex.ofReal_zero, add_zero, mem_preimage]
  exact mem_closure_of_dense_contacts hαω.1 hdω.2 hdω.1 h0 hfc (hr.trans (min_le_right _ _))


/-! ### The chart transport by a real translation -/

/-- **The chart transport by the translation chart `z ↦ z − x` is the translated field** `h(· + x)`
(`Exist.flowField x 0`): the transport relation tested on `φ'` with the transported test function `φ'(· − x)`. -/
theorem eq_flowField_of_isChartTransport {κ x : ℝ} {g g' : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport (Chart.id.recenter x) 1 0 (QuantumZipper.chiC κ) g g') :
    g' = Exist.flowField x 0 g := by
  refine DFunLike.ext _ _ fun φ' => ?_
  set φ := Chart.pushTest (Exist.isConformal_shiftChart x) φ' with hφ
  have hφa : ∀ z, φ z = φ' (z - x) := Exist.pushTest_shiftChart_apply x φ'
  have h1 := hT φ φ' (by
      intro z hz
      have hzH : z ∈ H := φ.tsupport_subset hz
      refine ⟨z - x, ?_, ?_⟩
      · change 0 < (z - (x : ℂ)).im
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
        exact hzH
      · change z - (x : ℂ) + (x : ℂ) = z
        ring) (by
      intro z _
      rw [hφa]
      have hd : deriv (Chart.id.recenter x).1 z = 1 := by
        change deriv (fun w : ℂ => w - (x : ℂ)) z = 1
        rw [deriv_sub_const, deriv_id'']
      rw [hd, norm_one, one_pow, mul_one]
      rfl)
  rw [h1, Exist.flowField_apply]
  change 1 * g φ + 0 * (∫ w, φ' w) + QuantumZipper.chiC κ * ∫ w, (0 : ℝ) * φ' w = g φ + 0 * ∫ w, φ' w
  simp

/-! ### The first piece from an arbitrary root -/

open GW1 PiecewiseConstantBoundaryData in
/-- **The first piece of a staged history from a root `x` is the angle-`θ` flow line of `h(· + x)`** with the data
`b(· + x)` (GW1's initial datum at the root `x`: the past is trivial, the chart is the translation `z ↦ z − x`, and
the conditional data agree with `b(· + x)` off a finite set). -/
theorem _root_.InteractingSLE.IsStagedHistory.isFlowLineDriver_first_root {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) {θ : ℝ} {t : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    IsFlowLineDriver κ (fun y => b (y + spec.1)) (jumps.image (· - spec.1)) θ P
      (fun ω => Exist.flowField spec.1 0 (h ω)) (fun t ω => (E 0 ω).1 t) (fun ω => (E 0 ω).2) := by
  obtain ⟨ω₀, hω₀⟩ := (hS.2.2.2 0).exists
  have hl := launches_run_one_of_cons κ b jumps spec hp (fun j => E j ω₀)
  obtain ⟨b', jumps', h', hb', hT, hF⟩ := hω₀ _ _ hl
  rw [pastSigma_zero_eq_bot, condExpKernel_bot_apply] at hF
  have hhh : h' = fun ω => Exist.flowField spec.1 0 (h ω) :=
    funext fun ω => eq_flowField_of_isChartTransport (hT ω)
  subst hhh
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hF
  have hshift : ∀ ω φ, h'' ω φ = Exist.flowField spec.1 0 (h ω) φ + θ * QuantumZipper.chiC κ * ∫ z, φ z :=
    fun ω φ => htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
  have hbx := Exist.isPiecewiseConstant_comp_add hb spec.1
  have hhx := Supp9.IsGFFWithBoundaryData.recenter hb spec.1 hh
  have hoff := eq_off_of_isGFF hκ hbx hb' θ hhx hshift hC.2.2.1
  have hlims := lims_eq_of_eq_off_finset (insert 0 (Exist.flowExcept b' jumps' 0 ∪ jumps.image (· - spec.1)))
    (fun y hy => hoff y (fun h0 => hy (Finset.mem_insert.2 (Or.inl h0)))
      fun hm => hy (Finset.mem_insert_of_mem hm))
  have hL : leftLim b' = leftLim (fun y => b (y + spec.1)) := funext fun x => (hlims x).1
  have hR : rightLim b' = rightLim (fun y => b (y + spec.1)) := funext fun x => (hlims x).2
  exact isFlowLineDriver_congr (jumpSet_eq_of_lims hb' hbx hL hR) hL hR ⟨h'', 𝓕, VL, VR, B, htr, hC⟩

/-! ### The first piece from a boundary root -/

/-- The physical points of a piece in the translated chart `z ↦ z − x` are those in the chart `z ↦ z`, moved by
`x`. -/
theorem tipSet_recenter_subset (x : ℝ) (W : ℝ≥0 → ℝ) (s : ℝ≥0∞) :
    (Chart.id.recenter x).tipSet W s ⊆ (fun z => z + (x : ℂ)) '' (Chart.id.recenter 0).tipSet W s := by
  rintro z ⟨t, ht, hlim⟩
  refine ⟨z - x, ⟨t, ht, ?_⟩, sub_add_cancel z (x : ℂ)⟩
  have h1 := hlim.sub_const (x : ℂ)
  simp only [recenter_id_inv, Complex.ofReal_zero, add_zero, add_sub_cancel_right] at h1 ⊢
  exact h1

/-- **The completed range of the counterflow retargeted at `v` (BR4a), moved by `v`, lies in the original completed
range**: its physical tips are original tips (BR4a's tip identification through `recenter v` and the inversion), and
its terminal point `0` is `v`, an original tip. -/
theorem add_mem_counterflowCompletedRange_of_tipAt {v : ℝ} {Wv W' : ℝ≥0 → ℝ} {ℓ : ℝ≥0 → ℝ≥0}
    (hid : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.recenter v).trans infinitySourceChart).tipAt Wv r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z)
    (hv : (v : ℂ) ∈ infinitySourceChart.tipSet W' ⊤) {z : ℂ} (hz : z ∈ counterflowCompletedRange Wv) :
    z + v ∈ counterflowCompletedRange W' := by
  rcases hz with ⟨r, -, hr⟩ | hz0
  · refine Or.inl ⟨ℓ r, le_top, (hid r (z + v)).1 ?_⟩
    exact hr.add_const (v : ℂ)
  · rw [mem_singleton_iff] at hz0
    subst hz0
    rw [zero_add]
    exact Or.inl hv


/-- **GW2a's first piece from a boundary root** (Lemma GW2, p. 621: "BR4a gives the full conditional pair targeted
at `v`. […] GB6 places each available prefix in this conditional counterflow range […] The same conclusion holds at a
finite endpoint by continuity"). For a staged history whose root `v ≠ 0` is almost surely a physical point of the
counterflow and whose first instruction is a flow at angle `θ ∈ [−π/2, π/2]`: almost surely the first piece, run for
its own time `t`, lies in the completed counterflow range. Conditional on Corollary BR4a (`BR4a.BR4aStatement`),
GB6's conditional-law half, Lemma GW0's forward implication and Theorem 1.3. -/
theorem ae_tipSet_first_subset_of_root (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hW' : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E) (hv0 : spec.1 ≠ 0)
    (hvR : ∀ᵐ ω ∂P, (spec.1 : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {t : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, (Chart.id.recenter spec.1).tipSet
        (fun r : ℝ≥0 => (E 0 ω).1 (min (r : ℝ≥0∞) (min t (E 0 ω).2)).toNNReal) (min t (E 0 ω).2) ⊆
      counterflowCompletedRange (fun s => W' s ω) := by
  obtain ⟨hv, Wv, ζv, ℓ, htrv, hcfv, -, hae⟩ := hBR4a κ hκ hκ4 b jumps hb P h hh W' ζ' hW' hζ' spec.1 hv0 hvR
  have hveq : hv = fun ω => Exist.flowField spec.1 0 (h ω) :=
    funext fun ω => eq_flowField_of_isChartTransport (htrv ω)
  subst hveq
  have hbv := Exist.isPiecewiseConstant_comp_add hb spec.1
  have hhv := Supp9.IsGFFWithBoundaryData.recenter hb spec.1 hh
  have hfl := hS.isFlowLineDriver_first_root hκ hb hh hp
  have hζv : ∀ᵐ ω ∂P, ζv ω = ⊤ := hae.mono fun ω hω => hω.1
  have hcore := ae_tipSet_subset_of_pair hGB6 hGW0 hT13 hκ hκ4 hbv hhv hcfv hζv hθ hfl (hS.2.2.1 0) t
  filter_upwards [hcore, hae, hvR] with ω hω hidω hvω
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := tipSet_recenter_subset spec.1 _ _ hz
  exact add_mem_counterflowCompletedRange_of_tipAt hidω.2.2.2.2 hvω (hω hz₀)

end GW2aPiece

end Theorem14

end InteractingSLE
