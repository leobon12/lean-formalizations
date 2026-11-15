/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeELive

/-!
# Contact and escape imply the terminal separation limit

At a finite relative lifetime, a physical contact limit or escape to infinity
forces the separation readout to tend to zero. The remaining source input
is stated as these physical alternatives, only on the record event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.GaugeE

open Exist.StagedLaw ReadD

theorem separationRead_nonneg (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) :
    0 ≤ separationRead s t (r, w) :=
  le_separationRead s t (r, w) le_rfl (fun _ => separationValue_nonneg _ _)

/-- The retained starting point makes the normalized contact test vanish
when the explored physical point escapes to infinity. -/
theorem tendsto_separationValue_escape {Y : Type*} {l : Filter Y} {z : Y → ℂ}
    (hz : Tendsto (fun y => ‖z y‖) l atTop) : Tendsto (fun y => separationValue (z y) 0) l (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left l 1 hz)
  have hm := (tendsto_const_nhds (x := (1 : ℝ))).min hi
  simpa only [separationValue, mul_zero, zero_add, norm_one, one_div, min_eq_right zero_le_one, Function.comp_def] using hm

/-- A finite physical contact limit gives the required terminal zero limit. -/
theorem tendsto_separationRead_contact (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (hs : 0 < s)
    {T : ℝ≥0} (hX : ContinuousOn (fun u => physicalTrace s u (r, w)) (Iio T))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) {z : ℂ} {v : ℝ≥0} (hv : v ≤ s)
    (hz : Tendsto (fun u => physicalTrace s u (r, w)) (𝓝[<] T) (𝓝 z))
    (hcontact : z * recordTrace v r + 1 = 0) :
    Tendsto (fun u => separationRead s u (r, w)) (𝓝[<] T) (𝓝 0) := by
  have hb := continuous_separationValue.tendsto (z, recordTrace v r) |>.comp (hz.prodMk_nhds tendsto_const_nhds)
  have hzero : separationValue z (recordTrace v r) = 0 := by simp only [separationValue, hcontact, norm_zero, zero_div, min_eq_right zero_le_one]
  rw [hzero] at hb
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  have hupper : ∀ᶠ u : ℝ≥0 in 𝓝[<] T,
      separationRead s u (r, w) ≤ separationValue (physicalTrace s u (r, w)) (recordTrace v r) := by
    filter_upwards [hu] with u hu
    exact separationRead_le_value s u r w hs (hX.mono fun q hq => lt_of_le_of_lt hq hu) hA hv
  exact squeeze_zero' (Eventually.of_forall fun u => separationRead_nonneg s u r w) hupper hb

/-- Escape of the reconstructed physical trace also gives the terminal
zero limit, through the retained seed. -/
theorem tendsto_separationRead_escape (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (hs : 0 < s)
    {T : ℝ≥0} (hX : ContinuousOn (fun u => physicalTrace s u (r, w)) (Iio T))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) (hA0 : recordTrace 0 r = 0)
    (hz : Tendsto (fun u => ‖physicalTrace s u (r, w)‖) (𝓝[<] T) atTop) :
    Tendsto (fun u => separationRead s u (r, w)) (𝓝[<] T) (𝓝 0) := by
  have hb := tendsto_separationValue_escape hz
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  have hupper : ∀ᶠ u : ℝ≥0 in 𝓝[<] T,
      separationRead s u (r, w) ≤ separationValue (physicalTrace s u (r, w)) 0 := by
    filter_upwards [hu] with u hu
    have h := separationRead_le_value s u r w hs (hX.mono fun q hq => lt_of_le_of_lt hq hu) hA (v := 0) zero_le
    rwa [hA0] at h
  exact squeeze_zero' (Eventually.of_forall fun u => separationRead_nonneg s u r w) hupper hb

/-- The remaining physical endpoint alternatives. This is a named input,
not an asserted source theorem: a finite contact limit, or physical escape. -/
def PhysicalTerminal (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (T : ℝ≥0) : Prop :=
  (∃ (z : ℂ) (v : ℝ≥0), v ≤ s ∧ z * recordTrace v r + 1 = 0 ∧
    Tendsto (fun u => physicalTrace s u (r, w)) (𝓝[<] T) (𝓝 z)) ∨
  Tendsto (fun u => ‖physicalTrace s u (r, w)‖) (𝓝[<] T) atTop

/-- The physical endpoint alternatives are required only on the record
event where the source coordinates are geometrically identified. -/
def HasPhysicalTerminalLimits {Ω : Type*} [MeasurableSpace Ω] (s : ℝ≥0) (P : Measure Ω)
    (rec : Ω → RecData) (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, rec ω ∈ gb6TS s → ∀ T : ℝ≥0, (T : ℝ≥0∞) = L ω →
    PhysicalTerminal s (rec ω) (fun u => D u ω) T

/-- All other clauses of the corrected live readout follow from the source
hypotheses. Only the physical terminal alternatives are used as a named input. -/
theorem hasLiveReadout_of_physicalTerminal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hterm : HasPhysicalTerminalLimits s P (gb6Rec s Wα ζα) D L) :
    HullId.HasLiveReadout s P (gb6Rec s Wα ζα) D L := by
  refine ⟨separationRead s, measurable_separationRead s, isCausal_separationRead s, ?_⟩
  filter_upwards [ae_separationRead_regular hκ hκ4 hF hα hW s hs hC, hterm] with ω hreg ht hrec
  obtain ⟨hc, hp, hA0, hA, hX⟩ := hreg hrec
  refine ⟨hc, hp, ?_⟩
  intro T hT
  have hXI : ContinuousOn (fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω))) (Iio T) :=
    hX.mono (fun u hu => by rw [← hT]; exact ENNReal.coe_lt_coe.2 hu)
  rcases ht hrec T hT with ⟨z, v, hv, hc, hz⟩ | hz
  · exact tendsto_separationRead_contact s _ _ hs hXI hA hv hz hc
  · exact tendsto_separationRead_escape s _ _ hs hXI hA hA0 hz

end InteractingSLE.Supp8.GB6.GaugeE
