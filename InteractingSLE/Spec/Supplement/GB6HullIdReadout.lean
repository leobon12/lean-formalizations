/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6HullIdWire

/-!
# GB6's read-back input: only on the record event

Packet PROVE-GB6-HULLID. PROVE-GB6-VERSION's remaining input `SourceC.GB6SourceReadoutStatement` asks for a causal
gauge read-back (`SourceC.AESeparationReadout`) of the coordinates `SourceC.sourceDriver`, `SourceC.sourceLife`. These
are `Exists.choose` witnesses of `SourceC.exists_relative_driver_of_flowlines`, constrained by
`SourceC.RelativeDriverCoordinates` only on the interior-tip event: off it, the chosen life may be any positive
measurable time (for instance one depending on randomness the record and the driver do not see), and then no readout of
(record, driver) can vanish exactly at it. So that input (and `ReadD.HasRegularSeparationVersion` for the same
coordinates) is not provable from what is exported about the coordinates.

This file asks for the read-back only where the coordinates are pinned down, on the record event `gb6TS s` (almost
surely the interior-tip event), and repairs the coordinates off it (zero driver, infinite life, constant gauge):

* `HasLiveReadout`: a measurable causal readout `G` whose read-back of the driver is, almost surely on the record event,
  continuous and positive before the life and tends to `0` at a finite life;
* `continuous_glue`, `fbGauge`: the gauge assembled from such a read-back, and a fallback gauge;
* **`exists_readoutCoord_of_liveReadout`**: `RelativeDriverCoordinates` + `HasLiveReadout` ⇒ coordinates with an
  `AESeparationReadout`;
* `GB6ReadoutCoordStatement` (the read-back with existentially chosen coordinates), implied by
  `SourceC.GB6SourceReadoutStatement` and by `GB6LiveReadoutStatement` (`HasLiveReadout` of the source coordinates);
* **`gb6HullDetStatement_of_liveReadout_stopKernel`**, `gb6HullDetStatement_of_readoutCoord_stopKernel`.

Nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.GB6.HullId

open RelDrv RelDrv.Version Exist.StagedLaw SourceC

/-! ### Gluing a gauge at the terminal time -/

/-- A function continuous before `L` and tending to `0` at a finite `L`, extended by `0` from `L` on, is continuous. -/
theorem continuous_glue {f : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hc : ContinuousOn f {t | (t : ℝ≥0∞) < L})
    (hlim : ∀ T : ℝ≥0, (T : ℝ≥0∞) = L → Tendsto f (𝓝[<] T) (𝓝 0)) :
    Continuous fun t : ℝ≥0 => if (t : ℝ≥0∞) < L then f t else 0 := by
  classical
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases lt_trichotomy (t : ℝ≥0∞) L with htL | htL | htL
  · have hev : (fun u : ℝ≥0 => if (u : ℝ≥0∞) < L then f u else 0) =ᶠ[𝓝 t] f := by
      filter_upwards [hopen.mem_nhds htL] with u hu
      exact ite_eq_left hu
    exact ((hc.continuousAt (hopen.mem_nhds htL)).congr hev.symm)
  · have hev : ∀ u : ℝ≥0, t ≤ u → (if (u : ℝ≥0∞) < L then f u else 0) = 0 := fun u hu =>
      ite_eq_right (not_lt.2 (htL ▸ ENNReal.coe_le_coe.2 hu))
    refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · have hl : Tendsto (fun u : ℝ≥0 => if (u : ℝ≥0∞) < L then f u else 0) (𝓝[<] t) (𝓝 0) := by
        refine (hlim t htL).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (ite_eq_left (htL ▸ ENNReal.coe_lt_coe.2 hu)).symm
      rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hev t le_rfl]
      exact hl
    · rw [ContinuousWithinAt, hev t le_rfl]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hev u hu).symm
  · have hLt : L ≠ ⊤ := ne_top_of_lt htL
    have hopen' : IsOpen {u : ℝ≥0 | L < (u : ℝ≥0∞)} := isOpen_lt continuous_const ENNReal.continuous_coe
    have hev : (fun u : ℝ≥0 => if (u : ℝ≥0∞) < L then f u else 0) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [hopen'.mem_nhds htL] with u hu
      exact ite_eq_right (not_lt.2 hu.le)
    exact continuousAt_const.congr hev.symm

/-- **The fallback gauge** of a life `L`: `1` if `L = ∞`, else `min 1 (max 0 (L − t))`. -/
def fbGauge (L : ℝ≥0∞) (t : ℝ≥0) : ℝ := if L = ⊤ then 1 else min 1 (max 0 (L.toReal - t))

theorem continuous_fbGauge (L : ℝ≥0∞) : Continuous (fbGauge L) := by
  unfold fbGauge
  split_ifs
  · exact continuous_const
  · exact continuous_const.min (continuous_const.max (continuous_const.sub NNReal.continuous_coe))

theorem fbGauge_pos {L : ℝ≥0∞} {t : ℝ≥0} (h : (t : ℝ≥0∞) < L) : 0 < fbGauge L t := by
  unfold fbGauge
  split_ifs with hL
  · exact zero_lt_one
  · have ht : (t : ℝ) < L.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hL).2 h
      rwa [ENNReal.coe_toReal] at this
    exact lt_min zero_lt_one (lt_max_of_lt_right (sub_pos.2 ht))

theorem fbGauge_terminal {L : ℝ≥0∞} {t : ℝ≥0} (h : (t : ℝ≥0∞) = L) : fbGauge L t = 0 := by
  simp only [fbGauge, ← h, ENNReal.coe_toReal, sub_self, max_self]
  exact min_eq_right zero_le_one

theorem fbGauge_top (t : ℝ≥0) : fbGauge ⊤ t = 1 := ite_eq_left rfl

theorem measurable_fbGauge {Ω : Type*} [MeasurableSpace Ω] {L : Ω → ℝ≥0∞} (hL : Measurable L) (t : ℝ≥0) :
    Measurable fun ω => fbGauge (L ω) t := by
  unfold fbGauge
  exact Measurable.ite (hL (measurableSet_singleton ⊤)) measurable_const
    (measurable_const.min (measurable_const.max (hL.ennreal_toReal.sub measurable_const)))

/-! ### The read-back on the record event -/

/-- **A causal read-back on the record event**: a measurable causal readout `G` whose read-back of the driver `D` is,
almost surely on the record event `gb6TS s`, continuous and positive before the life `L` and tends to `0` at a finite
life. -/
def HasLiveReadout (s : ℝ≥0) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (rec : Ω → RecData)
    (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) : Prop :=
  ∃ G : GaugeReadout, (∀ t, Measurable (G t)) ∧ IsCausal G ∧
    ∀ᵐ ω ∂P, rec ω ∈ gb6TS s →
      ContinuousOn (fun t => G t (rec ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → 0 < G t (rec ω, fun u => D u ω)) ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) = L ω → Tendsto (fun t => G t (rec ω, fun u => D u ω)) (𝓝[<] T) (𝓝 0)

/-- **Coordinates with an almost-sure separation readout from a read-back on the record event.** Off the record event
the coordinates are replaced by the zero driver with infinite life and the readout by the constant `1`; on it the
gauge is the read-back, cut off at the life. -/
theorem exists_readoutCoord_of_liveReadout {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hC : RelativeDriverCoordinates s P W Wα ζα γ α D L) (hrecm : Measurable (gb6Rec s Wα ζα))
    (hgood : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → GB6RecGood s Wα ζα α ω)
    (hL : HasLiveReadout s P (gb6Rec s Wα ζα) D L) :
    ∃ (D' : ℝ≥0 → Ω → ℝ) (L' : Ω → ℝ≥0∞) (g : ℝ≥0 → Ω → ℝ) (G' : GaugeReadout),
      RelativeDriverCoordinates s P W Wα ζα γ α D' L' ∧ AESeparationReadout P (gb6Rec s Wα ζα) D' L' g G' := by
  classical
  obtain ⟨G, hGm, hGc, hreg⟩ := hL
  set rec := gb6Rec s Wα ζα with hrec
  set E₀ : Set Ω := rec ⁻¹' gb6TS s with hE₀def
  have hE₀ : MeasurableSet E₀ := hrecm (measurableSet_gb6TS s)
  obtain ⟨Gd, hGdm, hGdae, hGd⟩ := exists_measurable_good hreg
  set E₁ : Set Ω := E₀ ∩ Gd with hE₁def
  have hE₁ : MeasurableSet E₁ := hE₀.inter hGdm
  set D' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E₀ then D t ω else 0 with hD'def
  set L' : Ω → ℝ≥0∞ := fun ω => if ω ∈ E₀ then L ω else ⊤ with hL'def
  set G' : GaugeReadout := fun t p => if p.1 ∈ gb6TS s then G t p else 1 with hG'def
  set g : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E₁ then (if (t : ℝ≥0∞) < L ω then G t (rec ω, fun u => D u ω) else 0)
    else fbGauge (L' ω) t with hgdef
  have hDE : ∀ ω ∈ E₀, (fun u => D' u ω) = fun u => D u ω := fun ω hω => funext fun u => ite_eq_left hω
  have hLE : ∀ ω ∈ E₀, L' ω = L ω := fun ω hω => ite_eq_left hω
  have hL'm : Measurable L' := Measurable.ite hE₀ hC.life_measurable measurable_const
  have hD'm : ∀ t, Measurable (D' t) := fun t => Measurable.ite hE₀ (hC.measurable t) measurable_const
  have hRm : ∀ t, Measurable fun ω => G t (rec ω, fun u => D u ω) := fun t =>
    (hGm t).comp (hrecm.prodMk (measurable_pi_iff.2 fun u => hC.measurable u))
  have hL'pos : ∀ ω, 0 < L' ω := fun ω => by
    by_cases hω : ω ∈ E₀
    · rw [hLE ω hω]; exact hC.life_pos ω
    · simp only [hL'def, hω, ↓reduceIte, ENNReal.zero_lt_top]
  refine ⟨D', L', g, G', ⟨hD'm, hL'm, hL'pos, fun ω => ?_, fun ω => ?_, ?_, ?_⟩, ⟨fun t => ?_, fun ω => ?_,
    fun ω => ?_, fun ω t ht => ?_, fun ω t ht => ?_, fun t => ?_, ?_, ?_⟩⟩
  -- RelativeDriverCoordinates
  · by_cases hω : ω ∈ E₀
    · rw [hLE ω hω, hDE ω hω]; exact hC.continuous ω
    · simp only [hD'def, hω, ↓reduceIte]; exact continuousOn_const
  · by_cases hω : ω ∈ E₀
    · simp only [hD'def, hω, ↓reduceIte]; exact hC.zero ω
    · simp only [hD'def, hω, ↓reduceIte]
  · intro t A hA
    exact (measurableSet_lt measurable_const hL'm).inter (hD'm t hA)
  · filter_upwards [hC.relative, hgood] with ω hrel hg hs hαs
    have hω : ω ∈ E₀ := (mem_gb6TS_iff hg).1 ⟨hs, hαs⟩
    have hD : (fun r : ℝ => D' r.toNNReal ω) = fun r : ℝ => D r.toNNReal ω := funext fun r => ite_eq_left hω
    rw [hLE ω hω, hD]
    exact hrel hs hαs
  -- AESeparationReadout
  · exact Measurable.ite hE₁ (Measurable.ite (measurableSet_lt measurable_const hC.life_measurable) (hRm t)
      measurable_const) (measurable_fbGauge hL'm t)
  · by_cases hω : ω ∈ E₁
    · simp only [hgdef, hω, ↓reduceIte]
      have h := hGd ω hω.2 hω.1
      exact continuous_glue h.1 h.2.2
    · simp only [hgdef, hω, ↓reduceIte]
      exact continuous_fbGauge _
  · by_cases hω : ω ∈ E₁
    · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < L ω := by rw [ENNReal.coe_zero]; exact hC.life_pos ω
      simp only [hgdef, hω, h0, ↓reduceIte]
      exact (hGd ω hω.2 hω.1).2.1 0 h0
    · simp only [hgdef, hω, ↓reduceIte]
      exact fbGauge_pos (by rw [ENNReal.coe_zero]; exact hL'pos ω)
  · by_cases hω : ω ∈ E₁
    · have ht' : (t : ℝ≥0∞) < L ω := by rwa [hLE ω hω.1] at ht
      simp only [hgdef, hω, ht', ↓reduceIte]
      exact (hGd ω hω.2 hω.1).2.1 t ht'
    · simp only [hgdef, hω, ↓reduceIte]
      exact fbGauge_pos ht
  · by_cases hω : ω ∈ E₁
    · have ht' : ¬ (t : ℝ≥0∞) < L ω := by rw [← hLE ω hω.1, ht]; exact lt_irrefl _
      simp only [hgdef, hω, ht', ↓reduceIte]
    · simp only [hgdef, hω, ↓reduceIte]
      exact fbGauge_terminal ht
  · exact Measurable.ite (measurableSet_preimage measurable_fst (measurableSet_gb6TS s)) (hGm t) measurable_const
  · intro t r w w' hw
    simp only [hG'def]
    split_ifs
    · exact hGc t r w w' hw
    · rfl
  · filter_upwards [hGdae] with ω hωG
    by_cases hω : ω ∈ E₀
    · have hω₁ : ω ∈ E₁ := ⟨hω, hωG⟩
      have hr : rec ω ∈ gb6TS s := hω
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < L ω := by rw [ENNReal.coe_zero]; exact hC.life_pos ω
      refine ⟨?_, fun t ht => ?_⟩
      · simp only [hG'def, hgdef, hr, hω₁, h0, ↓reduceIte]
        exact hGc 0 _ _ _ fun u hu => by
          rw [nonpos_iff_eq_zero.1 hu, hC.zero ω]
      · have ht' : (t : ℝ≥0∞) < L ω := by rwa [hLE ω hω] at ht
        simp only [hG'def, hgdef, hr, hω₁, ht', ↓reduceIte]
        rw [hDE ω hω]
    · have hr : rec ω ∉ gb6TS s := hω
      have hω₁ : ω ∉ E₁ := fun h => hω h.1
      have hL' : L' ω = ⊤ := ite_eq_right hω
      refine ⟨?_, fun t _ => ?_⟩
      · simp only [hG'def, hgdef, hr, hω₁, ↓reduceIte, hL', fbGauge_top]
      · simp only [hG'def, hgdef, hr, hω₁, ↓reduceIte, hL', fbGauge_top]

/-! ### The corrected read-back inputs and the wiring -/

/-- **The read-back input with existentially chosen coordinates** (the corrected form of
`SourceC.GB6SourceReadoutStatement`): for positive prefixes, some relative-driver coordinates carry an almost-sure
causal separation readout. -/
def GB6ReadoutCoordStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ s : ℝ≥0, 0 < s →
      ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) (g : ℝ≥0 → Ω → ℝ) (G : GaugeReadout),
        RelativeDriverCoordinates s P W Wα ζα γ α D L ∧ AESeparationReadout P (gb6Rec s Wα ζα) D L g G

/-- **The read-back on the record event for the source coordinates** (the provable form of
`SourceC.GB6SourceReadoutStatement`: only the record event, where `RelativeDriverCoordinates` pins the coordinates
down, is constrained). -/
def GB6LiveReadoutStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
      (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
        Tendsto (fun t => ‖γ ω t‖) atTop atTop)
      (hflow : IsFlowLineDriver κ b J θ P h Wα ζα)
      (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
      (s : ℝ≥0) (hs : 0 < s),
      HasLiveReadout s P (gb6Rec s Wα ζα)
        (sourceDriver hcf hflow (hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩) hα s hs)
        (sourceLife hcf hflow (hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩) hα s hs)

/-- The old input implies the corrected one (take the source coordinates). -/
theorem gb6ReadoutCoordStatement_of_sourceReadout (hread : GB6SourceReadoutStatement.{u}) :
    GB6ReadoutCoordStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hchart hcf hγ hflow hα s hs
  have hγ' : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) := hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩
  obtain ⟨g, G, hg⟩ := hread κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    hb hG hb' hchart hcf hγ hflow hα s hs
  exact ⟨_, _, g, G, sourceCoordinates_spec hcf hflow hγ' hα s hs, hg⟩

/-- **The read-back on the record event implies the corrected read-back input.** -/
theorem gb6ReadoutCoordStatement_of_liveReadout (hread : GB6LiveReadoutStatement.{u}) :
    GB6ReadoutCoordStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hchart hcf hγ hflow hα s hs
  have hγ' : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) := hγ.mono fun _ hω => ⟨hω.1, hω.2.1⟩
  exact exists_readoutCoord_of_liveReadout (sourceCoordinates_spec hcf hflow hγ' hα s hs)
    (measurable_recOf_cfE hflow s).2 (ae_gb6RecGood hflow hα s)
    (hread κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hchart hcf hγ hflow hα s hs)

/-- **R-form versions from the corrected read-back input.** -/
theorem gb6RelVersionRStatement_of_readoutCoord (hread : GB6ReadoutCoordStatement.{u}) :
    GB6RelVersionRStatement.{u} := by
  intro κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    hb hG hb' hchart hcf hγ hflow hα s
  by_cases hs : s = 0
  · subst s
    exact exists_versionsR_at_zero (hα.mono fun _ hω => hω.1)
  · have hsp : 0 < s := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ s) (Ne.symm hs)
    obtain ⟨D, L, g, G, hC, hg⟩ := hread κ θ hκ hκ4 hθl hθr Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
      hb hG hb' hchart hcf hγ hflow hα s hsp
    exact exists_versionsR_of_ae_readout hC hg

/-- **GB6's hull identity from the corrected read-back input and the plain stopped kernel.** -/
theorem gb6HullDetStatement_of_readoutCoord_stopKernel (hread : GB6ReadoutCoordStatement.{u})
    (hK : GB6RelStopKernelStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_relDrvDet
    (gb6RelDrvDetStatement_of_versionR_stopKernel (gb6RelVersionRStatement_of_readoutCoord hread) hK)

/-- **GB6's hull identity from the read-back on the record event and the plain stopped kernel.** -/
theorem gb6HullDetStatement_of_liveReadout_stopKernel (hread : GB6LiveReadoutStatement.{u})
    (hK : GB6RelStopKernelStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_readoutCoord_stopKernel (gb6ReadoutCoordStatement_of_liveReadout hread) hK

end InteractingSLE.Supp8.GB6.HullId
