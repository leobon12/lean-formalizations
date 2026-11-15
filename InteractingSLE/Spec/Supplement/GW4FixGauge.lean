/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopAnnounce
import InteractingSLE.Spec.Supplement.GB6GaugeEMinimum

/-!
# A self-read gauge for a relative driver: the running maximum

Packet PROVE-T14-GW4FIX. GB6's announced versions (`Q3Stop.isGB6RelVersionA_coord`) stop at the gauge stops of a
continuous gauge read back causally from (record, relative path). For a relative driver `D` with a life `L` at which
it blows up (`sup_{[0, L)} |D| = ∞` when `L` is finite), the path itself supplies such a gauge: the running maximum
`(1 + max_{[0,t]} |D|)⁻¹`, positive and continuous before `L`, tending to `0` at a finite `L`. This file builds it
for any record (generic; used for GW4 with a constant record):

* `maxIntegrand`, **`maxRead`**: the readout `(1 + max_{[0,t]} |w|)⁻¹` computed from rational fractions of `t`
  (measurable, causal); along a path continuous on `[0, t]` it is the compact minimum `squareMin` (GB6's
  `rationalInf_eq_squareMin`);
* `continuousOn_maxRead`, `tendsto_maxRead_zero`: continuity before the life and the terminal limit under blow-up;
* **`exists_aeSeparationReadout_maxRead`**: coordinates `(D, L)` with almost-sure blow-up at a finite life have an
  `AESeparationReadout` with the readout `maxRead`;
* the generic (any record) forms of GB6's coordinate-version facts: `ae_readout_coordDriver`,
  `ae_coordStop_eq_hitRule`, `ae_coordStop_le_iff`, **`ae_annRules_coord_rec`** (the announcing rules announce the
  coordinate stop; the proof of `Q3Stop.ae_annRules_coord` with the record left general).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
  Supp8.GB6.GaugeE Supp8.GB6.ReadD Supp8.Q3Stop

/-! ### The running-maximum readout -/

/-- The integrand of the running-maximum gauge at time `t`: `p ↦ (1 + |w(t p₁)|)⁻¹` on the unit square. -/
def maxIntegrand (w : ℝ≥0 → ℝ) (t : ℝ≥0) (p : UnitSquare) : ℝ := (1 + |w (t * (p.1 : ℝ≥0))|)⁻¹

theorem maxIntegrand_pos (w : ℝ≥0 → ℝ) (t : ℝ≥0) (p : UnitSquare) : 0 < maxIntegrand w t p :=
  inv_pos.2 (add_pos_of_pos_of_nonneg one_pos (abs_nonneg _))

theorem mul_unit_le (t : ℝ≥0) (q : UnitSegment) : t * (q : ℝ≥0) ≤ t :=
  mul_le_of_le_one_right zero_le q.2.2

/-- **The running-maximum readout** `(1 + max_{[0,t]} |w|)⁻¹`, read at the rational fractions of `t`. -/
def maxRead : GaugeReadout := fun t p =>
  (⨅ q : RationalUnit × RationalUnit,
    ENNReal.ofReal (maxIntegrand p.2 t (Prod.map fractionCast fractionCast q))).toReal

theorem measurable_maxRead (t : ℝ≥0) : Measurable (maxRead t) := by
  refine Measurable.ennreal_toReal (Measurable.iInf fun q => ENNReal.measurable_ofReal.comp ?_)
  exact (measurable_const.add ((measurable_pi_apply _).comp measurable_snd).abs).inv

theorem isCausal_maxRead : IsCausal maxRead := by
  intro t r w w' hw
  simp only [maxRead, maxIntegrand]
  congr 1
  refine iInf_congr fun q => ?_
  rw [hw _ (mul_unit_le t _)]

theorem continuous_maxIntegrand {w : ℝ≥0 → ℝ} {t : ℝ≥0} (hw : ContinuousOn w (Iic t)) :
    Continuous (maxIntegrand w t) := by
  have hc : Continuous fun p : UnitSquare => w (t * (p.1 : ℝ≥0)) :=
    hw.comp_continuous (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      fun p => mul_unit_le t p.1
  exact (continuous_const.add hc.abs).inv₀ fun p => (add_pos_of_pos_of_nonneg one_pos (abs_nonneg _)).ne'

/-- Along a path continuous on `[0, t]` the readout is the compact minimum. -/
theorem maxRead_eq_squareMin (r : RecData) {w : ℝ≥0 → ℝ} {t : ℝ≥0} (hw : ContinuousOn w (Iic t)) :
    maxRead t (r, w) = squareMin (maxIntegrand w t) := by
  have hc := continuous_maxIntegrand hw
  change (⨅ q : RationalUnit × RationalUnit,
    ENNReal.ofReal (maxIntegrand w t (Prod.map fractionCast fractionCast q))).toReal = _
  rw [rationalInf_eq_squareMin hc, ENNReal.toReal_ofReal
    (squareMin_nonneg hc fun p => (maxIntegrand_pos w t p).le)]

theorem maxRead_zero_path (r : RecData) (t : ℝ≥0) : maxRead t (r, fun _ => 0) = 1 := by
  have : Nonempty (RationalUnit × RationalUnit) := ⟨(⟨0, zero_le⟩, ⟨0, zero_le⟩)⟩
  simp only [maxRead, maxIntegrand, abs_zero, add_zero, inv_one, ENNReal.ofReal_one, iInf_const,
    ENNReal.toReal_one]

theorem continuousOn_Iic_of_lt {w : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hw : ContinuousOn w {u | (u : ℝ≥0∞) < L}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < L) : ContinuousOn w (Iic t) :=
  hw.mono fun _ hu => (ENNReal.coe_le_coe.2 hu).trans_lt ht

theorem maxRead_pos (r : RecData) {w : ℝ≥0 → ℝ} {t : ℝ≥0} (hw : ContinuousOn w (Iic t)) :
    0 < maxRead t (r, w) := by
  rw [maxRead_eq_squareMin r hw]
  exact squareMin_pos (continuous_maxIntegrand hw) (maxIntegrand_pos w t)

/-- **Continuity before the life.** -/
theorem continuousOn_maxRead (r : RecData) {w : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < L}) :
    ContinuousOn (fun t => maxRead t (r, w)) {t | (t : ℝ≥0∞) < L} := by
  intro t₀ ht₀
  obtain ⟨t₁, ht₀₁, ht₁L⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
  have ht₀₁' : t₀ < t₁ := ENNReal.coe_lt_coe.1 ht₀₁
  have hfz : Continuous (LP.freezeAt t₁ w) := LP.continuous_freezeAt (continuousOn_Iic_of_lt hw ht₁L)
  have hF : Continuous fun y : ℝ≥0 => squareMin (maxIntegrand (LP.freezeAt t₁ w) y) := by
    refine continuous_squareMin ?_
    have hc : Continuous fun x : ℝ≥0 × UnitSquare => LP.freezeAt t₁ w (x.1 * (x.2.1 : ℝ≥0)) :=
      hfz.comp (continuous_fst.mul (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
    exact (continuous_const.add hc.abs).inv₀ fun x =>
      (add_pos_of_pos_of_nonneg one_pos (abs_nonneg _)).ne'
  have hev : (fun t => maxRead t (r, w)) =ᶠ[𝓝 t₀] fun y => squareMin (maxIntegrand (LP.freezeAt t₁ w) y) := by
    filter_upwards [(isOpen_gt' t₁).mem_nhds ht₀₁'] with y hy
    have hyL : (y : ℝ≥0∞) < L := (ENNReal.coe_lt_coe.2 hy).trans ht₁L
    rw [maxRead_eq_squareMin r (continuousOn_Iic_of_lt hw hyL)]
    congr 1
    funext p
    simp only [maxIntegrand, LP.freezeAt, min_eq_left ((mul_unit_le y p.1).trans (le_of_lt hy))]
  exact (hF.continuousAt.congr hev.symm).continuousWithinAt

/-- **The terminal limit under blow-up**: if `|w|` is unbounded before a finite life `T`, the readout tends to `0`
at `T` from the left. -/
theorem tendsto_maxRead_zero (r : RecData) {w : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < (T : ℝ≥0∞)})
    (hblow : ∀ M : ℝ, ∃ s : ℝ≥0, s < T ∧ M < |w s|) :
    Tendsto (fun t => maxRead t (r, w)) (𝓝[<] T) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hsT, hs⟩ := hblow ε⁻¹
  filter_upwards [Ioo_mem_nhdsLT hsT] with t ht
  have htT : (t : ℝ≥0∞) < T := ENNReal.coe_lt_coe.2 ht.2
  have hwt := continuousOn_Iic_of_lt hw htT
  have hpos := maxRead_pos r hwt
  have ht0 : (t : ℝ≥0) ≠ 0 := (lt_of_le_of_lt zero_le ht.1).ne'
  set p : UnitSquare := (⟨s / t, zero_le, div_le_one_of_le₀ ht.1.le zero_le⟩, ⟨0, le_rfl, zero_le_one⟩) with hp
  obtain ⟨p₀, hmin, hle⟩ := exists_squareMin (continuous_maxIntegrand hwt)
  have hub : maxRead t (r, w) ≤ (1 + |w s|)⁻¹ := by
    rw [maxRead_eq_squareMin r hwt, hmin]
    refine (hle p).trans_eq ?_
    simp only [maxIntegrand, hp, mul_div_cancel₀ s ht0]
  have hlt : (1 + |w s|)⁻¹ < ε := by
    rw [inv_lt_comm₀ (add_pos_of_pos_of_nonneg one_pos (abs_nonneg _)) hε]
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  exact hub.trans_lt hlt

/-! ### The readout of coordinates that blow up at a finite life -/

section Readout

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The glued running-maximum gauge of coordinates `(D, L)`: the readout before `L`, `0` from `L` on. -/
def maxGauge (rec : Ω → RecData) (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < L ω then maxRead t (rec ω, fun u => D u ω) else 0

/-- **Coordinates that blow up at a finite life have a running-maximum separation readout.** For a measurable driver
`D`, continuous and `0` at `0` before a measurable positive life `L`, with `|D|` almost surely unbounded before a
finite `L`: on a measurable co-null set the gauge is the glued running maximum (`maxGauge`), off it GB6's fallback
gauge; the readout is `maxRead`. -/
theorem exists_aeSeparationReadout_maxRead {rec : Ω → RecData} (hrec : Measurable rec) {D : ℝ≥0 → Ω → ℝ}
    {L : Ω → ℝ≥0∞} (hDm : ∀ t, Measurable (D t)) (hLm : Measurable L) (hL0 : ∀ ω, 0 < L ω)
    (hDc : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω}) (hD0 : ∀ ω, D 0 ω = 0)
    (hblow : ∀ᵐ ω ∂P, L ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < L ω ∧ M < |D s ω|) :
    ∃ g : ℝ≥0 → Ω → ℝ, AESeparationReadout P rec D L g maxRead := by
  classical
  obtain ⟨Gd, hGdm, hGdae, hGd⟩ := exists_measurable_good hblow
  have h0L : ∀ ω, ((0 : ℝ≥0) : ℝ≥0∞) < L ω := fun ω => by rw [ENNReal.coe_zero]; exact hL0 ω
  refine ⟨fun t ω => if ω ∈ Gd then maxGauge rec D L t ω else fbGauge (L ω) t,
    ⟨fun t => ?_, fun ω => ?_, fun ω => ?_, fun ω t ht => ?_, fun ω t ht => ?_, measurable_maxRead,
      isCausal_maxRead, ?_⟩⟩
  · exact Measurable.ite hGdm (Measurable.ite (measurableSet_lt measurable_const hLm)
      ((measurable_maxRead t).comp (hrec.prodMk (measurable_pi_iff.2 hDm))) measurable_const)
      (measurable_fbGauge hLm t)
  · by_cases hω : ω ∈ Gd
    · simp only [hω, ↓reduceIte]
      change Continuous fun t : ℝ≥0 => if (t : ℝ≥0∞) < L ω then maxRead t (rec ω, fun u => D u ω) else 0
      refine continuous_glue (continuousOn_maxRead (rec ω) (hDc ω)) fun T hT => ?_
      have hc : ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < (T : ℝ≥0∞)} := by rw [hT]; exact hDc ω
      refine tendsto_maxRead_zero (rec ω) hc fun M => ?_
      obtain ⟨s, hs, hM⟩ := hGd ω hω (hT ▸ ENNReal.coe_ne_top) M
      exact ⟨s, ENNReal.coe_lt_coe.1 (hT ▸ hs), hM⟩
    · simp only [hω, ↓reduceIte]
      exact continuous_fbGauge _
  · by_cases hω : ω ∈ Gd
    · simp only [hω, ↓reduceIte, maxGauge, h0L ω]
      exact maxRead_pos (rec ω) (continuousOn_Iic_of_lt (hDc ω) (h0L ω))
    · simp only [hω, ↓reduceIte]
      exact fbGauge_pos (h0L ω)
  · by_cases hω : ω ∈ Gd
    · simp only [hω, ↓reduceIte, maxGauge, ht]
      exact maxRead_pos (rec ω) (continuousOn_Iic_of_lt (hDc ω) ht)
    · simp only [hω, ↓reduceIte]
      exact fbGauge_pos ht
  · by_cases hω : ω ∈ Gd
    · have ht' : ¬ (t : ℝ≥0∞) < L ω := by rw [ht]; exact lt_irrefl _
      simp only [hω, ↓reduceIte, maxGauge, ht']
    · simp only [hω, ↓reduceIte]
      exact fbGauge_terminal ht
  · filter_upwards [hGdae] with ω hω
    refine ⟨?_, fun t ht => ?_⟩
    · simp only [hω, ↓reduceIte, maxGauge, h0L ω]
      exact isCausal_maxRead 0 (rec ω) _ _ fun u hu => by
        rw [nonpos_iff_eq_zero.1 hu, hD0 ω]
    · simp only [hω, ↓reduceIte, maxGauge, ht]

end Readout

/-! ### The coordinate versions of a separation readout, for any record -/

section Coord

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData} {D : ℝ≥0 → Ω → ℝ}
  {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}

theorem coordStop_lt_life (hread : AESeparationReadout P rec D L g G) (m : ℕ) (ω : Ω) :
    (coordStop (g := g) m ω : ℝ≥0∞) < L ω :=
  localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m

theorem measurable_coordStop_of_readout (hread : AESeparationReadout P rec D L g G) (m : ℕ) :
    Measurable (coordStop (g := g) m) :=
  measurable_gaugeStop hread.measurable hread.continuous
    (((hread.measurable 0).div_const 2).min (measurable_const : Measurable fun _ : Ω => 1 / ((m : ℝ) + 1))) (m + 1)

/-- On the read-back event, the readout of the frozen driver is the gauge through the stop. -/
theorem ae_readout_coordDriver (hread : AESeparationReadout P rec D L g G) (m : ℕ) :
    ∀ᵐ ω ∂P, recLevel G m (rec ω) = gaugeLevel (g 0 ω) m ∧
      ∀ u ≤ gaugeStop (g · ω) (recLevel G m (rec ω)) (m + 1),
        G u (rec ω, fun u => coordDriver (D := D) (g := g) m u ω) = g u ω := by
  filter_upwards [hread.readout] with ω hω
  have hεω : recLevel G m (rec ω) = gaugeLevel (g 0 ω) m := by
    change gaugeLevel (G 0 (rec ω, fun _ => 0)) m = _
    rw [hω.1]
  refine ⟨hεω, fun u hu => ?_⟩
  rw [hεω] at hu
  have hu' : u ≤ coordStop (g := g) m ω := hu
  calc
    _ = G u (rec ω, fun u => D u ω) := hread.causal u _ _ _ fun v hv' => freeze_eq (hv'.trans hu')
    _ = g u ω := hω.2 u ((ENNReal.coe_le_coe.2 hu').trans_lt (coordStop_lt_life hread m ω))

/-- **The coordinate stop is the prefix-test path rule of the frozen driver**, almost surely. -/
theorem ae_coordStop_eq_hitRule (hread : AESeparationReadout P rec D L g G) (m : ℕ) :
    ∀ᵐ ω ∂P, (coordStop (g := g) m ω : ℝ≥0∞) =
      hitRule G (recLevel G m) (m + 1) (rec ω, fun u => coordDriver (D := D) (g := g) m u ω) := by
  filter_upwards [ae_readout_coordDriver hread m] with ω hω
  rw [hitRule_eq_gaugeStop (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
    (show recLevel G m (rec ω) < g 0 ω by rw [hω.1]; exact gaugeLevel_lt (hread.zero_pos ω) m) hω.2, hω.1]
  rfl

/-- **The coordinate stop is a stopping time of the path**: almost surely `{V ≤ t}` is the prefix test at `t`. -/
theorem ae_coordStop_le_iff (hread : AESeparationReadout P rec D L g G) (m : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ((coordStop (g := g) m ω : ℝ≥0∞) ≤ t ↔
      (rec ω, fun u => coordDriver (D := D) (g := g) m u ω) ∈ prefixHitSet G (recLevel G m) (m + 1) t) := by
  filter_upwards [ae_readout_coordDriver hread m] with ω hω
  have htst := mem_prefixHitSet_iff (hread.continuous ω) (by positivity : (0 : ℝ≥0) < m + 1)
    (show recLevel G m (rec ω) < g 0 ω by rw [hω.1]; exact gaugeLevel_lt (hread.zero_pos ω) m) hω.2 t
  rw [hω.1] at htst
  exact ENNReal.coe_le_coe.trans htst.symm

/-- **The announcing rules announce the coordinate stop** (`Q3Stop.ae_annRules_coord` for any record): on the
read-back event they are the gauge stops of the levels `ε_k` and caps `c_k`, strictly below the coordinate stop, with
supremum the coordinate stop. -/
theorem ae_annRules_coord_rec (hread : AESeparationReadout P rec D L g G) (m : ℕ) :
    ∀ᵐ ω ∂P, (∀ n, annRules G m n (rec ω, fun u => coordDriver (D := D) (g := g) m u ω) <
        (coordStop (g := g) m ω : ℝ≥0∞)) ∧
      ⨆ n, annRules G m n (rec ω, fun u => coordDriver (D := D) (g := g) m u ω) =
        (coordStop (g := g) m ω : ℝ≥0∞) := by
  have hv : ∀ ω, (coordStop (g := g) m ω : ℝ≥0∞) < L ω :=
    fun ω => localStop_lt (hread.continuous ω) (hread.zero_pos ω) (hread.terminal ω) m
  filter_upwards [hread.readout] with ω hω
  set r := rec ω with hr
  set w : ℝ≥0 → ℝ := fun u => coordDriver (D := D) (g := g) m u ω with hw
  set gω : ℝ≥0 → ℝ := fun t => g t ω with hgω
  have hgc : Continuous gω := hread.continuous ω
  set ε := gaugeLevel (gω 0) m with hεdef
  have hε0 : ε < gω 0 := gaugeLevel_lt (hread.zero_pos ω) m
  set T := coordStop (g := g) m ω with hTdef
  have hrec : recLevel G m r = ε := by
    change gaugeLevel (G 0 (r, fun _ => 0)) m = _
    rw [hω.1]
  have hG0 : G 0 (r, fun _ => 0) = gω 0 := hω.1
  have hrd : ∀ u ≤ T, G u (r, w) = gω u := fun u hu => by
    calc
      _ = G u (r, fun u => D u ω) := hread.causal u _ _ _ fun v hv' => freeze_eq (hv'.trans hu)
      _ = gω u := hω.2 u ((ENNReal.coe_le_coe.2 hu).trans_lt (hv ω))
  set εs : ℕ → ℝ := fun k => ε + (gω 0 - ε) / ((k : ℝ) + 2) with hεs
  have hlev : ∀ k, annLevel G m k r = εs k := fun k => by
    simp only [annLevel, hrec, hG0, hεs]
  have hεs_gt : ∀ k, ε < εs k := fun k =>
    lt_add_of_pos_right _ (div_pos (sub_pos.2 hε0) (by positivity))
  have hεs_lt : ∀ k, εs k < gω 0 := fun k => by
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have h2 : (gω 0 - ε) / ((k : ℝ) + 2) < gω 0 - ε := div_lt_self (sub_pos.2 hε0) hk
    simp only [hεs]
    linarith
  have hεs_anti : Antitone εs := fun k l hkl => by
    have : (gω 0 - ε) / ((l : ℝ) + 2) ≤ (gω 0 - ε) / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left (sub_pos.2 hε0).le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hkl 2)
    simp only [hεs]
    linarith
  have hstop : ∀ k, annRule G m k (r, w) = (gaugeStop gω (εs k) (annCap m k) : ℝ≥0∞) := fun k => by
    have hle : gaugeStop gω (εs k) (annCap m k) ≤ T :=
      gaugeStop_mono hgc (hεs_gt k).le (annCap_lt m k).le
    have hh : hitRule G (annLevel G m k) (annCap m k) (r, w) = gaugeStop gω (annLevel G m k r) (annCap m k) :=
      hitRule_eq_gaugeStop hgc (annCap_pos m k) (by rw [hlev]; exact hεs_lt k) fun u hu =>
        hrd u (by rw [hlev] at hu; exact hu.trans hle)
    rw [annRule, hh, hlev, min_eq_left (ENNReal.coe_le_coe.2 (gaugeStop_le _ _ _))]
  have hmono : Monotone fun k => gaugeStop gω (εs k) (annCap m k) := fun k l hkl =>
    gaugeStop_mono hgc (hεs_anti hkl) (annCap_mono m hkl)
  have hrules : ∀ n, annRules G m n (r, w) = (gaugeStop gω (εs n) (annCap m n) : ℝ≥0∞) := fun n => by
    refine le_antisymm (Finset.sup_le fun k hk => ?_) ?_
    · rw [hstop]
      exact ENNReal.coe_le_coe.2 (hmono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
    · rw [← hstop]
      exact Finset.le_sup (f := fun k => annRule G m k (r, w)) (Finset.self_mem_range_succ n)
  have hlt : ∀ n, gaugeStop gω (εs n) (annCap m n) < T := fun n =>
    gaugeStop_lt_of_lt hgc (hεs_gt n) (hεs_lt n) (annCap_lt m n)
  refine ⟨fun n => by rw [hrules]; exact ENNReal.coe_lt_coe.2 (hlt n),
    le_antisymm (iSup_le fun n => by rw [hrules]; exact ENNReal.coe_le_coe.2 (hlt n).le) ?_⟩
  refine le_of_forall_lt fun a ha => ?_
  have ha' : a ≠ ⊤ := (ha.trans ENNReal.coe_lt_top).ne
  have htT : a.toNNReal < T := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal ha']
    exact ha
  obtain ⟨n, hn⟩ := exists_lt_gaugeStop hgc htT (εs := εs) (cs := annCap m)
    (fun δ hδ => by
      obtain ⟨N, hN⟩ := exists_div_add_two_lt (sub_pos.2 hε0).le hδ
      exact ⟨N, fun n hn => by simp only [hεs]; linarith [hN n hn]⟩)
    (fun t' ht' => exists_lt_annCap m ht')
  rw [← ENNReal.coe_toNNReal ha']
  exact (ENNReal.coe_lt_coe.2 hn).trans_le (by
    rw [← hrules]
    exact le_iSup (fun n => annRules G m n (r, w)) n)

end Coord

end InteractingSLE.Theorem14.GW4Fix
