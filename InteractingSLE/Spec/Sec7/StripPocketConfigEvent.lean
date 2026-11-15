/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketConfig
import InteractingSLE.Spec.Ito.Measurability

/-!
# Theorem 1.3's pocket word: the strip pocket's configuration on a positive-probability walls event

Packet PROVE-STRIPSYS30. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L431–L489,
pp. 410–412): "Use a fixed conformal compactification in which the strip is a Jordan domain and all three complete
paths are continuous. […] almost surely there is a rational `r > 0` such that `E_r` (RS13.4) occurs. […] Fix one
deterministic rational `r` with `ℙ(E_r) > 0`. […] We proved `E_r ⊆ F_r`, so `ℙ(F_r) > 0`. […] Only `F_r` is used to
select initial incoming configurations".

`StripSys.exists_rat_contactEvent` (PROVE-STRIPSYS) is the source's choice of the rational change time on paths in a
metric space. Here the compactification is the Cayley disc: the walls are read as `cayley ∘ R` (terminal point `1`),
the counterflow (a curve from `0` in the chart `m(z) = −1/z`) as `−cayley ∘ η` (so that `cfPt` of its points are the
counterflow's points, and its first visits are `StripPocketConfig.discVisit`). From almost sure pathwise inputs on the
walls and the counterflow (simple proper walls, Lemma 5.7's reverse visit order, the counterflow's non-return to its
seed, the late points of `β` off `α` (RS13.3), the common prefix of `β` and `β^{(r)}`), this file produces a rational
`r > 0` and an event `G` of positive probability, measurable from the walls up to null sets, on which the change pocket
has the configuration `IsChangeConfigInc` and its selected right arc ends after the first change.

## Main results

* `firstVisit_discCf`: the first visits of the disc counterflow are `discVisit`;
* **`isSelectionConfig_disc`**: the hypotheses (RS13.2)–(RS13.4) of `StripSys.IsSelectionConfig` in the disc;
* **`isContactPoint_of_disc`**: the disc event `F_r` gives the half-plane one;
* `exists_measurableSet_nullSets_ae`: an almost sure property holds on a conull null-set-measurable event;
* **`exists_stripPocketEvent`**: the rational change time and the configuration event.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function MeasureTheory Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.StripPocketConfig

open WangWu Lemma71I PocketCoord PocketJordan PocketMeas

/-! ### Walls and counterflow in the Cayley disc -/

section Disc

variable {η : ℝ → ℂ} {R : ℝ≥0 → ℂ}

/-- The counterflow in the Cayley disc: `−cayley (η t)`, whose counterflow-chart point is `η t`. -/
def discCf (η : ℝ → ℂ) (t : ℝ≥0) : ℂ := -cayley (η t)

/-- A wall in the Cayley disc. -/
def discWall (R : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ := cayley (R t)

theorem measurable_cayley : Measurable cayley := by
  unfold QuantumZipper.CA.cayley
  fun_prop

theorem cayley_zero : cayley 0 = -1 := by
  simp [QuantumZipper.CA.cayley, Complex.I_ne_zero]

theorem eq_zero_of_cayley_eq_neg_one {z : ℂ} (hz : z ∈ Hbar) (h : cayley z = -1) : z = 0 := by
  rw [← QuantumZipper.CA.cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar hz), h]
  simp [QuantumZipper.CA.cayleyInv]

theorem discWall_eq_toDisc (R : ℝ≥0 → ℂ) (t : ℝ≥0) : discWall R t = toDisc (realPath R) (discTime t) :=
  (toDisc_realPath_discTime R t).symm

theorem discCf_ne_neg_one (hηH : ∀ t : ℝ, 0 ≤ t → η t ∈ Hbar) (t : ℝ≥0) : discCf η t ≠ -1 := fun h =>
  cayley_ne_one_of_Hbar (hηH t t.2) (neg_inj.1 h)

theorem discCf_eq_iff (hηH : ∀ t : ℝ, 0 ≤ t → η t ∈ Hbar) {w : ℂ} (hw : w ≠ -1) (t : ℝ≥0) :
    discCf η t = w ↔ nnPath η t = cfPt w := by
  constructor
  · rintro rfl
    exact (cfPt_neg_cayley (hηH t t.2)).symm
  · intro h
    rw [discCf, show η t = nnPath η t from rfl, h, neg_cayley_cfPt hw]

/-- **The first visits of the disc counterflow are `discVisit`.** -/
theorem firstVisit_discCf (hηH : ∀ t : ℝ, 0 ≤ t → η t ∈ Hbar) (w : ℂ) :
    Aux130.firstVisit (discCf η) w = discVisit η w := by
  by_cases hw : w = -1
  · rw [hw, discVisit_neg_one, Aux130.firstVisit_eq_top_iff]
    exact discCf_ne_neg_one hηH
  · rw [discVisit_of_ne hw]
    simp only [Aux130.firstVisit, discCf_eq_iff hηH hw]

theorem continuous_discCf (hηc : ContinuousOn η (Ici 0)) (hηH : ∀ t : ℝ, 0 ≤ t → η t ∈ Hbar) :
    Continuous (discCf η) :=
  continuous_iff_continuousAt.2 fun t => by
    show ContinuousAt ((fun z => -cayley z) ∘ nnPath η) t
    exact ContinuousAt.comp (g := fun z => -cayley z) (continuousAt_neg_cayley (hηH t t.2))
      (continuous_nnPath_of hηc).continuousAt

theorem continuous_discWall (hR : IsSimpleProper R) : Continuous (discWall R) := by
  have hHb : ∀ t, R t ∈ Hbar := fun t => by
    rcases eq_zero_or_pos t with ht | ht
    · rw [ht, hR.2.2.1]
      exact le_refl (0 : ℂ).im
    · exact le_of_lt (show (0 : ℝ) < (R t).im from hR.2.2.2.1 t ht)
  exact continuous_iff_continuousAt.2 fun t =>
    (QuantumZipper.CA.differentiableAt_cayley (add_I_ne_zero_of_mem_Hbar (hHb t))).continuousAt.comp
      hR.1.continuousAt

theorem discCf_zero (hη0 : η 0 = 0) : discCf η 0 = 1 := by
  simp [discCf, NNReal.coe_zero, hη0, cayley_zero]

/-- **The disc wall's points off the closure of its range** come from half-plane points off the wall. -/
theorem mem_range_of_cayley_mem_closure (hR : IsSimpleProper R) {z : ℂ} (hz : z ∈ Hbar)
    (hcl : cayley z ∈ closure (range (discWall R))) : z ∈ range R := by
  have hc : ContinuousAt cayleyInv (cayley z) := WangWu.continuousAt_cayleyInv (cayley_ne_one_of_Hbar hz)
  have h1 := mem_closure_image hc hcl
  rw [QuantumZipper.CA.cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar hz)] at h1
  have hsub : cayleyInv '' range (discWall R) ⊆ range R := by
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    have hHb : R t ∈ Hbar := by
      rcases eq_zero_or_pos t with ht | ht
      · rw [ht, hR.2.2.1]
        exact le_refl (0 : ℂ).im
      · exact le_of_lt (show (0 : ℝ) < (R t).im from hR.2.2.2.1 t ht)
    exact (QuantumZipper.CA.cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar hHb)).symm
  have h2 := closure_mono hsub h1
  rwa [(Lemma71Pin.IsSimpleProper.isClosed_range hR).closure_eq] at h2

end Disc

/-! ### The selection hypotheses (RS13.2)–(RS13.4) in the disc -/

section Selection

variable {η : ℝ → ℂ} {R β : ℝ≥0 → ℂ}

theorem mem_Hbar_of_isSimpleProper (hR : IsSimpleProper R) (t : ℝ≥0) : R t ∈ Hbar := by
  rcases eq_zero_or_pos t with ht | ht
  · rw [ht, hR.2.2.1]
    exact le_refl (0 : ℂ).im
  · exact le_of_lt (show (0 : ℝ) < (R t).im from hR.2.2.2.1 t ht)

theorem antitone_firstVisit_discWall (hR : IsSimpleProper R) (hηc : ContinuousOn η (Ici 0)) (hη0 : η 0 = 0)
    (hηH : ∀ t : ℝ, 0 ≤ t → η t ∈ Hbar) (hrev : IsWallReverseVisit R η) :
    Antitone fun t => Aux130.firstVisit (discCf η) (discWall R t) := by
  intro a b hab
  simp only [firstVisit_discCf hηH, discWall_eq_toDisc]
  refine antitoneOn_discVisit hR hηc hη0 hrev (discTime_mem_Icc a) (discTime_mem_Icc b) ?_
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact (discTime_lt_discTime a.coe_nonneg (NNReal.coe_lt_coe.2 h)).le

/-- **The hypotheses (RS13.2)–(RS13.4) of Aux. lemma 130's rational choice, in the Cayley disc**: for simple proper
walls `R = α` and `β = η_{π/2}`, visited in reverse order by a counterflow `η` from `0` with values in the closed
half-plane that does not return to its seed, and the late points of `β` off `R` ((RS13.3)), the disc paths satisfy
`StripSys.IsSelectionConfig` with terminal point `1`. -/
theorem isSelectionConfig_disc (hR : IsSimpleProper R) (hβ : IsSimpleProper β) (hηc : ContinuousOn η (Ici 0))
    (hη0 : η 0 = 0) (hηH : ∀ t : ℝ, 0 ≤ t → η t ∈ Hbar) (hrevβ : IsWallReverseVisit β η)
    (hvisβ : IsWallVisited β η) (hnohit : ∀ t : ℝ, 0 < t → η t ≠ 0)
    (hlate : ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β t ∉ range R) :
    StripSys.IsSelectionConfig (discCf η) (discWall R) (discWall β) 1 where
  continuous_γ := continuous_discCf hηc hηH
  continuous_α := continuous_discWall hR
  continuous_β := continuous_discWall hβ
  antitone_β := antitone_firstVisit_discWall hβ hηc hη0 hηH hrevβ
  firstVisit_lt_top := fun t ht => by
    rw [firstVisit_discCf hηH, discWall_eq_toDisc]
    have hs : discTime t ∈ Ioc (0 : ℝ) 1 := by
      refine ⟨?_, (discTime_mem_Icc t).2⟩
      have := discTime_lt_discTime le_rfl (show (0 : ℝ) < t from ht)
      simpa [discTime] using this
    have hc := hβ.isProperArc.isDiscCrosscut_toDisc
    rw [discVisit_of_ne (crosscut_ne_neg_one hc hs)]
    obtain ⟨u, hu⟩ := wall_visited hη0 hβ hvisβ hs
    exact firstVisit_lt_top_of_mem hu
  tendsto_β := by
    have h1 : Tendsto β atTop (cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 hβ.2.2.2.2
    exact QuantumZipper.CA.tendsto_cayley_cobounded.comp h1
  nonhit := fun t ht he => by
    have h1 : cayley (η t) = -1 := by
      have := congrArg Neg.neg he
      rwa [discCf, neg_neg] at this
    exact hnohit t ht (eq_zero_of_cayley_eq_neg_one (hηH t t.2) h1)
  late := fun N => by
    obtain ⟨t, hNt, ht⟩ := hlate N
    exact ⟨t, hNt, fun hcl => ht (mem_range_of_cayley_mem_closure hR (mem_Hbar_of_isSimpleProper hβ t) hcl)⟩
  firstVisit_pos := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h := Aux130.apply_of_firstVisit_eq (continuous_discCf hηc hηH) (t := 0) (by rw [h0]; rfl)
    rw [discCf_zero hη0] at h
    exact cayley_ne_one_of_Hbar (mem_Hbar_of_isSimpleProper hR 1) h.symm

/-- **The disc event `F_r` gives the half-plane one**: for a simple proper right wall and a left wall in the closed
half-plane, `StripSys.IsContactPoint` of the disc walls implies it for the half-plane walls. -/
theorem isContactPoint_of_disc {L : ℝ≥0 → ℂ} (hR : IsSimpleProper R) (hL : ∀ t, L t ∈ Hbar) {q : ℚ}
    (h : StripSys.IsContactPoint (discWall R) (discWall L) q) : StripSys.IsContactPoint R L q := by
  have hRcl : closure (range R) = range R := (Lemma71Pin.IsSimpleProper.isClosed_range hR).closure_eq
  refine ⟨fun hcl => h.1 ?_, fun s hrs hs => ?_⟩
  · rw [hRcl] at hcl
    obtain ⟨t, ht⟩ := hcl
    exact subset_closure ⟨t, by rw [discWall, discWall, ht]⟩
  · obtain ⟨a, ha, has⟩ := hs
    obtain ⟨u, hru, hus, hu⟩ := h.2 s hrs ⟨a, ha, by rw [discWall, discWall, has]⟩
    exact ⟨u, hru, hus, subset_closure (mem_range_of_cayley_mem_closure hR (hL u) hu)⟩

end Selection

/-! ### The configuration event -/

section Event

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- An almost sure property holds on a conull event of the null-set σ-algebra. -/
theorem exists_measurableSet_nullSets_ae {Q : Ω → Prop} (hQ : ∀ᵐ ω ∂P, Q ω) :
    ∃ G : Set Ω, MeasurableSet[Ito.nullSets P] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧ ∀ ω ∈ G, Q ω := by
  set N := toMeasurable P {ω | ¬ Q ω} with hNdef
  have hN : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hQ
  have hNm : MeasurableSet[Ito.nullSets P] N :=
    MeasurableSpace.measurableSet_generateFrom ⟨measurableSet_toMeasurable _ _, hN⟩
  refine ⟨Nᶜ, hNm.compl, measure_eq_zero_iff_ae_notMem.1 hN, fun ω hω => ?_⟩
  by_contra h
  exact hω (subset_toMeasurable P _ h)

/-- **Aux. lemma 130's rational change time and the strip pocket's configuration event** (pp. 410–412). Let `R = α`,
`β = η_{π/2}` and, for each rational `q > 0`, `Lr q = β^{(q)}` be random walls (`R` and every `Lr q` measurable at
fixed times for the walls' σ-algebra `𝓦`), and `η` a random counterflow from `0` in the chart `m(z) = −1/z`,
continuous on `[0, ∞)` with values in the closed half-plane. Assume, almost surely: the walls are simple proper
curves; `R` and `β` are entirely visited, and `R`, `β`, every `Lr q` visited in reverse order, by the counterflow
(Lemma 5.7); `Lr q` and `β` agree at the change time `q`; the counterflow does not return to its seed; `β` has points
off `R` at arbitrarily late times ((RS13.3)). Then there are a rational `q > 0` and an event `G`, measurable from the
walls up to null sets, of positive probability, on which the change pocket of `R` and `Lr q` at the change time `q`
has the configuration `IsChangeConfigInc`, its selected right arc ends after the first change (`discTime 1 <
rightHi`, (RS13.5)), and the walls' reverse visit facts hold. -/
theorem exists_stripPocketEvent [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω)) :
    ∃ q : ℚ, 0 < q ∧ ∃ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G ∧ 0 < P G ∧
      ∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q) ∧ IsWallReverseVisit (R ω) (η ω) ∧
        IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (R ω) (η ω) := by
  classical
  have hLall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → (IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q)) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · filter_upwards [hL q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  obtain ⟨G₀, hG₀m, hG₀ae, hG₀⟩ := exists_measurableSet_nullSets_ae (P := P) (hR.and (hβ.and hLall))
  have hG₀m' : MeasurableSet G₀ := Ito.nullSets_le P _ hG₀m
  have hcont : ∀ ω ∈ G₀, Continuous (discCf (η ω)) ∧ Continuous (discWall (R ω)) ∧
      Continuous (discWall (β ω)) := fun ω hω =>
    ⟨continuous_discCf (hηc ω) (hηH ω), continuous_discWall (hG₀ ω hω).1.1,
      continuous_discWall (hG₀ ω hω).2.1.1⟩
  have hmeas : ∀ q : ℚ, Measurable (fun ω => discCf (η ω) (StripSys.rt q)) ∧
      Measurable (fun ω => discWall (R ω) (StripSys.rt q)) ∧
      Measurable (fun ω => discWall (β ω) (StripSys.rt q)) := fun q =>
    ⟨(measurable_cayley.comp (hηm _ (StripSys.rt q).coe_nonneg)).neg,
      measurable_cayley.comp ((hRm _).mono h𝓦 le_rfl), measurable_cayley.comp (hβm _)⟩
  have hsel : ∀ᵐ ω ∂P, StripSys.IsSelectionConfig (discCf (η ω)) (discWall (R ω)) (discWall (β ω)) 1 := by
    filter_upwards [hR, hβ, hnohit, hlate] with ω hRω hβω hnω hlω
    exact isSelectionConfig_disc hRω.1 hβω.1 (hηc ω) (hη0 ω) (hηH ω) hβω.2.1 hβω.2.2 hnω hlω
  set βr : ℚ → Ω → ℝ≥0 → ℂ := fun r ω => if 0 < r then discWall (Lr r ω) else discWall (R ω) with hβr
  have hchange : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, Continuous (βr r ω) ∧
      βr r ω (StripSys.rt r) = discWall (β ω) (StripSys.rt r) ∧
      (Antitone fun t => Aux130.firstVisit (discCf (η ω)) (βr r ω t)) ∧
      Antitone fun t => Aux130.firstVisit (discCf (η ω)) (discWall (R ω) t) := by
    intro r hr
    filter_upwards [hR, hL r hr] with ω hRω hLω
    simp only [hβr, hr, ↓reduceIte]
    refine ⟨continuous_discWall hLω.1, ?_, antitone_firstVisit_discWall hLω.1 (hηc ω) (hη0 ω) (hηH ω) hLω.2.1,
      antitone_firstVisit_discWall hRω.1 (hηc ω) (hη0 ω) (hηH ω) hRω.2.1⟩
    show cayley (Lr r ω (StripSys.rt r)) = cayley (β ω (StripSys.rt r))
    rw [hLω.2.2]
  have hc' : ∀ ω ∈ G₀, Continuous (discWall (R ω)) ∧ ∀ r : ℚ, Continuous (βr r ω) := fun ω hω => by
    refine ⟨(hcont ω hω).2.1, fun r => ?_⟩
    by_cases hr : 0 < r
    · simp only [hβr, hr, ↓reduceIte]
      exact continuous_discWall ((hG₀ ω hω).2.2 r hr).1
    · simp only [hβr, hr, ↓reduceIte]
      exact (hcont ω hω).2.1
  have hm' : ∀ q : ℚ, Measurable[𝓦 ⊔ Ito.nullSets P] (fun ω => discWall (R ω) (StripSys.rt q)) ∧
      ∀ r : ℚ, Measurable[𝓦 ⊔ Ito.nullSets P] (fun ω => βr r ω (StripSys.rt q)) := fun q =>
    ⟨(measurable_cayley.comp (hRm _)).mono le_sup_left le_rfl, fun r => by
      by_cases hr : 0 < r
      · simp only [hβr, hr, ↓reduceIte]
        exact (measurable_cayley.comp (hLm r _)).mono le_sup_left le_rfl
      · simp only [hβr, hr, ↓reduceIte]
        exact (measurable_cayley.comp (hRm _)).mono le_sup_left le_rfl⟩
  obtain ⟨q, hq, hFm, hFpos⟩ := StripSys.exists_rat_contactEvent (P := P) hG₀m' hcont hmeas hG₀ae hsel hchange
    (𝓦 ⊔ Ito.nullSets P) (le_sup_right (a := 𝓦) _ hG₀m) hG₀ae hc' hm'
  refine ⟨q, hq, _, hFm, hFpos, fun ω hω => ?_⟩
  obtain ⟨hω₀, hcp⟩ := hω
  obtain ⟨hRω, -, hLall'⟩ := hG₀ ω hω₀
  have hLω := hLall' q hq
  have hcp' : StripSys.IsContactPoint (discWall (R ω)) (discWall (Lr q ω)) q := by
    have : βr q ω = discWall (Lr q ω) := by simp only [hβr, hq, ↓reduceIte]
    rw [← this]
    exact hcp
  have hcpH := isContactPoint_of_disc hRω.1 (mem_Hbar_of_isSimpleProper hLω.1) hcp'
  have hpos : 0 < StripSys.rt q := Real.toNNReal_pos.2 (Rat.cast_pos.2 hq)
  have hconf := isChangeConfigInc_of_reverseVisit hRω.1 hLω.1 (hηc ω) (hη0 ω) hRω.2.1 hLω.2.1 hRω.2.2 hpos
    fun hmem => hcpH.1 (subset_closure hmem)
  exact ⟨hconf, discTime_one_lt_rightHi_of_isContactPoint hconf hcpH, hRω.2.1, hLω.2.1, hRω.2.2⟩

/-- **`exists_stripPocketEvent` with further almost sure facts**: any family `Q q` of almost sure properties (for
instance the counterflow's remaining configuration facts at the change time `q`) also holds on the selected event,
after removing a null set. -/
theorem exists_stripPocketEvent_ae [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω))
    {Q : ℚ → Ω → Prop} (hQ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Q q ω) :
    ∃ q : ℚ, 0 < q ∧ ∃ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G ∧ 0 < P G ∧
      ∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q) ∧ IsWallReverseVisit (R ω) (η ω) ∧
        IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧ Q q ω := by
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ :=
    exists_stripPocketEvent (P := P) h𝓦 hRm hLm hβm hηm hηc hηH hη0 hR hβ hL hnohit hlate
  obtain ⟨G₁, hG₁m, hG₁ae, hG₁⟩ := exists_measurableSet_nullSets_ae (P := P) (hQ q hq)
  refine ⟨q, hq, G ∩ G₁, hGm.inter (le_sup_right (a := 𝓦) _ hG₁m), ?_, fun ω hω => ?_⟩
  · rwa [measure_inter_conull (ae_iff.1 hG₁ae)]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hG ω hω.1
    exact ⟨h1, h2, h3, h4, h5, hG₁ ω hω.2⟩

end Event

end InteractingSLE.Sec7.StripPocketConfig
