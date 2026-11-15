/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimePath
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Sec2.TwoSeedLawBridge

/-!
# The strip martingale: localization along the strip life

Packet PROVE-ZHAN-A2. For an integrated chordal evolution whose outermost left mark `v = V^{L, last}` is the strip
end (ruling R36), the strip observables of `StripTimeObs.lean` are localized at the times `σ_n`: the first exit of the
chordal state from the level-`n` box (`W − v ≥ 1/(n+1)`, every lower left mark at distance `≥ 1/(n+1)` right of `v`,
`‖state‖ ≤ n`), the exit of `|B|` from `(−n, n)`, and `n` (`stripLoc`). Off a full-measure event `G` of good paths
the localizing time is `0`.

Good paths (`IsGoodStrip`) satisfy the frozen pathwise conditions, have a continuous Brownian path started at `0`,
and an **unbounded strip clock on the strip life** (`HasUnboundedStripClock`, clause (1) of `HasStripEndpoint`). The
last condition makes every `σ_n` lie in the strip life (`isStripLife_stripLoc`): at the strip-life end either the end
mark meets the driver or the chordal lifetime ends, and both are excluded while the box is kept by the unbounded
clock (`W − v ≥ 1/(n+1)` on `[0, s]` gives `t(s) ≤ n (n+1)²`).

## Main results

* `HasUnboundedStripClock`, `IsGoodStrip`, `exists_good_strip`;
* `stripBox`, `stripKc` (the box with the initial point), `isCompact_stripKc`, `stripKc_subset`;
* `stripLoc` and `isStoppingTime_stripLoc` (stopping times of the usual augmentation);
* the pathwise facts on good paths: `isStripLife_stripLoc`, `mem_stripKc_of_le_stripLoc`,
  `stripLoc_mono`, `exists_le_stripLoc` (exhaustion of the strip life).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-- **The strip clock is unbounded on the strip life** (clause (1) of `Strip.HasStripEndpoint`). -/
def HasUnboundedStripClock (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∀ T : ℝ, ∃ s : ℝ≥0, Strip.IsStripLife w v ζ s ∧
    T ≤ Strip.stripClock (Strip.extPath w) (Strip.extPath v) s

/-- The level-`n` state functional: nonnegative iff `W − v ≥ δ`, `‖state‖ ≤ R` and every lower left mark is at
distance `≥ δ` right of the end mark. -/
def levelFun (δ R : ℝ) (st : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ)) : ℝ :=
  min (min (st.1 - st.2.1 (Fin.last nL) - δ) (R - ‖st‖))
    (-∑ i : Fin nL, max 0 (δ - (st.2.1 i.castSucc - st.2.1 (Fin.last nL))))

theorem continuous_levelFun (δ R : ℝ) : Continuous (levelFun (nL := nL) (nR := nR) δ R) := by
  unfold levelFun
  fun_prop

theorem levelFun_nonneg_iff {δ R : ℝ} {st : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ)} :
    0 ≤ levelFun δ R st ↔ δ ≤ st.1 - st.2.1 (Fin.last nL) ∧ ‖st‖ ≤ R ∧
      ∀ i : Fin nL, δ ≤ st.2.1 i.castSucc - st.2.1 (Fin.last nL) := by
  unfold levelFun
  simp only [le_min_iff, Left.nonneg_neg_iff]
  have hsum : ∑ i : Fin nL, max 0 (δ - (st.2.1 i.castSucc - st.2.1 (Fin.last nL))) ≤ 0 ↔
      ∀ i : Fin nL, δ ≤ st.2.1 i.castSucc - st.2.1 (Fin.last nL) := by
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin nL)),
        0 ≤ max 0 (δ - (st.2.1 i.castSucc - st.2.1 (Fin.last nL))) :=
      fun _ _ => le_max_left _ _
    constructor
    · intro h i
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
        (le_antisymm h (Finset.sum_nonneg hnn)) i (Finset.mem_univ i)
      have := le_max_right 0 (δ - (st.2.1 i.castSucc - st.2.1 (Fin.last nL)))
      linarith
    · intro h
      refine le_of_eq ((Finset.sum_eq_zero_iff_of_nonneg hnn).2 fun i _ => ?_)
      exact max_eq_left (by linarith [h i])
  rw [hsum]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-! ### Good paths -/

section Good

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Good paths**: the frozen pathwise conditions, a continuous Brownian path started at `0`, and an unbounded
strip clock on the strip life. -/
def IsGoodStrip (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
    Continuous (B · ω) ∧ B 0 ω = 0 ∧ HasUnboundedStripClock (W · ω) (VL (Fin.last nL) · ω) (ζ ω)

/-- A measurable full-measure event of good paths. -/
theorem exists_good_strip {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hclock : ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL (Fin.last nL) · ω) (ζ ω)) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω := by
  have hae : ∀ᵐ ω ∂P, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, hclock] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨(toMeasurable P {ω | ¬ IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

end Good

/-! ### The compact box -/

section Box

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)

/-- The level-`n` box of strip coordinates. -/
def stripBox (n : ℕ) : Set (SCoord nL nR × ℝ) :=
  {p | ‖p.1.1‖ ≤ n ∧ ‖p.1.2.1‖ ≤ n ∧ 0 ≤ p.1.2.2 ∧ p.1.2.2 ≤ n * ((n : ℝ) + 1) ^ 2 ∧ |p.2| ≤ n ∧
    1 / ((n : ℝ) + 1) ≤ gapArg κ xL xR ρL ρR p ∧
    (∀ i : Fin nL, 1 / ((n : ℝ) + 1) ≤ p.1.1 i.castSucc - p.1.1 (Fin.last nL)) ∧
    ∀ j, 1 / ((n : ℝ) + 1) ≤ p.1.2.1 j - p.1.1 (Fin.last nL)}

/-- The initial point `((x^L, x^R, 0), 0)`. -/
def stripInit : SCoord nL nR × ℝ := ((xL, xR, 0), 0)

/-- The box together with the initial point. -/
def stripKc (n : ℕ) : Set (SCoord nL nR × ℝ) := insert (stripInit xL xR) (stripBox κ xL xR ρL ρR n)

theorem isClosed_stripBox (n : ℕ) : IsClosed (stripBox κ xL xR ρL ρR n) := by
  have hg : Continuous (gapArg κ xL xR ρL ρR) := (contDiff_gapArg κ xL xR ρL ρR (n := 0)).continuous
  have e : stripBox κ xL xR ρL ρR n =
      {p : SCoord nL nR × ℝ | ‖p.1.1‖ ≤ n} ∩ {p | ‖p.1.2.1‖ ≤ n} ∩ {p | 0 ≤ p.1.2.2} ∩
        {p | p.1.2.2 ≤ n * ((n : ℝ) + 1) ^ 2} ∩ {p | |p.2| ≤ n} ∩
        {p | 1 / ((n : ℝ) + 1) ≤ gapArg κ xL xR ρL ρR p} ∩
        (⋂ i : Fin nL, {p | 1 / ((n : ℝ) + 1) ≤ p.1.1 i.castSucc - p.1.1 (Fin.last nL)}) ∩
        ⋂ j, {p | 1 / ((n : ℝ) + 1) ≤ p.1.2.1 j - p.1.1 (Fin.last nL)} := by
    ext p; simp [stripBox, and_assoc]
  rw [e]
  refine ((((((((isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)).inter (isClosed_le continuous_const (by fun_prop))).inter
    (isClosed_le (by fun_prop) continuous_const)).inter
    (isClosed_le (by fun_prop) continuous_const)).inter (isClosed_le continuous_const hg)).inter
    (isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop))).inter
    (isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)))

theorem stripBox_subset_closedBall (n : ℕ) :
    stripBox κ xL xR ρL ρR n ⊆ Metric.closedBall 0 (n * ((n : ℝ) + 1) ^ 2 + n) := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (0 : ℝ) ≤ n * ((n : ℝ) + 1) ^ 2 := by positivity
  rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs]
  refine max_le (max_le (by linarith) (max_le (by linarith) ?_)) (by linarith)
  rw [abs_of_nonneg h3]; linarith

theorem isCompact_stripKc (n : ℕ) : IsCompact (stripKc κ xL xR ρL ρR n) :=
  ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_stripBox κ xL xR ρL ρR n)
    (stripBox_subset_closedBall κ xL xR ρL ρR n)).insert _

theorem stripBox_subset_region (n : ℕ) : stripBox κ xL xR ρL ρR n ⊆ stripMartRegion κ xL xR ρL ρR := by
  intro p hp
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact ⟨hδ.trans_le hp.2.2.2.2.2.1, fun i => hδ.trans_le (hp.2.2.2.2.2.2.1 i),
    fun j => hδ.trans_le (hp.2.2.2.2.2.2.2 j)⟩

theorem stripKc_subset_region (h0 : stripInit xL xR ∈ stripMartRegion κ xL xR ρL ρR) (n : ℕ) :
    stripKc κ xL xR ρL ρR n ⊆ stripMartRegion κ xL xR ρL ρR :=
  insert_subset h0 (stripBox_subset_region κ xL xR ρL ρR n)

theorem gapArg_stripInit : gapArg κ xL xR ρL ρR (stripInit xL xR) = -xL (Fin.last nL) := by
  simp [gapArg, stripInit, driftLin]

/-- The initial point lies in the region when the end mark starts left of `0` and left of every other mark. -/
theorem stripInit_mem_region (h0 : xL (Fin.last nL) < 0) (hL : ∀ i : Fin nL, xL (Fin.last nL) < xL i.castSucc)
    (hR : ∀ j, xL (Fin.last nL) < xR j) : stripInit xL xR ∈ stripMartRegion κ xL xR ρL ρR :=
  ⟨by rw [gapArg_stripInit]; linarith, fun i => sub_pos.2 (hL i), fun j => sub_pos.2 (hR j)⟩

end Box

/-! ### The localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The exit time of the state from the level-`n` box (before `ζ`), on the good event `G` (`0` off it). -/
def hitLevel (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then
    Coupling.hitBelow (fun s => levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0
  else 0

/-- **The localizing time** `σ_n = n ∧ (exit of the state from the level-`n` box) ∧ (exit of `|B|` from `(−n, n)`)`,
`0` off the good event. -/
def stripLoc (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0))
    (fun ω => min (hitLevel G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

theorem stripLoc_le (n : ℕ) (ω : Ω) : stripLoc G W VL VR B ζ n ω ≤ n :=
  Sec2.TwoSeed.capTime_le _ _ ω

theorem stripLoc_of_not_mem {ω : Ω} (hω : ω ∉ G) (n : ℕ) : stripLoc G W VL VR B ζ n ω = 0 := by
  have h := Sec2.TwoSeed.capTime_le_right (fun _ => (n : ℝ≥0))
    (fun ω => min (hitLevel G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω
  simp only [hitLevel, hω, ↓reduceIte] at h
  have h0 : (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ 0 := h.trans (min_le_left _ _)
  exact le_antisymm (by exact_mod_cast h0) bot_le

theorem stripLoc_le_hitLevel (n : ℕ) (ω : Ω) :
    (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ hitLevel G W VL VR ζ n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_left _ _)

theorem stripLoc_le_exitTime (n : ℕ) (ω : Ω) :
    (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

section StoppingTime

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω)

include hGm hGc in
theorem measurableSet_good_usual (t : ℝ≥0) : MeasurableSet[usualAugmentation 𝓕 P t] G := by
  have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
  rwa [compl_compl] at this

include hgood in
theorem continuous_brownG_strip (ω : Ω) : Continuous (Sec2.TwoSeed.brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using (hgood ω hω).2.1
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- The Brownian motion modified off `G` is a Brownian motion of the usual augmentation. -/
theorem isFilteredBrownianReal_brownG_strip :
    IsFilteredBrownianReal (usualAugmentation 𝓕 P) (Sec2.TwoSeed.brownG G B) P := by
  have := (Ito.isFilteredBrownianReal_modify (Ito.isFilteredBrownianReal_usualAugmentation hE.1) hGm hGc
    fun ω hω => (hgood ω hω).2.1).1
  rwa [Ito.nullAugmented_usualAugmentation] at this

open scoped Classical in
include hE hGm hGc hgood in
theorem isStoppingTime_hitLevel (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) (hitLevel G W VL VR ζ n) := by
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hcont : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω)
      {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun ω hω => by
    have hF := (hgood ω hω).1.isForcePath
    exact hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR))
  have hτ := Coupling.isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
    (continuous_levelFun (nL := nL) (nR := nR) (1 / ((n : ℝ) + 1)) n) 0
  intro t
  have e : {ω | hitLevel G W VL VR ζ n ω ≤ t} = Gᶜ ∪ {ω | (if ω ∈ G then Coupling.hitBelow
      (fun s => levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else ⊤) ≤ t} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [hitLevel, hω]
    · simp only [hitLevel, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff,
        not_false_eq_true, true_or, iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [e]
  exact ((usualAugmentation 𝓕 P).mono (zero_le (a := t)) _ hG0).compl.union (hτ t)

include hE hGm hGc hgood in
/-- **The localizing times are stopping times of the usual augmentation.** -/
theorem isStoppingTime_stripLoc (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) :=
  Sec2.TwoSeed.isStoppingTime_capTime (isStoppingTime_const _ _)
    ((isStoppingTime_hitLevel hE hGm hGc hgood n).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_strip hE hGm hGc hgood).2.1 (continuous_brownG_strip hgood) n))

end StoppingTime

/-! ### Pathwise facts on good paths -/

section GoodFacts

variable {ω : Ω} {n : ℕ} (hω : IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω) (hωG : ω ∈ G)
include hω hωG

omit hω in
/-- Before `σ_n` (and `ζ`) the state is in the level-`n` box. -/
theorem levelFun_nonneg_of_lt_stripLoc {r : ℝ≥0} (hr : r < stripLoc G W VL VR B ζ n ω)
    (hrζ : (r : ℝ≥0∞) < ζ ω) :
    0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω) := by
  by_contra hneg
  push Not at hneg
  have h1 := Coupling.hitBelow_le (f := fun s => levelFun (1 / ((n : ℝ) + 1)) n
    (Coupling.stateAt W VL VR s ω)) hrζ hneg
  have h2 := stripLoc_le_hitLevel (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n ω
  simp only [hitLevel, hωG, ↓reduceIte] at h2
  have : (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ r := h2.trans h1
  exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 hr)

omit hω hωG in
/-- In the box, `W − v ≥ 1/(n+1)`, so the strip clock rate is at most `(n+1)²`. -/
theorem clockRate_le_of_levelFun {r : ℝ≥0}
    (h : 0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω)) :
    ((W r ω - VL (Fin.last nL) r ω) ^ 2)⁻¹ ≤ ((n : ℝ) + 1) ^ 2 := by
  have hg := (levelFun_nonneg_iff.1 h).1
  simp only [Coupling.stateAt] at hg
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsq : (1 / ((n : ℝ) + 1)) ^ 2 ≤ (W r ω - VL (Fin.last nL) r ω) ^ 2 :=
    pow_le_pow_left₀ hδ.le hg 2
  calc ((W r ω - VL (Fin.last nL) r ω) ^ 2)⁻¹ ≤ ((1 / ((n : ℝ) + 1)) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hsq
    _ = ((n : ℝ) + 1) ^ 2 := by rw [one_div, inv_pow, inv_inv]

/-- **`σ_n` lies in the strip life** (the unbounded strip clock excludes an end of the strip life inside the box). -/
theorem isStripLife_stripLoc :
    Strip.IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) (stripLoc G W VL VR B ζ n ω) := by
  set σ := stripLoc G W VL VR B ζ n ω with hσ
  obtain ⟨s₀, hs₀, hT⟩ := hω.2.2.2 ((n : ℝ) * ((n : ℝ) + 1) ^ 2 + 1)
  by_cases h : σ ≤ s₀
  · exact hs₀.mono h
  push Not at h
  exfalso
  have hF := hω.1.isForcePath
  have hint := intervalIntegrable_clockRate hF hs₀
  have hle : Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) s₀ ≤
      (s₀ : ℝ) * ((n : ℝ) + 1) ^ 2 := by
    have hbound := intervalIntegral.integral_mono_on s₀.coe_nonneg hint
      (intervalIntegrable_const (c := ((n : ℝ) + 1) ^ 2)) fun u hu => by
        have hu1 : u.toNNReal ≤ s₀ := Sec2.toNNReal_le_of_mem_Icc hu
        exact clockRate_le_of_levelFun (levelFun_nonneg_of_lt_stripLoc hωG (hu1.trans_lt h)
          (Sec2.toNNReal_lt_of_mem_Icc hs₀.1 hu))
    simpa [Strip.stripClock, Strip.extPath, intervalIntegral.integral_const, mul_comm] using hbound
  have hσn : (σ : ℝ) ≤ n := by exact_mod_cast stripLoc_le n ω
  have hs₀σ : (s₀ : ℝ) < σ := by exact_mod_cast h
  have : (s₀ : ℝ) * ((n : ℝ) + 1) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right (hs₀σ.le.trans hσn) (by positivity)
  linarith

/-- On `[0, σ_n]` the state is in the box, if `σ_n > 0`. -/
theorem levelFun_nonneg_of_le_stripLoc (hσ0 : 0 < stripLoc G W VL VR B ζ n ω) {r : ℝ≥0}
    (hr : r ≤ stripLoc G W VL VR B ζ n ω) :
    0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω) := by
  set σ := stripLoc G W VL VR B ζ n ω with hσ
  have hlife := isStripLife_stripLoc hω hωG (n := n)
  rcases hr.lt_or_eq with hlt | heq
  · exact levelFun_nonneg_of_lt_stripLoc hωG hlt (lt_of_le_of_lt (by exact_mod_cast hlt.le) hlife.1)
  · subst heq
    have hF := hω.1.isForcePath
    have hcont : ContinuousOn (fun s => levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR s ω))
        {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
      (continuous_levelFun _ _).comp_continuousOn (hF.continuousOn_w.prodMk
        ((continuousOn_pi.2 hF.continuousOn_vL).prodMk (continuousOn_pi.2 hF.continuousOn_vR)))
    have hat := hcont.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds hlife.1)
    have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact levelFun_nonneg_of_lt_stripLoc hωG hr'
      (lt_of_le_of_lt (by exact_mod_cast (le_of_lt hr')) hlife.1)

/-- The strip clock up to `σ_n` is at most `n (n+1)²`. -/
theorem stripClock_le_of_le_stripLoc {r : ℝ≥0} (hr : r ≤ stripLoc G W VL VR B ζ n ω) :
    Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) r ≤
      (n : ℝ) * ((n : ℝ) + 1) ^ 2 := by
  have hlife := (isStripLife_stripLoc hω hωG (n := n)).mono hr
  have hF := hω.1.isForcePath
  have hint := intervalIntegrable_clockRate hF hlife
  rcases (zero_le (a := stripLoc G W VL VR B ζ n ω)).eq_or_lt with h0 | h0
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hr) bot_le
    subst hr0
    simp only [Strip.stripClock, NNReal.coe_zero, intervalIntegral.integral_same]
    positivity
  have hbound := intervalIntegral.integral_mono_on r.coe_nonneg hint
    (intervalIntegrable_const (c := ((n : ℝ) + 1) ^ 2)) fun u hu => by
      have hu1 : u.toNNReal ≤ r := Sec2.toNNReal_le_of_mem_Icc hu
      exact clockRate_le_of_levelFun (levelFun_nonneg_of_le_stripLoc hω hωG h0 (hu1.trans hr))
  have hle : Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) r ≤
      (r : ℝ) * ((n : ℝ) + 1) ^ 2 := by
    simpa [Strip.stripClock, Strip.extPath, intervalIntegral.integral_const, mul_comm] using hbound
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr.trans (stripLoc_le n ω)
  exact hle.trans (mul_le_mul_of_nonneg_right hrn (by positivity))

omit hω in
/-- Before `σ_n` the Brownian path is bounded by `n`. -/
theorem abs_B_le_of_le_stripLoc (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω) {r : ℝ≥0}
    (hr0 : 0 < r) (hr : r ≤ stripLoc G W VL VR B ζ n ω) : |B r ω| ≤ n := by
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_strip hgood) hr0
    ((WithTop.coe_le_coe.2 hr).trans (stripLoc_le_exitTime n ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

omit hωG in
theorem stripCoordAt_zero_eq :
    (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) 0, B 0 ω) =
      stripInit xL xR := by
  have hF := hω.1.isForcePath
  refine Prod.ext (Prod.ext (funext fun i => hF.vL_zero i) (Prod.ext (funext fun j => hF.vR_zero j) ?_))
    hω.2.2.1
  simp [stripCoordAt, Strip.stripClock, stripInit]

/-- **Up to `σ_n` the strip coordinates and the Brownian path stay in the compact set `stripKc`.** -/
theorem mem_stripKc_of_le_stripLoc (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω)
    {r : ℝ≥0} (hr : r ≤ stripLoc G W VL VR B ζ n ω) :
    (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r, B r ω) ∈
      stripKc κ xL xR ρL ρR n := by
  rcases (zero_le (a := r)).eq_or_lt with h0 | h0
  · subst h0
    rw [stripCoordAt_zero_eq hω]
    exact mem_insert _ _
  have hσ0 : 0 < stripLoc G W VL VR B ζ n ω := h0.trans_le hr
  have hlife := (isStripLife_stripLoc hω hωG (n := n)).mono hr
  have hlev := levelFun_nonneg_of_le_stripLoc hω hωG hσ0 hr
  obtain ⟨hg, hnorm, hgaps⟩ := levelFun_nonneg_iff.1 hlev
  simp only [Coupling.stateAt] at hg hnorm hgaps
  have hF := hω.1.isForcePath
  have hW := w_eq_driftLin hω.1 hlife.1
  refine mem_insert_of_mem _ ⟨?_, ?_, ?_, stripClock_le_of_le_stripLoc hω hωG hr,
    abs_B_le_of_le_stripLoc hωG hgood h0 hr, ?_, fun i => hgaps i, fun j => ?_⟩
  · show ‖(fun i => VL i r ω)‖ ≤ n
    exact (norm_fst_le _).trans ((norm_snd_le (W r ω, (fun i => VL i r ω), fun j => VR j r ω)).trans
      hnorm)
  · show ‖(fun j => VR j r ω)‖ ≤ n
    exact ((norm_snd_le ((fun i => VL i r ω), fun j => VR j r ω)).trans
      (norm_snd_le (W r ω, (fun i => VL i r ω), fun j => VR j r ω))).trans hnorm
  · simp only [stripCoordAt, Strip.stripClock]
    refine intervalIntegral.integral_nonneg r.coe_nonneg fun u _ => ?_
    exact inv_nonneg.2 (sq_nonneg _)
  · simp only [gapArg, stripCoordAt]
    have : Real.sqrt κ * B r ω + driftLin xL xR ρL ρR (stripCoordAt (W · ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) r) = W r ω := hW.symm
    simp only [stripCoordAt] at this
    rw [this]
    exact hg
  · simp only [stripCoordAt]
    have := hF.w_le_vR hlife.1 j
    linarith

/-- The total-variation bound of the localization. -/
def stripKb (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (n : ℕ) : ℝ :=
  ((nL : ℝ) + 1) * (‖xL‖ + n) + nR * (‖xR‖ + n) + n * ((n : ℝ) + 1) ^ 2

omit hω hωG in
theorem stripKb_nonneg (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (n : ℕ) : 0 ≤ stripKb xL xR n := by
  unfold stripKb; positivity

/-- **The strip density has total variation at most `stripKb` up to `σ_n`.** -/
theorem integral_norm_stripDensAt_le_stripKb (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω) :
    ∫ s in (0 : ℝ)..(stripLoc G W VL VR B ζ n ω : ℝ),
      ‖stripDensAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s‖ ≤ stripKb xL xR n := by
  set σ := stripLoc G W VL VR B ζ n ω with hσdef
  rcases (zero_le (a := σ)).eq_or_lt with h0 | h0
  · rw [← h0, NNReal.coe_zero, intervalIntegral.integral_same]; exact stripKb_nonneg xL xR n
  have hlife := isStripLife_stripLoc hω hωG (n := n)
  have hF := hω.1.isForcePath
  have hbox := mem_stripKc_of_le_stripLoc hω hωG hgood (le_refl σ)
  have hbox' : (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) σ, B σ ω) ∈
      stripBox κ xL xR ρL ρR n := by
    rcases hbox with heq | hb
    · exfalso
      have h2 := congrArg (fun p : SCoord nL nR × ℝ => p.1.2.2) heq
      simp only [stripCoordAt, stripInit] at h2
      have hpos : 0 < Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) σ := by
        have hint := intervalIntegrable_clockRate hF hlife
        simp only [Strip.stripClock, Strip.extPath]
        rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' (Eventually.of_forall fun u =>
          inv_nonneg.2 (sq_nonneg _)) hint]
        refine ⟨by exact_mod_cast h0, ?_⟩
        have hsub : Ioc (0 : ℝ) σ ⊆ Function.support (fun s : ℝ =>
            ((W s.toNNReal ω - VL (Fin.last nL) s.toNNReal ω) ^ 2)⁻¹) ∩ Ioc 0 σ := fun u hu => by
          refine ⟨?_, hu⟩
          have := hlife.2 u.toNNReal (Sec2.toNNReal_le_of_mem_Icc ⟨hu.1.le, hu.2⟩)
          exact inv_ne_zero (pow_ne_zero 2 (sub_pos.2 this).ne')
        refine lt_of_lt_of_le ?_ (measure_mono hsub)
        rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos]
        exact_mod_cast h0
      linarith
    · exact hb
  obtain ⟨hL, hR, -, hT, -⟩ := hbox'
  refine (integral_norm_stripDensAt_le hF hlife).trans ?_
  have hLi : ∀ i, xL i - VL i σ ω ≤ ‖xL‖ + n := fun i => by
    have h1 : |xL i| ≤ ‖xL‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xL i
    have h2 : |VL i σ ω| ≤ n := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (fun i => VL i σ ω) i).trans hL
    linarith [le_abs_self (xL i), neg_abs_le (VL i σ ω)]
  have hRj : ∀ j, VR j σ ω - xR j ≤ ‖xR‖ + n := fun j => by
    have h1 : |xR j| ≤ ‖xR‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xR j
    have h2 : |VR j σ ω| ≤ n := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (fun j => VR j σ ω) j).trans hR
    linarith [le_abs_self (VR j σ ω), neg_abs_le (xR j)]
  have hsL : ∑ i, (xL i - VL i σ ω) ≤ ((nL : ℝ) + 1) * (‖xL‖ + n) := by
    calc ∑ i, (xL i - VL i σ ω) ≤ ∑ _i : Fin (nL + 1), (‖xL‖ + n) := Finset.sum_le_sum fun i _ => hLi i
      _ = _ := by simp; ring
  have hsR : ∑ j, (VR j σ ω - xR j) ≤ (nR : ℝ) * (‖xR‖ + n) := by
    calc ∑ j, (VR j σ ω - xR j) ≤ ∑ _j : Fin nR, (‖xR‖ + n) := Finset.sum_le_sum fun j _ => hRj j
      _ = _ := by simp; ring
  simp only [stripCoordAt] at hT
  unfold stripKb
  linarith

end GoodFacts

/-! ### Monotonicity and exhaustion -/

theorem levelFun_mono {δ δ' R R' : ℝ} (hδ : δ' ≤ δ) (hR : R ≤ R')
    (st : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ)) : levelFun δ R st ≤ levelFun δ' R' st := by
  unfold levelFun
  refine min_le_min (min_le_min (by linarith) (by linarith)) (neg_le_neg (Finset.sum_le_sum
    fun i _ => max_le_max le_rfl (by linarith)))

theorem hitBelow_mono_fun {f g : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} (hfg : ∀ s, f s ≤ g s) :
    Coupling.hitBelow f ζ' 0 ≤ Coupling.hitBelow g ζ' 0 := by
  by_cases hne : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ∧ f s < 0}.Nonempty
  · rw [Coupling.hitBelow_of_nonempty hne]
    exact Coupling.le_hitBelow fun s hs hgs => csInf_le (OrderBot.bddBelow _)
      ⟨hs, lt_of_le_of_lt (hfg s) hgs⟩
  · have hne' : ¬ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ∧ g s < 0}.Nonempty := fun ⟨s, hs, hgs⟩ =>
      hne ⟨s, hs, lt_of_le_of_lt (hfg s) hgs⟩
    rw [Coupling.hitBelow_of_not_nonempty hne, Coupling.hitBelow_of_not_nonempty hne']

/-- **The localizing times increase with the level.** -/
theorem stripLoc_mono (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω) (ω : Ω) {m n : ℕ}
    (hmn : m ≤ n) : stripLoc G W VL VR B ζ m ω ≤ stripLoc G W VL VR B ζ n ω := by
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hhit : hitLevel G W VL VR ζ m ω ≤ hitLevel G W VL VR ζ n ω := by
    unfold hitLevel
    split_ifs with hω
    · refine hitBelow_mono_fun fun s => levelFun_mono ?_ hmn' _
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · exact le_rfl
  have hex := MathFin.exitTime_mono (continuous_brownG_strip hgood) hmn ω
  have h := min_le_min (WithTop.coe_le_coe.2 (show (m : ℝ≥0) ≤ n by exact_mod_cast hmn))
    (min_le_min hhit hex)
  have em : (stripLoc G W VL VR B ζ m ω : WithTop ℝ≥0) = min ((m : ℝ≥0) : WithTop ℝ≥0)
      (min (hitLevel G W VL VR ζ m ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) m ω)) :=
    Sec2.TwoSeed.coe_capTime _ _ ω
  have en : (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) = min ((n : ℝ≥0) : WithTop ℝ≥0)
      (min (hitLevel G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) :=
    Sec2.TwoSeed.coe_capTime _ _ ω
  rw [← em, ← en] at h
  exact WithTop.coe_le_coe.1 h

/-- **The localizing times exhaust the strip life of a good path.** -/
theorem exists_le_stripLoc (hgood : ∀ ω ∈ G, IsGoodStrip κ xL xR ρL ρR W VL VR B ζ ω)
    (hxL : ∀ i : Fin nL, xL (Fin.last nL) < xL i.castSucc) {ω : Ω} (hωG : ω ∈ G) {s : ℝ≥0}
    (hs : Strip.IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s) :
    ∃ n : ℕ, s ≤ stripLoc G W VL VR B ζ n ω := by
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  have hsub : Icc (0 : ℝ≥0) s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hs.1
  have hne : (Icc (0 : ℝ≥0) s).Nonempty := ⟨0, le_rfl, bot_le⟩
  -- a uniform lower bound for `W − v` and the lower left gaps on `[0, s]`
  have hGc : ContinuousOn (fun r => W r ω - VL (Fin.last nL) r ω) (Icc 0 s) :=
    (hF.continuousOn_w.sub (hF.continuousOn_vL _)).mono hsub
  obtain ⟨r₀, hr₀, hmin₀⟩ := isCompact_Icc.exists_isMinOn hne hGc
  have hG0 : 0 < W r₀ ω - VL (Fin.last nL) r₀ ω := sub_pos.2 (hs.2 r₀ hr₀.2)
  have hgap : ∀ i : Fin nL, ∃ δ > 0, ∀ r ∈ Icc (0 : ℝ≥0) s,
      δ ≤ VL i.castSucc r ω - VL (Fin.last nL) r ω := fun i => by
    have hc : ContinuousOn (fun r => VL i.castSucc r ω - VL (Fin.last nL) r ω) (Icc 0 s) :=
      ((hF.continuousOn_vL _).sub (hF.continuousOn_vL _)).mono hsub
    obtain ⟨r₁, hr₁, hmin₁⟩ := isCompact_Icc.exists_isMinOn hne hc
    refine ⟨_, sub_pos.2 (hF.vL_lt_vL_of_lt ((hs.mono hr₁.2).1) (hxL i)
      fun r hr => hs.2 r (hr.trans hr₁.2)), fun r hr => hmin₁ hr⟩
  choose δi hδi hδile using hgap
  obtain ⟨δg, hδg, hδglt⟩ : ∃ δ > 0, ∀ i : Fin nL, δ < δi i := by
    set S := insert (1 : ℝ) (Finset.univ.image δi)
    have hS : S.Nonempty := Finset.insert_nonempty _ _
    have h0 : 0 < S.min' hS := (Finset.lt_min'_iff S hS).2 fun y hy => by
      rcases Finset.mem_insert.1 hy with rfl | hy
      · norm_num
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact hδi i
    refine ⟨S.min' hS / 2, by linarith, fun i => ?_⟩
    have := Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem δi
      (Finset.mem_univ i)))
    linarith
  -- bounds for the state and the Brownian path on `[0, s]`
  have hstc : ContinuousOn (fun r => ‖Coupling.stateAt W VL VR r ω‖) (Icc 0 s) :=
    (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR))).norm.mono hsub
  obtain ⟨r₂, hr₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hstc
  obtain ⟨r₃, hr₃, hmax₃⟩ := isCompact_Icc.exists_isMaxOn hne (hω.2.1.abs.continuousOn (s := Icc 0 s))
  set δ := min (W r₀ ω - VL (Fin.last nL) r₀ ω) δg with hδ
  have hδpos : 0 < δ := lt_min hG0 hδg
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max (s : ℝ) (‖Coupling.stateAt W VL VR r₂ ω‖ + |B r₃ ω| + 1))
    (1 / δ))
  have hns : (s : ℝ) < n := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hn)
  have hnR : ‖Coupling.stateAt W VL VR r₂ ω‖ + |B r₃ ω| + 1 < n :=
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hn)
  have hnδ : 1 / δ < n := (le_max_right _ _).trans_lt hn
  have hδn : 1 / ((n : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδpos] at hnδ
    nlinarith
  refine ⟨n, ?_⟩
  -- the level functional is nonnegative on `[0, s]`
  have hlev : ∀ r ∈ Icc (0 : ℝ≥0) s, 0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω) := by
    intro r hr
    refine levelFun_nonneg_iff.2 ⟨?_, ?_, fun i => ?_⟩
    · simp only [Coupling.stateAt]
      exact hδn.trans ((min_le_left _ _).trans (hmin₀ hr))
    · have := isMaxOn_iff.1 hmax₂ r hr
      have h3 := abs_nonneg (B r₃ ω)
      linarith
    · simp only [Coupling.stateAt]
      exact hδn.trans ((min_le_right _ _).trans ((hδglt i).le.trans (hδile i r hr)))
  have hhit : (s : WithTop ℝ≥0) ≤ hitLevel G W VL VR ζ n ω := by
    simp only [hitLevel, hωG, ↓reduceIte]
    refine Coupling.le_hitBelow fun r hrζ hr => ?_
    by_contra hlt
    push Not at hlt
    exact absurd (hlev r ⟨bot_le, hlt.le⟩) (not_le.2 hr)
  have hexit : (s : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨r, hr, hBr⟩ := (MathFin.exitTime_le_iff (continuous_brownG_strip hgood) n u ω).1 hu.symm.le
    have hus : u < s := by rw [← hu] at hlt; exact WithTop.coe_lt_coe.1 hlt
    have hrs : r ∈ Icc (0 : ℝ≥0) s := ⟨bot_le, hr.2.trans hus.le⟩
    have := isMaxOn_iff.1 hmax₃ r hrs
    simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hBr
    have h2 := norm_nonneg (Coupling.stateAt W VL VR r₂ ω)
    linarith
  have h := le_min (WithTop.coe_le_coe.2 (show s ≤ (n : ℝ≥0) by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact hns.le)) (le_min hhit hexit)
  have en : (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) = min ((n : ℝ≥0) : WithTop ℝ≥0)
      (min (hitLevel G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) :=
    Sec2.TwoSeed.coe_capTime _ _ ω
  rw [← en] at h
  exact WithTop.coe_le_coe.1 h

end Loc

end Zhan

end InteractingSLE
