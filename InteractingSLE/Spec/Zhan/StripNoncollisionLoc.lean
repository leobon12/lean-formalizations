/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollisionGen
import InteractingSLE.Spec.Zhan.StripTimeMart

/-!
# Noncollision on the strip life: localization without an a priori strip clock

Packet PROVE-ZHAN-A3. The localization of `StripTimeLoc.lean` (PROVE-ZHAN-A2) keeps the chordal state in a box and
uses the unbounded strip clock to stay in the strip life. Here the strip clock is what is to be proved, so the
localizing times `σ_{n,m}` (`ncLoc`) are built from two hitting times of the killed state (`Coupling.hitBelow`):

* the level-`n` box of `StripTimeLoc.lean` (`hitLevel`: `W − v ≥ 1/(n+1)`, every lower left mark `≥ 1/(n+1)` right of
  `v`, `‖state‖ ≤ n`), together with `n` and the exit time of `|B|` from `(−n, n)`;
* the level-`m` Lyapunov constraints (`hitM`, `mLevel`): `e^{−(m+1)} ≤ G ≤ e^{m+1}` and the nearest strip gaps
  `X, Y ≥ 1/(m+1)`, i.e. `V^{L,0} − v ≤ e^{−1/(m+1)} G`, `G ≤ e^{−1/(m+1)} (V^{R,0} − v)`.

On good paths (`IsNcGood`: the frozen pathwise conditions, a continuous Brownian path started at `0`, and the
**end-collision property** `ζ < ∞ → inf_{[0, ζ)} (W − v) = 0`, which Aux. lemma 3 provides for strip words) the
times `σ_{n,m}` lie in the strip life (`isStripLife_ncLoc`) and keep the coordinates in the compact set `ncKc n m`
inside the region of the Lyapunov observable. The localized Itô formula then gives the martingale
`Ψ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen Ψ` (`martingale_ncLyap`).

## Main results

* `mLevel`, `mLevel_nonneg_iff`; `ncBox`, `ncKc`, `isCompact_ncKc`, `ncKc_subset_region`;
* `IsNcGood`, `hitM`, `ncLoc`, `isStoppingTime_ncLoc`;
* `isStripLife_ncLoc`, `levelFun_nonneg_of_le_ncLoc`, `mLevel_nonneg_of_le_ncLoc`, `mem_ncKc_of_le_ncLoc`,
  `integral_norm_stripDensAt_le_ncLoc`;
* `measurable_coordS_ncLoc`, `martingale_ncLyap`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-! ### The level-`m` constraints -/

/-- The level-`m` functional of the Lyapunov constraints (state `(W, V^L, V^R)`, `G = W − v`): nonnegative iff
`e^{−(m+1)} ≤ G ≤ e^{m+1}`, `V^{L,0} − v ≤ e^{−1/(m+1)} G` (if `nL > 0`) and `G ≤ e^{−1/(m+1)} (V^{R,0} − v)` (if
`nR > 0`). -/
def mLevel (m : ℕ) (st : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ)) : ℝ :=
  min (min (st.1 - st.2.1 (Fin.last nL) - Real.exp (-((m : ℝ) + 1)))
      (Real.exp ((m : ℝ) + 1) - (st.1 - st.2.1 (Fin.last nL))))
    (min (if h : 0 < nL then Real.exp (-(1 / ((m : ℝ) + 1))) * (st.1 - st.2.1 (Fin.last nL)) -
        (st.2.1 (Fin.castSucc ⟨0, h⟩) - st.2.1 (Fin.last nL)) else 1)
      (if h : 0 < nR then Real.exp (-(1 / ((m : ℝ) + 1))) * (st.2.2 ⟨0, h⟩ - st.2.1 (Fin.last nL)) -
        (st.1 - st.2.1 (Fin.last nL)) else 1))

theorem continuous_mLevel (m : ℕ) : Continuous (mLevel (nL := nL) (nR := nR) m) := by
  unfold mLevel
  refine Continuous.min (by fun_prop) (Continuous.min ?_ ?_)
  · by_cases h : 0 < nL
    · simp only [h, ↓reduceDIte]; fun_prop
    · simp only [h, ↓reduceDIte]; exact continuous_const
  · by_cases h : 0 < nR
    · simp only [h, ↓reduceDIte]; fun_prop
    · simp only [h, ↓reduceDIte]; exact continuous_const

theorem mLevel_nonneg_iff {m : ℕ} {st : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ)} :
    0 ≤ mLevel m st ↔ Real.exp (-((m : ℝ) + 1)) ≤ st.1 - st.2.1 (Fin.last nL) ∧
      st.1 - st.2.1 (Fin.last nL) ≤ Real.exp ((m : ℝ) + 1) ∧
      (∀ h : 0 < nL, st.2.1 (Fin.castSucc ⟨0, h⟩) - st.2.1 (Fin.last nL) ≤
        Real.exp (-(1 / ((m : ℝ) + 1))) * (st.1 - st.2.1 (Fin.last nL))) ∧
      (∀ h : 0 < nR, st.1 - st.2.1 (Fin.last nL) ≤
        Real.exp (-(1 / ((m : ℝ) + 1))) * (st.2.2 ⟨0, h⟩ - st.2.1 (Fin.last nL))) := by
  unfold mLevel
  simp only [le_min_iff, sub_nonneg]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, h2, fun h => ?_, fun h => ?_⟩
    · simpa only [h, ↓reduceDIte, sub_nonneg] using h3
    · simpa only [h, ↓reduceDIte, sub_nonneg] using h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, ?_⟩
    · by_cases h : 0 < nL
      · simpa only [h, ↓reduceDIte, sub_nonneg] using h3 h
      · simp only [h, ↓reduceDIte, zero_le_one]
    · by_cases h : 0 < nR
      · simpa only [h, ↓reduceDIte, sub_nonneg] using h4 h
      · simp only [h, ↓reduceDIte, zero_le_one]

/-! ### The compact box -/

section Box

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)

/-- The chordal state `(W, V^L, V^R)` of strip coordinates `p = ((V^L, V^R, T), b)`, `W = √κ b + ℓ(V)`. -/
def stateOf (p : SCoord nL nR × ℝ) : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ) :=
  (Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1, p.1.1, p.1.2.1)

theorem continuous_stateOf : Continuous (stateOf κ xL xR ρL ρR (nL := nL) (nR := nR)) := by
  unfold stateOf driftLin; fun_prop

/-- The level-`(n, m)` box: the box of `StripTimeLoc.lean` with the Lyapunov constraints. -/
def ncBox (n m : ℕ) : Set (SCoord nL nR × ℝ) :=
  stripBox κ xL xR ρL ρR n ∩ {p | 0 ≤ mLevel m (stateOf κ xL xR ρL ρR p)}

/-- The box together with the initial point. -/
def ncKc (n m : ℕ) : Set (SCoord nL nR × ℝ) := insert (stripInit xL xR) (ncBox κ xL xR ρL ρR n m)

theorem isCompact_ncKc (n m : ℕ) : IsCompact (ncKc κ xL xR ρL ρR n m) :=
  ((isCompact_closedBall _ _).of_isClosed_subset ((isClosed_stripBox κ xL xR ρL ρR n).inter
    (isClosed_le continuous_const ((continuous_mLevel m).comp (continuous_stateOf κ xL xR ρL ρR))))
    (inter_subset_left.trans (stripBox_subset_closedBall κ xL xR ρL ρR n))).insert _

theorem gapArg_eq_stateOf (p : SCoord nL nR × ℝ) :
    gapArg κ xL xR ρL ρR p = (stateOf κ xL xR ρL ρR p).1 - (stateOf κ xL xR ρL ρR p).2.1 (Fin.last nL) :=
  rfl

theorem ncBox_subset_region (n m : ℕ) : ncBox κ xL xR ρL ρR n m ⊆ ncRegion κ xL xR ρL ρR := by
  intro p hp
  obtain ⟨hb, hm⟩ := hp
  obtain ⟨-, -, hX, hY⟩ := mLevel_nonneg_iff.1 (mem_ofPred_eq ▸ hm)
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hg : 0 < gapArg κ xL xR ρL ρR p := hδ.trans_le hb.2.2.2.2.2.1
  have he1 : Real.exp (-(1 / ((m : ℝ) + 1))) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  refine ⟨hg, fun h => ⟨hδ.trans_le (hb.2.2.2.2.2.2.1 _), ?_⟩, fun h => ?_⟩
  · have := hX h
    rw [← gapArg_eq_stateOf] at this
    simp only [stateOf] at this
    simp only [ncEL]
    nlinarith
  · have := hY h
    rw [← gapArg_eq_stateOf] at this
    simp only [stateOf] at this
    have hf : 0 < ncFR (nL := nL) ⟨0, h⟩ p := hδ.trans_le (hb.2.2.2.2.2.2.2 _)
    simp only [ncFR] at hf ⊢
    nlinarith

theorem ncKc_subset_region (h0 : stripInit xL xR ∈ ncRegion κ xL xR ρL ρR) (n m : ℕ) :
    ncKc κ xL xR ρL ρR n m ⊆ ncRegion κ xL xR ρL ρR :=
  insert_subset h0 (ncBox_subset_region κ xL xR ρL ρR n m)

/-- The initial point lies in the region for a separated word: `x^L_{last} < x^L_0 < 0 < x^R_0`. -/
theorem stripInit_mem_ncRegion (h0 : xL (Fin.last nL) < 0)
    (hL : ∀ h : 0 < nL, xL (Fin.last nL) < xL (Fin.castSucc ⟨0, h⟩) ∧ xL (Fin.castSucc ⟨0, h⟩) < 0)
    (hR : ∀ h : 0 < nR, 0 < xR ⟨0, h⟩) : stripInit xL xR ∈ ncRegion κ xL xR ρL ρR := by
  have hg : gapArg κ xL xR ρL ρR (stripInit xL xR) = -xL (Fin.last nL) := gapArg_stripInit κ xL xR ρL ρR
  refine ⟨by rw [hg]; linarith, fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · simp only [ncEL, stripInit]; linarith [(hL h).1]
  · rw [hg]; simp only [ncEL, stripInit]; linarith [(hL h).2]
  · rw [hg]; simp only [ncFR, stripInit]; linarith [hR h]

end Box

/-! ### Good paths and the localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Good paths** for the noncollision argument: the frozen pathwise conditions, a continuous Brownian path started
at `0`, and the end-collision property (at a finite lifetime the end mark meets the driver: `W − v` takes arbitrarily
small values before `ζ`). -/
def IsNcGood (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
    Continuous (B · ω) ∧ B 0 ω = 0 ∧
    (ζ ω ≠ ⊤ → ∀ ε > 0, ∃ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω ∧ W s ω - VL (Fin.last nL) s ω < ε)

open scoped Classical in
/-- The first time before `ζ` at which the level-`m` constraints fail, on the good event (`0` off it). -/
def hitM (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (m : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => mLevel m (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0

/-- **The localizing times** `σ_{n,m} = n ∧ (exit of the level-`n` box) ∧ (failure of the level-`m` constraints) ∧
(exit of `|B|` from `(−n, n)`)`, `0` off the good event. -/
def ncLoc (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n m : ℕ) (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0))
    (fun ω => min (min (hitLevel G W VL VR ζ n ω) (hitM G W VL VR ζ m ω))
      (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

theorem coe_ncLoc (n m : ℕ) (ω : Ω) : (ncLoc G W VL VR B ζ n m ω : WithTop ℝ≥0) =
    min ((n : ℝ≥0) : WithTop ℝ≥0) (min (min (hitLevel G W VL VR ζ n ω) (hitM G W VL VR ζ m ω))
      (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) :=
  Sec2.TwoSeed.coe_capTime _ _ ω

theorem ncLoc_le (n m : ℕ) (ω : Ω) : ncLoc G W VL VR B ζ n m ω ≤ n :=
  Sec2.TwoSeed.capTime_le _ _ ω

theorem ncLoc_le_hitLevel (n m : ℕ) (ω : Ω) :
    (ncLoc G W VL VR B ζ n m ω : WithTop ℝ≥0) ≤ hitLevel G W VL VR ζ n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans ((min_le_left _ _).trans (min_le_left _ _))

theorem ncLoc_le_hitM (n m : ℕ) (ω : Ω) :
    (ncLoc G W VL VR B ζ n m ω : WithTop ℝ≥0) ≤ hitM G W VL VR ζ m ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans ((min_le_left _ _).trans (min_le_right _ _))

theorem ncLoc_le_exitTime (n m : ℕ) (ω : Ω) :
    (ncLoc G W VL VR B ζ n m ω : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

theorem ncLoc_of_not_mem {ω : Ω} (hω : ω ∉ G) (n m : ℕ) : ncLoc G W VL VR B ζ n m ω = 0 := by
  have h := ncLoc_le_hitLevel (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n m ω
  simp only [hitLevel, hω, ↓reduceIte] at h
  exact le_antisymm (by exact_mod_cast h) bot_le

section StoppingTime

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsNcGood κ xL xR ρL ρR W VL VR B ζ ω)

include hgood in
theorem continuous_brownG_nc (ω : Ω) : Continuous (Sec2.TwoSeed.brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using (hgood ω hω).2.1
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
theorem isFilteredBrownianReal_brownG_nc :
    IsFilteredBrownianReal (usualAugmentation 𝓕 P) (Sec2.TwoSeed.brownG G B) P := by
  have := (Ito.isFilteredBrownianReal_modify (Ito.isFilteredBrownianReal_usualAugmentation hE.1) hGm hGc
    fun ω hω => (hgood ω hω).2.1).1
  rwa [Ito.nullAugmented_usualAugmentation] at this

include hgood in
theorem continuousOn_stateAt_nc {ω : Ω} (hω : ω ∈ G) :
    ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := by
  have hF := (hgood ω hω).1.isForcePath
  exact hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
    (continuousOn_pi.2 hF.continuousOn_vR))

open scoped Classical in
include hE hGm hGc hgood in
theorem isStoppingTime_hit_nc {Φ : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ) → ℝ} (hΦ : Continuous Φ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω =>
      if ω ∈ G then Coupling.hitBelow (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0 := by
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hτ := Coupling.isStoppingTime_hitBelow_state hWa hVLa hVRa hG0
    (fun ω hω => continuousOn_stateAt_nc hgood hω) hΦ 0
  intro t
  have e : {ω | (if ω ∈ G then Coupling.hitBelow (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) 0
      else 0) ≤ (t : WithTop ℝ≥0)} = Gᶜ ∪ {ω | (if ω ∈ G then Coupling.hitBelow
      (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else ⊤) ≤ t} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [hω]
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff, not_false_eq_true, true_or,
        iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [e]
  exact ((usualAugmentation 𝓕 P).mono (zero_le (a := t)) _ hG0).compl.union (hτ t)

include hE hGm hGc hgood in
/-- **The localizing times are stopping times of the usual augmentation.** -/
theorem isStoppingTime_ncLoc (n m : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ncLoc G W VL VR B ζ n m ω : WithTop ℝ≥0) :=
  Sec2.TwoSeed.isStoppingTime_capTime (isStoppingTime_const _ _)
    (((isStoppingTime_hit_nc hE hGm hGc hgood (continuous_levelFun (1 / ((n : ℝ) + 1)) n)).min
      (isStoppingTime_hit_nc hE hGm hGc hgood (continuous_mLevel m))).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_nc hE hGm hGc hgood).2.1 (continuous_brownG_nc hgood) n))

end StoppingTime

/-! ### Pathwise facts on good paths -/

section GoodFacts

variable {ω : Ω} {n m : ℕ} (hω : IsNcGood κ xL xR ρL ρR W VL VR B ζ ω) (hωG : ω ∈ G)
include hω hωG

omit hω in
theorem levelFun_nonneg_of_lt_ncLoc {r : ℝ≥0} (hr : r < ncLoc G W VL VR B ζ n m ω)
    (hrζ : (r : ℝ≥0∞) < ζ ω) :
    0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω) := by
  by_contra hneg
  push Not at hneg
  have h1 := Coupling.hitBelow_le (f := fun s => levelFun (1 / ((n : ℝ) + 1)) n
    (Coupling.stateAt W VL VR s ω)) hrζ hneg
  have h2 := ncLoc_le_hitLevel (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n m ω
  simp only [hitLevel, hωG, ↓reduceIte] at h2
  exact absurd (WithTop.coe_le_coe.1 (h2.trans h1)) (not_le.2 hr)

omit hω in
theorem mLevel_nonneg_of_lt_ncLoc {r : ℝ≥0} (hr : r < ncLoc G W VL VR B ζ n m ω)
    (hrζ : (r : ℝ≥0∞) < ζ ω) : 0 ≤ mLevel m (Coupling.stateAt W VL VR r ω) := by
  by_contra hneg
  push Not at hneg
  have h1 := Coupling.hitBelow_le (f := fun s => mLevel m (Coupling.stateAt W VL VR s ω)) hrζ hneg
  have h2 := ncLoc_le_hitM (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n m ω
  simp only [hitM, hωG, ↓reduceIte] at h2
  exact absurd (WithTop.coe_le_coe.1 (h2.trans h1)) (not_le.2 hr)

/-- `σ_{n,m}` is strictly before the lifetime (the end-collision property excludes a finite lifetime with the end
mark separated from the driver). -/
theorem ncLoc_lt_lifetime : (ncLoc G W VL VR B ζ n m ω : ℝ≥0∞) < ζ ω := by
  set f : ℝ≥0 → ℝ := fun s => levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR s ω) with hf
  have h2 := ncLoc_le_hitLevel (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n m ω
  simp only [hitLevel, hωG, ↓reduceIte] at h2
  by_cases htop : Coupling.hitBelow f (ζ ω) 0 = ⊤
  swap
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 htop
    have htζ := Coupling.lt_of_hitBelow_eq ht.symm
    rw [← ht] at h2
    exact lt_of_le_of_lt (by exact_mod_cast WithTop.coe_le_coe.1 h2) htζ
  · -- the box is never left before `ζ`; then `ζ = ∞`
    have hall : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → 0 ≤ f s := fun s hs => by
      by_contra hneg
      push Not at hneg
      have := Coupling.hitBelow_le (f := f) hs hneg
      rw [htop] at this
      exact absurd this (not_le.2 (WithTop.coe_lt_top _))
    have hζ : ζ ω = ⊤ := by
      by_contra hne
      have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨s, hs, hGs⟩ := hω.2.2.2 hne _ hδ
      have := (levelFun_nonneg_iff.1 (hall s hs)).1
      simp only [Coupling.stateAt] at this
      linarith
    rw [hζ]; exact ENNReal.coe_lt_top

/-- **`σ_{n,m}` lies in the strip life.** -/
theorem isStripLife_ncLoc (h0 : xL (Fin.last nL) < 0) :
    Strip.IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) (ncLoc G W VL VR B ζ n m ω) := by
  set σ := ncLoc G W VL VR B ζ n m ω with hσ
  have hσζ : (σ : ℝ≥0∞) < ζ ω := ncLoc_lt_lifetime hω hωG
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hlt : ∀ r < σ, VL (Fin.last nL) r ω < W r ω := fun r hr => by
    have := (levelFun_nonneg_iff.1 (levelFun_nonneg_of_lt_ncLoc hωG hr
      (lt_of_le_of_lt (by exact_mod_cast hr.le) hσζ))).1
    simp only [Coupling.stateAt] at this
    linarith
  refine ⟨hσζ, fun r hr => ?_⟩
  rcases hr.lt_or_eq with hr | rfl
  · exact hlt r hr
  rcases (zero_le (a := σ)).eq_or_lt with h00 | hσ0
  · have h1 : W 0 ω = 0 := hω.1.1
    have h2 : VL (Fin.last nL) 0 ω = xL (Fin.last nL) := hω.1.2.1 _
    rw [← h00]
    show VL (Fin.last nL) 0 ω < W 0 ω
    rw [h1, h2]; exact h0
  -- at `σ > 0` by continuity from the left
  have hF := hω.1.isForcePath
  have hc : ContinuousOn (fun s => W s ω - VL (Fin.last nL) s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    hF.continuousOn_w.sub (hF.continuousOn_vL _)
  have hat := hc.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds hσζ)
  have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
  have hge : 1 / ((n : ℝ) + 1) ≤ W σ ω - VL (Fin.last nL) σ ω := by
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    have := (levelFun_nonneg_iff.1 (levelFun_nonneg_of_lt_ncLoc hωG hr'
      (lt_of_le_of_lt (by exact_mod_cast (le_of_lt hr')) hσζ))).1
    simpa only [Coupling.stateAt] using this
  linarith

omit hω hωG in
theorem continuousOn_comp_stateAt {Φ : ℝ × (Fin (nL + 1) → ℝ) × (Fin nR → ℝ) → ℝ} (hΦ : Continuous Φ)
    (hF : Sec2.IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)) :
    ContinuousOn (fun s => Φ (Coupling.stateAt W VL VR s ω)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
  hΦ.comp_continuousOn (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
    (continuousOn_pi.2 hF.continuousOn_vR)))

/-- On `[0, σ_{n,m}]` the state is in the level-`n` box, if `σ_{n,m} > 0`. -/
theorem levelFun_nonneg_of_le_ncLoc (hσ0 : 0 < ncLoc G W VL VR B ζ n m ω) {r : ℝ≥0}
    (hr : r ≤ ncLoc G W VL VR B ζ n m ω) :
    0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω) := by
  set σ := ncLoc G W VL VR B ζ n m ω with hσ
  have hσζ : (σ : ℝ≥0∞) < ζ ω := ncLoc_lt_lifetime hω hωG
  rcases hr.lt_or_eq with hlt | heq
  · exact levelFun_nonneg_of_lt_ncLoc hωG hlt (lt_of_le_of_lt (by exact_mod_cast hlt.le) hσζ)
  · subst heq
    have hat := (continuousOn_comp_stateAt (continuous_levelFun (1 / ((n : ℝ) + 1)) n)
      hω.1.isForcePath).continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds hσζ)
    have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact levelFun_nonneg_of_lt_ncLoc hωG hr' (lt_of_le_of_lt (by exact_mod_cast (le_of_lt hr')) hσζ)

/-- On `[0, σ_{n,m}]` the level-`m` constraints hold, if `σ_{n,m} > 0`. -/
theorem mLevel_nonneg_of_le_ncLoc (hσ0 : 0 < ncLoc G W VL VR B ζ n m ω) {r : ℝ≥0}
    (hr : r ≤ ncLoc G W VL VR B ζ n m ω) : 0 ≤ mLevel m (Coupling.stateAt W VL VR r ω) := by
  set σ := ncLoc G W VL VR B ζ n m ω with hσ
  have hσζ : (σ : ℝ≥0∞) < ζ ω := ncLoc_lt_lifetime hω hωG
  rcases hr.lt_or_eq with hlt | heq
  · exact mLevel_nonneg_of_lt_ncLoc hωG hlt (lt_of_le_of_lt (by exact_mod_cast hlt.le) hσζ)
  · subst heq
    have hat := (continuousOn_comp_stateAt (continuous_mLevel m)
      hω.1.isForcePath).continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds hσζ)
    have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact mLevel_nonneg_of_lt_ncLoc hωG hr' (lt_of_le_of_lt (by exact_mod_cast (le_of_lt hr')) hσζ)

/-- The strip clock up to `σ_{n,m}` is at most `n (n+1)²`. -/
theorem stripClock_le_of_le_ncLoc (h0 : xL (Fin.last nL) < 0) {r : ℝ≥0}
    (hr : r ≤ ncLoc G W VL VR B ζ n m ω) :
    Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) r ≤
      (n : ℝ) * ((n : ℝ) + 1) ^ 2 := by
  have hlife := (isStripLife_ncLoc hω hωG h0 (n := n) (m := m)).mono hr
  have hF := hω.1.isForcePath
  have hint := intervalIntegrable_clockRate hF hlife
  rcases (zero_le (a := ncLoc G W VL VR B ζ n m ω)).eq_or_lt with h00 | h00
  · have hr0 : r = 0 := le_antisymm (h00 ▸ hr) bot_le
    subst hr0
    simp only [Strip.stripClock, NNReal.coe_zero, intervalIntegral.integral_same]
    positivity
  have hbound := intervalIntegral.integral_mono_on r.coe_nonneg hint
    (intervalIntegrable_const (c := ((n : ℝ) + 1) ^ 2)) fun u hu => by
      have hu1 : u.toNNReal ≤ r := Sec2.toNNReal_le_of_mem_Icc hu
      exact clockRate_le_of_levelFun (levelFun_nonneg_of_le_ncLoc hω hωG h00 (hu1.trans hr))
  have hle : Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) r ≤
      (r : ℝ) * ((n : ℝ) + 1) ^ 2 := by
    simpa [Strip.stripClock, Strip.extPath, intervalIntegral.integral_const, mul_comm] using hbound
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr.trans (ncLoc_le n m ω)
  exact hle.trans (mul_le_mul_of_nonneg_right hrn (by positivity))

omit hω in
theorem abs_B_le_of_le_ncLoc (hgood : ∀ ω ∈ G, IsNcGood κ xL xR ρL ρR W VL VR B ζ ω) {r : ℝ≥0}
    (hr0 : 0 < r) (hr : r ≤ ncLoc G W VL VR B ζ n m ω) : |B r ω| ≤ n := by
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_nc hgood) hr0
    ((WithTop.coe_le_coe.2 hr).trans (ncLoc_le_exitTime n m ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

omit hωG in
theorem stripCoordAt_zero_eq_nc :
    (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) 0, B 0 ω) =
      stripInit xL xR := by
  have hF := hω.1.isForcePath
  refine Prod.ext (Prod.ext (funext fun i => hF.vL_zero i) (Prod.ext (funext fun j => hF.vR_zero j) ?_))
    hω.2.2.1
  simp [stripCoordAt, Strip.stripClock, stripInit]

/-- **Up to `σ_{n,m}` the strip coordinates and the Brownian path stay in the compact set `ncKc n m`.** -/
theorem mem_ncKc_of_le_ncLoc (hgood : ∀ ω ∈ G, IsNcGood κ xL xR ρL ρR W VL VR B ζ ω)
    (h0 : xL (Fin.last nL) < 0) {r : ℝ≥0} (hr : r ≤ ncLoc G W VL VR B ζ n m ω) :
    (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r, B r ω) ∈
      ncKc κ xL xR ρL ρR n m := by
  rcases (zero_le (a := r)).eq_or_lt with hr0 | hr0
  · subst hr0
    rw [stripCoordAt_zero_eq_nc hω]
    exact mem_insert _ _
  have hσ0 : 0 < ncLoc G W VL VR B ζ n m ω := hr0.trans_le hr
  have hlife := (isStripLife_ncLoc hω hωG h0 (n := n) (m := m)).mono hr
  have hlev := levelFun_nonneg_of_le_ncLoc hω hωG hσ0 hr
  have hm := mLevel_nonneg_of_le_ncLoc hω hωG hσ0 hr
  obtain ⟨hg, hnorm, hgaps⟩ := levelFun_nonneg_iff.1 hlev
  simp only [Coupling.stateAt] at hg hnorm hgaps
  have hF := hω.1.isForcePath
  have hW := w_eq_driftLin hω.1 hlife.1
  have hst : stateOf κ xL xR ρL ρR (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r,
      B r ω) = Coupling.stateAt W VL VR r ω := by
    refine Prod.ext ?_ rfl
    exact hW.symm
  refine mem_insert_of_mem _ ⟨⟨?_, ?_, ?_, stripClock_le_of_le_ncLoc hω hωG h0 hr,
    abs_B_le_of_le_ncLoc hωG hgood hr0 hr, ?_, fun i => hgaps i, fun j => ?_⟩, ?_⟩
  · show ‖(fun i => VL i r ω)‖ ≤ n
    exact (norm_fst_le _).trans ((norm_snd_le (W r ω, (fun i => VL i r ω), fun j => VR j r ω)).trans
      hnorm)
  · show ‖(fun j => VR j r ω)‖ ≤ n
    exact ((norm_snd_le ((fun i => VL i r ω), fun j => VR j r ω)).trans
      (norm_snd_le (W r ω, (fun i => VL i r ω), fun j => VR j r ω))).trans hnorm
  · simp only [stripCoordAt, Strip.stripClock]
    refine intervalIntegral.integral_nonneg r.coe_nonneg fun u _ => ?_
    exact inv_nonneg.2 (sq_nonneg _)
  · rw [gapArg_eq_stateOf, hst]
    exact hg
  · simp only [stripCoordAt]
    have := hF.w_le_vR hlife.1 j
    linarith
  · show 0 ≤ mLevel m (stateOf κ xL xR ρL ρR _)
    rw [hst]; exact hm

/-- **The strip density has total variation at most `stripKb` up to `σ_{n,m}`.** -/
theorem integral_norm_stripDensAt_le_ncLoc (h0 : xL (Fin.last nL) < 0) :
    ∫ s in (0 : ℝ)..(ncLoc G W VL VR B ζ n m ω : ℝ),
      ‖stripDensAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s‖ ≤ stripKb xL xR n := by
  set σ := ncLoc G W VL VR B ζ n m ω with hσdef
  rcases (zero_le (a := σ)).eq_or_lt with h00 | h00
  · rw [← h00, NNReal.coe_zero, intervalIntegral.integral_same]; exact stripKb_nonneg xL xR n
  have hlife := isStripLife_ncLoc hω hωG h0 (n := n) (m := m)
  have hF := hω.1.isForcePath
  have hlev := levelFun_nonneg_of_le_ncLoc hω hωG h00 (le_refl σ)
  obtain ⟨-, hnorm, -⟩ := levelFun_nonneg_iff.1 hlev
  simp only [Coupling.stateAt] at hnorm
  have hL : ‖(fun i => VL i σ ω)‖ ≤ n :=
    (norm_fst_le _).trans ((norm_snd_le (W σ ω, (fun i => VL i σ ω), fun j => VR j σ ω)).trans hnorm)
  have hR : ‖(fun j => VR j σ ω)‖ ≤ n :=
    ((norm_snd_le ((fun i => VL i σ ω), fun j => VR j σ ω)).trans
      (norm_snd_le (W σ ω, (fun i => VL i σ ω), fun j => VR j σ ω))).trans hnorm
  have hT := stripClock_le_of_le_ncLoc hω hωG h0 (le_refl σ)
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
  unfold stripKb
  linarith

end GoodFacts

/-! ### Adaptedness and the localized Itô formula -/

section Adapted

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsNcGood κ xL xR ρL ρR W VL VR B ζ ω) (h0 : xL (Fin.last nL) < 0)

include hE hGm hGc hgood h0 in
/-- The stopped gap is adapted. -/
theorem measurable_gapStop_nc (n m : ℕ) (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (gapStop G W VL (ncLoc G W VL VR B ζ n m) r) := by
  obtain ⟨-, hWa, hVLa, -, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_ncLoc hE hGm hGc hgood n m
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      killedAt ζ W s ω - killedAt ζ (VL (Fin.last nL)) s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed hWa s).sub (Sec2.TwoSeed.measurable_killed (hVLa _) s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => W s ω - VL (Fin.last nL) s ω) hσ hK hG0
    (1 : ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · exact h
  · have hlife := (isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)).mono hs
    simp only [killedAt, hlife.1, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (ncLoc G W VL VR B ζ n m ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      ((isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)).mono hs).1
    exact (hF.continuousOn_w.sub (hF.continuousOn_vL _)).mono hsub

include hgood h0 in
theorem continuous_gapStop_nc (n m : ℕ) (ω : Ω) :
    Continuous fun r => gapStop G W VL (ncLoc G W VL VR B ζ n m) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (ncLoc G W VL VR B ζ n m ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      ((isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)).mono hs).1
    have hc := (hF.continuousOn_w.sub (hF.continuousOn_vL (Fin.last nL))).mono hsub
    simp only [gapStop, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [gapStop, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood h0 in
/-- **The stopped strip coordinates are adapted.** -/
theorem measurable_coordS_ncLoc (n m : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      coordS xL xR G W VL VR (min t (ncLoc G W VL VR B ζ n m ω)) ω := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  set σ := ncLoc G W VL VR B ζ n m
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_ncLoc hE hGm hGc hgood n m
  have hprog : IsStronglyProgressive 𝓖 (gapStop G W VL σ) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_gapStop_nc hE hGm hGc hgood h0 n m r).stronglyMeasurable)
      (continuous_gapStop_nc hgood h0 n m)
  set K : ℝ≥0 → Ω → SCoord nL nR := fun s ω => ((fun i => killedAt ζ (VL i) s ω),
    (fun j => killedAt ζ (VR j) s ω), ∫ u in (0 : ℝ)..s, ((gapStop G W VL σ u.toNNReal ω) ^ 2)⁻¹)
    with hKdef
  have hK : ∀ s, Measurable[𝓖 s] (K s) := fun s => by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact @Measurable.of_eval Ω (Fin (nL + 1)) (fun _ => ℝ) (𝓖 s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVLa i) s
    · exact @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 s) _ _ fun j =>
        Sec2.TwoSeed.measurable_killed (hVRa j) s
    · exact (Girsanov.stronglyMeasurable_integral_comp hprog
        (g := fun x : ℝ => (x ^ 2)⁻¹) (by fun_prop) s).measurable
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) hσ hK hG0
    ((xL, xR, 0) : SCoord nL nR) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · exact h
  · have hlife := (isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)).mono hs
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    · simp only [hKdef, killedAt, hlife.1, ↓reduceIte, stripCoordAt]
    · simp only [hKdef, killedAt, hlife.1, ↓reduceIte, stripCoordAt]
    · simp only [hKdef, stripCoordAt, Strip.stripClock, Strip.extPath]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le s.coe_nonneg] at hu
      have hus : u.toNNReal ≤ σ ω := (Sec2.toNNReal_le_of_mem_Icc hu).trans hs
      simp only [gapStop, hω, ↓reduceIte, min_eq_left hus]
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (hlife.mono hs).1
    have hT : ContinuousOn (fun s : ℝ≥0 => Strip.stripClock (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) s) (Iic (σ ω)) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ ω))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le (σ ω).coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hT)

include hE hGm hGc hgood in
/-- The modified Brownian motion stopped at `σ_{n,m}` is adapted. -/
theorem measurable_brownG_ncLoc (n m : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      Sec2.TwoSeed.brownG G B (min t (ncLoc G W VL VR B ζ n m ω)) ω := by
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hB' := isFilteredBrownianReal_brownG_nc hE hGm hGc hgood
  have h := Ito.measurable_stopped_of_agree (X := Sec2.TwoSeed.brownG G B)
    (isStoppingTime_ncLoc hE hGm hGc hgood n m) hB'.2.1 hG0 (0 : ℝ) (fun ω _ s _ => rfl)
    (fun ω _ => (continuous_brownG_nc hgood ω).continuousOn) t
  convert h using 2 with ω
  by_cases hω : ω ∈ G <;> simp [Sec2.TwoSeed.brownG, hω]

include hE hGm hGc hgood h0 in
/-- **The localized Itô formula for the Lyapunov observable**: `Ψ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen Ψ` is a
martingale of the usual augmentation (`σ = σ_{n,m}`). -/
theorem martingale_ncLyap (hreg : stripInit xL xR ∈ ncRegion κ xL xR ρL ρR) (β c₁ c₂ lam : ℝ)
    (n m : ℕ) :
    Martingale (fun t ω => ncLyap κ xL xR ρL ρR β c₁ c₂ lam
        (coordS xL xR G W VL VR (min t (ncLoc G W VL VR B ζ n m ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (ncLoc G W VL VR B ζ n m ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (ncLoc G W VL VR B ζ n m ω) : ℝ≥0),
        Ito.itoGen (ncLyap κ xL xR ρL ρR β c₁ c₂ lam)
          (coordS xL xR G W VL VR s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
          (densS G W VL VR s ω)) (usualAugmentation 𝓕 P) P := by
  set σ := ncLoc G W VL VR B ζ n m with hσdef
  have hB' := isFilteredBrownianReal_brownG_nc hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (densS G W VL VR · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densS, hω, ↓reduceIte] using intervalIntegrable_stripDensAt
        (hgood ω hω).1.isForcePath (isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m))
    · simp only [densS, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordS xL xR G W VL VR t ω =
      coordS xL xR G W VL VR 0 ω + ∫ s in (0 : ℝ)..t, densS G W VL VR s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordS, densS, hω, ↓reduceIte]
      exact stripCoordAt_eq_add_integral (hgood ω hω).1.isForcePath
        ((isStripLife_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)).mono ht)
    · simp only [coordS, densS, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densS G W VL VR s ω‖ ≤ stripKb xL xR n := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [densS, hω, ↓reduceIte] using
        integral_norm_stripDensAt_le_ncLoc (hgood ω hω) hω h0 (n := n) (m := m)
    · simp only [densS, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact stripKb_nonneg xL xR n
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordS xL xR G W VL VR t ω, Sec2.TwoSeed.brownG G B t ω) ∈ ncKc κ xL xR ρL ρR n m := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simpa only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
        mem_ncKc_of_le_ncLoc (hgood ω hω) hω hgood h0 ht
    · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  exact Ito.martingale_itoLocalized hB' (continuous_brownG_nc hgood)
    (isOpen_ncRegion κ xL xR ρL ρR) contDiffOn_ncLyap (isCompact_ncKc κ xL xR ρL ρR n m)
    (ncKc_subset_region κ xL xR ρL ρR hreg n m) (isStoppingTime_ncLoc hE hGm hGc hgood n m)
    (measurable_coordS_ncLoc hE hGm hGc hgood h0 n m) hlam hΛ hKb hK

end Adapted

end Loc

end Zhan

end InteractingSLE
