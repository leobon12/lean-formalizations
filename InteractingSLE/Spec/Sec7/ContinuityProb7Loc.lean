/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Obs
import InteractingSLE.Spec.Sec7.ContinuityProbGaps
import InteractingSLE.Spec.Zhan.StripNoncollisionLoc
import InteractingSLE.Spec.Coupling.AnnounceLifetime

/-!
# Aux. lemma 102: localization before the lifetime and the localized Itô formula

Packet PROVE-SEC7-C7. For an integrated `SLE_κ(ρ)` evolution of a word with marks `Fin (nL + 1)` on the left and
`Fin (nR + 1)` on the right and a positive initial cross-gap `D₀ = x^{R,0} − x^{L,0}`, the coordinates
`Λ = (V^L, V^R, I)` (with an extra absolutely continuous coordinate `I = ∫ c`, used for the band argument) and the
Brownian path are localized at the times

  `σ_n = n ∧ T_n ∧ (exit of ‖(V^L, V^R)‖ from [0, n]) ∧ (exit of |B| from (−n, n))`

(`angLoc`), where `T_n` is an announcing sequence of the lifetime (`Coupling.exists_isAnnouncingSeq`, PROVE-T11-ANN).
This replaces any analysis of the continuation threshold: `σ_n ≤ T_n < ζ`, and the `σ_n` exhaust `[0, ζ)`
(`exists_forall_le_angLoc`). Up to `σ_n` the coordinates stay in a compact subset of `{D > 0}` (the cross-gap is
nondecreasing, so `D ≥ D₀`), and the localized Itô formula (`Ito.martingale_itoLocalized`) gives, for every `C³`
function `Φ` on `{D > 0}`, the martingale `Φ(Λ_{t∧σ_n}, B_{t∧σ_n}) − ∫₀^{t∧σ_n} itoGen Φ` of the usual augmentation
(`martingale_angLoc`).

## Main results

* `IsAngGood`, `exists_good_ang`; `angLoc`, `isStoppingTime_angLoc`, `angLoc_lt_lifetime`, `exists_forall_le_angLoc`;
* `coordA`, `densA`, `angKc`, `isCompact_angKc`, `angKc_subset`;
* `martingale_angLoc`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Clock

open Zhan

variable {nL nR : ℕ}

/-! ### The compact box -/

section Box

variable (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ)

/-- The initial coordinates `((x^L, x^R, 0), 0)`. -/
def angInit : SCoord nL (nR + 1) × ℝ := ((xL, xR, 0), 0)

/-- The level-`n` box: `‖V^L‖, ‖V^R‖, |b| ≤ n`, `|I| ≤ K_I`, `D ≥ D₀`. -/
def angBox (n : ℕ) (KI D₀ : ℝ) : Set (SCoord nL (nR + 1) × ℝ) :=
  {p | ‖p.1.1‖ ≤ n ∧ ‖p.1.2.1‖ ≤ n ∧ |p.1.2.2| ≤ KI ∧ |p.2| ≤ n ∧ D₀ ≤ gapD p}

/-- The box together with the initial point. -/
def angKc (n : ℕ) (KI D₀ : ℝ) : Set (SCoord nL (nR + 1) × ℝ) := insert (angInit xL xR) (angBox n KI D₀)

theorem isCompact_angKc (n : ℕ) (KI D₀ : ℝ) : IsCompact (angKc xL xR n KI D₀) := by
  refine IsCompact.insert ?_ _
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have c1 : Continuous fun p : SCoord nL (nR + 1) × ℝ => ‖p.1.1‖ := by fun_prop
    have c2 : Continuous fun p : SCoord nL (nR + 1) × ℝ => ‖p.1.2.1‖ := by fun_prop
    have c3 : Continuous fun p : SCoord nL (nR + 1) × ℝ => |p.1.2.2| := by fun_prop
    have c4 : Continuous fun p : SCoord nL (nR + 1) × ℝ => |p.2| := by fun_prop
    exact (isClosed_le c1 continuous_const).inter ((isClosed_le c2 continuous_const).inter
      ((isClosed_le c3 continuous_const).inter ((isClosed_le c4 continuous_const).inter
        (isClosed_le continuous_const continuous_gapD))))
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max n KI, fun p hp => ?_⟩
    obtain ⟨h1, h2, h3, h4, -⟩ := hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def, Prod.norm_def]
    refine max_le (max_le (h1.trans (le_max_left _ _)) (max_le (h2.trans (le_max_left _ _)) ?_)) ?_
    · rw [Real.norm_eq_abs]; exact h3.trans (le_max_right _ _)
    · rw [Real.norm_eq_abs]; exact h4.trans (le_max_left _ _)

theorem gapD_angInit : gapD (angInit xL xR) = xR 0 - xL 0 := rfl

theorem angKc_subset {D₀ : ℝ} (hD₀ : 0 < D₀) (h0 : 0 < xR 0 - xL 0) (n : ℕ) (KI : ℝ) :
    angKc xL xR n KI D₀ ⊆ angRegion := by
  refine insert_subset ?_ fun p hp => ?_
  · show 0 < gapD (angInit xL xR)
    rw [gapD_angInit]; exact h0
  · exact hD₀.trans_le hp.2.2.2.2

end Box

/-! ### Good paths and the localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Good paths**: the frozen pathwise conditions, a continuous Brownian path started at `0`, and an announcing
sequence `T` of the lifetime (`T_n < ζ`, exhausting `[0, ζ)`). -/
def IsAngGood (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
    Continuous (B · ω) ∧ B 0 ω = 0 ∧ (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω

/-- A measurable full-measure event of good paths. -/
theorem exists_good_ang {P : Measure Ω} {𝓕 𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ}
    {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hT : Coupling.IsAnnouncingSeq 𝓖 P ζ T) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω := by
  have hae : ∀ᵐ ω ∂P, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hT.2.2.1, hT.2.2.2]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  refine ⟨(toMeasurable P {ω | ¬ IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h
    exact hω (subset_toMeasurable _ _ h)

/-- The box level `n − ‖(V^L, V^R)‖` of a state `(W, V^L, V^R)`. -/
def boxLev (n : ℕ) (st : ℝ × (Fin (nL + 1) → ℝ) × (Fin (nR + 1) → ℝ)) : ℝ := n - ‖st.2‖

theorem continuous_boxLev (n : ℕ) : Continuous (boxLev (nL := nL) (nR := nR) n) := by
  unfold boxLev; fun_prop

open scoped Classical in
/-- The first time before `ζ` at which the marks leave the level-`n` box, on the good event (`0` off it). -/
def hitBox (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => boxLev n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0

/-- **The localizing times** `σ_n = n ∧ T_n ∧ (exit of the box) ∧ (exit of |B| from (−n, n))`, `0` off the good
event. -/
def angLoc (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (fun ω => min (n : ℝ≥0) (T n ω))
    (fun ω => min (hitBox G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

theorem coe_angLoc (n : ℕ) (ω : Ω) : (angLoc G T W VL VR B ζ n ω : WithTop ℝ≥0) =
    min ((min (n : ℝ≥0) (T n ω) : ℝ≥0) : WithTop ℝ≥0)
      (min (hitBox G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) :=
  Sec2.TwoSeed.coe_capTime _ _ ω

theorem angLoc_le_n (n : ℕ) (ω : Ω) : angLoc G T W VL VR B ζ n ω ≤ n :=
  (Sec2.TwoSeed.capTime_le _ _ ω).trans (min_le_left _ _)

theorem angLoc_le_T (n : ℕ) (ω : Ω) : angLoc G T W VL VR B ζ n ω ≤ T n ω :=
  (Sec2.TwoSeed.capTime_le _ _ ω).trans (min_le_right _ _)

theorem angLoc_le_hitBox (n : ℕ) (ω : Ω) :
    (angLoc G T W VL VR B ζ n ω : WithTop ℝ≥0) ≤ hitBox G W VL VR ζ n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_left _ _)

theorem angLoc_le_exitTime (n : ℕ) (ω : Ω) :
    (angLoc G T W VL VR B ζ n ω : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

theorem angLoc_of_not_mem {ω : Ω} (hω : ω ∉ G) (n : ℕ) : angLoc G T W VL VR B ζ n ω = 0 := by
  have h := angLoc_le_hitBox (G := G) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n ω
  simp only [hitBox, hω, ↓reduceIte] at h
  exact le_antisymm (by exact_mod_cast h) bot_le

section StoppingTime

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)

include hgood in
theorem continuous_brownG_ang (ω : Ω) : Continuous (Sec2.TwoSeed.brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using (hgood ω hω).2.1
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
theorem isFilteredBrownianReal_brownG_ang :
    IsFilteredBrownianReal (usualAugmentation 𝓕 P) (Sec2.TwoSeed.brownG G B) P := by
  have := (Ito.isFilteredBrownianReal_modify (Ito.isFilteredBrownianReal_usualAugmentation hE.1) hGm hGc
    fun ω hω => (hgood ω hω).2.1).1
  rwa [Ito.nullAugmented_usualAugmentation] at this

include hgood in
theorem continuousOn_stateAt_ang {ω : Ω} (hω : ω ∈ G) :
    ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := by
  have hF := (hgood ω hω).1.isForcePath
  exact hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
    (continuousOn_pi.2 hF.continuousOn_vR))

include hE hGm hGc hgood in
theorem isStoppingTime_hitBox (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => hitBox G W VL VR ζ n ω := by
  classical
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hτ := Coupling.isStoppingTime_hitBelow_state hWa hVLa hVRa hG0
    (fun ω hω => continuousOn_stateAt_ang hgood hω) (continuous_boxLev n) 0
  intro t
  have e : {ω | hitBox G W VL VR ζ n ω ≤ (t : WithTop ℝ≥0)} = Gᶜ ∪ {ω | (if ω ∈ G then Coupling.hitBelow
      (fun s => boxLev n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else ⊤) ≤ t} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [hitBox, hω]
    · simp only [hitBox, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff, not_false_eq_true,
        true_or, iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [e]
  exact ((usualAugmentation 𝓕 P).mono (zero_le (a := t)) _ hG0).compl.union (hτ t)

include hE hGm hGc hgood in
/-- **The localizing times are stopping times of the usual augmentation**, given that `T` is an announcing
sequence there. -/
theorem isStoppingTime_angLoc (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (angLoc G T W VL VR B ζ n ω : WithTop ℝ≥0) := by
  refine Sec2.TwoSeed.isStoppingTime_capTime ?_
    ((isStoppingTime_hitBox hE hGm hGc hgood n).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_ang hE hGm hGc hgood).2.1 (continuous_brownG_ang hgood) n))
  have h := (isStoppingTime_const (usualAugmentation 𝓕 P) (n : ℝ≥0)).min (hT.1 n)
  convert h using 2 with ω
  push_cast
  rfl

end StoppingTime

/-! ### Pathwise facts on good paths -/

section GoodFacts

variable {ω : Ω} {n : ℕ} (hω : IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
include hω

/-- `σ_n` is strictly before the lifetime. -/
theorem angLoc_lt_lifetime : (angLoc G T W VL VR B ζ n ω : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast angLoc_le_T n ω) (hω.2.2.2.1 n)

include hωG in
theorem boxLev_nonneg_of_lt_angLoc {r : ℝ≥0} (hr : r < angLoc G T W VL VR B ζ n ω) :
    0 ≤ boxLev n (Coupling.stateAt W VL VR r ω) := by
  by_contra hneg
  push Not at hneg
  have hrζ : (r : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast hr.le) (angLoc_lt_lifetime hω)
  have h1 := Coupling.hitBelow_le (f := fun s => boxLev n (Coupling.stateAt W VL VR s ω)) hrζ hneg
  have h2 := angLoc_le_hitBox (G := G) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n ω
  simp only [hitBox, hωG, ↓reduceIte] at h2
  exact absurd (WithTop.coe_le_coe.1 (h2.trans h1)) (not_le.2 hr)

include hωG in
/-- On `[0, σ_n]` the marks are in the level-`n` box, if `σ_n > 0`. -/
theorem boxLev_nonneg_of_le_angLoc (hσ0 : 0 < angLoc G T W VL VR B ζ n ω) {r : ℝ≥0}
    (hr : r ≤ angLoc G T W VL VR B ζ n ω) : 0 ≤ boxLev n (Coupling.stateAt W VL VR r ω) := by
  set σ := angLoc G T W VL VR B ζ n ω with hσ
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω
  rcases hr.lt_or_eq with hlt | heq
  · exact boxLev_nonneg_of_lt_angLoc hω hωG hlt
  · subst heq
    have hat := (Zhan.continuousOn_comp_stateAt (continuous_boxLev n)
      hω.1.isForcePath).continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds hσζ)
    have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact boxLev_nonneg_of_lt_angLoc hω hωG hr'

omit hω in
include hωG in
theorem abs_B_le_of_le_angLoc (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) {r : ℝ≥0}
    (hr0 : 0 < r) (hr : r ≤ angLoc G T W VL VR B ζ n ω) : |B r ω| ≤ n := by
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_ang hgood) hr0
    ((WithTop.coe_le_coe.2 hr).trans (angLoc_le_exitTime n ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

/-- The cross-gap is at least its initial value before `ζ`. -/
theorem le_gap_of_lt {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ ω) : xR 0 - xL 0 ≤ VR 0 r ω - VL 0 r ω := by
  have hF := hω.1.isForcePath
  have h := hF.crossGap_le 0 0 (zero_le (a := r)) hr
  rwa [hF.vR_zero, hF.vL_zero] at h

/-- **Exhaustion**: every time before the lifetime is eventually below `σ_n`. -/
theorem exists_forall_le_angLoc (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
    (hTm : Monotone (T · ω)) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → s ≤ angLoc G T W VL VR B ζ n ω := by
  have hF := hω.1.isForcePath
  have hsub : Icc (0 : ℝ≥0) s ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hs
  have hne : (Icc (0 : ℝ≥0) s).Nonempty := ⟨0, le_rfl, bot_le⟩
  have hstc : ContinuousOn (fun r => ‖(Coupling.stateAt W VL VR r ω).2‖) (Icc 0 s) :=
    ((continuousOn_pi.2 hF.continuousOn_vL).prodMk (continuousOn_pi.2 hF.continuousOn_vR)).norm.mono hsub
  obtain ⟨r₂, hr₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hstc
  obtain ⟨r₃, hr₃, hmax₃⟩ := isCompact_Icc.exists_isMaxOn hne (hω.2.1.abs.continuousOn (s := Icc 0 s))
  obtain ⟨m₀, hm₀⟩ := hω.2.2.2.2 s hs
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (max (s : ℝ) (‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1))
  refine ⟨max m₀ n₁, fun n hn => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_right _ _).trans hn
  have hnR : max (s : ℝ) (‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1) < n :=
    hn₁.trans_le (by exact_mod_cast hn1)
  have hns : (s : ℝ) < n := (le_max_left _ _).trans_lt hnR
  have hnS : ‖(Coupling.stateAt W VL VR r₂ ω).2‖ + |B r₃ ω| + 1 < n := (le_max_right _ _).trans_lt hnR
  have hsT : s ≤ T n ω := hm₀.trans (hTm ((le_max_left _ _).trans hn))
  have hhit : (s : WithTop ℝ≥0) ≤ hitBox G W VL VR ζ n ω := by
    simp only [hitBox, hωG, ↓reduceIte]
    refine Coupling.le_hitBelow fun r hrζ hr => ?_
    by_contra hlt
    push Not at hlt
    have := isMaxOn_iff.1 hmax₂ r ⟨bot_le, hlt.le⟩
    simp only [boxLev] at hr
    have h3 := abs_nonneg (B r₃ ω)
    linarith
  have hexit : (s : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨r, hr, hBr⟩ := (MathFin.exitTime_le_iff (continuous_brownG_ang hgood) n u ω).1 hu.symm.le
    have hus : u < s := by rw [← hu] at hlt; exact WithTop.coe_lt_coe.1 hlt
    have hrs : r ∈ Icc (0 : ℝ≥0) s := ⟨bot_le, hr.2.trans hus.le⟩
    have := isMaxOn_iff.1 hmax₃ r hrs
    simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hBr
    have h2 := norm_nonneg (Coupling.stateAt W VL VR r₂ ω).2
    linarith
  have hsn : s ≤ min (n : ℝ≥0) (T n ω) := le_min (by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact hns.le) hsT
  have h := le_min (WithTop.coe_le_coe.2 hsn) (le_min hhit hexit)
  rw [← coe_angLoc] at h
  exact WithTop.coe_le_coe.1 h

end GoodFacts

/-! ### The coordinates along the path -/

section Coords

/-- The coordinates `(V^L, V^R, I)` on the good event (`(x^L, x^R, 0)` off it). -/
def coordA (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (I : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : SCoord nL (nR + 1) :=
  open scoped Classical in
  if ω ∈ G then (fun i => VL i t ω, fun j => VR j t ω, I t ω) else (xL, xR, 0)

/-- Their density: the force-point velocities and the rate `c` of `I` on the good event (`0` off it). -/
def densA (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (c : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : SCoord nL (nR + 1) :=
  open scoped Classical in
  if ω ∈ G then angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω) (fun j => VR j s.toNNReal ω) (c s ω)
  else 0

/-- The total-variation bound of the coordinates up to `σ_n`. -/
def angKb (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (n : ℕ) (Kc : ℝ) : ℝ :=
  ((nL : ℝ) + 1) * (‖xL‖ + n) + ((nR : ℝ) + 1) * (‖xR‖ + n) + Kc

end Coords

section Mart

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

theorem norm_le_of_boxLev {n : ℕ} {st : ℝ × (Fin (nL + 1) → ℝ) × (Fin (nR + 1) → ℝ)}
    (h : 0 ≤ boxLev n st) : ‖st.2.1‖ ≤ n ∧ ‖st.2.2‖ ≤ n := by
  simp only [boxLev, sub_nonneg] at h
  exact ⟨(norm_fst_le _).trans h, (norm_snd_le _).trans h⟩

include hgood in
/-- **The total variation of the coordinates up to `σ_n`.** -/
theorem integral_norm_densA_le {n : ℕ} {c : ℝ → Ω → ℝ} {Kc : ℝ} {ω : Ω} (hωG : ω ∈ G)
    (hcI : IntervalIntegrable (c · ω) volume 0 (angLoc G T W VL VR B ζ n ω))
    (hcb : ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ), |c s ω| ≤ Kc) :
    ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ), ‖densA G W VL VR c s ω‖ ≤ angKb xL xR n Kc := by
  set σ := angLoc G T W VL VR B ζ n ω with hσdef
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω
  have hKc0 : 0 ≤ Kc := (intervalIntegral.integral_nonneg σ.coe_nonneg fun s _ => abs_nonneg _).trans hcb
  rcases (zero_le (a := σ)).eq_or_lt with h00 | h00
  · rw [← h00, NNReal.coe_zero, intervalIntegral.integral_same]
    unfold angKb; positivity
  have hbox := norm_le_of_boxLev (boxLev_nonneg_of_le_angLoc hω hωG h00 (le_refl σ))
  simp only [Coupling.stateAt] at hbox
  have hL := fun i => (hF.intervalIntegrable_forceL hσζ i).abs
  have hR := fun j => (hF.intervalIntegrable_forceR hσζ j).abs
  have hLs : IntervalIntegrable (fun s => ∑ i, |2 / (VL i s.toNNReal ω - W s.toNNReal ω)|) volume 0 σ := by
    have h1 := IntervalIntegrable.sum Finset.univ fun i _ => hL i
    rw [Finset.sum_fn] at h1; exact h1
  have hRs : IntervalIntegrable (fun s => ∑ j, |2 / (VR j s.toNNReal ω - W s.toNNReal ω)|) volume 0 σ := by
    have h2 := IntervalIntegrable.sum Finset.univ fun j _ => hR j
    rw [Finset.sum_fn] at h2; exact h2
  have hint : IntervalIntegrable (fun s => densA G W VL VR c s ω) volume 0 σ := by
    simp only [densA, hωG, ↓reduceIte, angDens]
    exact intervalIntegrable_scoord (fun i => hF.intervalIntegrable_forceL hσζ i)
      (fun j => hF.intervalIntegrable_forceR hσζ j) hcI
  calc ∫ s in (0 : ℝ)..σ, ‖densA G W VL VR c s ω‖
      ≤ ∫ s in (0 : ℝ)..σ, (∑ i, |2 / (VL i s.toNNReal ω - W s.toNNReal ω)| +
          ∑ j, |2 / (VR j s.toNNReal ω - W s.toNNReal ω)| + |c s ω|) := by
        refine intervalIntegral.integral_mono_on σ.coe_nonneg hint.norm ((hLs.add hRs).add hcI.abs)
          fun s _ => ?_
        refine (norm_scoord_le _).trans (le_of_eq ?_)
        simp only [densA, hωG, ↓reduceIte, angDens]
    _ = ∑ i, (xL i - VL i σ ω) + ∑ j, (VR j σ ω - xR j) + ∫ s in (0 : ℝ)..σ, |c s ω| := by
        rw [intervalIntegral.integral_add (hLs.add hRs) hcI.abs, intervalIntegral.integral_add hLs hRs,
          intervalIntegral.integral_finsetSum fun i _ => hL i,
          intervalIntegral.integral_finsetSum fun j _ => hR j]
        simp only [integral_abs_forceL hF hσζ, integral_abs_forceR hF hσζ]
    _ ≤ angKb xL xR n Kc := by
        have hLi : ∀ i, xL i - VL i σ ω ≤ ‖xL‖ + n := fun i => by
          have h1 : |xL i| ≤ ‖xL‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xL i
          have h2 : |VL i σ ω| ≤ n := by
            rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (fun i => VL i σ ω) i).trans hbox.1
          linarith [le_abs_self (xL i), neg_abs_le (VL i σ ω)]
        have hRj : ∀ j, VR j σ ω - xR j ≤ ‖xR‖ + n := fun j => by
          have h1 : |xR j| ≤ ‖xR‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xR j
          have h2 : |VR j σ ω| ≤ n := by
            rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (fun j => VR j σ ω) j).trans hbox.2
          linarith [le_abs_self (VR j σ ω), neg_abs_le (xR j)]
        have hsL : ∑ i, (xL i - VL i σ ω) ≤ ((nL : ℝ) + 1) * (‖xL‖ + n) := by
          calc ∑ i, (xL i - VL i σ ω) ≤ ∑ _i : Fin (nL + 1), (‖xL‖ + n) :=
                Finset.sum_le_sum fun i _ => hLi i
            _ = _ := by simp; ring
        have hsR : ∑ j, (VR j σ ω - xR j) ≤ ((nR : ℝ) + 1) * (‖xR‖ + n) := by
          calc ∑ j, (VR j σ ω - xR j) ≤ ∑ _j : Fin (nR + 1), (‖xR‖ + n) :=
                Finset.sum_le_sum fun j _ => hRj j
            _ = _ := by simp; ring
        unfold angKb
        linarith

include hE hGm hGc hgood hT in
/-- **The stopped coordinates are adapted** (given an adapted version of the extra coordinate `I`). -/
theorem measurable_coordA_angLoc (n : ℕ) {I : ℝ≥0 → Ω → ℝ}
    (hIK : ∃ K : ℝ≥0 → Ω → ℝ, (∀ s, Measurable[usualAugmentation 𝓕 P s] (K s)) ∧
      ∀ ω ∈ G, ∀ s ≤ angLoc G T W VL VR B ζ n ω, K s ω = I s ω)
    (hIc : ∀ ω ∈ G, ContinuousOn (I · ω) (Iic (angLoc G T W VL VR B ζ n ω))) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      coordA xL xR G VL VR I (min t (angLoc G T W VL VR B ζ n ω)) ω := by
  set σ := angLoc G T W VL VR B ζ n with hσdef
  have hσst := isStoppingTime_angLoc hE hGm hGc hgood hT n
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  obtain ⟨KI', hKI', hKIeq⟩ := hIK
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  set K : ℝ≥0 → Ω → SCoord nL (nR + 1) := fun s ω => ((fun i => killedAt ζ (VL i) s ω),
    (fun j => killedAt ζ (VR j) s ω), KI' s ω) with hKdef
  have hKm : ∀ s, Measurable[usualAugmentation 𝓕 P s] (K s) := fun s => by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (hKI' s))
    · exact @Measurable.of_eval Ω (Fin (nL + 1)) (fun _ => ℝ) (usualAugmentation 𝓕 P s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVLa i) s
    · exact @Measurable.of_eval Ω (Fin (nR + 1)) (fun _ => ℝ) (usualAugmentation 𝓕 P s) _ _ fun j =>
        Sec2.TwoSeed.measurable_killed (hVRa j) s
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => ((fun i => VL i s ω, fun j => VR j s ω, I s ω) : SCoord nL (nR + 1))) hσst hKm hG0
    ((xL, xR, 0) : SCoord nL (nR + 1)) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [coordA, hω, hσdef]
  · have hsζ : (s : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    · simp only [hKdef, killedAt, hsζ, ↓reduceIte]
    · simp only [hKdef, killedAt, hsζ, ↓reduceIte]
    · exact hKIeq ω hω s hs
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk (hIc ω hω))

include hE hGm hGc hgood hT hx in
/-- **The localized Itô formula along the evolution**: for `Φ` of class `C³` on `{D > 0}` and an extra coordinate
`I = ∫ c` (adapted, continuous, with `|I| ≤ K_I` and `∫|c| ≤ K_c` up to `σ_n`),
`Φ(Λ_{t∧σ_n}, B_{t∧σ_n}) − ∫₀^{t∧σ_n} itoGen Φ (Λ_s, B_s) λ_s ds` is a martingale of the usual augmentation. -/
theorem martingale_angLoc {Φ : SCoord nL (nR + 1) × ℝ → ℝ} (hΦ : ContDiffOn ℝ 3 Φ angRegion) (n : ℕ)
    {I : ℝ≥0 → Ω → ℝ} {c : ℝ → Ω → ℝ} {KI Kc : ℝ}
    (hI : ∀ ω ∈ G, ∀ t ≤ angLoc G T W VL VR B ζ n ω, I t ω = ∫ s in (0 : ℝ)..t, c s ω)
    (hcI : ∀ ω ∈ G, IntervalIntegrable (c · ω) volume 0 (angLoc G T W VL VR B ζ n ω))
    (hcb : ∀ ω ∈ G, ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ), |c s ω| ≤ Kc)
    (hIb : ∀ ω ∈ G, ∀ t ≤ angLoc G T W VL VR B ζ n ω, |I t ω| ≤ KI)
    (hIK : ∃ K : ℝ≥0 → Ω → ℝ, (∀ s, Measurable[usualAugmentation 𝓕 P s] (K s)) ∧
      ∀ ω ∈ G, ∀ s ≤ angLoc G T W VL VR B ζ n ω, K s ω = I s ω)
    (hIc : ∀ ω ∈ G, ContinuousOn (I · ω) (Iic (angLoc G T W VL VR B ζ n ω))) :
    Martingale (fun t ω => Φ (coordA xL xR G VL VR I (min t (angLoc G T W VL VR B ζ n ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
          Ito.itoGen Φ (coordA xL xR G VL VR I s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
            (densA G W VL VR c s ω)) (usualAugmentation 𝓕 P) P := by
  set σ := angLoc G T W VL VR B ζ n with hσdef
  have hB' := isFilteredBrownianReal_brownG_ang hE hGm hGc hgood
  have hσst := isStoppingTime_angLoc hE hGm hGc hgood hT n
  have hlam : ∀ ω, IntervalIntegrable (densA G W VL VR c · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · have hF := (hgood ω hω).1.isForcePath
      have hσζ : (σ ω : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime (hgood ω hω)
      simp only [densA, hω, ↓reduceIte, angDens]
      exact intervalIntegrable_scoord (fun i => hF.intervalIntegrable_forceL hσζ i)
        (fun j => hF.intervalIntegrable_forceR hσζ j) (hcI ω hω)
    · simp only [densA, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordA xL xR G VL VR I t ω =
      coordA xL xR G VL VR I 0 ω + ∫ s in (0 : ℝ)..t, densA G W VL VR c s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · have hF := (hgood ω hω).1.isForcePath
      have htζ : (t : ℝ≥0∞) < ζ ω :=
        lt_of_le_of_lt (by exact_mod_cast ht) (angLoc_lt_lifetime (hgood ω hω))
      have hint : IntervalIntegrable (fun s => densA G W VL VR c s ω) volume 0 t :=
        (hlam ω).mono_set (by
          rw [uIcc_of_le t.coe_nonneg, uIcc_of_le (σ ω).coe_nonneg]
          exact Icc_subset_Icc_right (by exact_mod_cast ht))
      have hI0 : I 0 ω = 0 := by rw [hI ω hω 0 bot_le]; simp
      refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
      · simp only [Prod.fst_add, Pi.add_apply, integral_scoord_L hint]
        simp only [coordA, densA, hω, ↓reduceIte, angDens, hF.vL_zero]
        exact hF.vL_eq htζ i
      · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_scoord_R hint]
        simp only [coordA, densA, hω, ↓reduceIte, angDens, hF.vR_zero]
        exact hF.vR_eq htζ j
      · simp only [Prod.snd_add, integral_scoord_T hint]
        simp only [coordA, densA, hω, ↓reduceIte, angDens, hI0, zero_add]
        exact hI ω hω t ht
    · simp only [coordA, densA, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densA G W VL VR c s ω‖ ≤ angKb xL xR n Kc := by
    intro ω
    by_cases hω : ω ∈ G
    · exact integral_norm_densA_le hgood hω (hcI ω hω) (hcb ω hω)
    · simp only [densA, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
        by_contra h
        rw [not_nonempty_iff_eq_empty] at h
        have hP := hE.1.isProbabilityMeasure'
        rw [h, compl_empty, measure_univ] at hGc
        exact one_ne_zero hGc
      have hKc0 : 0 ≤ Kc :=
        (intervalIntegral.integral_nonneg (σ ω₀).coe_nonneg fun s _ => abs_nonneg _).trans (hcb ω₀ hω₀)
      unfold angKb; positivity
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordA xL xR G VL VR I t ω, Sec2.TwoSeed.brownG G B t ω) ∈ angKc xL xR n KI (xR 0 - xL 0) := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · have hω' := hgood ω hω
      have hF := hω'.1.isForcePath
      rcases (zero_le (a := t)).eq_or_lt with ht0 | ht0
      · subst ht0
        have hI0 : I 0 ω = 0 := by rw [hI ω hω 0 bot_le]; simp
        refine Set.mem_insert_iff.2 (Or.inl ?_)
        have e1 : (fun i => VL i 0 ω) = xL := funext hF.vL_zero
        have e2 : (fun j => VR j 0 ω) = xR := funext hF.vR_zero
        simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, e1, e2, hI0, hω'.2.2.1, angInit]
      have hσ0 : 0 < σ ω := ht0.trans_le ht
      have htζ : (t : ℝ≥0∞) < ζ ω :=
        lt_of_le_of_lt (by exact_mod_cast ht) (angLoc_lt_lifetime hω')
      have hbox := norm_le_of_boxLev (boxLev_nonneg_of_le_angLoc hω' hω hσ0 ht)
      simp only [Coupling.stateAt] at hbox
      refine mem_insert_of_mem _ ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [coordA, hω, ↓reduceIte] using hbox.1
      · simpa only [coordA, hω, ↓reduceIte] using hbox.2
      · simpa only [coordA, hω, ↓reduceIte] using hIb ω hω t ht
      · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using abs_B_le_of_le_angLoc hω hgood ht0 ht
      · simpa only [gapD, coordA, hω, ↓reduceIte] using le_gap_of_lt hω' htζ
    · simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  have hΛm := measurable_coordA_angLoc hE hGm hGc hgood hT n hIK hIc
  exact Ito.martingale_itoLocalized hB' (continuous_brownG_ang hgood) isOpen_angRegion hΦ
    (isCompact_angKc xL xR n KI (xR 0 - xL 0)) (angKc_subset xL xR hx hx n KI) hσst hΛm hlam hΛ hKb hK

end Mart

end Loc

end Clock

end Sec7

end InteractingSLE
