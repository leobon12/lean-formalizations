/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefFullDil
import InteractingSLE.Spec.Sec7.Lemma725RefStop
import InteractingSLE.Spec.Sec7.Aux50Ge8Main
import InteractingSLE.Spec.Sec7.Aux126

/-!
# Aux. lemma 126: from one stopped graph to the determined two-seed coupling; the reference of Lemma 7.25

Packet PROVE-LEMMA725REF2. Specification §7.4, Aux. lemma 126's proof (`source/spec/p385-432.md` L251–L316,
pp. 401–402), "Universal field determination":

> Dilating the reference extension constructed above therefore gives, for each `R_n`, a full original two-seed coupling
> whose stopped history at `S_{R_n}` is determined by its whole field. At this stage finite-time continuity has already
> been proved from the driving marginal alone. **Aux.** lemma 50 therefore applies to every original two-seed coupling
> through the bounded stop `S_{R_n}`. […] Together with integrated driving uniqueness this identifies the full joint
> law of the whole field and the stopped history. Comparing with the dilated reference transfers its graph to every
> original coupling. […] Since `S_{R_n} ↑ ∞`, this gives a Borel function recovering the entire driving evolution in
> every original coupling.

This file proves the remaining step `Lemma725RefStop.StoppedToFullDeterminationStatement` of PROVE-LEMMA725REF, given
finite-time continuity of the two-seed traces (`stoppedToFullDetermination_of_trace`), and with it Lemma 7.25's
determination reference from its reference alone (`lemma725DetReferenceStatement_of_reference`).

## Proof

Let `C = (W, h)` be the coupling with a field-determined history stopped at the capped local stop of radius `r`, and
`K` its killed dyadic history (`LawUnique.killedHistory`; the lifetime is infinite).

1. **The stop read from the dyadic history** (`dyStop`): `S_R = (R²/64) ∧ inf {dyadic t : |W_t| > R/4}`; for a
   continuous driver this is the capped local stop (`dyExit_eq_hitBelow`: the exit set is open, so its infimum is
   approached by the dyadic times `upperDyadic`). Hence the dyadic history stopped at `S_r`
   (`Sec4.stopHistory (dyStop r) K`) is a measurable function `histOfStopped` of the recorded stopped history, so it is
   a Borel function `g` of the field.
2. **Transfer to the dilations.** For `c = 4ⁿ` the dilated coupling `C^c` (`IsOptionalHullCoupling.dilate`, field
   `h(2ⁿ ·)`) is again a two-seed coupling with a continuous trace; Aux. lemma 50 and Theorem 2.2's uniqueness give one
   joint law of the field and the killed history (`Aux50.map_prod_killedHistory_eq` with `Aux50Ge8.hasTraceStopKernel`).
   The identity `(stopHistory (dyStop r) K)_q = g(h)_q`, a measurable event of that pair, therefore holds in `C^c`.
3. **Back to `C`.** At the dyadic index `q = (m + 2n, k)` (time `k/2^{m+2n}`), the dilated history is `2⁻ⁿ K_{(m,k)}`,
   and it is not yet stopped once `2ⁿ r` exceeds the running maximum of `|W|` and `4ⁿ r²/64` exceeds `k/2^m`. So
   `2ⁿ g(h(2ⁿ ·))_q → K_{(m,k)}`, and `K` is a Borel function of `h` (`IsAEDeterminedBy.of_tendsto`).

## Main results

* `stoppedToFullDetermination_of_trace`: `StoppedToFullDeterminationStatement κ rL rR` for `κ > 0`, `rL, rR > −2`, if
  every two-seed evolution has a continuous trace through its lifetime;
* **`lemma725DetReferenceStatement_of_reference`**: `Aux50Hit.Lemma725DetReferenceStatement` from
  `Lemma725ReferenceStatement` alone (with Aux. lemma 126's trace part `Aux126.lemma725TraceStatement_of_reference`),
  and `lemma725DetReferenceStatement_of_pocketWordField'` from the pocket inputs alone.

Ruling R48: nothing here takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma725RefFull

open LawUnique

/-! ### The local stop read from the dyadic history -/

section DyStop

/-- The first dyadic time at which the driver exceeds `R / 4` in absolute value (`⊤` if there is none). -/
def dyExit (R : ℝ) (x : HistorySpace 1 1) : ℝ≥0∞ :=
  ⨅ p : ℕ × ℕ, if R / 4 < |(x.2 p).1| then (dyadicTime p : ℝ≥0∞) else ⊤

/-- **The local stop `S_R = (R²/64) ∧ inf {t : |W_t| > R/4}` read from the dyadic history.** -/
def dyStop (R : ℝ) (x : HistorySpace 1 1) : ℝ≥0 :=
  (min (LocalExt.stopHorizon R : ℝ≥0∞) (dyExit R x)).toNNReal

theorem measurable_dyExit (R : ℝ) : Measurable (dyExit R) := by
  refine Measurable.iInf fun p => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((measurable_pi_apply p).comp measurable_snd).fst)

theorem measurable_dyStop (R : ℝ) : Measurable (dyStop R) :=
  ENNReal.measurable_toNNReal.comp (measurable_const.min (measurable_dyExit R))

/-- A lower bound for the dyadic exit time: no dyadic time before `t` exceeds the level. -/
theorem le_dyExit {R : ℝ} {x : HistorySpace 1 1} {t : ℝ≥0∞}
    (h : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < t → |(x.2 p).1| ≤ R / 4) : t ≤ dyExit R x := by
  refine le_iInf fun p => ?_
  split_ifs with hp
  · by_contra hlt
    exact absurd (h p (not_le.1 hlt)) (not_le.2 hp)
  · exact le_top

/-- **For a continuous driver, the dyadic exit time is the exit time**: the exit set `{t : |w_t| > R/4}` is open, so its
infimum is the limit of the dyadic times `upperDyadic s n ↓ s` at any of its points `s`. -/
theorem dyExit_eq_hitBelow (R : ℝ) {w : ℝ≥0 → ℝ} (hw : Continuous w) {x : HistorySpace 1 1}
    (hx : ∀ p, (x.2 p).1 = w (dyadicTime p)) :
    dyExit R x = (Coupling.hitBelow (LocalExt.stopGap R w) ⊤ 0 : ℝ≥0∞) := by
  have hO : ∀ s : ℝ≥0, (s ∈ {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤ ∧ LocalExt.stopGap R w s < 0} ↔ R / 4 < |w s|) := by
    intro s
    simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, LocalExt.stopGap, sub_neg]
  unfold Coupling.hitBelow
  split_ifs with hne
  · change dyExit R x = ((sInf {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤ ∧ LocalExt.stopGap R w s < 0} : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_sInf hne]
    refine le_antisymm (le_iInf₂ fun s hs => ?_) (le_iInf fun p => ?_)
    · have hopen : IsOpen {t : ℝ≥0 | R / 4 < |w t|} := isOpen_lt continuous_const (continuous_abs.comp hw)
      have hev : ∀ᶠ n in atTop, dyadicTime (upperDyadic s n) ∈ {t : ℝ≥0 | R / 4 < |w t|} :=
        (tendsto_dyadicTime_upperDyadic s).eventually (hopen.mem_nhds ((hO s).1 hs))
      have hle : ∀ᶠ n in atTop, dyExit R x ≤ (dyadicTime (upperDyadic s n) : ℝ≥0∞) := by
        filter_upwards [hev] with n hn
        refine (iInf_le _ (upperDyadic s n)).trans ?_
        have hc : R / 4 < |(x.2 (upperDyadic s n)).1| := by rw [hx]; exact hn
        simp only [hc, ↓reduceIte, le_refl]
      exact ge_of_tendsto ((ENNReal.continuous_coe.tendsto s).comp (tendsto_dyadicTime_upperDyadic s)) hle
    · split_ifs with hp
      · exact iInf₂_le (dyadicTime p) ((hO _).2 (by rwa [hx] at hp))
      · exact le_top
  · refine iInf_eq_top.2 fun p => ?_
    split_ifs with hp
    · exact absurd ⟨dyadicTime p, (hO _).2 (by rwa [hx] at hp)⟩ hne
    · rfl

/-- **The dyadic local stop is the local stop** of a continuous driver with infinite lifetime. -/
theorem coe_dyStop_eq_localStopPath (R : ℝ) {w : ℝ≥0 → ℝ} (hw : Continuous w) {x : HistorySpace 1 1}
    (hx : ∀ p, (x.2 p).1 = w (dyadicTime p)) :
    ((dyStop R x : ℝ≥0) : WithTop ℝ≥0) = LocalExt.localStopPath R ⊤ w := by
  have hlt : min (LocalExt.stopHorizon R : ℝ≥0∞) (dyExit R x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  change ((dyStop R x : ℝ≥0) : ℝ≥0∞) = min (LocalExt.stopHorizon R : ℝ≥0∞)
    (Coupling.hitBelow (LocalExt.stopGap R w) ⊤ 0 : ℝ≥0∞)
  rw [dyStop, ENNReal.coe_toNNReal hlt, dyExit_eq_hitBelow R hw hx]

end DyStop

/-! ### The dyadic history of a recorded stopped history -/

section Stopped

/-- The dyadic rational `k / 2ⁿ` of the index `(n, k)`. -/
def dyRat (p : ℕ × ℕ) : ℚ≥0 := (p.2 : ℚ≥0) / 2 ^ p.1

theorem coe_dyRat (p : ℕ × ℕ) : ((dyRat p : ℚ≥0) : ℝ≥0) = dyadicTime p := by
  simp [dyRat, dyadicTime]

/-- **The dyadic history of a recorded stopped history** `(τ, (X_{q ∧ τ})_{q ∈ ℚ≥0})`: lifetime `τ`, the value `X_p` at
the dyadic times `p ≤ τ`, `0` after. -/
def histOfStopped (z : WithTop ℝ≥0 × (ℚ≥0 → DrivingValue 1 1)) : HistorySpace 1 1 :=
  (((z.1.untopD 0 : ℝ≥0) : ℝ≥0∞), fun p => if dyadicTime p ≤ z.1.untopD 0 then z.2 (dyRat p) else 0)

theorem measurable_histOfStopped : Measurable histOfStopped := by
  have h1 : Measurable fun z : WithTop ℝ≥0 × (ℚ≥0 → DrivingValue 1 1) => (z.1.untopD 0 : ℝ≥0) :=
    ENNReal.measurable_toNNReal.comp measurable_fst
  refine (measurable_coe_nnreal_ennreal.comp h1).prodMk (measurable_pi_iff.2 fun p => ?_)
  exact Measurable.ite (measurableSet_le measurable_const h1) ((measurable_pi_apply _).comp measurable_snd)
    measurable_const

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem killedHistory_apply_of_top {ω : Ω} (hζ : ζ ω = ⊤) (p : ℕ × ℕ) :
    (killedHistory W VL VR ζ ω).2 p = (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω),
      fun i => VR i (dyadicTime p) ω) := by
  simp only [killedHistory, hζ, ENNReal.coe_lt_top, ↓reduceIte]

/-- **On a good path with infinite lifetime, the dyadic history stopped at the dyadic local stop is read off the
recorded history stopped at the capped local stop.** -/
theorem histOfStopped_stoppedHistory {G : Set Ω} (R : ℝ) {ω : Ω} (hω : ω ∈ G) (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) :
    histOfStopped (stoppedHistory (completedState W VL VR ζ) (LocalExt.capStop R G ζ W) ω) =
      Sec4.stopHistory (dyStop R) (killedHistory W VL VR ζ ω) := by
  have hx : ∀ p, ((killedHistory W VL VR ζ ω).2 p).1 = W (dyadicTime p) ω := fun p => by
    rw [killedHistory_apply_of_top hζ]
  have hcap : LocalExt.capStop R G ζ W ω = ((dyStop R (killedHistory W VL VR ζ ω) : ℝ≥0) : WithTop ℝ≥0) := by
    rw [coe_dyStop_eq_localStopPath R hw hx, LocalExt.capStop, LocalExt.localStop_of_mem hω, hζ]
    exact min_eq_left le_top
  refine Prod.ext ?_ (funext fun p => ?_)
  · simp only [histOfStopped, stoppedHistory, Sec4.stopHistory, hcap, WithTop.untopD_coe]
  · simp only [histOfStopped, stoppedHistory, Sec4.stopHistory, hcap, WithTop.untopD_coe]
    split_ifs with hp
    · rw [stopAt_of_eq_coe hcap, coe_dyRat, min_eq_left hp, killedHistory_apply_of_top hζ]
      simp only [completedState, hζ, ENNReal.coe_lt_top, ↓reduceIte, drivingState]
    · rfl

end Stopped

/-! ### The dilations `c = 4ⁿ` read on the dyadic history -/

section Dilations

open _root_.InteractingSLE.Sec7.Dilation

/-- The dyadic index `(m + 2n, k)`: the time `k / 2^m` divided by `4ⁿ`. -/
def shiftIdx (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + 2 * n, p.2)

theorem four_pow_mul_dyadicTime_shiftIdx (n : ℕ) (p : ℕ × ℕ) :
    (4 : ℝ≥0) ^ n * dyadicTime (shiftIdx n p) = dyadicTime p := by
  have h2 : (2 : ℝ≥0) ^ p.1 ≠ 0 := pow_ne_zero _ two_ne_zero
  have h4 : (4 : ℝ≥0) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [dyadicTime, shiftIdx]
  rw [pow_add, pow_mul, show (2 : ℝ≥0) ^ 2 = 4 by norm_num]
  field_simp

theorem sqrt_four_pow (n : ℕ) : √(((4 : ℝ≥0) ^ n : ℝ≥0) : ℝ) = 2 ^ n := by
  rw [NNReal.coe_pow, show ((4 : ℝ≥0) : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
  exact Real.sqrt_sq (by positivity)

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The killed history of the dilated process, at an infinite lifetime. -/
theorem killedHistory_dil_apply {c : ℝ≥0} {ω : Ω} (hζ : ζ ω = ⊤) (q : ℕ × ℕ) :
    (killedHistory (dilProc c W) (fun i => dilProc c (VL i)) (fun j => dilProc c (VR j)) (fun ω => ζ ω / c) ω).2 q =
      stateMul (√(c : ℝ))⁻¹ (W (c * dyadicTime q) ω, (fun i => VL i (c * dyadicTime q) ω),
        fun j => VR j (c * dyadicTime q) ω) := by
  have hζc : ζ ω / c = ⊤ := by rw [hζ]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top
  rw [killedHistory_apply_of_top (ζ := fun ω => ζ ω / c) hζc]
  rfl

theorem killedHistory_four_pow_shiftIdx {n : ℕ} {ω : Ω} (hζ : ζ ω = ⊤) (p : ℕ × ℕ) :
    (killedHistory (dilProc ((4 : ℝ≥0) ^ n) W) (fun i => dilProc ((4 : ℝ≥0) ^ n) (VL i))
        (fun j => dilProc ((4 : ℝ≥0) ^ n) (VR j)) (fun ω => ζ ω / ((4 : ℝ≥0) ^ n : ℝ≥0)) ω).2 (shiftIdx n p) =
      stateMul ((2 : ℝ) ^ n)⁻¹ ((killedHistory W VL VR ζ ω).2 p) := by
  rw [killedHistory_dil_apply hζ, four_pow_mul_dyadicTime_shiftIdx, sqrt_four_pow,
    killedHistory_apply_of_top hζ]

/-- **The dilated history is not yet stopped at a fixed dyadic time, for all large `n`**: once `2ⁿ r/4` exceeds the
running maximum of `|w|` up to `k/2^m` and `4ⁿ r²/64` exceeds `k/2^m`. -/
theorem eventually_le_dyStop {r : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) (hr : 0 < r) (p : ℕ × ℕ)
    {x : ℕ → HistorySpace 1 1}
    (hx : ∀ n q, ((x n).2 q).1 = ((2 : ℝ) ^ n)⁻¹ * w ((4 : ℝ≥0) ^ n * dyadicTime q)) :
    ∀ᶠ n in atTop, dyadicTime (shiftIdx n p) ≤ dyStop r (x n) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := dyadicTime p)).exists_bound_of_continuousOn
    hw.continuousOn
  have h4 : Tendsto (fun n : ℕ => (4 : ℝ) ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h2 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * M) atTop (𝓝 (0 * M)) :=
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))).mul_const M
  rw [zero_mul] at h2
  have hr64 : 0 < r ^ 2 / 64 := by positivity
  have e1 : ∀ᶠ n : ℕ in atTop, (dyadicTime p : ℝ) / (r ^ 2 / 64) ≤ (4 : ℝ) ^ n := h4.eventually_ge_atTop _
  have e2 : ∀ᶠ n : ℕ in atTop, ((2 : ℝ) ^ n)⁻¹ * M ≤ r / 4 := h2.eventually (ge_mem_nhds (by positivity))
  filter_upwards [e1, e2] with n hn1 hn2
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have htime : ((4 : ℝ≥0) ^ n * dyadicTime (shiftIdx n p) : ℝ≥0) = dyadicTime p :=
    four_pow_mul_dyadicTime_shiftIdx n p
  have htimeR : (4 : ℝ) ^ n * (dyadicTime (shiftIdx n p) : ℝ) = dyadicTime p := by
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) htime
    simpa using this
  have hne : min (LocalExt.stopHorizon r : ℝ≥0∞) (dyExit r (x n)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  refine ENNReal.le_toNNReal_of_coe_le (le_min ?_ (le_dyExit fun q hq => ?_)) hne
  · refine ENNReal.coe_le_coe.2 ?_
    rw [← NNReal.coe_le_coe, LocalExt.coe_stopHorizon]
    rw [div_le_iff₀ hr64] at hn1
    nlinarith
  · have hq : dyadicTime q < dyadicTime (shiftIdx n p) := ENNReal.coe_lt_coe.1 hq
    have hmem : (4 : ℝ≥0) ^ n * dyadicTime q ∈ Icc (0 : ℝ≥0) (dyadicTime p) :=
      ⟨zero_le, htime ▸ mul_le_mul_of_nonneg_left hq.le zero_le⟩
    have hb := hM _ hmem
    rw [Real.norm_eq_abs] at hb
    rw [hx, abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
    calc ((2 : ℝ) ^ n)⁻¹ * |w ((4 : ℝ≥0) ^ n * dyadicTime q)| ≤ ((2 : ℝ) ^ n)⁻¹ * M :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ r / 4 := hn2

end Dilations

/-! ### The assembly -/

section Assembly

open _root_.InteractingSLE.Sec7.Dilation

/-- The two-seed positions are invariant under the dilation. -/
theorem twoSeedX_dil (c : ℝ≥0) : (fun i => (√(c : ℝ))⁻¹ * LP.twoSeedXL i) = LP.twoSeedXL := by
  funext i
  simp [LP.twoSeedXL]

theorem twoSeedXR_dil (c : ℝ≥0) : (fun i => (√(c : ℝ))⁻¹ * LP.twoSeedXR i) = LP.twoSeedXR := by
  funext i
  simp [LP.twoSeedXR]

/-- **Transfer of one coordinate identity along equal joint laws** of the field and the killed history. -/
theorem ae_coord_eq_of_map_eq {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    {K₁ : Ω₁ → HistorySpace 1 1} {K₂ : Ω₂ → HistorySpace 1 1} (hm₁ : Measurable fun ω => (h₁ ω, K₁ ω))
    (hm₂ : Measurable fun ω => (h₂ ω, K₂ ω))
    (hmap : P₁.map (fun ω => (h₁ ω, K₁ ω)) = P₂.map (fun ω => (h₂ ω, K₂ ω)))
    {F : HistorySpace 1 1 → DrivingValue 1 1} (hF : Measurable F) {g : DistOn upperHalfPlaneOpens → DrivingValue 1 1}
    (hg : Measurable g) (h₁e : ∀ᵐ ω ∂P₁, F (K₁ ω) = g (h₁ ω)) : ∀ᵐ ω ∂P₂, F (K₂ ω) = g (h₂ ω) := by
  have hE : MeasurableSet {x : DistOn upperHalfPlaneOpens × HistorySpace 1 1 | F x.2 = g x.1} :=
    measurableSet_eq_fun (hF.comp measurable_snd) (hg.comp measurable_fst)
  have h1 : ∀ᵐ x ∂(P₁.map fun ω => (h₁ ω, K₁ ω)), x ∈ {x : DistOn upperHalfPlaneOpens × HistorySpace 1 1 |
      F x.2 = g x.1} := (ae_map_iff hm₁.aemeasurable hE).2 h₁e
  rw [hmap] at h1
  exact (ae_map_iff hm₂.aemeasurable hE).1 h1

/-- **Aux. lemma 126, from one stopped graph to the determined coupling** (pp. 401–402), given finite-time continuity
of the two-seed traces: the named input `Lemma725RefStop.StoppedToFullDeterminationStatement` of PROVE-LEMMA725REF,
for `κ > 0` and seed weights `rL, rR > −2`. The coupling with the stopped graph itself has a field-determined killed
driving history. -/
theorem stoppedToFullDetermination_of_trace {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (htr : ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) :
    Lemma725RefStop.StoppedToFullDeterminationStatement.{u} κ rL rR := by
  rintro ⟨r, hr, Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, G, hGm, hG0, hG, hdet⟩
  refine ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, ?_⟩
  obtain ⟨Kk, hKm, hK₁, hK₂⟩ := Aux50Ge8.hasTraceStopKernel.{u, u} hκ hL hR
  have hT := R7.ae_lifetime_eq_top hκ hL hR hC.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hpath := hC.1.2.2.2.2
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG0
  -- the good paths: infinite lifetime and a continuous driver
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous fun t => W t ω := by
    filter_upwards [hT, hpath] with ω hζ hp
    refine ⟨hζ, continuousOn_univ.1 ?_⟩
    have h1 := hp.2.2.2.1
    rwa [hζ, show {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ from eq_univ_of_forall fun _ => ENNReal.coe_lt_top] at h1
  -- step 1: the dyadic history stopped at radius `r` is a Borel function `g` of the field
  have hY : IsAEDeterminedBy P h fun ω => Sec4.stopHistory (dyStop r) (killedHistory W VL VR ζ ω) := by
    refine (hdet.comp measurable_histOfStopped).congr_ae ?_
    filter_upwards [hGae, hgood] with ω hωG hω
    exact histOfStopped_stoppedHistory r hωG hω.1 hω.2
  obtain ⟨g, hg, hYg⟩ := hY
  have hm₁ : Measurable fun ω => (h ω, killedHistory W VL VR ζ ω) := hC.2.1.prodMk (measurable_killedHistory hX)
  have htr₁ := htr P 𝓕 W VL VR B ζ hC.1
  -- step 2: the identity transfers to every dilation `c = 4ⁿ`, coordinatewise
  have hc : ∀ n : ℕ, ((4 : ℝ≥0) ^ n) ≠ 0 := fun n => pow_ne_zero _ (by norm_num)
  have hrn : ∀ n : ℕ, 0 < (√(((4 : ℝ≥0) ^ n : ℝ≥0) : ℝ))⁻¹ := fun n => inv_pos.2 (sqrt_pos_of_ne (hc n))
  have htrans : ∀ (n : ℕ) (q : ℕ × ℕ), ∀ᵐ ω ∂P,
      (Sec4.stopHistory (dyStop r) (killedHistory (dilProc ((4 : ℝ≥0) ^ n) W)
        (fun i => dilProc ((4 : ℝ≥0) ^ n) (VL i)) (fun j => dilProc ((4 : ℝ≥0) ^ n) (VR j))
        (fun ω => ζ ω / ((4 : ℝ≥0) ^ n : ℝ≥0)) ω)).2 q = (g (dilField (hrn n) (h ω))).2 q := by
    intro n q
    have hCn := IsOptionalHullCoupling.dilate (hc n) hC
    rw [twoSeedX_dil, twoSeedXR_dil] at hCn
    obtain ⟨hXn, -⟩ := hCn.2.2.2
    have hmap := Aux50.map_prod_killedHistory_eq hκ hL hR hKm hK₁ hK₂ hC htr₁ hCn
      (htr P _ _ _ _ _ _ hCn.1)
    have hm₂ : Measurable fun ω => (dilField (hrn n) (h ω), killedHistory (dilProc ((4 : ℝ≥0) ^ n) W)
        (fun i => dilProc ((4 : ℝ≥0) ^ n) (VL i)) (fun j => dilProc ((4 : ℝ≥0) ^ n) (VR j))
        (fun ω => ζ ω / ((4 : ℝ≥0) ^ n : ℝ≥0)) ω) := hCn.2.1.prodMk (measurable_killedHistory hXn)
    refine ae_coord_eq_of_map_eq hm₁ hm₂ hmap (F := fun x => (Sec4.stopHistory (dyStop r) x).2 q)
      ((measurable_pi_apply q).comp ((Sec4.measurable_stopHistory (measurable_dyStop r)).snd))
      ((measurable_pi_apply q).comp hg.snd) ?_
    filter_upwards [hYg] with ω hω
    rw [hω]
    rfl
  -- step 3: each coordinate of the killed history is a limit of determined variables
  have hcoord : ∀ p : ℕ × ℕ, IsAEDeterminedBy P h fun ω => (killedHistory W VL VR ζ ω).2 p := by
    intro p
    refine IsAEDeterminedBy.of_tendsto hC.2.1 (Y := fun n ω => stateMul ((2 : ℝ) ^ n)
      ((g (dilField (hrn n) (h ω))).2 (shiftIdx n p))) (fun n => ⟨fun x => stateMul ((2 : ℝ) ^ n)
      ((g (dilField (hrn n) x)).2 (shiftIdx n p)), (measurable_stateMul _).comp
      ((measurable_pi_apply _).comp (hg.comp (measurable_dilField _)).snd), ae_of_all _ fun _ => rfl⟩) ?_
    filter_upwards [hgood, ae_all_iff.2 fun n => htrans n (shiftIdx n p)] with ω hω htω
    have hx : ∀ n q, ((killedHistory (dilProc ((4 : ℝ≥0) ^ n) W) (fun i => dilProc ((4 : ℝ≥0) ^ n) (VL i))
        (fun j => dilProc ((4 : ℝ≥0) ^ n) (VR j)) (fun ω => ζ ω / ((4 : ℝ≥0) ^ n : ℝ≥0)) ω).2 q).1 =
        ((2 : ℝ) ^ n)⁻¹ * (fun t => W t ω) ((4 : ℝ≥0) ^ n * dyadicTime q) := by
      intro n q
      rw [killedHistory_dil_apply hω.1, sqrt_four_pow]
      rfl
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [eventually_le_dyStop hω.2 hr p hx] with n hn
    rw [← htω n, Sec4.stopHistory]
    simp only [hn, ↓reduceIte]
    rw [killedHistory_four_pow_shiftIdx hω.1, stateMul_stateMul_inv (pow_ne_zero n two_ne_zero)]
  -- the killed history is determined, hence the coupling is field-determined
  have hK : IsAEDeterminedBy P h (killedHistory W VL VR ζ) := by
    have h1 : IsAEDeterminedBy P h ζ :=
      (isAEDeterminedBy_const (⊤ : ℝ≥0∞)).congr_ae (hT.mono fun ω hω => hω.symm)
    exact (h1.prodMk (isAEDeterminedBy_pi hcoord)).congr_ae (ae_of_all _ fun ω => rfl)
  refine Prop73Ref.isFieldDeterminedHistory_of_isAEDeterminedBy hK ?_
  filter_upwards [hpath] with ω hp
  exact ⟨hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩

end Assembly

/-! ### Lemma 7.25's determination reference -/

/-- **Aux. lemma 126's remaining step from the reference of Lemma 7.25**: for `κ > 4` and both seed weights in
`(−2, κ/2 − 4)`, `StoppedToFullDeterminationStatement` holds; the trace input is Aux. lemma 126's finite-time continuity
(`Aux126.lemma725TraceStatement_of_reference`, from the same reference). -/
theorem stoppedToFullDeterminationStatement_of_reference (hRef : Lemma725ReferenceStatement.{u}) {κ : ℝ}
    (hκ : 4 < κ) {rL rR : ℝ} (hL : -2 < rL) (hLd : rL < κ / 2 - 4) (hR : -2 < rR) (hRd : rR < κ / 2 - 4) :
    Lemma725RefStop.StoppedToFullDeterminationStatement.{u} κ rL rR :=
  stoppedToFullDetermination_of_trace (by linarith) hL hR fun P _ 𝓕 W VL VR B ζ hE =>
    Aux126.lemma725TraceStatement_of_reference hRef κ hκ rL rR hL hLd hR hRd P 𝓕 W VL VR B ζ hE

/-- **Lemma 7.25's determination reference (`href725`) from its reference alone** (Aux. lemma 126 with all of its proof:
the exact stopped two-seed coupling `Lemma725RefStop.exists_twoSeed_stoppedGraph_of_reference`, finite-time continuity
by dilation of the driving law, and universal field determination, `stoppedToFullDetermination_of_trace`). -/
theorem lemma725DetReferenceStatement_of_reference (hRef : Lemma725ReferenceStatement.{u}) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  Lemma725RefStop.lemma725DetReferenceStatement_of_ref hRef fun _ hκ _ _ hL hLd hR hRd =>
    stoppedToFullDeterminationStatement_of_reference hRef hκ hL hLd hR hRd

/-- **Lemma 7.25's determination reference (`href725`) from the pocket inputs alone**: the `P`-side pockets with their
distant marks (`Lemma725RefK2.PocketWordFieldStatement`, Aux. lemmas 119–125 in the fixed-exterior form of ruling R52)
give the reference (Aux. lemma 127), and Aux. lemma 126 is now proved. -/
theorem lemma725DetReferenceStatement_of_pocketWordField'
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Lemma725RefK2.PocketWordFieldStatement.{u} κ rL rR) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  lemma725DetReferenceStatement_of_reference (Lemma725RefK2.lemma725ReferenceStatement_of_pocketWordField h)

end Lemma725RefFull

end Sec7

end InteractingSLE
