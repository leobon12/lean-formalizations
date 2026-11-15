/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.SeparatedJacobi
import InteractingSLE.Spec.Zhan.SeparatedShift
import InteractingSLE.Spec.Zhan.TwoForceSeed
import InteractingSLE.Spec.Sec2.JacobiExists

/-!
# From the seed to a separated pair: the restart at a ratio-hitting time

Packet PROVE-ZHAN-B3. Astra, *Formalization proofs and dependency audit* (ruling R35), L1416–L1419: "For any
separated pair `p_L < 0 < p_R`, stop the seed law when `R/L = p_R/(−p_L)`; recurrence makes this finite. Affine
normalization gives exactly that separated pair. Strong Markov … transfer the proved limit."

Here, for `0 < κ ≤ 4`, weights `ρ_L, ρ_R ≥ κ/2 − 2` and a ratio `r > 0`:

* `measure_exists_ratio_pos`: the two-seed evolution (marks at `0⁻, 0⁺`) reaches, with positive probability, a time
  with separation `V^R − V^L ≥ 1` and `R = r L` (`L = W − V^L`, `R = V^R − W`): its logarithmic-clock angle
  `U = L/(L + R)` solves the Jacobi martingale problem (`Sec2.TwoSeed.exists_isJacobiMP_logAngle`), which hits the
  level `1/(1 + r)` after time `0` with positive probability (`IsJacobiMP.measure_exists_eq_pos`);
* the first such time is a stopping time of the usual augmentation (`MathFin.exitTime` of a continuous adapted
  process built on a full-measure good event); capped at `n + 1` it is positive;
* the restart there (`Sec7.RandRestart.measure_restart_codeEvent`, Borel trace coding `traceCodeSet`) and the
  transience of the seed trace (`Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed`), transferred to the
  restarted driver pathwise (`traceEvent_shiftNN`), show that the canonical probability of the trace event is `1` at
  almost every realized word `(−L, rL)`.

## Main result

* `exists_codeLaw_traceCodeSet_eq_one`: for every `r > 0` there is `λ > 0` with
  `codeLaw κ ρL ρR traceCodeSetᶜ (−λ, rλ) = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec7.RandRestart (TraceEvent traceCodeSet codeLaw wordAt)

/-! ### One mark on each side -/

/-- With one mark on each side, the side partial sums are admissible iff both weights are at least `k/2 − 2`. -/
theorem hasAdmissiblePartialSums_one {k : ℝ} {ρL ρR : Fin 1 → ℝ} (hL : k / 2 - 2 ≤ ρL 0)
    (hR : k / 2 - 2 ≤ ρR 0) (xL xR : Fin 1 → ℝ) : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR := by
  refine ⟨fun x _ ⟨i, hi⟩ => ?_, fun x _ ⟨i, hi⟩ => ?_⟩
  · have e : (Finset.univ.filter fun j => x < xL j) = Finset.univ := by
      ext j
      fin_cases j; fin_cases i
      simpa using hi
    rw [e, Fin.sum_univ_one]
    exact hL
  · have e : (Finset.univ.filter fun j => xR j ≤ x) = Finset.univ := by
      ext j
      fin_cases j; fin_cases i
      simpa using hi
    rw [e, Fin.sum_univ_one]
    exact hR

/-! ### The ratio `R/L` takes every value with positive probability -/

section Ratio

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The event that at some time before the lifetime the separation is at least `1` and `R = r L`. -/
def RatioHit (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ 1 ≤ VR 0 t ω - VL 0 t ω ∧
    VR 0 t ω - W t ω = r * (W t ω - VL 0 t ω)}

/-- **The two-seed ratio `R/L` takes the value `r` at a separation `≥ 1` with positive probability** (weights
`> −2`, infinite lifetime): the log-clock angle `L/(L + R)` is a stationary Jacobi diffusion, which hits
`1/(1 + r)` after time `0` with positive probability. -/
theorem measure_ratioHit_pos (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {r : ℝ} (hr : 0 < r) :
    0 < P (RatioHit r W VL VR ζ) := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨U, hU, hUae⟩ := Sec2.TwoSeed.exists_isJacobiMP_logAngle hE hκ hρL hρR
  set α : ℝ := 1 / (1 + r) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by linarith)]; linarith
  have hpos := hU.measure_exists_eq_pos hκ (by linarith) (by linarith) hα0 hα1
  refine hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [hUae, hζ, hE.2.2.2.2] with ω hUω hζω hp
  rintro ⟨u, hu, hUu⟩
  rw [hζω] at hp
  have hUu' : Sec2.TwoSeed.logAngle (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) ⊤ u = α := by
    rw [← hζω, ← hUω u]; exact hUu
  obtain ⟨t₀, -, ht₀⟩ := Sec2.TwoSeed.sepN_unbounded_of_top hp (Real.exp u)
  obtain ⟨-, hsep⟩ := Sec2.TwoSeed.hitTime_spec hp (t₀ := t₀) ENNReal.coe_lt_top ht₀
  set t := Sec2.TwoSeed.hitTime (fun i t => VL i t ω) (fun i t => VR i t ω) ⊤ u with ht
  refine ⟨t, by rw [hζω]; exact ENNReal.coe_lt_top, ?_, ?_⟩
  · have : Sec2.TwoSeed.sepN (fun i t => VL i t ω) (fun i t => VR i t ω) t = VR 0 t ω - VL 0 t ω := rfl
    rw [← this, hsep]
    exact Real.one_le_exp hu
  · have hl : (W t ω - VL 0 t ω) / Real.exp u = α := by rw [← hUu']; rfl
    have hs : VR 0 t ω - VL 0 t ω = Real.exp u := hsep
    have he := Real.exp_pos u
    rw [div_eq_iff he.ne'] at hl
    have h1r : (1 + r) * α = 1 := by rw [hα]; field_simp
    have hX : W t ω - VL 0 t ω = α * Real.exp u := hl
    calc VR 0 t ω - W t ω = (VR 0 t ω - VL 0 t ω) - (W t ω - VL 0 t ω) := by ring
      _ = r * (α * Real.exp u) := by rw [hs, hX]; linear_combination (-Real.exp u) * h1r
      _ = r * (W t ω - VL 0 t ω) := by rw [hX]

end Ratio

/-! ### The ratio-hitting time -/

section Hit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `max 0 (1 − Y)` with `Y = max 0 (1 − (v_R − v_L)) + |v_R − w − r (w − v_L)|`: its absolute value reaches `1`
exactly when the separation is at least `1` and `v_R − w = r (w − v_L)`. -/
def ratioFn (r w vl vr : ℝ) : ℝ := max 0 (1 - (max 0 (1 - (vr - vl)) + |vr - w - r * (w - vl)|))

theorem continuous_ratioFn (r : ℝ) : Continuous fun p : ℝ × ℝ × ℝ => ratioFn r p.1 p.2.1 p.2.2 := by
  unfold ratioFn
  fun_prop

theorem one_le_abs_ratioFn_iff {r w vl vr : ℝ} :
    1 ≤ |ratioFn r w vl vr| ↔ 1 ≤ vr - vl ∧ vr - w = r * (w - vl) := by
  unfold ratioFn
  have h1 : 0 ≤ max 0 (1 - (vr - vl)) := le_max_left _ _
  have h2 : 0 ≤ |vr - w - r * (w - vl)| := abs_nonneg _
  rw [abs_of_nonneg (le_max_left _ _)]
  constructor
  · intro h
    have hY : max 0 (1 - (vr - vl)) + |vr - w - r * (w - vl)| ≤ 0 := by
      rcases le_total 0 (1 - (max 0 (1 - (vr - vl)) + |vr - w - r * (w - vl)|)) with h' | h'
      · rw [max_eq_right h'] at h; linarith
      · rw [max_eq_left h'] at h; linarith
    have ha : max 0 (1 - (vr - vl)) = 0 := le_antisymm (by linarith) h1
    have hb : |vr - w - r * (w - vl)| = 0 := le_antisymm (by linarith) h2
    exact ⟨by linarith [le_max_right 0 (1 - (vr - vl))], by linarith [abs_eq_zero.1 hb]⟩
  · rintro ⟨h1', h2'⟩
    have ha : max 0 (1 - (vr - vl)) = 0 := max_eq_left (by linarith)
    have hb : |vr - w - r * (w - vl)| = 0 := abs_eq_zero.2 (by linarith)
    rw [ha, hb]
    norm_num

/-- The value of a process killed at `ζ`. -/
def kil (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

open Classical in
/-- The ratio-hitting process: `ratioFn` of the killed driver and marks on the event `G`, `0` off `G`. -/
def ratioProc (G : Set Ω) (r : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then ratioFn r (kil ζ W t ω) (kil ζ (VL 0) t ω) (kil ζ (VR 0) t ω) else 0

/-- The first time the separation is at least `1` and `R = r L` (on `G`; `⊤` off `G`). -/
def ratioTime (G : Set Ω) (r : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) :
    Ω → WithTop ℝ≥0 :=
  MathFin.exitTime (ratioProc G r ζ W VL VR) 1

variable {G : Set Ω} {r : ℝ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}

theorem ratioProc_of_mem {ω : Ω} (hω : ω ∈ G) (hζ : ζ ω = ⊤) (t : ℝ≥0) :
    ratioProc G r ζ W VL VR t ω = ratioFn r (W t ω) (VL 0 t ω) (VR 0 t ω) := by
  have ht : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  simp only [ratioProc, hω, ↓reduceIte, kil, ht]

theorem continuous_ratioProc
    (hG : ∀ ω ∈ G, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω)) (ω : Ω) : Continuous fun t => ratioProc G r ζ W VL VR t ω := by
  by_cases hω : ω ∈ G
  · obtain ⟨hζ, hW, hL, hR⟩ := hG ω hω
    simp_rw [ratioProc_of_mem hω hζ]
    exact (continuous_ratioFn r).comp (hW.prodMk (hL.prodMk hR))
  · simp only [ratioProc, hω, ↓reduceIte]
    exact continuous_const

theorem measurable_kil {𝓖 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓖 ζ X) (t : ℝ≥0) :
    Measurable[𝓖 t] (kil ζ X t) :=
  Sec2.TwoSeed.measurable_killed hX t

theorem measurable_ratioProc {𝓖 : Filtration ℝ≥0 mΩ} (hGm : ∀ t, MeasurableSet[𝓖 t] G)
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : AdaptedBefore 𝓖 ζ (VL 0)) (hVR : AdaptedBefore 𝓖 ζ (VR 0)) (t : ℝ≥0) :
    Measurable[𝓖 t] (ratioProc G r ζ W VL VR t) := by
  have hw := measurable_kil hW t
  have hl := measurable_kil hVL t
  have hr := measurable_kil hVR t
  have habs : Measurable[𝓖 t] fun ω =>
      |kil ζ (VR 0) t ω - kil ζ W t ω - r * (kil ζ W t ω - kil ζ (VL 0) t ω)| :=
    continuous_abs.measurable.comp ((hr.sub hw).sub ((hw.sub hl).const_mul r))
  have hf : Measurable[𝓖 t] fun ω => ratioFn r (kil ζ W t ω) (kil ζ (VL 0) t ω) (kil ζ (VR 0) t ω) :=
    measurable_const.max (measurable_const.sub ((measurable_const.max (measurable_const.sub (hr.sub hl))).add habs))
  exact Measurable.ite (p := (· ∈ G)) (hGm t) hf measurable_const

theorem ratioTime_le_iff
    (hG : ∀ ω ∈ G, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω)) {ω : Ω} (hω : ω ∈ G) (i : ℝ≥0) :
    ratioTime G r ζ W VL VR ω ≤ (i : WithTop ℝ≥0) ↔
      ∃ s ∈ Icc (0 : ℝ≥0) i, 1 ≤ VR 0 s ω - VL 0 s ω ∧ VR 0 s ω - W s ω = r * (W s ω - VL 0 s ω) := by
  rw [ratioTime, MathFin.exitTime_le_iff (continuous_ratioProc hG)]
  simp only [Nat.cast_one, ratioProc_of_mem hω (hG ω hω).1, one_le_abs_ratioFn_iff]

theorem not_ratioTime_le_of_notMem
    (hG : ∀ ω ∈ G, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω)) {ω : Ω} (hω : ω ∉ G) (i : ℝ≥0) :
    ¬ ratioTime G r ζ W VL VR ω ≤ (i : WithTop ℝ≥0) := by
  rw [ratioTime, MathFin.exitTime_le_iff (continuous_ratioProc hG)]
  rintro ⟨s, -, hs⟩
  simp only [ratioProc, hω, ↓reduceIte, abs_zero, Nat.cast_one] at hs
  linarith

theorem isStoppingTime_ratioTime {𝓖 : Filtration ℝ≥0 mΩ} (hGm : ∀ t, MeasurableSet[𝓖 t] G)
    (hG : ∀ ω ∈ G, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω))
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : AdaptedBefore 𝓖 ζ (VL 0)) (hVR : AdaptedBefore 𝓖 ζ (VR 0)) :
    IsStoppingTime 𝓖 (ratioTime G r ζ W VL VR) :=
  MathFin.isStoppingTime_exitTime_of_measurable (measurable_ratioProc hGm hW hVL hVR)
    (continuous_ratioProc hG) 1

/-- A `WithTop`-valued time capped at `c`, as an `ℝ≥0`-valued time. -/
def capTime (τ : Ω → WithTop ℝ≥0) (c : ℝ≥0) (ω : Ω) : ℝ≥0 := (min (τ ω) c).untopD c

theorem coe_capTime (τ : Ω → WithTop ℝ≥0) (c : ℝ≥0) (ω : Ω) :
    ((capTime τ c ω : ℝ≥0) : WithTop ℝ≥0) = min (τ ω) c := by
  have hne : min (τ ω) (c : WithTop ℝ≥0) ≠ ⊤ :=
    ((min_le_right _ _).trans_lt (WithTop.coe_lt_top c)).ne
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [capTime, ← hx]
  rfl

theorem isStoppingTime_capTime {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (c : ℝ≥0) : IsStoppingTime 𝓖 fun ω => (capTime τ c ω : WithTop ℝ≥0) := by
  have h := hτ.min (isStoppingTime_const 𝓖 c)
  have e : (fun ω => min (τ ω) (c : WithTop ℝ≥0)) = fun ω => ((capTime τ c ω : ℝ≥0) : WithTop ℝ≥0) :=
    funext fun ω => (coe_capTime τ c ω).symm
  rwa [e] at h

/-- `{τ ≤ c}` is known at the capped time `τ ∧ c`. -/
theorem measurableSet_le_capTime {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (c : ℝ≥0) : MeasurableSet[(isStoppingTime_capTime hτ c).measurableSpace] {ω | τ ω ≤ c} := by
  rw [IsStoppingTime.measurableSet]
  refine ⟨le_iSup (fun i => (𝓖 i : MeasurableSpace Ω)) c _ (hτ c), fun i => ?_⟩
  rcases le_or_gt c i with hci | hic
  · have e : {ω | τ ω ≤ c} ∩ {ω | ((capTime τ c ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} = {ω | τ ω ≤ c} := by
      refine inter_eq_left.2 fun ω _ => ?_
      rw [mem_ofPred_eq, coe_capTime]
      exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 hci)
    rw [e]
    exact 𝓖.mono hci _ (hτ c)
  · have e : {ω | τ ω ≤ c} ∩ {ω | ((capTime τ c ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} = {ω | τ ω ≤ i} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, coe_capTime]
      constructor
      · rintro ⟨-, h⟩
        rcases min_choice (τ ω) (c : WithTop ℝ≥0) with h' | h'
        · rwa [h'] at h
        · rw [h'] at h
          exact absurd (WithTop.coe_le_coe.1 h) (not_le.2 hic)
      · intro h
        exact ⟨h.trans (WithTop.coe_le_coe.2 hic.le), (min_le_left _ _).trans h⟩
    rw [e]
    exact hτ i

end Hit

/-! ### The restart at the ratio-hitting time -/

section Restart

open WangWu.TraceGlue (ShiftGood)

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The pathwise properties of a two-seed evolution used at the restart: infinite lifetime, continuity, the seed
start, separation at positive times, simple mapped-out futures at rational times, and transience. -/
def SeedGood (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧ Continuous (fun t => VR 0 t ω) ∧
    W 0 ω = 0 ∧ VL 0 0 ω = 0 ∧ VR 0 0 ω = 0 ∧
    (∀ t : ℝ≥0, 0 < t → VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω) ∧
    ShiftGood (fun s : ℝ => W s.toNNReal ω) (range ((↑) : ℚ → ℝ)) ∧
    ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

theorem IsIntegratedSLEEvolution.ae_seedGood (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hρL : κ / 2 - 2 ≤ ρL 0)
    (hρR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, SeedGood W VL VR ζ ω := by
  have hadm := hasAdmissiblePartialSums_one hρL hρR (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
  filter_upwards [IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 isOrderedForceWord_zero hadm hE,
    IsIntegratedSLEEvolution.ae_shiftGood hκ hκ4 isOrderedForceWord_zero hadm hE,
    IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed hκ hκ4 hadm hE, hE.2.2.2.2] with ω
    ⟨hζ, hsep, _⟩ ⟨_, hWc, hW0, hg⟩ htr hp
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => by
      show (t : ℝ≥0∞) < ζ ω
      rw [hζ]; exact ENNReal.coe_lt_top)
  exact ⟨hζ, hWc, hcont (hp.2.2.2.2.1 0), hcont (hp.2.2.2.2.2.1 0), hW0, hp.2.1 0, hp.2.2.1 0,
    fun t ht => ⟨(hsep t ht).1 0, (hsep t ht).2 0⟩, hg, htr⟩

/-- **The canonical trace event has probability one at some separated pair `(−λ, rλ)`** (the complement has
canonical probability `0`) (`0 < κ ≤ 4`, weights
`≥ κ/2 − 2`, `r > 0`): restart the two-seed evolution at the first time with separation `≥ 1` and `R = rL`
(capped so that it is hit with positive probability), where the restarted driver has the trace event. -/
theorem exists_codeLaw_traceCodeSet_eq_one (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hρL : κ / 2 - 2 ≤ ρL 0)
    (hρR : κ / 2 - 2 ≤ ρR 0) {r : ℝ} (hr : 0 < r) :
    ∃ l : ℝ, 0 < l ∧
      codeLaw κ ρL ρR (traceCodeSet (nL := 1) (nR := 1))ᶜ ((fun _ => -l), fun _ => r * l) = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    Sec2.exists_isIntegratedSLEEvolution_twoSeed hκ (xL := fun _ => 0) (xR := fun _ => 0)
      (fun _ => rfl) (fun _ => rfl) ρL ρR
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hgood := IsIntegratedSLEEvolution.ae_seedGood hκ hκ4 hρL hρR hE
  set G : Set Ω := (toMeasurable P {ω | ¬ SeedGood W VL VR ζ ω})ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGc : P Gᶜ = 0 := by rw [hG, compl_compl, measure_toMeasurable]; exact ae_iff.1 hgood
  have hGg : ∀ ω ∈ G, SeedGood W VL VR ζ ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG𝓖 : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] G := fun t => by
    have h := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
    rwa [compl_compl] at h
  have hGc' : ∀ ω ∈ G, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω) := fun ω hω =>
    ⟨(hGg ω hω).1, (hGg ω hω).2.1, (hGg ω hω).2.2.1, (hGg ω hω).2.2.2.1⟩
  set τ := ratioTime G r ζ W VL VR with hτ
  have hτs : IsStoppingTime (usualAugmentation 𝓕 P) τ :=
    isStoppingTime_ratioTime hG𝓖 hGc' hE𝓖.2.1 (hE𝓖.2.2.1 0) (hE𝓖.2.2.2.1 0)
  -- some cap `n + 1` is reached with positive probability
  have hpos := measure_ratioHit_pos hE hκ (by linarith) (by linarith) (hgood.mono fun ω h => h.1) hr
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < P {ω | τ ω ≤ (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)} := by
    by_contra hall
    push Not at hall
    have h0 : P (⋃ n : ℕ, {ω | τ ω ≤ (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)}) = 0 :=
      measure_iUnion_null fun n => le_antisymm (hall n) bot_le
    have hsub : RatioHit r W VL VR ζ ⊆
        (⋃ n : ℕ, {ω | τ ω ≤ (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)}) ∪ Gᶜ := by
      rintro ω ⟨t, -, h1, h2⟩
      by_cases hω : ω ∈ G
      · left
        obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
        refine mem_iUnion.2 ⟨n, ?_⟩
        have hle : τ ω ≤ (t : WithTop ℝ≥0) :=
          (ratioTime_le_iff hGc' hω t).2 ⟨t, ⟨zero_le, le_rfl⟩, h1, h2⟩
        refine hle.trans (WithTop.coe_le_coe.2 ?_)
        rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
        push_cast
        linarith
      · exact Or.inr hω
    have hle := (measure_mono hsub).trans (measure_union_le (μ := P) _ _)
    rw [h0, hGc, add_zero] at hle
    exact absurd (hpos.trans_le hle) (lt_irrefl 0)
  set c : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) with hc
  set T := capTime τ c with hT
  have hTs := isStoppingTime_capTime hτs c
  set A : Set Ω := {ω | τ ω ≤ (c : WithTop ℝ≥0)} with hAdef
  have hA := measurableSet_le_capTime hτs c
  have hAm : MeasurableSet A := hTs.measurableSpace_le _ hA
  have hAG : ∀ ω ∈ A, ω ∈ G := fun ω hω => by
    by_contra h; exact not_ratioTime_le_of_notMem hGc' h c hω
  have hTτ : ∀ ω ∈ A, (T ω : WithTop ℝ≥0) = τ ω := fun ω hω => by
    rw [hT, coe_capTime]; exact min_eq_left hω
  have hhit : ∀ ω ∈ A, 1 ≤ VR 0 (T ω) ω - VL 0 (T ω) ω ∧
      VR 0 (T ω) ω - W (T ω) ω = r * (W (T ω) ω - VL 0 (T ω) ω) := by
    intro ω hω
    have hωG := hAG ω hω
    obtain ⟨s, hs, h1, h2⟩ := (ratioTime_le_iff hGc' hωG (T ω)).1 (hTτ ω hω).ge
    have hsT : s = T ω := by
      refine le_antisymm hs.2 ?_
      have hle : τ ω ≤ (s : WithTop ℝ≥0) :=
        (ratioTime_le_iff hGc' hωG s).2 ⟨s, ⟨zero_le, le_rfl⟩, h1, h2⟩
      rw [← hTτ ω hω] at hle
      exact WithTop.coe_le_coe.1 hle
    rw [← hsT]
    exact ⟨h1, h2⟩
  have hTpos : ∀ ω ∈ A, 0 < T ω := by
    intro ω hω
    have hg := hGg ω (hAG ω hω)
    rcases (zero_le (a := T ω)).eq_or_lt with h0 | h0
    · obtain ⟨h1, -⟩ := hhit ω hω
      rw [← h0, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1] at h1
      norm_num at h1
    · exact h0
  -- the restart
  have hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧
      (0 < T ω ∨ ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < (fun _ : Fin 1 => (0 : ℝ)) j) := fun ω hω =>
    ⟨by rw [(hGg ω (hAG ω hω)).1]; exact ENNReal.coe_lt_top, Or.inl (hTpos ω hω)⟩
  have hev : ∀ ω ∈ A, TraceEvent (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω) := by
    intro ω hω
    obtain ⟨hζ, hWc, -, -, hW0, -, -, -, hsg, htr⟩ := hGg ω (hAG ω hω)
    rw [hζ, ENNReal.top_sub_coe]
    exact traceEvent_shiftNN hWc hW0 hsg htr (T ω)
  have hlaw := Sec7.RandRestart.measure_restart_codeEvent hκ hE𝓖 hTs hA hAT
    (Φ := fun w τ => ¬ TraceEvent w τ) Sec7.RandRestart.measurableSet_traceCodeSet.compl
    Sec7.RandRestart.compl_traceCodeSet_iff Sec7.RandRestart.not_traceEvent_congr
  have hempty : A ∩ {ω | ¬ TraceEvent (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)} = ∅ :=
    eq_empty_of_forall_notMem fun ω h => h.2 (hev ω h.1)
  rw [hempty, measure_empty] at hlaw
  -- the canonical probability of no trace is `0` almost everywhere on `A`
  obtain ⟨st, _, _, hstm, _, _, hid⟩ := Sec7.RandRestart.restart_core hκ hE𝓖 hTs hA hAT
  have hcongr : (fun ω => codeLaw κ ρL ρR (traceCodeSet (nL := 1) (nR := 1))ᶜ (wordAt W VL VR T ω)) =ᵐ[P.restrict A]
      fun ω => codeLaw κ ρL ρR (traceCodeSet (nL := 1) (nR := 1))ᶜ (st ω) := by
    filter_upwards [(ae_restrict_iff' hAm).2 hid] with ω h
    rw [h.1]
  have hmeas : Measurable fun ω => codeLaw κ ρL ρR (traceCodeSet (nL := 1) (nR := 1))ᶜ (st ω) :=
    (Sec7.RandRestart.measurable_codeLaw Sec7.RandRestart.measurableSet_traceCodeSet.compl).comp hstm
  rw [lintegral_congr_ae hcongr, eq_comm, lintegral_eq_zero_iff hmeas] at hlaw
  have hAne : P.restrict A ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hn.ne'
  have : (ae (P.restrict A)).NeBot := ae_neBot.2 hAne
  obtain ⟨ω, ⟨hfω, hst⟩, hωA⟩ := ((hlaw.and ((ae_restrict_iff' hAm).2 hid)).and (ae_restrict_mem hAm)).exists
  have hfω' : codeLaw κ ρL ρR (traceCodeSet (nL := 1) (nR := 1))ᶜ (wordAt W VL VR T ω) = 0 := by
    rw [← hst.1]; exact hfω
  have hg := hGg ω (hAG ω hωA)
  obtain ⟨-, h2⟩ := hhit ω hωA
  refine ⟨W (T ω) ω - VL 0 (T ω) ω, sub_pos.2 (hg.2.2.2.2.2.2.2.1 (T ω) (hTpos ω hωA)).1, ?_⟩
  have hword : wordAt W VL VR T ω =
      ((fun _ => -(W (T ω) ω - VL 0 (T ω) ω)), fun _ => r * (W (T ω) ω - VL 0 (T ω) ω)) := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · rw [Fin.fin_one_eq_zero i]
      simp only [wordAt]
      ring
    · rw [Fin.fin_one_eq_zero j]
      simp only [wordAt]
      rw [← h2]
  rw [← hword]
  exact hfω'

end Restart

end InteractingSLE.Zhan
