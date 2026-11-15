/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceLift

/-!
# One force: the near-mark event and its canonical probability

Packet PROVE-ZHAN-GT4-B3. The restart inequality for one left force (`OneForceBand.lean`) bounds the probability of a
real terminal cluster point by the canonical probability that the restarted trace has a real terminal cluster point
in the band `[(1 + θ) m, (1 − θ) m]` around its mark `m < 0`. This file codes that event (`NearEvent`, Borel through the
rational trace values, as GT4-B2's band event), proves its real-time form, its dilation invariance and its monotonicity
in `θ`, and shows that its canonical probability tends to zero as `θ ↓ 0`: the bands shrink to the mark, which is not a
terminal cluster point (`ae_not_isTermCluster_mark_oneForce`, B.2 (E5)).

## Main results

* `oneBandDist`, `NearEvent`, `nearCodeSet` (Borel), `RealNear`, `nearEvent_top_iff`, `realNear_of_isTermCluster`.
* `codeLaw_near_dilate`: dilation invariance.
* `tendsto_codeLaw_near`: the canonical near-mark probabilities tend to `0`.
* `topCodeSetN`, `codeLaw_compl_topCodeSetN_eq_zero`: the canonical one-force law has a trace on `[0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart QuantumZipper

/-! ### The near-mark event -/

/-- The distance from `z` to the band `[(1 + θ) m, (1 − θ) m]` around the left mark `m = s.1 0` of a one-force word. -/
def oneBandDist (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (z : ℂ) : ℝ :=
  dIcc ((1 + θ) * s.1 0) ((1 - θ) * s.1 0) z

theorem continuous_oneBandDist (θ : ℝ) : Continuous fun p : ℝ × ℂ => dIcc ((1 + θ) * p.1) ((1 - θ) * p.1) p.2 :=
  continuous_dIcc.comp ((continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul continuous_fst).prodMk continuous_snd))

/-- **The near-mark event** of (start, driver, horizon): infinite horizon, a continuous generating trace on `[0, ∞)`,
and trace values at arbitrarily late rational times arbitrarily close to the band around the mark. -/
def NearEvent (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ (fun q : ℚ≥0 => w q) ∈ topSet ∧
    ∀ k N : ℕ, ∃ q : ℚ≥0, (N : ℝ≥0) ≤ q ∧ oneBandDist θ s (ratTrace w q) < 1 / ((k : ℝ) + 1)

/-- The Borel set of solution codes with the near-mark event of their own start. -/
def nearCodeSet (θ : ℝ) : Set (XCode 1 0) := {x | NearEvent θ (startOf x) (cw x) (cζ x)}

theorem measurableSet_nearCodeSet (θ : ℝ) : MeasurableSet (nearCodeSet θ) := by
  have hR : Measurable fun x : XCode 1 0 => fun q : ℚ≥0 => cw x q :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply (q : ℝ≥0)).comp measurable_cw_cζ.fst
  have h1 : MeasurableSet {x : XCode 1 0 | cζ x = ⊤} := measurable_cζ (measurableSet_singleton ⊤)
  have h2 : MeasurableSet {x : XCode 1 0 | (fun q : ℚ≥0 => cw x q) ∈ topSet} := hR measurableSet_topSet
  have h3 : ∀ (k N : ℕ) (q : ℚ≥0), MeasurableSet {x : XCode 1 0 | (N : ℝ≥0) ≤ q ∧
      oneBandDist θ (startOf x) (ratTrace (cw x) q) < 1 / ((k : ℝ) + 1)} := by
    intro k N q
    rw [ofPred_and]
    refine (MeasurableSet.const _).inter (measurableSet_lt ?_ measurable_const)
    have hz : Measurable fun x : XCode 1 0 => ratTrace (cw x) q :=
      (LP.measurable_traceAt (q : ℝ≥0)).comp (Sec7.measurable_extendRat.comp hR)
    exact (continuous_oneBandDist θ).measurable.comp ((measurable_startOf_fst 0).prodMk hz)
  have e : nearCodeSet θ = {x : XCode 1 0 | cζ x = ⊤} ∩ ({x | (fun q : ℚ≥0 => cw x q) ∈ topSet} ∩
      ⋂ k : ℕ, ⋂ N : ℕ, ⋃ q : ℚ≥0, {x : XCode 1 0 | (N : ℝ≥0) ≤ q ∧
        oneBandDist θ (startOf x) (ratTrace (cw x) q) < 1 / ((k : ℝ) + 1)}) := by
    ext x
    simp only [nearCodeSet, NearEvent, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
  rw [e]
  exact h1.inter (h2.inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun N =>
    MeasurableSet.iUnion fun q => h3 k N q))

theorem nearEvent_congr (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hb : NearEvent θ s w τ) : NearEvent θ s w' τ := by
  obtain ⟨hτ, h2⟩ := hb
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact ⟨rfl, h2⟩

/-- The near-mark event in real time, for a continuous generating trace. -/
def RealNear (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (η : ℝ≥0 → ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ N : ℝ≥0, ∃ t : ℝ≥0, N ≤ t ∧ oneBandDist θ s (η t) < ε

/-- **The near-mark event of a continuous driver with a generating trace on `[0, ∞)`** is the real-time condition. -/
theorem nearEvent_top_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) :
    NearEvent θ s w ⊤ ↔ RealNear θ s η := by
  have hηc : Continuous η :=
    continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  constructor
  · rintro ⟨-, -, h⟩ ε hε N
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨M, hM⟩ := exists_nat_ge (N : ℝ)
    obtain ⟨q, hq, hd⟩ := h k M
    refine ⟨q, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe]; exact hM.trans (by exact_mod_cast hq)
    · rw [ratTrace_eq hw hw0 hη] at hd; linarith
  · intro h
    refine ⟨rfl, (ratVals_mem_topSet_iff hw hw0).2 ⟨η, hη⟩, fun k N => ?_⟩
    obtain ⟨t, ht, hd⟩ := h (1 / ((k : ℝ) + 1)) (by positivity) N
    have hcd : Continuous fun z => oneBandDist θ s z :=
      (continuous_oneBandDist θ).comp (continuous_const.prodMk continuous_id)
    have hlim : Tendsto (fun m => oneBandDist θ s (η (Sec7.ratAbove t m))) atTop
        (𝓝 (oneBandDist θ s (η t))) :=
      ((hcd.comp hηc).tendsto t).comp (Sec7.tendsto_ratAbove t)
    obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hd)).exists
    refine ⟨Sec7.ratAbove t m, ht.trans (Sec7.le_ratAbove t m), ?_⟩
    rw [ratTrace_eq hw hw0 hη]; exact hm

/-- A real terminal cluster point in the band gives the real-time near-mark condition. -/
theorem realNear_of_isTermCluster {θ : ℝ} {s : (Fin 1 → ℝ) × (Fin 0 → ℝ)} {η : ℝ≥0 → ℂ} {y : ℝ}
    (hy : y ∈ Icc ((1 + θ) * s.1 0) ((1 - θ) * s.1 0)) (hcl : IsTermCluster η y) : RealNear θ s η := by
  intro ε hε N
  have hfr := (mapClusterPt_iff_frequently.1 hcl) _ (ball_mem_nhds (y : ℂ) hε)
  obtain ⟨t, ht1, ht2⟩ := (hfr.and_eventually (eventually_ge_atTop N)).exists
  rw [mem_ball, dist_eq_norm] at ht1
  exact ⟨t, ht2, lt_of_le_of_lt (dIcc_le _ hy) ht1⟩

/-- The near-mark event is monotone in the fraction (for a negative mark). -/
theorem nearEvent_mono {s : (Fin 1 → ℝ) × (Fin 0 → ℝ)} (hs : s.1 0 < 0) {θ θ' : ℝ} (hθ : 0 ≤ θ)
    (hθθ' : θ ≤ θ') {w : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (h : NearEvent θ s w τ) : NearEvent θ' s w τ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun k N => ?_⟩
  obtain ⟨q, hq, hd⟩ := h3 k N
  refine ⟨q, hq, lt_of_le_of_lt ?_ hd⟩
  unfold oneBandDist
  have hab : (1 + θ) * s.1 0 ≤ (1 - θ) * s.1 0 := by nlinarith
  refine dIcc_le _ ⟨le_trans (by nlinarith) (clamp_mem_Icc hab _).1, (clamp_mem_Icc hab _).2.trans (by nlinarith)⟩

/-- If the near-mark condition holds for every fraction `1/(m+1)`, the mark is a terminal cluster point. -/
theorem isTermCluster_of_forall_realNear {s : (Fin 1 → ℝ) × (Fin 0 → ℝ)} (hs : s.1 0 < 0) {η : ℝ≥0 → ℂ}
    (h : ∀ m : ℕ, RealNear (1 / ((m : ℝ) + 1)) s η) : IsTermCluster η (s.1 0) := by
  rw [isTermCluster_iff_not]
  rintro ⟨d, hd, hev⟩
  set M := -s.1 0 with hM
  have hM0 : 0 < M := by linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < d / 8 / M by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨t, ht, hdist⟩ := h m (d / 2) (by positivity) N
  set θ : ℝ := 1 / ((m : ℝ) + 1) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθM : θ * M < d / 8 := by rwa [lt_div_iff₀ hM0] at hm
  have hab : (1 + θ) * s.1 0 ≤ (1 - θ) * s.1 0 := by nlinarith
  have h1 := norm_sub_left_le_dIcc hab (η t)
  have h2 := hN t ht
  unfold oneBandDist at hdist
  have h3 : ‖η t - s.1 0‖ ≤ ‖η t - ((1 + θ) * s.1 0 : ℝ)‖ + θ * M := by
    calc ‖η t - s.1 0‖ = ‖(η t - ((1 + θ) * s.1 0 : ℝ)) + (((1 + θ) * s.1 0 : ℝ) - s.1 0 : ℂ)‖ := by ring_nf
      _ ≤ ‖η t - ((1 + θ) * s.1 0 : ℝ)‖ + ‖(((1 + θ) * s.1 0 : ℝ) - s.1 0 : ℂ)‖ := norm_add_le _ _
      _ = ‖η t - ((1 + θ) * s.1 0 : ℝ)‖ + θ * M := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            show (1 + θ) * s.1 0 - s.1 0 = -(θ * M) by rw [hM]; ring, abs_neg, abs_of_nonneg (by positivity)]
  have h4 : (1 - θ) * s.1 0 - (1 + θ) * s.1 0 = 2 * (θ * M) := by rw [hM]; ring
  linarith

/-! ### Dilation invariance -/

theorem oneBandDist_smul {c : ℝ} (hc : 0 < c) (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (z : ℂ) :
    oneBandDist θ ((fun i => c * s.1 i), fun j => c * s.2 j) ((c : ℂ) * z) = c * oneBandDist θ s z := by
  unfold oneBandDist
  rw [show (1 + θ) * (c * s.1 0) = c * ((1 + θ) * s.1 0) by ring,
    show (1 - θ) * (c * s.1 0) = c * ((1 - θ) * s.1 0) by ring, dIcc_smul hc]

/-- The real-time near-mark condition is invariant under Brownian scaling of the trace and the start. -/
theorem realNear_dilate {c : ℝ≥0} (hc : c ≠ 0) (θ : ℝ) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) {η : ℝ≥0 → ℂ} :
    RealNear θ ((fun i => (√(c : ℝ))⁻¹ * s.1 i), fun j => (√(c : ℝ))⁻¹ * s.2 j)
        (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) ↔ RealNear θ s η := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  have hcc : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
  set l : ℝ := (√(c : ℝ))⁻¹ with hl
  have hl0 : 0 < l := inv_pos.2 (Real.sqrt_pos.2 hc')
  simp only [RealNear, oneBandDist_smul hl0]
  constructor
  · intro h ε hε N
    obtain ⟨t, ht, hd⟩ := h (l * ε) (mul_pos hl0 hε) (N / c)
    refine ⟨c * t, ?_, (mul_lt_mul_iff_of_pos_left hl0).1 hd⟩
    rwa [div_le_iff₀ hcc, mul_comm] at ht
  · intro h ε hε N
    obtain ⟨t, ht, hd⟩ := h (ε / l) (div_pos hε hl0) (c * N)
    refine ⟨t / c, ?_, ?_⟩
    · rw [le_div_iff₀ hcc, mul_comm]; exact ht
    · rw [mul_div_cancel₀ t hc]
      rwa [lt_div_iff₀ hl0, mul_comm] at hd

section Canonical

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL ρL : Fin 1 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The canonical probability of the near-mark event is the probability for any evolution of a separated word. -/
theorem measure_near_eq_codeLaw [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (θ : ℝ) :
    P {ω | NearEvent θ (xL, xR) (fun t => W t ω) (ζ ω)} = codeLaw κ ρL ρR (nearCodeSet θ) (xL, xR) :=
  measure_eventOf_eq_codeLawS hκ (fun _ j => j.elim0) hE (measurableSet_nearCodeSet θ) (fun _ _ _ => Iff.rfl)
    (nearEvent_congr θ)

/-- **Dilation invariance of the near-mark probability.** -/
theorem codeLaw_near_dilate [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (htr : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) {c : ℝ≥0}
    (hc : c ≠ 0) (θ : ℝ) :
    codeLaw κ ρL ρR (nearCodeSet θ) ((fun i => (√(c : ℝ))⁻¹ * xL i), fun j => (√(c : ℝ))⁻¹ * xR j) =
      codeLaw κ ρL ρR (nearCodeSet θ) (xL, xR) := by
  rw [← measure_near_eq_codeLaw hκ (hE.dilate hc), ← measure_near_eq_codeLaw hκ hE]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [htr, hE.2.2.2.2] with ω ⟨hζω, η, hη⟩ hp
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζω] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hdc : Continuous (Sec7.Dilation.dilPath c fun t => W t ω) :=
    continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
  have hd0 : Sec7.Dilation.dilPath c (fun t => W t ω) 0 = 0 := by simp [Sec7.Dilation.dilPath, hp.1]
  have hη' := hη.dilate hc
  rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hη'
  show NearEvent θ _ (Sec7.Dilation.dilPath c fun t => W t ω) (ζ ω / c) ↔
    NearEvent θ (xL, xR) (fun t => W t ω) (ζ ω)
  rw [hζω, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top, nearEvent_top_iff hdc hd0 hη',
    nearEvent_top_iff hwc hp.1 hη]
  exact realNear_dilate hc θ (xL, xR)

/-- The codes with the near-mark event for every fraction `1/(k+1)`, `k ≤ m`. -/
def nearCodeSetLE (m : ℕ) : Set (XCode 1 0) := ⋂ k : ℕ, ⋂ (_ : k ≤ m), nearCodeSet (1 / ((k : ℝ) + 1))

theorem measurableSet_nearCodeSetLE (m : ℕ) : MeasurableSet (nearCodeSetLE m) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_nearCodeSet _

/-- **The near-mark probabilities tend to zero** (B.2 (E5): the mark is not a terminal cluster point). -/
theorem IsIntegratedSLEEvolution.tendsto_codeLaw_near.{u} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 0 < κ) (hx : xL 0 < 0)
    (hρ : κ / 2 - 2 ≤ ρL 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    Tendsto (fun m : ℕ => codeLaw κ ρL ρR (nearCodeSet (1 / ((m : ℝ) + 1))) (xL, xR)) atTop (𝓝 0) := by
  have hsep : ∀ (i : Fin 1) (j : Fin 0), xL i < xR j := fun _ j => j.elim0
  have hcong : ∀ (Φ : ℕ → (Fin 1 → ℝ) × (Fin 0 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop),
      (∀ k, ∀ (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → Φ k s w τ → Φ k s w' τ) →
      ∀ (p : ℕ → Prop) (s : (Fin 1 → ℝ) × (Fin 0 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → (∀ k, p k → Φ k s w τ) → ∀ k, p k → Φ k s w' τ :=
    fun Φ hΦ p s w w' τ h hk k hpk => hΦ k s w w' τ h (hk k hpk)
  have heq : ∀ m : ℕ, codeLaw κ ρL ρR (nearCodeSet (1 / ((m : ℝ) + 1))) (xL, xR) =
      codeLaw κ ρL ρR (nearCodeSetLE m) (xL, xR) := by
    intro m
    rw [← measure_near_eq_codeLaw hκ hE, ← measure_eventOf_eq_codeLawS hκ hsep hE
      (measurableSet_nearCodeSetLE m)
      (Φ := fun s w τ => ∀ k : ℕ, k ≤ m → NearEvent (1 / ((k : ℝ) + 1)) s w τ)
      (fun x _ _ => by simp only [nearCodeSetLE, mem_iInter]; rfl)
      (hcong (fun k s w τ => NearEvent (1 / ((k : ℝ) + 1)) s w τ) (fun k => nearEvent_congr _) _)]
    congr 1
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro h k hk
      refine nearEvent_mono hx (by positivity) ?_ h
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    · intro h; exact h m le_rfl
  simp_rw [heq]
  have hanti : Antitone nearCodeSetLE := fun m m' hmm' x hx => by
    simp only [nearCodeSetLE, mem_iInter] at hx ⊢
    exact fun k hk => hx k (hk.trans hmm')
  have hlim := tendsto_codeLaw_iInter (a := κ) (ρL := ρL) (ρR := ρR) measurableSet_nearCodeSetLE hanti (xL, xR)
  convert hlim using 2
  rw [← measure_eventOf_eq_codeLawS hκ hsep hE (MeasurableSet.iInter measurableSet_nearCodeSetLE)
    (Φ := fun s w τ => ∀ m k : ℕ, k ≤ m → NearEvent (1 / ((k : ℝ) + 1)) s w τ)
    (fun x _ _ => by simp only [nearCodeSetLE, mem_iInter]; rfl)
    (fun s w w' τ h hb m k hk => nearEvent_congr _ s w w' τ h (hb m k hk))]
  symm
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [IsIntegratedSLEEvolution.ae_not_isTermCluster_mark_oneForce hκ hx hρ hE,
    IsIntegratedSLEEvolution.ae_good_oneForce hκ hx hρ hE] with ω hmark ⟨hζ, hw, hw0, _⟩ hall
  obtain ⟨-, hTop, -⟩ := hall 0 0 le_rfl
  obtain ⟨η, hη⟩ := (ratVals_mem_topSet_iff hw hw0).1 hTop
  have hb : ∀ m : ℕ, RealNear (1 / ((m : ℝ) + 1)) (xL, xR) η := fun m => by
    have h := hall m m le_rfl
    rw [hζ] at h
    exact (nearEvent_top_iff hw hw0 hη _ _).1 h
  exact hmark η hη (isTermCluster_of_forall_realNear (s := (xL, xR)) hx hb)

end Canonical

/-! ### The canonical one-force law has a trace -/

/-- The Borel set of solution codes with infinite lifetime and a generating trace on `[0, ∞)` (any word). -/
def topCodeSetN {nL nR : ℕ} : Set (XCode nL nR) :=
  (fun x => (cw x, cζ x)) ⁻¹' {p : (ℝ≥0 → ℝ) × ℝ≥0∞ | p.2 = ⊤ ∧ (fun q : ℚ≥0 => p.1 q) ∈ topSet}

theorem measurableSet_topCodeSetN {nL nR : ℕ} : MeasurableSet (topCodeSetN (nL := nL) (nR := nR)) := by
  have hm : Measurable fun p : (ℝ≥0 → ℝ) × ℝ≥0∞ => fun q : ℚ≥0 => p.1 q :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_fst
  exact measurable_cw_cζ ((measurable_snd (measurableSet_singleton ⊤)).inter (hm measurableSet_topSet))

/-- At a separated one-force word with weight `≥ κ/2 − 2`, the canonical probability of no trace on `[0, ∞)` is zero. -/
theorem codeLaw_compl_topCodeSetN_eq_zero {κ : ℝ} (hκ : 0 < κ) {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ}
    (hρ : κ / 2 - 2 ≤ ρL 0) {s : (Fin 1 → ℝ) × (Fin 0 → ℝ)} (hs : s.1 0 < 0)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    codeLaw κ ρL ρR topCodeSetNᶜ s = 0 := by
  have hsep : ∀ (i : Fin 1) (j : Fin 0), s.1 i < s.2 j := fun _ j => j.elim0
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hev : ∀ᵐ ω ∂P, TopEvent (fun t => W t ω) (ζ ω) := by
    filter_upwards [hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ
      (isOrderedForceWord_oneLeft hs.le) (hasAdmissiblePartialSums_oneLeft hρ)
      (fun i => by rw [Fin.fin_one_eq_zero i]; exact hs) (fun j => j.elim0),
      IsIntegratedSLEEvolution.ae_good_oneForce hκ hs hρ hE] with ω ⟨hζ, η, hη⟩ ⟨_, hwc, hw0, _⟩
    rw [hζ]
    exact ⟨rfl, (ratVals_mem_topSet_iff hwc hw0).2 ⟨η, hη⟩⟩
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ TopEvent w τ)
    measurableSet_topCodeSetN.compl (fun _ _ _ => Iff.rfl) not_topEvent_congr
  rw [← e]
  exact ae_iff.1 hev

end InteractingSLE.ZhanGT4
