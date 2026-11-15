/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TpRead

/-!
# The launch gauge at every root, part 2: the gauge from a read-back physical curve

Packet PROVE-GW2-RELDET (round 27). Round 24's launch gauge (`launchGauge`) with the readers of `GW2TpRead` (built
from a read-back `X` of the physical curve) in place of the root-`0` readers, and read strictly to the LEFT of the own
time, so that the path frozen at `t` is never read at its endpoint:

* `dyadS`, `evalDnS`: the causal evaluation at the dyadic times strictly below `τ` (`0` at `τ = 0`);
  `evalDnS_eq_of_continuousWithinAt`, `evalDnS_congr`, `evalDnS_zero`, `measurable_evalDnS`;
* `launchGaugeOfS`, `ownTimeC`, **`launchGaugeC κ θ B T cap X`**: Borel (`measurable_launchGaugeC`), causal
  (`isCausal_launchGaugeC`), nonnegative;
* **`launchGaugeC_eq`**: along one sample, the gauge at relative time `t` is the normalized launch distance at the own
  time `min cap (t' − T)` (`t'` the physical time of `t`);
* **`launchGaugeC_sample`**: along one sample, the gauge is continuous before the coordinates' life, positive before
  `launchLife` and zero at it, and `0 < launchLife` (round 24's `launchGauge_sample` for these readers).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId
open Restart (BoundaryWord)

/-! ### Evaluation strictly to the left -/

/-- The dyadic time strictly below `τ` (`0` at `τ = 0`). -/
def dyadS (n : ℕ) (τ : ℝ≥0) : ℝ≥0 := dyadLo n τ - ((2 : ℝ≥0) ^ n)⁻¹

theorem dyadS_le (n : ℕ) (τ : ℝ≥0) : dyadS n τ ≤ τ := tsub_le_self.trans (dyadLo_le n τ)

theorem dyadS_lt (n : ℕ) {τ : ℝ≥0} (hτ : 0 < τ) : dyadS n τ < τ := by
  unfold dyadS
  have hε : 0 < ((2 : ℝ≥0) ^ n)⁻¹ := inv_pos.2 (pow_pos two_pos n)
  by_cases h : ((2 : ℝ≥0) ^ n)⁻¹ ≤ dyadLo n τ
  · exact (tsub_lt_self (hε.trans_le h) hε).trans_le (dyadLo_le n τ)
  · rw [tsub_eq_zero_of_le (le_of_lt (not_le.1 h))]
    exact hτ

theorem dyadS_zero (n : ℕ) : dyadS n 0 = 0 := le_zero_iff.1 (dyadS_le n 0)

theorem tendsto_dyadS (τ : ℝ≥0) : Tendsto (fun n => dyadS n τ) atTop (𝓝 τ) := by
  have h1 := tendsto_dyadLo τ
  have h2 : Tendsto (fun n : ℕ => ((2 : ℝ≥0) ^ n)⁻¹) atTop (𝓝 0) := by
    have h := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num)
    refine h.congr fun n => ?_
    rw [inv_pow]
  have h := h1.sub h2
  rw [tsub_zero] at h
  exact h

/-- **Causal evaluation strictly to the left**: the limsup of the values at the dyadic times below `τ`. -/
def evalDnS (p : ℝ≥0 → ℝ) (τ : ℝ≥0) : ℝ := limsup (fun n => p (dyadS n τ)) atTop

theorem evalDnS_eq_of_continuousWithinAt {p : ℝ≥0 → ℝ} {τ : ℝ≥0} (hp : ContinuousWithinAt p (Iic τ) τ) :
    evalDnS p τ = p τ := by
  have ht : Tendsto (fun n => dyadS n τ) atTop (𝓝[Iic τ] τ) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadS τ, Eventually.of_forall fun n => dyadS_le n τ⟩
  exact (hp.tendsto.comp ht).limsup_eq

theorem evalDnS_zero (p : ℝ≥0 → ℝ) : evalDnS p 0 = p 0 := by
  unfold evalDnS
  simp only [dyadS_zero, limsup_const]

theorem evalDnS_congr {p p' : ℝ≥0 → ℝ} {τ : ℝ≥0} (hτ : 0 < τ) (h : ∀ u < τ, p u = p' u) :
    evalDnS p τ = evalDnS p' τ := by
  unfold evalDnS
  congr 1
  funext n
  exact h _ (dyadS_lt n hτ)

theorem measurable_evalDnS {α : Type*} [MeasurableSpace α] {p : α → ℝ≥0 → ℝ}
    (hp : ∀ t, Measurable fun a => p a t) {τ : α → ℝ≥0} (hτ : Measurable τ) :
    Measurable fun a => evalDnS (p a) (τ a) := by
  refine Measurable.limsup fun n => ?_
  set g : α × ℕ → ℝ := fun q => p q.1 (((q.2 : ℝ) / 2 ^ n).toNNReal - ((2 : ℝ≥0) ^ n)⁻¹) with hg
  have hgm : Measurable g := measurable_from_prod_countable_left fun m =>
    show Measurable fun a => p a (((m : ℝ) / 2 ^ n).toNNReal - ((2 : ℝ≥0) ^ n)⁻¹) from hp _
  have hfl : Measurable fun a => ⌊(τ a : ℝ) * 2 ^ n⌋₊ :=
    ((measurable_coe_nnreal_real.comp hτ).mul_const _).nat_floor
  exact hgm.comp (measurable_id.prodMk hfl)

/-! ### The gauge -/

section Defs

variable (κ θ : ℝ) (B : (ℝ≥0 → ℝ) → BoundaryWord) (T cap : ℝ≥0) (X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ)

/-- The normalized launch distance, read strictly to the left of the own time `σ`. -/
def launchGaugeOfS (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : ℝ :=
  if launchStart κ θ B w = 0 then 1 else min 1 (max 0 (evalDnS (launchDist κ θ B T w) σ) / launchStart κ θ B w)

/-- The candidate's own time at relative time `t`, capped at `cap`. -/
def ownTimeC (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℝ≥0 := min cap ((capT X t p).toNNReal - T)

/-- **The launch gauge read from a read-back physical curve.** -/
def launchGaugeC : GaugeReadout := fun t p =>
  launchGaugeOfS κ θ B T (drvC X (frz t p)) (ownTimeC T cap X t (frz t p))

end Defs

variable {κ θ : ℝ} {B : (ℝ≥0 → ℝ) → BoundaryWord} {T cap : ℝ≥0} {X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ}

theorem measurable_launchGaugeOfS (hB : Measurable B) {α : Type*} [MeasurableSpace α] {w : α → ℝ≥0 → ℝ}
    (hw : Measurable w) {σ : α → ℝ≥0} (hσ : Measurable σ) :
    Measurable fun a => launchGaugeOfS κ θ B T (w a) (σ a) := by
  unfold launchGaugeOfS
  have hs : Measurable fun a => launchStart κ θ B (w a) := (measurable_launchStart hB).comp hw
  have he : Measurable fun a => evalDnS (launchDist κ θ B T (w a)) (σ a) :=
    measurable_evalDnS (p := fun a σ' => launchDist κ θ B T (w a) σ')
      (fun σ' => (measurable_launchDist hB σ').comp hw) hσ
  exact Measurable.ite (hs (measurableSet_singleton 0)) measurable_const
    (measurable_const.min ((measurable_const.max he).div hs))

theorem measurable_ownTimeC (hX : ∀ u, Measurable (X u)) (t : ℝ≥0) : Measurable (ownTimeC T cap X t) :=
  measurable_const.min ((measurable_capT hX t).real_toNNReal.sub measurable_const)

/-- **The launch gauge is Borel.** -/
theorem measurable_launchGaugeC (hB : Measurable B) (hX : ∀ u, Measurable (X u)) (t : ℝ≥0) :
    Measurable (launchGaugeC κ θ B T cap X t) :=
  measurable_launchGaugeOfS hB ((measurable_drvC_path hX).comp (measurable_frz t))
    ((measurable_ownTimeC hX t).comp (measurable_frz t))

/-- **The launch gauge is causal** (it reads the path frozen at `t`). -/
theorem isCausal_launchGaugeC : IsCausal (launchGaugeC κ θ B T cap X) := by
  intro t r w w' h
  simp only [launchGaugeC, frz, LP.freezeAt_congr h]

theorem launchGaugeOfS_nonneg (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : 0 ≤ launchGaugeOfS κ θ B T w σ := by
  unfold launchGaugeOfS
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (div_nonneg (le_max_left _ _) (launchStart_nonneg w))

theorem launchGaugeC_nonneg (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ launchGaugeC κ θ B T cap X t p :=
  launchGaugeOfS_nonneg _ _

/-- **At own time `0` the gauge is `1`.** -/
theorem launchGaugeOfS_zero (w : ℝ≥0 → ℝ) : launchGaugeOfS κ θ B T w 0 = 1 := by
  unfold launchGaugeOfS
  rw [evalDnS_zero, launchDist_zero]
  split_ifs with h
  · rfl
  · rw [max_eq_right (launchStart_nonneg w), div_self h, min_self]

/-! ### Along one sample -/

section Sample

variable {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}
  (hXcaus : ∀ u r w w', (∀ v ≤ u, w v = w' v) → X u (r, w) = X u (r, w'))

include hXcaus in
/-- **The gauge along one sample**: with `t'` the physical time of the relative time `t` before the life, the gauge
is the normalized launch distance at the own time `min cap (t' − T)`. -/
theorem launchGaugeC_eq (hBc : ∀ w : ℝ≥0 → ℝ, (∀ u ≤ T, w u = W u) → B w = B W)
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L})
    {t t' : ℝ≥0} (htL : (t : ℝ≥0∞) < L) (ht' : (t' : ℝ≥0∞) < Tc) (hat : a t' = t) :
    launchGaugeC κ θ B T cap X t p =
      if launchStart κ θ B W = 0 then 1 else min 1 (launchDist κ θ B T W (min cap (t' - T)) / launchStart κ θ B W) := by
  obtain ⟨r, w⟩ := p
  have hcap : capT X t (frz t (r, w)) = t' := by
    rw [frz, capT_freeze hXcaus r w t le_rfl]
    exact capT_eq hW hW0 hγ ham hback hread hXc htL ht' hat
  have hown : ownTimeC T cap X t (frz t (r, w)) = min cap (t' - T) := by
    rw [ownTimeC, hcap, Real.toNNReal_coe]
  -- the physical driver of the frozen path is the explored driver strictly before `t'`
  have hdrv : ∀ u < t', drvC X (frz t (r, w)) u = W u := by
    intro u hu
    have hut : (u : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 hu.le).trans_lt ht'
    rw [frz, drvC_freeze hXcaus r w t fun ρ hρ => ?_]
    · exact drvC_eq hW hW0 hγ ham haL hback hread hXc hut
    · have hρt : (ρ : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 (hρ.trans hu.le)).trans_lt ht'
      rw [relT_eq hW hW0 hγ ham haL hback hread hXc hρt, ← ENNReal.ofReal_coe_nnreal, ← hat]
      have h1 : a ρ < a t' := ham hρt ht' (lt_of_le_of_lt hρ hu)
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (haL ρ hρt).1).2 h1
  unfold launchGaugeC
  rw [hown]
  by_cases hσ : min cap (t' - T) = 0
  · rw [hσ, launchGaugeOfS_zero, launchDist_zero]
    split_ifs with h
    · rfl
    · rw [div_self h, min_self]
  have hσpos : 0 < min cap (t' - T) := pos_iff_ne_zero.2 hσ
  have hT : T < t' := by
    by_contra hle
    exact hσ (by rw [tsub_eq_zero_of_le (not_lt.1 hle), min_eq_right zero_le])
  have hBe : B (drvC X (frz t (r, w))) = B W := hBc _ fun u hu => hdrv u (hu.trans_lt hT)
  have hst : launchStart κ θ B (drvC X (frz t (r, w))) = launchStart κ θ B W := by
    unfold launchStart; rw [hBe]
  have hσt : T + min cap (t' - T) ≤ t' := by
    calc T + min cap (t' - T) ≤ T + (t' - T) := add_le_add_right (min_le_right _ _) T
      _ = t' := add_tsub_cancel_of_le hT.le
  have hev : evalDnS (launchDist κ θ B T (drvC X (frz t (r, w)))) (min cap (t' - T)) =
      launchDist κ θ B T W (min cap (t' - T)) := by
    rw [evalDnS_congr (p' := launchDist κ θ B T W) hσpos fun σ hσ' => ?_]
    · exact evalDnS_eq_of_continuousWithinAt (continuous_launchDist hγ hW hW0).continuousWithinAt
    · unfold launchDist launchTr
      rw [hBe, LP.traceAt_congr (w' := Sec7.shiftNN W T) fun v hv => ?_]
      simp only [Sec7.shiftNN]
      have h1 : T + v < t' := (add_lt_add_right (lt_of_le_of_lt hv hσ') T).trans_le hσt
      rw [hdrv _ h1, hdrv _ (lt_of_le_of_lt le_self_add h1)]
  have hnn : 0 ≤ launchDist κ θ B T W (min cap (t' - T)) := badDist_nonneg _ _
  unfold launchGaugeOfS
  rw [hst, hev, max_eq_right hnn]

include hXcaus in
/-- **The launch gauge along one sample of relative coordinates** (any root): continuous before the life, positive
before `launchLife` and zero at it, and `0 < launchLife`. -/
theorem launchGaugeC_sample (hBc : ∀ w : ℝ≥0 → ℝ, (∀ u ≤ T, w u = W u) → B w = B W)
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L}) :
    0 < launchLife κ θ B T cap W a Tc ∧
      ContinuousOn (fun t => launchGaugeC κ θ B T cap X t p) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < launchLife κ θ B T cap W a Tc →
        0 < launchGaugeC κ θ B T cap X t p) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = launchLife κ θ B T cap W a Tc →
        launchGaugeC κ θ B T cap X t p = 0 := by
  classical
  set f := launchDist κ θ B T W with hfdef
  set d0 := launchStart κ θ B W with hd0def
  have hfc : Continuous f := continuous_launchDist hγ hW hW0
  have hf0 : f 0 = d0 := launchDist_zero W
  have hfnn : ∀ σ, 0 ≤ f σ := fun σ => badDist_nonneg _ _
  set ψ : ℝ≥0 → ℝ≥0 := fun t => (capT X t p).toNNReal with hψdef
  have hψ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (ψ t : ℝ≥0∞) < Tc ∧ a (ψ t) = t := by
    intro t ht
    obtain ⟨t', ht', hat⟩ := hback t ht
    have he : ψ t = t' := by
      simp only [hψdef, capT_eq hW hW0 hγ ham hback hread hXc ht ht' hat, Real.toNNReal_coe]
    rw [he]
    exact ⟨ht', hat⟩
  set g : ℝ≥0 → ℝ := fun σ => if d0 = 0 then 1 else min 1 (f σ / d0) with hgdef
  have hrep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → launchGaugeC κ θ B T cap X t p = g (min cap (ψ t - T)) := fun t ht =>
    launchGaugeC_eq hXcaus hBc hγ hW hW0 ham haL hback hread hXc ht (hψ t ht).1 (hψ t ht).2
  set Z : Set ℝ≥0 := {σ | σ ≤ cap ∧ f σ = 0} with hZdef
  have hZc : IsClosed Z := (isClosed_le continuous_id continuous_const).inter (isClosed_eq hfc continuous_const)
  -- the life, unfolded
  have hlife : launchLife κ θ B T cap W a Tc =
      if d0 ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc then
        ENNReal.ofReal (a (T + sInf Z)) else ⊤ := rfl
  -- the gauge where the launch distance vanishes at the own time of `t`
  refine ⟨?_, ?_, fun t ht hlt => ?_, fun t ht heq => ?_⟩
  · -- the life is positive
    rw [hlife]
    split_ifs with hc
    · obtain ⟨hd, σ₀, hσ₀, hf₀, hT₀⟩ := hc
      have hmem : sInf Z ∈ Z := hZc.csInf_mem ⟨σ₀, hσ₀, hf₀⟩ (OrderBot.bddBelow Z)
      have hle : sInf Z ≤ σ₀ := csInf_le (OrderBot.bddBelow Z) ⟨hσ₀, hf₀⟩
      have hTc : ((T + sInf Z : ℝ≥0) : ℝ≥0∞) < Tc :=
        (ENNReal.coe_le_coe.2 (add_le_add_right hle T)).trans_lt hT₀
      have hpos : 0 < T + sInf Z := by
        refine lt_of_le_of_ne zero_le fun h0 => ?_
        have hz : sInf Z = 0 := le_zero_iff.1 (le_of_le_of_eq le_add_self h0.symm)
        have := hmem.2
        rw [hz, hf0] at this
        exact hd this
      have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 zero_le).trans_lt hTc
      have := ham h0Tc hTc hpos
      rw [ha0] at this
      exact ENNReal.ofReal_pos.2 this
    · exact ENNReal.zero_lt_top
  · -- continuity
    have hψc := continuousOn_invClock ham haL hψ
    have hg : Continuous g := by
      by_cases hd : d0 = 0
      · simp only [hgdef, hd, ↓reduceIte]
        exact continuous_const
      · simp only [hgdef, hd, ↓reduceIte]
        exact continuous_const.min (hfc.div_const d0)
    have hσc : ContinuousOn (fun t => min cap (ψ t - T)) {t | (t : ℝ≥0∞) < L} :=
      (continuous_const.min (continuous_id.sub continuous_const)).comp_continuousOn hψc
    exact (hg.comp_continuousOn hσc).congr fun t ht => hrep t ht
  · -- positivity before the life
    rw [hrep t ht]
    by_cases hd : d0 = 0
    · simp only [hgdef, hd, ↓reduceIte, zero_lt_one]
    have hd0 : 0 < d0 := lt_of_le_of_ne (launchStart_nonneg W) (Ne.symm hd)
    simp only [hgdef, hd, ↓reduceIte]
    refine lt_min one_pos (div_pos (lt_of_le_of_ne (hfnn _) fun hf => ?_) hd0)
    set σt := min cap (ψ t - T) with hσt
    by_cases hT : T ≤ ψ t
    · have hσle : T + σt ≤ ψ t := by
        calc T + σt ≤ T + (ψ t - T) := add_le_add_right (min_le_right _ _) T
          _ = ψ t := add_tsub_cancel_of_le hT
      have hTc : ((T + σt : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 hσle).trans_lt (hψ t ht).1
      have hc : d0 ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc :=
        ⟨hd, σt, min_le_left _ _, hf.symm, hTc⟩
      rw [hlife, ite_eq_left_of_eq_true _ _ (eq_true hc)] at hlt
      have hle : sInf Z ≤ σt := csInf_le (OrderBot.bddBelow Z) ⟨min_le_left _ _, hf.symm⟩
      have hT1 : T + sInf Z ≤ ψ t := (add_le_add_right hle T).trans hσle
      have h1 : a (T + sInf Z) ≤ a (ψ t) :=
        ham.monotoneOn ((ENNReal.coe_le_coe.2 hT1).trans_lt (hψ t ht).1) (hψ t ht).1 hT1
      rw [(hψ t ht).2] at h1
      have h2 : ENNReal.ofReal (a (T + sInf Z)) ≤ (t : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal h1
      exact absurd hlt (not_lt.2 h2)
    · have h0 : σt = 0 := by
        rw [hσt, tsub_eq_zero_of_le (le_of_lt (not_le.1 hT)), min_eq_right (zero_le (a := cap))]
      rw [h0, hf0] at hf
      exact hd hf.symm
  · -- zero at the life
    have hne : launchLife κ θ B T cap W a Tc ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have hc : d0 ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ f σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc := by
      by_contra hc
      rw [hlife, ite_eq_right_of_eq_false _ _ (eq_false hc)] at hne
      exact hne rfl
    rw [hlife, ite_eq_left_of_eq_true _ _ (eq_true hc)] at heq
    obtain ⟨hd, σ₀, hσ₀, hf₀, hT₀⟩ := hc
    set τ := sInf Z with hτ
    have hmem : τ ∈ Z := hZc.csInf_mem ⟨σ₀, hσ₀, hf₀⟩ (OrderBot.bddBelow Z)
    have hle : τ ≤ σ₀ := csInf_le (OrderBot.bddBelow Z) ⟨hσ₀, hf₀⟩
    have hTc : ((T + τ : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 (add_le_add_right hle T)).trans_lt hT₀
    have hat : a (T + τ) = t := by
      have h0 := (haL _ hTc).1
      have h1 : ENNReal.ofReal (a (T + τ)) = ENNReal.ofReal (t : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact heq.symm
      exact (ENNReal.ofReal_eq_ofReal_iff h0 t.coe_nonneg).1 h1
    have hψt : ψ t = T + τ := by
      refine ham.injOn (hψ t ht).1 hTc ?_
      rw [(hψ t ht).2, hat]
    rw [hrep t ht, hψt, add_tsub_cancel_left, min_eq_right hmem.1]
    simp only [hgdef, hd, ↓reduceIte, hmem.2, zero_div, min_eq_right zero_le_one]

end Sample

end InteractingSLE.Theorem14.GW2Rd
