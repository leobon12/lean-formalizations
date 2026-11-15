/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Coordinates
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.Loewner.ForwardFlow
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Sec2.RestartPath
import InteractingSLE.Frozen.Spec.couplingMean
import InteractingSLE.Frozen.Spec.Chart_loewner
import InteractingSLE.Frozen.Spec.Chart_id

/-!
# The Loewner flow property for the coupling mean (Aux. lemma 53, deterministic part)

Packet PROVE-SEC5-D. Aux. lemma 53 (specification p. 245): "Conformal invariance of the Green kernel transports this
relative identity to the half-plane. The chain rule with the inherited derivative logarithm gives the canonical
finite-force mean from the current force coordinates". For a continuous driver `w`, `t, s ≥ 0` and the restarted driver
`w'(r) = w(t + r) − w(t)` (`f_{t+s} = f'_s ∘ f_t`, QuantumZipper's `fwdMap_add`):

* `logDerivFwd_add`: the inherited branch is additive, `log f_{t+s}′(z) = log f_t′(z) + log f'_s′(f_t z)`;
* `couplingMean_add`: `𝔥_{t+s}(z) = 𝔥'_s(f_t z) − χ arg f_t′(z)` — the coupling mean at the later time is the restarted
  coupling mean read through the chart `f_t` minus the chart's lift (rule (1.4) with lift `arg f_t′`);
* `image_fwdMapInv_diff_fwdHull`: `F_t(ℍ ∖ K'_s) = ℍ ∖ K_{t+s}` (the later hull seen through the chart);
* `couplingMean_add_loewner`: the same identity in the chart notation `Chart.id.loewner w t` at the points `F_t(ℍ ∖ K'_s)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Markov

variable {w : ℝ → ℝ} {z : ℂ} {t s : ℝ}

/-- **The inherited derivative logarithm is additive along the flow**:
`log f_{t+s}′(z) = log f_t′(z) + log f'_s′(f_t z)` for `z` not swallowed by time `t + s`. -/
theorem logDerivFwd_add (hw : Continuous w) (ht : 0 ≤ t) (hs : 0 ≤ s) (hz : z ∈ H \ fwdHull w (t + s)) :
    logDerivFwd w (t + s) z = logDerivFwd w t z + logDerivFwd (fun r => w (t + r) - w t) s (fwdMap w t z) := by
  have hts : 0 ≤ t + s := add_nonneg ht hs
  have hcont := Ito.continuousOn_two_div_fwdMap_sq hw hts hz
  have hint : ∀ a b, a ∈ Icc (0 : ℝ) (t + s) → b ∈ Icc (0 : ℝ) (t + s) →
      IntervalIntegrable (fun r => 2 / fwdMap w r z ^ 2) volume a b := fun a b ha hb =>
    (hcont.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (t + s) := ⟨le_rfl, hts⟩
  have htm : t ∈ Icc (0 : ℝ) (t + s) := ⟨ht, by linarith⟩
  have htop : t + s ∈ Icc (0 : ℝ) (t + s) := ⟨hts, le_rfl⟩
  unfold logDerivFwd
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 t h0 htm) (hint t (t + s) htm htop)]
  have hshift : ∫ r in t..t + s, 2 / fwdMap w r z ^ 2 = ∫ r in (0 : ℝ)..s, 2 / fwdMap w (t + r) z ^ 2 := by
    have := intervalIntegral.integral_comp_add_left (fun r => 2 / fwdMap w r z ^ 2) t (a := 0) (b := s)
    simpa only [add_zero] using this.symm
  have hcongr : ∫ r in (0 : ℝ)..s, 2 / fwdMap w (t + r) z ^ 2 =
      ∫ r in (0 : ℝ)..s, 2 / fwdMap (fun r => w (t + r) - w t) r (fwdMap w t z) ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    have hz' : z ∈ H \ fwdHull w (t + r) := Ito.mem_diff_fwdHull_of_le hz (by linarith [hr.2])
    rw [fwdMap_add hw hz.1 ht hr.1 (Ito.exists_isForwardSol_of_mem (by linarith [hr.1]) hz')]
  rw [hshift, hcongr]
  ring

/-- **The coupling mean at the later time through the chart `f_t`**: for `z` not swallowed by time `t + s`,
`𝔥_{t+s}(z) = 𝔥'_s(f_t z) − χ Im log f_t′(z)`, where `𝔥'` is the coupling mean of the restarted driver
`w'(r) = w(t + r) − w(t)` with the same harmonic function `u`. -/
theorem couplingMean_add (κ : ℝ) (u : ℂ → ℝ) (hw : Continuous w) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hz : z ∈ H \ fwdHull w (t + s)) :
    couplingMean κ w (t + s) u z =
      couplingMean κ (fun r => w (t + r) - w t) s u (fwdMap w t z) - chiC κ * (logDerivFwd w t z).im := by
  unfold couplingMean
  rw [fwdMap_add hw hz.1 ht hs (Ito.exists_isForwardSol_of_mem (add_nonneg ht hs) hz),
    logDerivFwd_add hw ht hs hz, Complex.add_im]
  ring

/-- **The later hull seen through the chart `f_t`**: `F_t(ℍ ∖ K'_s) = ℍ ∖ K_{t+s}`, where `K'` is the hull of the
restarted driver `w'(r) = w(t + r) − w(t)`. -/
theorem image_fwdMapInv_diff_fwdHull (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    fwdMapInv w t '' (H \ fwdHull (fun r => w (t + r) - w t) s) = H \ fwdHull w (t + s) := by
  have hdiff := fwdHull_add_diff hw ht hs
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hz := RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hv.1
    refine ⟨hz.1, fun hzK => hv.2 ?_⟩
    have hmem : fwdMapInv w t v ∈ fwdHull w (t + s) \ fwdHull w t := ⟨hzK, hz.2⟩
    rw [hdiff] at hmem
    have := hmem.2
    rwa [RS.fwdMap_fwdMapInv hw hw0 ht hv.1] at this
  · intro hz
    have hzt : z ∈ H \ fwdHull w t := Ito.mem_diff_fwdHull_of_le hz (by linarith)
    refine ⟨fwdMap w t z, ⟨Ito.im_fwdMap_pos hw ht hzt ⟨ht, le_rfl⟩, fun hK => hz.2 ?_⟩,
      RS.fwdMapInv_fwdMap hw hw0 ht hzt⟩
    have hmem : z ∈ {z ∈ H \ fwdHull w t | fwdMap w t z ∈ fwdHull (fun r => w (t + r) - w t) s} :=
      ⟨hzt, hK⟩
    rw [← hdiff] at hmem
    exact hmem.1

/-- **The integrand of the restarted clause** (rule (1.4) for the chart `Chart.id.loewner w t`, height shift `0`, lift
coefficient `χ`): at every point of `F_t(ℍ ∖ K'_s)`, the restarted coupling mean read through the chart minus `χ` times
the chart's lift is the original coupling mean at time `t + s`. -/
theorem couplingMean_add_loewner (κ : ℝ) (u : ℂ → ℝ) (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t)
    (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ (Chart.id.loewner w t).2.1 '' (H \ fwdHull (fun r => w (t + r) - w t) s)) :
    couplingMean κ (fun r => w (t + r) - w t) s u ((Chart.id.loewner w t).1 z) - 0 -
        chiC κ * (Chart.id.loewner w t).2.2 z = couplingMean κ w (t + s) u z := by
  have hz' : z ∈ H \ fwdHull w (t + s) := by
    rw [← image_fwdMapInv_diff_fwdHull hw hw0 ht hs]
    exact hz
  rw [couplingMean_add κ u hw ht hs hz']
  simp only [Chart.loewner, Chart.id, add_zero, sub_zero]

/-! ### Drivers continuous before a lifetime -/

/-- The coupling mean at time `t` only depends on the driver on `[0, T]`, `t ≤ T`. -/
theorem couplingMean_congr_of_eqOn {w w' : ℝ → ℝ} {T : ℝ} (h : EqOn w w' (Icc 0 T)) (ht : 0 ≤ t)
    (htT : t ≤ T) (κ : ℝ) (u : ℂ → ℝ) (z : ℂ) : couplingMean κ w t u z = couplingMean κ w' t u z := by
  unfold couplingMean
  rw [Ito.fwdMap_congr_of_eqOn_of_le h htT, Ito.logDerivFwd_congr_of_eqOn h ht htT]

/-- **The restart identities along a driver path continuous before its lifetime** (the form used by the frozen
coupling, driver `s ↦ w(s⁺)`; restarted driver `s ↦ w(T + s⁺) − w(T)`): for `T + r < ζ`,
`F_T(ℍ ∖ K'_r) = ℍ ∖ K_{T+r}`, and at every point of this set the restarted coupling mean read through the chart
`Chart.id.loewner w T` minus `χ` times its lift is the original coupling mean at time `T + r`. -/
theorem restart_path {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {T r : ℝ≥0} (hr : ((T + r : ℝ≥0) : ℝ≥0∞) < ζ) (κ : ℝ) (u : ℂ → ℝ) :
    (Chart.id.loewner (fun s : ℝ => w s.toNNReal) T).2.1 ''
        (H \ fwdHull (fun s : ℝ => w (T + s.toNNReal) - w T) r) =
      H \ fwdHull (fun s : ℝ => w s.toNNReal) ((T + r : ℝ≥0) : ℝ) ∧
    ∀ z ∈ (Chart.id.loewner (fun s : ℝ => w s.toNNReal) T).2.1 ''
        (H \ fwdHull (fun s : ℝ => w (T + s.toNNReal) - w T) r),
      couplingMean κ (fun s : ℝ => w (T + s.toNNReal) - w T) r u
          ((Chart.id.loewner (fun s : ℝ => w s.toNNReal) T).1 z) - 0 -
        chiC κ * (Chart.id.loewner (fun s : ℝ => w s.toNNReal) T).2.2 z =
      couplingMean κ (fun s : ℝ => w s.toNNReal) ((T + r : ℝ≥0) : ℝ) u z := by
  obtain ⟨t₂, hTr₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  have hTr₂' : ((T + r : ℝ≥0) : ℝ) < t₂ := by exact_mod_cast hTr₂
  have hT₂ : (T : ℝ) < t₂ := lt_of_le_of_lt (by push_cast; linarith [r.coe_nonneg]) hTr₂'
  have hr₂ : (r : ℝ) < t₂ - T := by push_cast at hTr₂'; linarith
  set v : ℝ → ℝ := fun s => w s.toNNReal with hv
  set v' : ℝ → ℝ := Ito.clampDrv v t₂ with hv'
  have hvc : Continuous v' := Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ)
  have heq : EqOn v' v (Icc 0 t₂) := Ito.clampDrv_eqOn
  have hv0 : v' 0 = 0 := by rw [heq ⟨le_rfl, t₂.coe_nonneg⟩]; simp [hv, hw0]
  have heq' : ∀ x ∈ Icc (0 : ℝ) t₂, v x = v' x := fun x hx => (heq hx).symm
  -- the restarted drivers
  set u₁ : ℝ → ℝ := fun s => w (T + s.toNNReal) - w T with hu₁
  set u₂ : ℝ → ℝ := fun s => v' (T + s) - v' T with hu₂
  have hTmem : (T : ℝ) ∈ Icc (0 : ℝ) t₂ := ⟨T.coe_nonneg, hT₂.le⟩
  have hu : ∀ x ∈ Icc (0 : ℝ) (t₂ - T), u₁ x = u₂ x := fun x hx => by
    have hx2 : (T : ℝ) + x ∈ Icc (0 : ℝ) t₂ := ⟨by linarith [hx.1, T.coe_nonneg], by linarith [hx.2]⟩
    simp only [hu₁, hu₂]
    rw [heq hx2, heq hTmem]
    simp only [hv, Real.toNNReal_coe, Sec2.Restart.toNNReal_add_of_nonneg T hx.1]
  have huEq : EqOn u₁ u₂ (Icc 0 (t₂ - T)) := fun x hx => hu x hx
  have hK' : fwdHull u₁ r = fwdHull u₂ r := fwdHull_eq_of_eqOn r.coe_nonneg hr₂ hu
  have hK : fwdHull v ((T + r : ℝ≥0) : ℝ) = fwdHull v' ((T + r : ℝ≥0) : ℝ) :=
    fwdHull_eq_of_eqOn (T + r).coe_nonneg hTr₂' heq'
  have hinv : fwdMapInv v T = fwdMapInv v' T := fwdMapInv_eq_of_eqOn T.coe_nonneg hT₂ heq'
  have hfwd : ∀ z, fwdMap v T z = fwdMap v' T z := fun z =>
    fwdMap_eq_of_eqOn T.coe_nonneg fun x hx => heq' x ⟨hx.1, hx.2.trans hT₂.le⟩
  have hlog : ∀ z, logDerivFwd v T z = logDerivFwd v' T z := fun z =>
    Ito.logDerivFwd_congr_of_eqOn (EqOn.symm heq) T.coe_nonneg hT₂.le
  have hcm₁ : ∀ y, couplingMean κ u₁ r u y = couplingMean κ u₂ r u y := fun y =>
    couplingMean_congr_of_eqOn huEq r.coe_nonneg hr₂.le κ u y
  have hcm : ∀ z, couplingMean κ v ((T + r : ℝ≥0) : ℝ) u z = couplingMean κ v' ((T + r : ℝ≥0) : ℝ) u z :=
    fun z => couplingMean_congr_of_eqOn (EqOn.symm heq) (T + r).coe_nonneg hTr₂'.le κ u z
  have hchart : Chart.id.loewner v T = Chart.id.loewner v' T := by
    simp only [Chart.loewner, Chart.id, hinv, hlog, hfwd]
  have himg := image_fwdMapInv_diff_fwdHull hvc hv0 T.coe_nonneg r.coe_nonneg
  have hcast : ((T + r : ℝ≥0) : ℝ) = (T : ℝ) + r := NNReal.coe_add T r
  rw [hchart, hK', hK]
  refine ⟨?_, fun z hz => ?_⟩
  · rw [hcast]; exact himg
  · rw [hcm₁, hcm, hcast]
    exact couplingMean_add_loewner κ u hvc hv0 T.coe_nonneg r.coe_nonneg hz

end Markov

end Sec5

end InteractingSLE
