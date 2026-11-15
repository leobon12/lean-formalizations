/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi4Mart

/-!
# The critical side oscillation is small after a tight time

Packet PROVE-TRIALS-HI4. Specification §7.3, Aux. lemma 111 ("Both totals are at least `c`"; "A sole right mark is
allowed to continue"). Consider an evolution whose only nonzero weights are `r` at the nearest left mark and `s` at
the nearest right mark, with `s ≥ κ/2 − 2` (critical or supercritical). At a deterministic time `q`, on an event
`A ∈ 𝓕_q` where the right spread is below the nearest right gap and the Lyapunov value
`Φ = (Δ/R₀)^μ + K (Δ/D)^μ` is at most `η` (`critVal`), the probability that later the spread reaches the nearest
gap, or the side oscillation `∫_q^t (1/R₀² − 1/X²)` exceeds `4/μ`, while the nearest right mark is never hit and the
lifetime is infinite, is at most `η P(A)` (`measure_critBad_le`).

Proof: optional sampling from `q` of the localized Itô martingale of `Φ` (cut off below `e_m/2`) at the exit `ρ_m`
from `{e_m < Δ < R₀}` capped by `m`; the generator is `≤ −(μ/4)(1/R₀² − 1/X²)` there (`critGenE_le`), so
`Z_m = η + M_{ρ_m} − M_q` dominates `Φ(ρ_m) + (μ/4) ∫_q^{ρ_m} osc`, with `∫_A Z_m = η P(A)`. On the bad event, as
`m → ∞` either the exit is through `Δ = R₀`, where `Φ ≥ 1`, or the oscillation exceeds `4/μ`; Fatou concludes.

## Main results

* `critMu`, `critK`, `critVal`, `critBad`;
* `critGen_le_path` (the generator bound along the path);
* **`measure_critBad_le`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi4

open Zhan Clock ZhanGT4 TrialsHi3

/-! ### Constants -/

/-- The exponent `μ = min(1, 1/(2κ))`. -/
def critMu (κ : ℝ) : ℝ := min 1 (1 / (2 * κ))

/-- The weight `K = 2|r|(1 + 4|r|)` of the cross-gap term. -/
def critK (r : ℝ) : ℝ := 2 * |r| * (1 + 4 * |r|)

theorem critMu_pos {κ : ℝ} (hκ : 0 < κ) : 0 < critMu κ := lt_min one_pos (by positivity)

theorem critMu_le_one (κ : ℝ) : critMu κ ≤ 1 := min_le_left _ _

theorem mul_critMu_le {κ : ℝ} (hκ : 0 < κ) : κ * critMu κ ≤ 1 / 2 := by
  have h := min_le_right 1 (1 / (2 * κ))
  calc κ * critMu κ ≤ κ * (1 / (2 * κ)) := mul_le_mul_of_nonneg_left h hκ.le
    _ = 1 / 2 := by field_simp

theorem critK_nonneg (r : ℝ) : 0 ≤ critK r := by unfold critK; positivity

/-- **The Lyapunov value** `(Δ/R₀)^μ + K (Δ/D)^μ` of a state `W = w`, `V^{L,0} = l`, `V^{R,0} = r₀`,
`V^{R,last} = r₁`. -/
def critVal (κ r w l r₀ r₁ : ℝ) : ℝ := ((r₁ - r₀) / (r₀ - w)) ^ critMu κ + critK r * ((r₁ - r₀) / (r₀ - l)) ^ critMu κ

/-- **The bad event after `q`**: infinite lifetime, the nearest right mark never hit, and after `q` either the right
spread reaches the nearest right gap or the side oscillation exceeds `C`. -/
def critBad {Ω : Type*} {nR : ℕ} (C : ℝ) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ζ ω = ⊤ ∧ (∀ t, W t ω < VR 0 t ω) ∧
    ((∃ t, q ≤ t ∧ VR 0 t ω - W t ω ≤ VR (Fin.last nR) t ω - VR 0 t ω) ∨
      ∃ t, q ≤ t ∧ C < ∫ s in (q : ℝ)..t, (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
        1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2))}

/-! ### The generator bound along the path -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The generator bound along the path** at a time where the nearest left and right gaps are positive and
`0 < Δ ≤ R₀`. -/
theorem critGen_le_path (hρL : ∀ i, i ≠ 0 → ρL i = 0) (hρR : ∀ j, j ≠ 0 → ρR j = 0) (hs : κ / 2 - 2 ≤ ρR 0)
    {μ K : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hκμ : κ * μ ≤ 1 / 2) (hK : 2 * |ρL 0| * (1 + 4 * |ρL 0|) ≤ K)
    {t : ℝ≥0} (hL : vL 0 t < w t) (hR : w t < vR 0 t) (hΔ : 0 < vR (Fin.last nR) t - vR 0 t)
    (hΔR : vR (Fin.last nR) t - vR 0 t ≤ vR 0 t - w t) :
    critGen κ ρL ρR μ K w vL vR (t : ℝ) ≤
      -(μ / 4 * (1 / (vR 0 t - w t) ^ 2 - 1 / (vR (Fin.last nR) t - w t) ^ 2)) := by
  set R := vR 0 t - w t with hRdef
  set Δ := vR (Fin.last nR) t - vR 0 t with hΔdef
  set L := w t - vL 0 t with hLdef
  have hR0 : 0 < R := sub_pos.2 hR
  have hL0 : 0 < L := sub_pos.2 hL
  have hsumL : ∑ i, ρL i * (w t - vL i t)⁻¹ = ρL 0 * L⁻¹ :=
    Finset.sum_eq_single 0 (fun i _ hi => by rw [hρL i hi, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)
  have hsumR : ∑ j, ρR j * (w t - vR j t)⁻¹ = ρR 0 * (w t - vR 0 t)⁻¹ :=
    Finset.sum_eq_single 0 (fun j _ hj => by rw [hρR j hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)
  have hdrift : driftX ρL ρR 0 w vL vR t = (2 + ρR 0) / R - ρL 0 / L := by
    simp only [driftX, hsumL, hsumR]
    rw [show w t - vR 0 t = -R by simp only [hRdef]; ring, ← hRdef]
    field_simp
    ring
  have hX : vR (Fin.last nR) t - w t = R + Δ := by simp only [hRdef, hΔdef]; ring
  have hD : vR 0 t - vL 0 t = R + L := by simp only [hRdef, hLdef]; ring
  have hgD : 2 / (vR 0 t - w t) - 2 / (vL 0 t - w t) = 2 / R + 2 / L := by
    rw [show vL 0 t - w t = -L by simp only [hLdef]; ring, div_neg]; ring
  have e : critGen κ ρL ρR μ K w vL vR (t : ℝ) =
      critGenE κ μ K R Δ (R + L) ((2 + ρR 0) / R - ρL 0 / L) (2 / (R + Δ) - 2 / R) (2 / R + 2 / L) := by
    simp only [critGen, Real.toNNReal_coe]
    rw [hdrift, hX, hD, hgD]
  rw [e, hX]
  exact critGenE_le hR0 hΔ hL0 hΔR hs hμ hμ1 hκμ hK

/-- The oscillation integrand `1/R₀² − 1/X²` is nonnegative where the nearest right gap is positive. -/
theorem osc_nonneg (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hpos : w t < vR 0 t) : 0 ≤ 1 / (vR 0 t - w t) ^ 2 - 1 / (vR (Fin.last nR) t - w t) ^ 2 := by
  have hR := sub_pos.2 hpos
  have hX : vR 0 t - w t ≤ vR (Fin.last nR) t - w t :=
    sub_le_sub_right (hp.isForcePath.monotone_vR ht (Fin.zero_le _)) _
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hR.le hX 2)

/-- The oscillation integrand is continuous on `[t₁, t₂]`, `t₂ < ζ`, where the nearest right gap is positive. -/
theorem continuousOn_osc (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {t₁ t₂ : ℝ≥0}
    (ht₂ : (t₂ : ℝ≥0∞) < ζ) (hpos : ∀ s : ℝ≥0, t₁ ≤ s → s ≤ t₂ → w s < vR 0 s) :
    ContinuousOn (fun s : ℝ => 1 / (vR 0 s.toNNReal - w s.toNNReal) ^ 2 -
      1 / (vR (Fin.last nR) s.toNNReal - w s.toNNReal) ^ 2) (Icc (t₁ : ℝ) t₂) := by
  have hF := hp.isForcePath
  have hmaps : MapsTo (fun s : ℝ => s.toNNReal) (Icc (t₁ : ℝ) t₂) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht₂
  have hc : ∀ (f : ℝ≥0 → ℝ), ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} →
      ContinuousOn (fun s : ℝ => f s.toNNReal) (Icc (t₁ : ℝ) t₂) := fun f hf =>
    hf.comp continuous_real_toNNReal.continuousOn hmaps
  have hpos' : ∀ s ∈ Icc (t₁ : ℝ) t₂, w s.toNNReal < vR 0 s.toNNReal := fun s hs =>
    hpos _ ((Real.le_toNNReal_iff_coe_le (t₁.coe_nonneg.trans hs.1)).2 hs.1) (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hX : ∀ s ∈ Icc (t₁ : ℝ) t₂, vR 0 s.toNNReal - w s.toNNReal ≤ vR (Fin.last nR) s.toNNReal - w s.toNNReal :=
    fun s hs => sub_le_sub_right (hF.monotone_vR (hmaps hs) (Fin.zero_le _)) _
  refine ContinuousOn.sub (continuousOn_const.div (((hc _ (hF.continuousOn_vR 0)).sub
    (hc _ hF.continuousOn_w)).pow 2) fun s hs => ?_) (continuousOn_const.div (((hc _ (hF.continuousOn_vR _)).sub
    (hc _ hF.continuousOn_w)).pow 2) fun s hs => ?_)
  · have := hpos' s hs; positivity
  · have h1 := hpos' s hs; have h2 := hX s hs
    have : 0 < vR (Fin.last nR) s.toNNReal - w s.toNNReal := by linarith
    positivity

end Path

/-! ### The main estimate -/

section Main

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- A continuous function above `e` on `[q, r)` is at least `e` at `r`. -/
theorem le_of_lt_on_Ico {f : ℝ≥0 → ℝ} {q r : ℝ≥0} {e : ℝ} (hc : ContinuousOn f (Icc q r)) (hqr : q < r)
    (h : ∀ s, q ≤ s → s < r → e < f s) : e ≤ f r := by
  have hca : ContinuousWithinAt f (Ico q r) r := (hc r ⟨hqr.le, le_rfl⟩).mono Ico_subset_Icc_self
  have hne : (𝓝[Ico q r] r).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hqr.ne]
    exact ⟨hqr.le, le_rfl⟩
  exact ge_of_tendsto hca (eventually_nhdsWithin_of_forall fun s hs => (h s hs.1 hs.2).le)

/-- **The critical side oscillation after a tight time** (Aux. lemma 111, driver form). -/
theorem measure_critBad_le (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hx : 1 < xR 0 - xL 0) (hxR : xR 0 < xR (Fin.last nR))
    (hρL : ∀ i, i ≠ 0 → ρL i = 0) (hρR : ∀ j, j ≠ 0 → ρR j = 0) (hs : κ / 2 - 2 ≤ ρR 0) {q : ℝ≥0}
    {A : Set Ω} (hA : MeasurableSet[usualAugmentation 𝓕 P q] A) {η : ℝ} (hη : 0 ≤ η)
    (hAq : ∀ ω ∈ A, (q : ℝ≥0∞) < ζ ω → VR (Fin.last nR) q ω - VR 0 q ω < VR 0 q ω - W q ω ∧
      critVal κ (ρL 0) (W q ω) (VL 0 q ω) (VR 0 q ω) (VR (Fin.last nR) q ω) ≤ η) :
    P (A ∩ critBad (4 / critMu κ) q W VR ζ) ≤ ENNReal.ofReal η * P A := by
  have hP := hE.1.isProbabilityMeasure'
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have h0 := ae_iff.1 (ae_ne_top_of_thresholdCondition hE hthr)
    rw [measure_mono_null (fun ω hω => by simpa using hω.2.1) h0]
    exact bot_le
  obtain ⟨T, G, hT, hGm, hGc, hgood⟩ := exists_setup hκ hE hthr
  have hx0 : 0 < xR 0 - xL 0 := one_pos.trans hx
  set μ := critMu κ with hμdef
  set K := critK (ρL 0) with hKdef
  have hμ0 : 0 < μ := critMu_pos hκ
  have hμ1 : μ ≤ 1 := critMu_le_one κ
  have hκμ : κ * μ ≤ 1 / 2 := mul_critMu_le hκ
  have hK0 : 0 ≤ K := critK_nonneg _
  have hKle : 2 * |ρL 0| * (1 + 4 * |ρL 0|) ≤ K := le_rfl
  -- levels, cutoffs, Lyapunov functions, martingales
  set e : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hedef
  have he0 : ∀ m, 0 < e m := fun m => by positivity
  set a : ℕ → ℝ := fun m => e m / 2 with hadef
  have ha0 : ∀ m, 0 < a m := fun m => by have := he0 m; positivity
  have hae : ∀ m, a m < e m := fun m => by have := he0 m; simp only [hadef]; linarith
  set Φ : ℕ → SCoord nL (nR + 1) × ℝ → ℝ := fun m => critPhi κ xL xR ρL ρR (a m) μ K with hΦdef
  have hΦc : ∀ m, ContDiff ℝ 3 (Φ m) := fun m => contDiff_critPhi κ xL xR ρL ρR (ha0 m) μ K
  set Mm : ℕ → ℝ≥0 → Ω → ℝ := fun m => genMart (Φ m) xL xR G T W VL VR B ζ m with hMmdef
  have hM : ∀ m, Martingale (Mm m) (usualAugmentation 𝓕 P) P := fun m =>
    martingale_genMart hE hGm hGc hgood hT hx0 (hΦc m) m
  have hMrc : ∀ m ω t, ContinuousWithinAt (Mm m · ω) (Ici t) t := fun m ω t =>
    (continuous_genMart hgood (hΦc m) m ω (κ := κ) (ρL := ρL) (ρR := ρR)).continuousWithinAt
  -- the exits and the sampling times
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hcont : ∀ ω ∉ Gᶜ, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR (Fin.last nR) t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω => by
    have hF := (hgood ω (not_not.1 hω)).1.isForcePath
    exact ⟨hF.continuousOn_w, hF.continuousOn_vR 0, hF.continuousOn_vR _⟩
  have hτ : ∀ m, IsStoppingTime (usualAugmentation 𝓕 P)
      fun ω => (critExit Gᶜ ζ (e m) q W VR ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_critExit hEa.2.1 (hEa.2.2.2.1 0) (hEa.2.2.2.1 _)
      (fun t => (measurableSet_good_usual hGm hGc t).compl) hcont
  set ρs : ℕ → Ω → WithTop ℝ≥0 := fun m ω =>
    max (min (critExit Gᶜ ζ (e m) q W VR ω : WithTop ℝ≥0) ((max (m : ℝ≥0) q : ℝ≥0) : WithTop ℝ≥0))
      (q : WithTop ℝ≥0) with hρsdef
  have hρs : ∀ m, IsStoppingTime (usualAugmentation 𝓕 P) (ρs m) := fun m =>
    ((hτ m).min_const (max (m : ℝ≥0) q)).max_const q
  have hρsle : ∀ m ω, ρs m ω ≤ ((max (m : ℝ≥0) q : ℝ≥0) : WithTop ℝ≥0) := fun m ω =>
    max_le (min_le_right _ _) (by exact_mod_cast le_max_right _ _)
  have hMi : ∀ m, Integrable (stoppedValue (Mm m) (ρs m)) P := fun m =>
    (tendsto_lintegral_stoppedValue_dyadicUpperTime (hM m).supermartingale (hMrc m) (hρs m) (hρsle m)).2.1
  -- optional sampling on `A`
  have hAm : MeasurableSet A := (usualAugmentation 𝓕 P).le q _ hA
  have hos : ∀ m, ∫ ω in A, Mm m q ω ∂P = ∫ ω in A, stoppedValue (Mm m) (ρs m) ω ∂P := by
    intro m
    have hA' : MeasurableSet[(isStoppingTime_const (usualAugmentation 𝓕 P) q).measurableSpace] A := by
      rw [IsStoppingTime.measurableSpace_const]; exact hA
    have h := setIntegral_stoppedValue_eq_of_rightContinuous (hM m) (hMrc m)
      (isStoppingTime_const (usualAugmentation 𝓕 P) q) (hρs m) (fun ω => le_max_right _ _) (hρsle m) hA'
    simpa only [stoppedValue_const] using h
  -- the sampled variables
  set Z : ℕ → Ω → ℝ := fun m ω => η + stoppedValue (Mm m) (ρs m) ω - Mm m q ω with hZdef
  have hZi : ∀ m, Integrable (Z m) P := fun m =>
    ((integrable_const η).add (hMi m)).sub ((hM m).integrable q)
  have hZint : ∀ m, ∫ ω in A, Z m ω ∂P = η * P.real A := by
    intro m
    simp only [hZdef]
    rw [integral_sub (f := fun ω => η + stoppedValue (Mm m) (ρs m) ω) (g := Mm m q)
      ((integrable_const η).add (hMi m)).integrableOn ((hM m).integrable q).integrableOn,
      integral_add (f := fun _ => η) (g := stoppedValue (Mm m) (ρs m)) (integrable_const η).integrableOn
        (hMi m).integrableOn, setIntegral_const, ← hos m]
    simp only [smul_eq_mul, add_sub_cancel_right]
    ring
  -- the pathwise bound
  have hpath : ∀ m, ∀ ω ∈ A, ω ∈ G → 0 ≤ Z m ω ∧ ∀ r : ℝ≥0, ρs m ω = r →
      q ≤ angLoc G T W VL VR B ζ m ω →
      Φ m (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
          (min r (angLoc G T W VL VR B ζ m ω))) +
        μ / 4 * ∫ s in (q : ℝ)..((min r (angLoc G T W VL VR B ζ m ω) : ℝ≥0) : ℝ),
          (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
            1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) ≤ Z m ω := by
    intro m ω hωA hωG
    have hω' := hgood ω hωG
    have hp := hω'.1
    have hF := hp.isForcePath
    set σ := angLoc G T W VL VR B ζ m ω with hσdef
    have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
    obtain ⟨r, hr, hqr, -, hrlt, -⟩ := TrialsHi2.max_min_eq_coe
      (critExit Gᶜ ζ (e m) q W VR ω : WithTop ℝ≥0) (le_max_right (m : ℝ≥0) q)
    have hρr : ρs m ω = r := hr
    have hSV : stoppedValue (Mm m) (ρs m) ω = Mm m r ω := by
      simp only [stoppedValue, hρr, WithTop.untopD_coe]
    by_cases hqσ : q ≤ σ
    · set r' := min r σ with hr'def
      have hqr' : q ≤ r' := le_min hqr hqσ
      have hr'σ : r' ≤ σ := min_le_right _ _
      have hr'ζ : (r' : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr'σ) hσζ
      have hqζ : (q : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hqσ) hσζ
      obtain ⟨hAΔ, hAΦ⟩ := hAq ω hωA hqζ
      have hM1 := genMart_eq (Φ m) m hωG q hqσ (xL := xL) (xR := xR) (T := T) (W := W) (B := B) (ζ := ζ)
        (VL := VL) (VR := VR)
      have hM2 : Mm m r ω = Φ m (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r') -
          ∫ s in (0 : ℝ)..(r' : ℝ), Ito.itoGen (Φ m)
            (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 s.toNNReal)
            (angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω) (fun j => VR j s.toNNReal ω) 0) := by
        simp only [hMmdef]
        rw [genMart_min]
        exact genMart_eq (Φ m) m hωG r' hr'σ
      -- the region on `[q, r')`
      have hreg : ∀ s : ℝ≥0, q ≤ s → s < r' →
          VR (Fin.last nR) s ω - VR 0 s ω < VR 0 s ω - W s ω ∧ e m < VR (Fin.last nR) s ω - VR 0 s ω :=
        fun s hqs hsr => critLev_pos_iff.1 (pos_of_lt_critExit (not_not.2 hωG) hqs
          (hrlt s hqs (lt_of_lt_of_le hsr (min_le_left _ _)))).2
      -- the nearest right gap is positive on `[q, r']`
      have hRpos : ∀ s : ℝ≥0, q ≤ s → s ≤ r' → W s ω < VR 0 s ω := by
        intro s hqs hsr
        rcases hsr.lt_or_eq with hlt | heq
        · have h := hreg s hqs hlt
          have hΔ0 : 0 ≤ VR (Fin.last nR) s ω - VR 0 s ω :=
            sub_nonneg.2 (hF.monotone_vR (lt_of_le_of_lt (by exact_mod_cast hsr) hr'ζ) (Fin.zero_le _))
          linarith
        · subst heq
          rcases hqr'.lt_or_eq with hlt' | heq'
          · have hc : ContinuousOn (fun t => VR 0 t ω - W t ω) (Icc q r') :=
              ((hF.continuousOn_vR 0).sub hF.continuousOn_w).mono fun t ht =>
                lt_of_le_of_lt (by exact_mod_cast ht.2) hr'ζ
            have := le_of_lt_on_Ico hc hlt' (e := e m) fun t hqt htr => by
              have h := hreg t hqt htr
              linarith
            linarith [he0 m]
          · rw [← heq']
            have hΔ0 : 0 ≤ VR (Fin.last nR) q ω - VR 0 q ω :=
              sub_nonneg.2 (hF.monotone_vR hqζ (Fin.zero_le _))
            linarith
      have hoscC := continuousOn_osc hp hr'ζ hRpos
      have hoscI : IntervalIntegrable (fun s : ℝ => 1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) volume q r' :=
        (hoscC.mono (by rw [uIcc_of_le (by exact_mod_cast hqr')])).intervalIntegrable
      have hosc0 : 0 ≤ ∫ s in (q : ℝ)..(r' : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) := by
        refine intervalIntegral.integral_nonneg (by exact_mod_cast hqr') fun s hs => ?_
        have hs0 : 0 ≤ s := q.coe_nonneg.trans hs.1
        have h1 : q ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).2 hs.1
        have h2 : s.toNNReal ≤ r' := Real.toNNReal_le_iff_le_coe.2 hs.2
        exact osc_nonneg hp (lt_of_le_of_lt (by exact_mod_cast h2) hr'ζ) (hRpos _ h1 h2)
      -- the generator integral
      have hgi := intervalIntegrable_genMart hgood (hΦc m) m hωG (κ := κ) (xL := xL) (xR := xR)
        (ρL := ρL) (ρR := ρR) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ)
      simp only [coord_eq_pathCoord hωG, densA_eq_angDens hωG] at hgi
      have hsubI : ∀ {c d : ℝ≥0}, c ≤ d → d ≤ σ → ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 σ →
          IntervalIntegrable f volume c d := fun {c d} hcd hdσ {f} hf => hf.mono_set (by
        rw [uIcc_of_le (by exact_mod_cast hcd), uIcc_of_le σ.coe_nonneg]
        exact Icc_subset_Icc c.coe_nonneg (by exact_mod_cast hdσ))
      have hgen_le : ∫ s in (q : ℝ)..(r' : ℝ), Ito.itoGen (Φ m)
            (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 s.toNNReal)
            (angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω) (fun j => VR j s.toNNReal ω) 0) ≤
          ∫ s in (q : ℝ)..(r' : ℝ), -(μ / 4 * (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
            1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2)) := by
        refine intervalIntegral.integral_mono_ae_restrict (by exact_mod_cast hqr') (hsubI hqr' hr'σ hgi)
          (hoscI.const_mul (μ / 4)).neg ?_
        refine (ae_restrict_iff' measurableSet_Icc).2 ?_
        filter_upwards [Measure.ae_ne volume (r' : ℝ),
          measure_eq_zero_iff_ae_notMem.1 (hF.volume_collisionL 0)] with s hsr hcol hsI
        have hs0 : 0 ≤ s := q.coe_nonneg.trans hsI.1
        have h1 : q ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).2 hsI.1
        have h2 : s.toNNReal < r' := (Real.toNNReal_lt_iff_lt_coe hs0).2 (lt_of_le_of_ne hsI.2 hsr)
        have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast h2.le) hr'ζ
        obtain ⟨hΔR, heΔ⟩ := hreg _ h1 h2
        have hR0 := hRpos _ h1 h2.le
        have hL0 : VL 0 s.toNNReal ω < W s.toNNReal ω :=
          lt_of_le_of_ne (hF.vL_le_w hsζ 0) fun he => hcol ⟨hs0, hsζ, he.symm⟩
        have hD : 1 < VR 0 s.toNNReal ω - VL 0 s.toNNReal ω := lt_of_lt_of_le hx (le_gapAt hp hsζ)
        rw [itoGen_critPhi_pathCoord hp hκ.le (ha0 m) μ K 0 0 hsζ (by linarith [hae m])
          (by linarith [hae m]) hD]
        have := critGen_le_path (w := fun t => W t ω) (vL := fun i t => VL i t ω) (vR := fun j t => VR j t ω)
          hρL hρR hs hμ0 hμ1 hκμ hKle hL0 hR0 (by linarith [he0 m]) hΔR.le
        simpa only [Real.coe_toNNReal _ hs0] using this
      -- `Φ(q) ≤ η`
      have hΦq : Φ m (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 q) ≤ η := by
        have hR0q : 0 < VR 0 q ω - W q ω := by
          have := sub_nonneg.2 (hF.monotone_vR hqζ (Fin.zero_le (Fin.last nR))); linarith
        have hDq : 0 < VR 0 q ω - VL 0 q ω := lt_trans one_pos (lt_of_lt_of_le hx (le_gapAt hp hqζ))
        refine (critPhi_pathCoord_le hp (ha0 m) μ hK0 0 hqζ hR0q
          (sub_nonneg.2 (hF.monotone_vR hqζ (Fin.zero_le _))) hDq).trans ?_
        exact hAΦ
      have hsplit := intervalIntegral.integral_interval_sub_left (hsubI (zero_le) hr'σ hgi)
        (hsubI (zero_le) hqσ hgi)
      simp only [NNReal.coe_zero] at hsplit
      have hΦr'0 := critPhi_nonneg κ xL xR ρL ρR (ha0 m) μ hK0
        (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r')
      have hneg : ∫ s in (q : ℝ)..(r' : ℝ), -(μ / 4 * (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
            1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2)) =
          -(μ / 4 * ∫ s in (q : ℝ)..(r' : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
            1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2)) := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      have hZe : Z m ω = η + Mm m r ω - Mm m q ω := by simp only [hZdef, hSV]
      have hmain : Φ m (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r') +
          μ / 4 * ∫ s in (q : ℝ)..(r' : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
            1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) ≤ Z m ω := by
        rw [hZe, hM2]
        simp only [hMmdef] at hM1 ⊢
        rw [hM1]
        linarith
      refine ⟨le_trans (by positivity) hmain, fun r₂ hr₂ _ => ?_⟩
      have : r₂ = r := WithTop.coe_injective (hr₂.symm.trans hρr)
      subst this
      exact hmain
    · push Not at hqσ
      have hZe : Z m ω = η := by
        have e1 : Mm m r ω = Mm m σ ω := by
          simp only [hMmdef]
          rw [genMart_min, min_eq_right (hqσ.le.trans hqr)]
        have e2 : Mm m q ω = Mm m σ ω := by
          simp only [hMmdef]
          rw [genMart_min, min_eq_right hqσ.le]
        simp only [hZdef, hSV, e1, e2]
        ring
      exact ⟨by rw [hZe]; exact hη, fun _ _ h => absurd h (not_le.2 hqσ)⟩
  -- Fatou
  set f : ℕ → Ω → ℝ≥0∞ := fun m ω => ENNReal.ofReal (Z m ω) with hfdef
  have hfm : ∀ m, AEMeasurable (f m) P := fun m => (hZi m).aemeasurable.ennreal_ofReal
  set g : ℕ → Ω → ℝ≥0∞ := fun m => (hfm m).mk (f m) with hgdef
  have hgm : ∀ m, Measurable (g m) := fun m => (hfm m).measurable_mk
  have hfg : ∀ᵐ ω ∂P, ∀ m, f m ω = g m ω := ae_all_iff.2 fun m => (hfm m).ae_eq_mk
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := (measure_eq_zero_iff_ae_notMem.1 hGc).mono fun ω h => by simpa using h
  have hfl : ∀ m, ∫⁻ ω in A, g m ω ∂P = ENNReal.ofReal η * P A := by
    intro m
    have hnn : 0 ≤ᵐ[P.restrict A] Z m := by
      refine (ae_restrict_iff' hAm).2 ?_
      filter_upwards [hGae] with ω hωG hωA
      exact (hpath m ω hωA hωG).1
    rw [← lintegral_congr_ae (ae_restrict_of_ae (hfm m).ae_eq_mk),
      ← ofReal_integral_eq_lintegral_ofReal (hZi m).integrableOn hnn, hZint m, ENNReal.ofReal_mul hη,
      measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P A)]
  have hlim : ∫⁻ ω in A, liminf (fun m => g m ω) atTop ∂P ≤ ENNReal.ofReal η * P A :=
    (lintegral_liminf_le' fun m => (hgm m).aemeasurable).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall fun m => (hfl m).le))
  -- the lower bound on the bad event
  have he_lim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbad : ∀ᵐ ω ∂P, ω ∈ A ∩ critBad (4 / μ) q W VR ζ → 1 ≤ liminf (fun m => g m ω) atTop := by
    filter_upwards [hfg, hGae] with ω hωfg hωG hωAB
    obtain ⟨hωA, hζ, hNC, hcase⟩ := hωAB
    have hω' := hgood ω hωG
    have hp := hω'.1
    have hF := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact ENNReal.coe_lt_top
    have hfgω : (fun m => f m ω) = fun m => g m ω := funext hωfg
    rw [← hfgω]
    have hΔpos : ∀ t, 0 < VR (Fin.last nR) t ω - VR 0 t ω := fun t =>
      sub_pos.2 (vR_lt_vR_of_pos hp hxR (hlt t) fun s _ => hNC s)
    have hanti : ∀ t₁ t₂ : ℝ≥0, t₁ ≤ t₂ →
        VR (Fin.last nR) t₂ ω - VR 0 t₂ ω ≤ VR (Fin.last nR) t₁ ω - VR 0 t₁ ω := fun t₁ t₂ h =>
      vR_sub_vR_antitone hp (Fin.zero_le _) h (hlt t₂)
    have hqζ : (q : ℝ≥0∞) < ζ ω := hlt q
    obtain ⟨hAΔ, -⟩ := hAq ω hωA hqζ
    -- eventually the level, the cap and the localization are good up to `t₁`
    have hev : ∀ t₁ : ℝ≥0, ∀ᶠ m in atTop, e m < VR (Fin.last nR) t₁ ω - VR 0 t₁ ω ∧ t₁ ≤ (m : ℝ≥0) ∧
        t₁ ≤ angLoc G T W VL VR B ζ m ω := by
      intro t₁
      obtain ⟨n₀, hn₀⟩ := exists_forall_le_angLoc hω' hgood hωG (hT.2.1 ω) (hlt t₁)
      have h1 := he_lim.eventually (gt_mem_nhds (hΔpos t₁))
      have h2 : ∀ᶠ m : ℕ in atTop, t₁ ≤ (m : ℝ≥0) := (eventually_ge_atTop ⌈(t₁ : ℝ)⌉₊).mono fun m hm => by
        rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact (Nat.le_ceil _).trans (by exact_mod_cast hm)
      filter_upwards [h1, h2, eventually_ge_atTop n₀] with m hm1 hm2 hm3
      exact ⟨hm1, hm2, hn₀ m hm3⟩
    have hlev : ∀ m, ContinuousOn (fun t => critLev (e m) (W t ω, VR 0 t ω, VR (Fin.last nR) t ω))
        {t | (t : ℝ≥0∞) < ζ ω} := fun m =>
      (continuous_critLev (e m)).comp_continuousOn (hF.continuousOn_w.prodMk
        ((hF.continuousOn_vR 0).prodMk (hF.continuousOn_vR _)))
    have hcT : ∀ m, ContinuousOn (fun t => critTest (e m) q W VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω} :=
      fun m => continuousOn_critTest hF.continuousOn_w (hF.continuousOn_vR 0) (hF.continuousOn_vR _)
    have hosc_int : ∀ t₂ : ℝ≥0, IntervalIntegrable (fun s : ℝ => 1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
        1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) volume q t₂ := fun t₂ => by
      rcases le_total q t₂ with h | h
      · exact ((continuousOn_osc hp (hlt t₂) fun s _ _ => hNC s).mono
          (by rw [uIcc_of_le (by exact_mod_cast h)])).intervalIntegrable
      · exact (((continuousOn_osc hp (hlt q) fun s _ _ => hNC s).mono
          (by rw [uIcc_of_le (by exact_mod_cast h)])).intervalIntegrable).symm
    -- the bad exit through `Δ = R₀`
    have caseA : ∀ t₀ : ℝ≥0, q ≤ t₀ → VR 0 t₀ ω - W t₀ ω ≤ VR (Fin.last nR) t₀ ω - VR 0 t₀ ω →
        1 ≤ liminf (fun m => f m ω) atTop := by
      intro t₀ hqt₀ hle
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hev t₀] with m ⟨hem, htm, htσ⟩
      have hexle : critExit Gᶜ ζ (e m) q W VR ω ≤ t₀ := by
        rw [critExit, zeroOn_of_notMem (not_not.2 hωG)]
        refine firstMeet_le_of (hlt t₀) ?_
        simp only [critTest, zeroProc, max_le_iff]
        exact ⟨(min_le_left _ _).trans (by linarith), by
          have : (q : ℝ) ≤ t₀ := by exact_mod_cast hqt₀
          linarith⟩
      obtain ⟨m₀, hm₀, -, hqm₀, hl1, hl2⟩ := critLev_critExit (not_not.2 hωG) (hcT m) (hlev m)
        (lt_of_le_of_lt hexle (hlt t₀))
      have hm₀t : m₀ ≤ t₀ := by rw [hm₀] at hexle; exact_mod_cast hexle
      have hΔm₀ : e m < VR (Fin.last nR) m₀ ω - VR 0 m₀ ω := hem.trans_le (hanti m₀ t₀ hm₀t)
      have hqm₀' : q < m₀ := by
        refine lt_of_le_of_ne hqm₀ fun heq => ?_
        subst heq
        have : 0 < critLev (e m) (W q ω, VR 0 q ω, VR (Fin.last nR) q ω) := critLev_pos_iff.2 ⟨hAΔ, hΔm₀⟩
        linarith
      have hl0 := hl2 hqm₀'
      simp only [critLev] at hl1 hl0
      have hR_eq : VR 0 m₀ ω - W m₀ ω = VR (Fin.last nR) m₀ ω - VR 0 m₀ ω := by
        have h1 := le_min_iff.1 hl0
        rcases min_le_iff.1 hl1 with h | h
        · linarith [h1.1]
        · linarith
      have hρm : ρs m ω = m₀ := by
        simp only [hρsdef]
        rw [show (critExit Gᶜ ζ (e m) q W VR ω : WithTop ℝ≥0) = (m₀ : WithTop ℝ≥0) from hm₀]
        rw [min_eq_left (by exact_mod_cast hm₀t.trans (htm.trans (le_max_left _ _))),
          max_eq_left (by exact_mod_cast hqm₀)]
      have hσm₀ : m₀ ≤ angLoc G T W VL VR B ζ m ω := hm₀t.trans htσ
      have h := (hpath m ω hωA hωG).2 m₀ hρm (hqm₀.trans hσm₀)
      rw [min_eq_left hσm₀] at h
      have hosc0 : 0 ≤ ∫ s in (q : ℝ)..(m₀ : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) :=
        intervalIntegral.integral_nonneg (by exact_mod_cast hqm₀) fun s hs =>
          osc_nonneg hp (hlt _) (hNC _)
      have hR0 : 0 < VR 0 m₀ ω - W m₀ ω := sub_pos.2 (hNC m₀)
      have hΦ1 : 1 ≤ Φ m (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 m₀) := by
        have hD : 1 < VR 0 m₀ ω - VL 0 m₀ ω := lt_of_lt_of_le hx (le_gapAt hp (hlt m₀))
        simp only [hΦdef]
        rw [critPhi_pathCoord hp (ha0 m) μ K 0 (hlt m₀) (by linarith [hae m]) (by linarith [hae m]) hD,
          ← hR_eq, div_self hR0.ne', Real.one_rpow]
        have : 0 ≤ K * ((VR 0 m₀ ω - W m₀ ω) / (VR 0 m₀ ω - VL 0 m₀ ω)) ^ μ :=
          mul_nonneg hK0 (Real.rpow_nonneg (div_nonneg hR0.le (by linarith)) _)
        linarith
      have hZ1 : 1 ≤ Z m ω := by nlinarith
      simpa [hfdef] using (ENNReal.one_le_ofReal.2 hZ1)
    rcases hcase with ⟨t₀, hqt₀, hle⟩ | ⟨t₁, hqt₁, hC⟩
    · exact caseA t₀ hqt₀ hle
    by_cases hA' : ∃ t₀ : ℝ≥0, q ≤ t₀ ∧ VR 0 t₀ ω - W t₀ ω ≤ VR (Fin.last nR) t₀ ω - VR 0 t₀ ω
    · obtain ⟨t₀, hqt₀, hle⟩ := hA'
      exact caseA t₀ hqt₀ hle
    push Not at hA'
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hev t₁] with m ⟨hem, htm, htσ⟩
    have hgt : (t₁ : ℝ≥0∞) < critExit Gᶜ ζ (e m) q W VR ω :=
      lt_critExit_of_forall (not_not.2 hωG) (hcT m) (hlt t₁) fun s hqs hst =>
        critLev_pos_iff.2 ⟨hA' s hqs, hem.trans_le (hanti s t₁ hst)⟩
    obtain ⟨r, hr, -, -, -, -⟩ := TrialsHi2.max_min_eq_coe
      (critExit Gᶜ ζ (e m) q W VR ω : WithTop ℝ≥0) (le_max_right (m : ℝ≥0) q)
    have hρr : ρs m ω = r := hr
    have ht₁r : t₁ ≤ r := by
      have h1 : (t₁ : WithTop ℝ≥0) ≤ ρs m ω := by
        simp only [hρsdef]
        refine le_max_of_le_left (le_min ?_ (by exact_mod_cast htm.trans (le_max_left _ _)))
        exact (show ((t₁ : ℝ≥0∞) : WithTop ℝ≥0) ≤ (critExit Gᶜ ζ (e m) q W VR ω : WithTop ℝ≥0) from hgt.le)
      rw [hρr] at h1
      exact_mod_cast h1
    have hσq : q ≤ angLoc G T W VL VR B ζ m ω := hqt₁.trans htσ
    have h := (hpath m ω hωA hωG).2 r hρr hσq
    set r' := min r (angLoc G T W VL VR B ζ m ω) with hr'def
    have ht₁r' : t₁ ≤ r' := le_min ht₁r htσ
    have hmono : ∫ s in (q : ℝ)..(t₁ : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) ≤
        ∫ s in (q : ℝ)..(r' : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) := by
      refine intervalIntegral.integral_mono_interval le_rfl (by exact_mod_cast hqt₁) (by exact_mod_cast ht₁r')
        ?_ (hosc_int r')
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
      exact osc_nonneg hp (hlt _) (hNC _)
    have hΦ0 := critPhi_nonneg κ xL xR ρL ρR (ha0 m) μ hK0
      (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r')
    have h4 : μ / 4 * (4 / μ) = 1 := by field_simp
    have hZ1 : 1 ≤ Z m ω := by
      have : μ / 4 * (4 / μ) ≤ μ / 4 * ∫ s in (q : ℝ)..(r' : ℝ), (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2) :=
        mul_le_mul_of_nonneg_left (hC.le.trans hmono) (by positivity)
      linarith
    simpa [hfdef] using (ENNReal.one_le_ofReal.2 hZ1)
  -- conclusion
  have hFm : Measurable fun ω => liminf (fun m => g m ω) atTop := Measurable.liminf hgm
  calc P (A ∩ critBad (4 / μ) q W VR ζ) ≤ P (A ∩ {ω | 1 ≤ liminf (fun m => g m ω) atTop}) := by
        refine measure_mono_ae ?_
        filter_upwards [hbad] with ω h hω
        exact ⟨hω.1, h hω⟩
    _ = P.restrict A {ω | 1 ≤ liminf (fun m => g m ω) atTop} := by
        rw [Measure.restrict_apply (measurableSet_le measurable_const hFm), inter_comm]
    _ ≤ ∫⁻ ω in A, liminf (fun m => g m ω) atTop ∂P := by
        have := mul_meas_ge_le_lintegral₀ hFm.aemeasurable 1 (μ := P.restrict A)
        simpa using this
    _ ≤ _ := hlim

end Main

end TrialsHi4

end Sec7

end InteractingSLE
