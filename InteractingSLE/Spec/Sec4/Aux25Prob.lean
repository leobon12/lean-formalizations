/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Ident
import InteractingSLE.Spec.Sec4.Aux25
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# Aux. lemma 25: the endpoint case has probability zero

Packet PROVE-AUX25. Specification p. 127: "That event has probability zero by the independent one-force
first-swallow law (B1) in Aux. lemma 99. In fact, `ρ_* > −2 > κ/2 − 4` implies that the first endpoint is
strictly beyond the marked point if a finite swallow occurs." This file discharges the named input
`Aux25.EndpointExclusionStatement`:

1. **Girsanov.** For a group `S` of right marks, the drift of all other marks, cut at `δ`, is removed by
   `Girsanov.girsanov_cutDrift`; a continuous version of the new Brownian motion (`exists_continuous_version`) is
   restarted at the rational time `r` (`isFilteredBrownianReal_restart_cond`), a Brownian motion of a filtration
   whose time `0` contains `𝓕_r`.
2. **The hitting bound** (`Aux25Hit.lean`) for the tamed one-group process started at `(û(r), y)`, `y` on the
   geometric grid `b^{j+1}`, `b = 1/c`, on the `𝓕_r`-event `û(r) ∈ [b^j, b^{j+1})`.
3. **Identification** (`Aux25Ident.lean`): on the endpoint case the tamed process hits for every large level.
4. **Summation** over the grid: the endpoint case has probability at most `(S∞ − F(c))/S∞ → 0` as `c → 1`.

## Main results

* `IsIntegratedSLEEvolution.ae_noRightEndpoint`;
* `Aux25.endpointExclusionStatement : Aux25.EndpointExclusionStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Aux25

open Girsanov

section Setup

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Girsanov removal of the marks off a group, a continuous version, and the restart at `r`.** -/
theorem exists_girsanov_restart [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (S : Finset (Fin nR)) {δ : ℝ}
    (hδ : 0 < δ) (r T : ℝ≥0) :
    ∃ (Q : Measure Ω) (Bv : ℝ≥0 → Ω → ℝ) (𝓖 : Filtration ℝ≥0 mΩ),
      IsProbabilityMeasure Q ∧ P ≪ Q ∧ Q ≪ P ∧
      IsFilteredBrownianReal 𝓖 (fun t ω => Bv (r + t) ω - Bv r ω) Q ∧ (∀ ω, Continuous (Bv · ω)) ∧
      (∀ s : Set Ω, MeasurableSet[𝓕 r] s → MeasurableSet[𝓖 0] s) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (ζ ω) (T : ℝ≥0∞) →
        Bv t ω = B t ω + ∫ s in (0 : ℝ)..(t : ℝ), (Real.sqrt κ)⁻¹ *
          addedDriftCut (removedWeights ρL ρR S) δ (W s.toNNReal ω)
            (fun j => allMarks VL VR j s.toNNReal ω) := by
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  set U : Fin (nL + nR) → ℝ≥0 → Ω → ℝ := allMarks VL VR with hUdef
  set σ' := removedWeights ρL ρR S with hσ'
  set F : ℝ → (Fin (nL + nR) → ℝ) → ℝ := fun w u => (Real.sqrt κ)⁻¹ * addedDriftCut σ' δ w u
    with hFdef
  have hFc : Continuous fun p : ℝ × (Fin (nL + nR) → ℝ) => F p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ' hδ)
  have hFb : ∀ w u, |F w u| ≤ (Real.sqrt κ)⁻¹ * ((∑ j, |σ' j|) * δ⁻¹) := fun w u => by
    rw [hFdef, abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg κ))]
    exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ' hδ w u)
      (inv_nonneg.2 (Real.sqrt_nonneg κ))
  set τ : Ω → ℝ≥0∞ := fun ω => min (ζ ω) (T : ℝ≥0∞) with hτdef
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s} := by
    intro s
    have h1 : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)} :=
      hW s univ MeasurableSet.univ
    have h2 : {ω | τ ω ≤ s} = {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ (univ : Set ℝ)}ᶜ ∪
        {_ω : Ω | (T : ℝ≥0∞) ≤ s} := by
      ext ω
      simp [hτdef, min_le_iff, not_lt]
    rw [h2]
    exact h1.compl.union (MeasurableSet.const _)
  have hτζ : ∀ ω, τ ω ≤ ζ ω := fun ω => min_le_left _ _
  have hτT : ∀ ω, τ ω ≤ (T : ℝ≥0∞) := fun ω => min_le_right _ _
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (U k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hVL i
    | right i => simpa [hUdef, allMarks] using hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => U k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [hUdef, allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [hUdef, allMarks] using hp.2.2.2.2.2.1 i
  obtain ⟨hequiv, hBM, hident⟩ := girsanov_cutDrift hBF hFc hFb hW hU hτ hτζ hτT hcont
  set Q := girsanovMeasure P 𝓕 B (cutDrift τ ζ F W U) (T + 1) with hQ
  set Bh := girsanovProcess B (cutDrift τ ζ F W U) with hBh
  have : IsProbabilityMeasure Q := hequiv.isProb
  obtain ⟨Bv, -, hBvc, hBvBM, hBvae⟩ := Sec2.Restart.exists_continuous_version hBM
  have hT0 : IsStoppingTime (usualAugmentation 𝓕 Q) fun _ : Ω => ((r : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_const _ _
  have hres := Sec2.Restart.isFilteredBrownianReal_restart_cond hBvBM hBvc hT0 (A := univ)
    MeasurableSet.univ (by simp)
  rw [cond_univ] at hres
  refine ⟨Q, Bv, Sec2.Restart.restartFiltration (usualAugmentation 𝓕 Q) (fun _ => r) hT0, inferInstance,
    hequiv.ac', hequiv.ac, hres, hBvc, fun s hs => ?_, ?_⟩
  · rw [Sec2.Restart.restartFiltration_zero, IsStoppingTime.measurableSpace_const]
    exact Ito.le_usualAugmentation 𝓕 Q r s hs
  · filter_upwards [hident, hequiv.ac'.ae_le hBvae] with ω hid hv t ht
    rw [hv t]
    exact hid t ht

end Setup

/-! ### The endpoint case along one path -/

section Case

variable {nL nR : ℕ}

/-- The endpoint case of `NoRightEndpoint` at `(q, k, m, σ)` along one path. -/
def EndpointCase (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (q : ℚ)
    (k : Fin nR) (m : ℕ) (σ : ℝ≥0) : Prop :=
  ratTime q < σ ∧ (σ : ℝ≥0∞) < ζ ∧ w (ratTime q) < vR k (ratTime q) ∧
    (∀ s : ℝ≥0, ratTime q ≤ s → s < σ → w s < vR k s) ∧ vR k σ = w σ ∧
    (∀ j, vR k (ratTime q) ≤ vR j (ratTime q)) ∧
    (∀ s : ℝ≥0, ratTime q ≤ s → s ≤ σ → ∀ j, vR j (ratTime q) ≠ vR k (ratTime q) →
      1 / ((m : ℝ) + 1) ≤ vR j s - w s) ∧
    (∀ s : ℝ≥0, ratTime q ≤ s → s ≤ σ → ∀ i, 1 / ((m : ℝ) + 1) ≤ w s - vL i s) ∧
    ∀ y : ℝ, vR k (ratTime q) - w (ratTime q) < y → AliveFrom w (ratTime q) σ y

theorem noRightEndpoint_of {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (h : ∀ q k m σ, ¬ EndpointCase w vL vR ζ q k m σ) : NoRightEndpoint w vL vR ζ :=
  fun q k m σ h1 h2 h3 h4 h5 h6 h7 h8 h9 => h q k m σ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The weight of the group exceeds `−2`**: at the collision time `σ` the right marks meeting the driver are
exactly those of the group of `k` (the others have gaps `≥ 1/(m+1)`), and the threshold fails at `σ < ζ`. -/
theorem neg_two_lt_of_endpointCase (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {q : ℚ}
    {k : Fin nR} {m : ℕ} {σ : ℝ≥0} (h : EndpointCase w vL vR ζ q k m σ) {S : Finset (Fin nR)}
    (hS : ∀ j, vR j (ratTime q) = vR k (ratTime q) ↔ j ∈ S) : -2 < ∑ j ∈ S, ρR j := by
  obtain ⟨h1, h2, -, -, h5, -, h7, -, -⟩ := h
  have hnot := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 σ h2
  have hfil : Finset.univ.filter (fun j => vR j σ = w σ) = S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hjS
      have hne : vR j (ratTime q) ≠ vR k (ratTime q) := fun he => hjS ((hS j).1 he)
      have := h7 σ h1.le le_rfl j hne
      have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    · intro hjS
      rw [vR_eq_of_eq hp h1.le h2 ((hS j).2 hjS), h5]
  unfold ForceWord.ThresholdCondition at hnot
  push Not at hnot
  have h3 := hnot.2
  rwa [hfil] at h3

end Case

/-- The norm of the start state. -/
theorem norm_start_le (g y : ℝ) :
    ‖((((0 : ℝ), (fun _ => g), (fun _ => (0 : ℝ)), y), (0 : ℝ)) : StateE 0 1 × ℝ)‖ ≤ |g| + |y| := by
  have hg : 0 ≤ |g| := abs_nonneg g
  have hy : 0 ≤ |y| := abs_nonneg y
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨by simp; positivity, norm_prod_le_iff.2
    ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩⟩, by simp; positivity⟩
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun _ => ?_
    rw [Real.norm_eq_abs]; linarith
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun _ => ?_
    simp; positivity
  · rw [Real.norm_eq_abs]; linarith

/-! ### The bound on one grid cell -/

section Cell

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ} {κ sk ρ α β : ℝ}

open Classical in
/-- The clamped initial force gap at level `L`: the gap on the cell where it is below `(1 − 1/L) y`, else `3y/4`. -/
def clampGap (I : Set Ω) (gap : Ω → ℝ) (y L : ℝ) (ω : Ω) : ℝ :=
  if ω ∈ I ∧ gap ω < (1 - 1 / L) * y then gap ω else 3 * y / 4

/-- The cell event at level `L` together with the hit of the clamped tamed process. -/
def cellHit (sk ρ y : ℝ) (I : Set Ω) (gap : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (N : ℝ≥0) (L : ℕ) : Set Ω :=
  {ω | ω ∈ I ∧ gap ω < (1 - 1 / (L : ℝ)) * y} ∩
    {ω | gapU sk 0 (statePath (tState sk ρ (1 / (L : ℝ)) y (clampGap I gap y L) B) B
        (hitStop (tState sk ρ (1 / (L : ℝ)) y (clampGap I gap y L) B) B
          (exitC sk (1 / (L : ℝ)) L) N ω) ω) ≤
      gapX sk (statePath (tState sk ρ (1 / (L : ℝ)) y (clampGap I gap y L) B) B
        (hitStop (tState sk ρ (1 / (L : ℝ)) y (clampGap I gap y L) B) B
          (exitC sk (1 / (L : ℝ)) L) N ω) ω) / 2}

/-- **The cell bound.** -/
theorem cell_bound (hB : IsFilteredBrownianReal 𝓖 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hκ : 0 < κ) (hsk : sk ^ 2 = κ) (hρ : -2 < ρ)
    (hα : α = 2 * (2 + ρ) / κ) (hβ : β = 2 * (4 + ρ - κ) / κ) (hβ1 : -1 < β) {cc y : ℝ}
    (hcc : 2 / 3 ≤ cc) (hcc1 : cc < 1) (hy : 0 < y) {gap : Ω → ℝ} (hgap : Measurable[𝓖 0] gap)
    {I : Set Ω} (hI : MeasurableSet[𝓖 0] I) (hIgap : ∀ ω ∈ I, cc * y ≤ gap ω ∧ gap ω < y)
    (N : ℝ≥0) :
    ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L →
      Q (cellHit sk ρ y I gap B N L) ≤
        ENNReal.ofReal ((scaleTop α β - scaleFn α β cc) / scaleTop α β) * Q I := by
  classical
  have hQ := hB.isProbabilityMeasure'
  obtain ⟨L₁, hL₁⟩ := exists_nat_gt (4 + 2 / y + 2 * y)
  refine ⟨L₁, fun L hL => ?_⟩
  have hLr : (L₁ : ℝ) ≤ L := by exact_mod_cast hL
  have h2y : 0 ≤ 2 / y := by positivity
  have hLbig : 4 + 2 / y + 2 * y < L := lt_of_lt_of_le hL₁ hLr
  have hLpos : (0 : ℝ) < L := by linarith
  set c : ℝ := 1 / (L : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have hc4 : c < 1 / 4 := by
    rw [hcdef, div_lt_div_iff₀ hLpos (by norm_num)]; linarith
  have h2c : 2 * c < y := by
    have h1 : 2 / y < L := by linarith
    rw [div_lt_iff₀ hy] at h1
    rw [hcdef, show 2 * (1 / (L : ℝ)) = 2 / L by ring, div_lt_iff₀ hLpos]; linarith
  set J : Set Ω := {ω | ω ∈ I ∧ gap ω < (1 - 1 / (L : ℝ)) * y} with hJdef
  have hJ : MeasurableSet[𝓖 0] J :=
    hI.inter (measurableSet_lt hgap measurable_const)
  set g₀ := clampGap I gap y L with hg₀def
  have hg₀m : Measurable[𝓖 0] g₀ := by
    have : g₀ = J.piecewise gap (fun _ => 3 * y / 4) := by
      funext ω; simp [hg₀def, clampGap, Set.piecewise, hJdef]
    rw [this]
    exact Measurable.piecewise hJ hgap measurable_const
  -- the start is inside the region
  have hstart : ∀ ω, statePath (tState sk ρ c y g₀ B) B 0 ω ∉ exitC sk c L := by
    intro ω hC
    have hz1 : tU1 sk ρ c g₀ B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω
    have hz2 : tU2 sk ρ c y g₀ B 0 ω = 0 := Sec2.markFlow_zero _ _ _ _ ω
    have hsp : statePath (tState sk ρ c y g₀ B) B 0 ω =
        ((((0 : ℝ), (fun _ => g₀ ω), (fun _ => (0 : ℝ)), y), (0 : ℝ)) : StateE 0 1 × ℝ) := by
      simp [statePath, tState, hz1, hz2, hB0]
    rw [hsp] at hC
    have hnorm := norm_start_le (g₀ ω) y
    have hgU : gapU sk 0 ((((0 : ℝ), (fun _ => g₀ ω), (fun _ => (0 : ℝ)), y), (0 : ℝ)) :
        StateE 0 1 × ℝ) = g₀ ω := by simp [gapU, stW]
    have hgX : gapX sk ((((0 : ℝ), (fun _ => g₀ ω), (fun _ => (0 : ℝ)), y), (0 : ℝ)) :
        StateE 0 1 × ℝ) = y := by simp [gapX, stW]
    simp only [exitC, mem_ofPred_eq, hgU, hgX] at hC
    by_cases hω : ω ∈ I ∧ gap ω < (1 - 1 / (L : ℝ)) * y
    · have hgv : g₀ ω = gap ω := by
        show clampGap I gap y L ω = gap ω
        rw [clampGap, ite_eq_left hω]
      rw [hgv] at hC hnorm
      obtain ⟨hl, hu⟩ := hIgap ω hω.1
      have hgpos : 0 < gap ω := by nlinarith
      rw [abs_of_pos hgpos, abs_of_pos hy] at hnorm
      rcases hC with h | h | h | h | h
      · nlinarith
      · rw [← hcdef] at hω; linarith [hω.2]
      · linarith
      · linarith
      · linarith
    · have hgv : g₀ ω = 3 * y / 4 := by
        show clampGap I gap y L ω = 3 * y / 4
        rw [clampGap, ite_eq_right hω]
      rw [hgv] at hC hnorm
      rw [abs_of_pos (by positivity : (0 : ℝ) < 3 * y / 4), abs_of_pos hy] at hnorm
      rcases hC with h | h | h | h | h
      · linarith
      · rw [← hcdef] at h; nlinarith
      · linarith
      · linarith
      · linarith
  have hbd := hit_bound (N := N) hB hBc hB0 hκ hsk hρ hα hβ hβ1 hc hLpos hg₀m hstart hJ
  -- the integrand is at most `S∞ − F(cc)` on the cell
  have hTop := scaleTop_pos (α := α) hβ1
  have hint : ∫ ω in J, (scaleTop α β - scaleFn α β (g₀ ω / y)) ∂Q ≤
      (scaleTop α β - scaleFn α β cc) * Q.real J := by
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
    · refine (ae_restrict_iff' (𝓖.le 0 J hJ)).2 (Eventually.of_forall fun ω hω => ?_)
      have hgv : g₀ ω = gap ω := by
        show clampGap I gap y L ω = gap ω
        rw [clampGap, ite_eq_left (show ω ∈ I ∧ gap ω < (1 - 1 / (L : ℝ)) * y from hω)]
      obtain ⟨hl, hu⟩ := hIgap ω hω.1
      beta_reduce
      rw [hgv]
      have hr : gap ω / y ∈ Icc (1 / 2 : ℝ) 1 := ⟨by rw [le_div_iff₀ hy]; nlinarith,
        by rw [div_le_one hy]; exact hu.le⟩
      exact sub_nonneg.2 (scaleFn_le_scaleTop hβ1 hr)
    · refine (ae_restrict_iff' (𝓖.le 0 J hJ)).2 (Eventually.of_forall fun ω hω => ?_)
      have hgv : g₀ ω = gap ω := by
        show clampGap I gap y L ω = gap ω
        rw [clampGap, ite_eq_left (show ω ∈ I ∧ gap ω < (1 - 1 / (L : ℝ)) * y from hω)]
      obtain ⟨hl, hu⟩ := hIgap ω hω.1
      beta_reduce
      rw [hgv]
      have h1 : cc ≤ gap ω / y := by rw [le_div_iff₀ hy]; exact hl
      have h2 : gap ω / y < 1 := by rw [div_lt_one hy]; exact hu
      have := scaleFn_le_scaleFn (α := α) (β := β) ⟨by linarith, hcc1⟩
        ⟨lt_of_lt_of_le (by linarith) h1, h2⟩ h1
      show scaleTop α β - scaleFn α β (gap ω / y) ≤ scaleTop α β - scaleFn α β cc
      linarith
  have hJI : Q.real J ≤ Q.real I := measureReal_mono (fun ω hω => hω.1)
  have hcF : 0 ≤ scaleTop α β - scaleFn α β cc :=
    sub_nonneg.2 (scaleFn_le_scaleTop hβ1 ⟨by linarith, hcc1.le⟩)
  have hreal : Q.real (cellHit sk ρ y I gap B N L) ≤
      (scaleTop α β - scaleFn α β cc) / scaleTop α β * Q.real I := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hTop]
    have h3 := hbd.trans hint
    have h4 : (scaleTop α β - scaleFn α β cc) * Q.real J ≤ (scaleTop α β - scaleFn α β cc) * Q.real I :=
      mul_le_mul_of_nonneg_left hJI hcF
    have h5 : Q.real (cellHit sk ρ y I gap B N L) = Q.real (J ∩ {ω | gapU sk 0 (statePath
        (tState sk ρ c y g₀ B) B (hitStop (tState sk ρ c y g₀ B) B (exitC sk c L) N ω) ω) ≤
          gapX sk (statePath (tState sk ρ c y g₀ B) B
            (hitStop (tState sk ρ c y g₀ B) B (exitC sk c L) N ω) ω) / 2}) := rfl
    rw [h5]
    linarith
  rw [← ofReal_measureReal (measure_ne_top Q _), ← ofReal_measureReal (measure_ne_top Q I),
    ← ENNReal.ofReal_mul (div_nonneg hcF hTop.le)]
  exact ENNReal.ofReal_le_ofReal hreal

end Cell

/-! ### The endpoint case has probability zero -/

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The `𝓕_r`-measurable grid cell of the initial gap (killed coordinates at `r`). -/
def gridCell (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (r : ℝ≥0) (k : Fin nR)
    (S : Finset (Fin nR)) (b : ℝ) (j : ℤ) : Set Ω :=
  {ω | (r : ℝ≥0∞) < ζ ω ∧
    (∀ j', killed ζ (VR j') r ω = killed ζ (VR k) r ω ↔ j' ∈ S) ∧
    (∀ j', killed ζ (VR k) r ω ≤ killed ζ (VR j') r ω) ∧
    b ^ j ≤ killed ζ (VR k) r ω - killed ζ W r ω ∧ killed ζ (VR k) r ω - killed ζ W r ω < b ^ (j + 1)}

theorem measurableSet_gridCell (hW : AdaptedBefore 𝓕 ζ W) (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (r : ℝ≥0) (k : Fin nR) (S : Finset (Fin nR)) (b : ℝ) (j : ℤ) :
    MeasurableSet[𝓕 r] (gridCell W VR ζ r k S b j) := by
  have hζ : MeasurableSet[𝓕 r] {ω | (r : ℝ≥0∞) < ζ ω} := by
    simpa using hW r univ MeasurableSet.univ
  have hk := measurable_killed (hVR k) r
  have hw := measurable_killed hW r
  have h1 : MeasurableSet[𝓕 r] {ω | ∀ j', killed ζ (VR j') r ω = killed ζ (VR k) r ω ↔ j' ∈ S} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun j' => ?_
    have hm := measurableSet_eq_fun (measurable_killed (hVR j') r) hk
    by_cases hj : j' ∈ S
    · have e : {ω | killed ζ (VR j') r ω = killed ζ (VR k) r ω ↔ j' ∈ S} =
          {ω | killed ζ (VR j') r ω = killed ζ (VR k) r ω} := by ext; simp [hj]
      rw [e]; exact hm
    · have e : {ω | killed ζ (VR j') r ω = killed ζ (VR k) r ω ↔ j' ∈ S} =
          {ω | killed ζ (VR j') r ω = killed ζ (VR k) r ω}ᶜ := by ext; simp [hj]
      rw [e]; exact hm.compl
  have h2 : MeasurableSet[𝓕 r] {ω | ∀ j', killed ζ (VR k) r ω ≤ killed ζ (VR j') r ω} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun j' => measurableSet_le hk (measurable_killed (hVR j') r)
  have h3 : MeasurableSet[𝓕 r] {ω | b ^ j ≤ killed ζ (VR k) r ω - killed ζ W r ω} :=
    measurableSet_le measurable_const (hk.sub hw)
  have h4 : MeasurableSet[𝓕 r] {ω | killed ζ (VR k) r ω - killed ζ W r ω < b ^ (j + 1)} :=
    measurableSet_lt (hk.sub hw) measurable_const
  have e : gridCell W VR ζ r k S b j = {ω | (r : ℝ≥0∞) < ζ ω} ∩
      ({ω | ∀ j', killed ζ (VR j') r ω = killed ζ (VR k) r ω ↔ j' ∈ S} ∩
        ({ω | ∀ j', killed ζ (VR k) r ω ≤ killed ζ (VR j') r ω} ∩
          ({ω | b ^ j ≤ killed ζ (VR k) r ω - killed ζ W r ω} ∩
            {ω | killed ζ (VR k) r ω - killed ζ W r ω < b ^ (j + 1)}))) := by
    ext ω; simp [gridCell]
  rw [e]
  exact hζ.inter (h1.inter (h2.inter (h3.inter h4)))

/-- **The endpoint case has probability zero**, for a fixed restart time `r = q⁺`, mark `k`, level `m`, group `S`
of `k` at `r` and horizon `N`. -/
theorem ae_not_endpointCase_group [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (q : ℚ) (k : Fin nR) (m : ℕ)
    (S : Finset (Fin nR)) (N : ℕ) :
    ∀ᵐ ω ∂P, ∀ σ : ℝ≥0, EndpointCase (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (ζ ω) q k m σ → (∀ j, VR j (ratTime q) ω = VR k (ratTime q) ω ↔ j ∈ S) →
        (σ : ℝ) - ratTime q ≤ N → False := by
  set r := ratTime q with hrdef
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set ρS := ∑ j ∈ S, ρR j with hρSdef
  by_cases hρS : -2 < ρS
  swap
  · filter_upwards [hE.2.2.2.2] with ω hp σ hcase hgrp _
    exact hρS (neg_two_lt_of_endpointCase hp hcase hgrp)
  have hE' := hE
  obtain ⟨hBF, hWad, -, hVRad, hpathE⟩ := hE'
  obtain ⟨Q, Bv, 𝓖, hQprob, hPQ, hQP, hBt, hBvc, h𝓖0, hident⟩ :=
    exists_girsanov_restart hE S hδ r (r + (N : ℝ≥0) + 1)
  set Bt : ℝ≥0 → Ω → ℝ := fun t ω => Bv (r + t) ω - Bv r ω with hBtdef
  have hBtc : ∀ ω, Continuous (Bt · ω) := fun ω =>
    ((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hBt0 : ∀ ω, Bt 0 ω = 0 := fun ω => by simp [hBtdef]
  set sk := Real.sqrt κ with hskdef
  have hsk : sk ^ 2 = κ := Real.sq_sqrt hκ.le
  set α : ℝ := 2 * (2 + ρS) / κ with hαdef
  set β : ℝ := 2 * (4 + ρS - κ) / κ with hβdef
  have hβ1 : -1 < β := by rw [hβdef, lt_div_iff₀ hκ]; linarith
  set Bad : Set Ω := {ω | ∃ σ : ℝ≥0, EndpointCase (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω) q k m σ ∧ (∀ j, VR j r ω = VR k r ω ↔ j ∈ S) ∧
        (σ : ℝ) - r ≤ N} with hBaddef
  set Good : Set Ω := {ω | IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (ζ ω) ((r + (N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) →
        Bv t ω = B t ω + ∫ s in (0 : ℝ)..(t : ℝ), (Real.sqrt κ)⁻¹ *
          addedDriftCut (removedWeights ρL ρR S) δ (W s.toNNReal ω)
            (fun j => allMarks VL VR j s.toNNReal ω)} with hGooddef
  have hGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hpathE, hident] with ω h1 h2
    exact ⟨h1, h2⟩
  suffices hQ0 : Q (Bad ∩ Good) = 0 by
    have hP0 : P (Bad ∩ Good) = 0 := hPQ hQ0
    have hPG : P Goodᶜ = 0 := ae_iff.1 hGood
    have hPB : P Bad = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (measure_union_null hP0 hPG)
      by_cases hg : ω ∈ Good
      · exact Or.inl ⟨hω, hg⟩
      · exact Or.inr hg
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPB] with ω hω σ h1 h2 h3
    exact hω ⟨σ, h1, h2, h3⟩
  -- the bound for each grid ratio `cc`
  have hbound : ∀ n : ℕ, Q (Bad ∩ Good) ≤ ENNReal.ofReal ((scaleTop α β -
      scaleFn α β (1 - 1 / ((n : ℝ) + 3))) / scaleTop α β) := by
    intro n
    set cc : ℝ := 1 - 1 / ((n : ℝ) + 3) with hccdef
    have hn3 : (3 : ℝ) ≤ (n : ℝ) + 3 := by linarith [n.cast_nonneg (α := ℝ)]
    have hcc : 2 / 3 ≤ cc := by
      rw [hccdef]
      have : 1 / ((n : ℝ) + 3) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hn3
      linarith
    have hcc1 : cc < 1 := by
      have : 0 < 1 / ((n : ℝ) + 3) := by positivity
      rw [hccdef]; linarith
    have hcc0 : 0 < cc := by linarith
    set b : ℝ := 1 / cc with hbdef
    have hb : 1 < b := by rw [hbdef, lt_div_iff₀ hcc0]; linarith
    have hb32 : b ≤ 3 / 2 := by rw [hbdef, div_le_iff₀ hcc0]; linarith
    have hccb : cc * b = 1 := by rw [hbdef]; field_simp
    set ε := (scaleTop α β - scaleFn α β cc) / scaleTop α β with hεdef
    have hcell : ∀ j : ℤ, Q (Bad ∩ Good ∩ gridCell W VR ζ r k S b j) ≤
        ENNReal.ofReal ε * Q (gridCell W VR ζ r k S b j) := by
      intro j
      set I := gridCell W VR ζ r k S b j with hIdef
      set y : ℝ := b ^ (j + 1) with hydef
      have hbj : 0 < b ^ j := zpow_pos (by linarith) j
      have hy : 0 < y := zpow_pos (by linarith) (j + 1)
      have hyb : y = b ^ j * b := by rw [hydef, zpow_add_one₀ (by linarith)]
      set gapK : Ω → ℝ := fun ω => killed ζ (VR k) r ω - killed ζ W r ω with hgapKdef
      have hgapK : Measurable[𝓖 0] gapK := fun t ht =>
        h𝓖0 _ (((measurable_killed (hVRad k) r).sub (measurable_killed hWad r)) ht)
      have hI : MeasurableSet[𝓖 0] I := h𝓖0 _ (measurableSet_gridCell hWad hVRad r k S b j)
      have hIgap : ∀ ω ∈ I, cc * y ≤ gapK ω ∧ gapK ω < y := fun ω hω => by
        obtain ⟨-, -, -, h1, h2⟩ := hω
        refine ⟨?_, h2⟩
        have : cc * y = b ^ j := by rw [hyb, ← mul_assoc, mul_comm cc, mul_assoc, hccb, mul_one]
        rw [this]; exact h1
      obtain ⟨L₁, hL₁⟩ := cell_bound hBt hBtc hBt0 hκ hsk hρS hαdef hβdef hβ1 hcc hcc1 hy hgapK hI
        hIgap (N : ℝ≥0)
      have hsub : Bad ∩ Good ∩ I ⊆ ⋃ L₀ : ℕ, ⋂ L : ℕ, ⋂ (_ : max L₀ L₁ ≤ L),
          cellHit sk ρS y I gapK Bt (N : ℝ≥0) L := by
        rintro ω ⟨⟨⟨σ, hcase, hgrp, hσN⟩, hp, hid⟩, hωI⟩
        have hcase' := hcase
        obtain ⟨h1, h2, -, h4, h5, -, h7, h8, h9⟩ := hcase'
        have hrζ : (r : ℝ≥0∞) < ζ ω := lt_trans (ENNReal.coe_lt_coe.2 h1) h2
        have hgapeq : gapK ω = VR k r ω - W r ω := by
          simp only [hgapKdef, killed_of_lt hrζ]
        have hωI' := hωI
        obtain ⟨-, -, -, hj1, hj2⟩ := hωI'
        rw [show killed ζ (VR k) r ω - killed ζ W r ω = gapK ω from rfl, hgapeq] at hj1 hj2
        have hgrpS : ∀ j' ∈ S, ∀ s : ℝ≥0, r ≤ s → s ≤ σ → VR j' s ω = VR k s ω :=
          fun j' hj' s hrs hsσ => vR_eq_of_eq hp hrs (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsσ) h2)
            ((hgrp j').2 hj')
        have hσle : (σ : ℝ) ≤ r + N := by linarith
        have hστ : (σ : ℝ≥0∞) ≤ min (ζ ω) ((r + (N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) := by
          refine le_min h2.le (ENNReal.coe_le_coe.2 ?_)
          rw [← NNReal.coe_le_coe]; push_cast; linarith
        have hdrv : ∀ s : ℝ≥0, r ≤ s → s ≤ σ → W s ω - W r ω = sk * (Bv s ω - Bv r ω) +
            ∫ t in (r : ℝ)..s, ρS / (W t.toNNReal ω - VR k t.toNNReal ω) := fun s hrs hsσ =>
          driver_oneGroup (w := fun t => W t ω) (vL := fun i t => VL i t ω) (vR := fun j t => VR j t ω)
            (b := fun t => B t ω) hκ hδ hp (S := S) (k := k) (u := fun j t => allMarks VL VR j t ω)
            (fun i => by funext t; simp [allMarks]) (fun j => by funext t; simp [allMarks])
            (bh := fun t => Bv t ω) hid hστ h2 hgrpS
            (fun s hrs hsσ j hj => h7 s hrs hsσ j fun he => hj ((hgrp j).1 he)) h8 hrs hsσ
        have hy1 : y / 2 < VR k r ω - W r ω := by
          have : y ≤ b ^ j * (3 / 2) := by rw [hyb]; exact mul_le_mul_of_nonneg_left hb32 hbj.le
          linarith
        have halive := h9 y hj2
        have hσN' : (σ : ℝ) - r ≤ ((N : ℝ≥0) : ℝ) := by push_cast; exact hσN
        obtain ⟨L₀, hL₀⟩ := tamed_hit_of_endpoint (w := fun t => W t ω) (vL := fun i t => VL i t ω)
          (vR := fun j t => VR j t ω) (b := fun t => B t ω) hκ hp h1 h2 hρS (hBvc ω) hdrv h4 h5 hy1
          halive hσN' (B := Bt) (g₀ := fun _ => VR k r ω - W r ω) (ω := ω) (fun t => rfl) rfl
        refine mem_iUnion.2 ⟨L₀, mem_iInter₂.2 fun L hL => ?_⟩
        obtain ⟨hst, hhit⟩ := hL₀ L (le_of_max_le_left hL)
        have hz1 : tU1 sk ρS (1 / (L : ℝ)) (fun _ => VR k r ω - W r ω) Bt 0 ω = 0 :=
          Sec2.markFlow_zero _ _ _ _ ω
        have hz2 : tU2 sk ρS (1 / (L : ℝ)) y (fun _ => VR k r ω - W r ω) Bt 0 ω = 0 :=
          Sec2.markFlow_zero _ _ _ _ ω
        have hlt : gapK ω < (1 - 1 / (L : ℝ)) * y := by
          rw [hgapeq]
          by_contra hcon
          refine hst (Or.inr (Or.inl ?_))
          simp only [gapU, gapX, stW, statePath, tState, tU1, tU2, Sec2.markFlow_zero, hBt0]
          linarith [not_lt.1 hcon]
        refine ⟨⟨hωI, hlt⟩, ?_⟩
        have hcl : clampGap I gapK y L ω = (fun _ : Ω => VR k r ω - W r ω) ω := by
          rw [clampGap, ite_eq_left ⟨hωI, hlt⟩, hgapeq]
        show gapU sk 0 (statePath (tState sk ρS (1 / (L : ℝ)) y (clampGap I gapK y L) Bt) Bt
            (hitStop (tState sk ρS (1 / (L : ℝ)) y (clampGap I gapK y L) Bt) Bt
              (exitC sk (1 / (L : ℝ)) L) (N : ℝ≥0) ω) ω) ≤ _
        rw [hitStop_congr (g₀' := fun _ : Ω => VR k r ω - W r ω) hcl]
        simp only [statePath, tState_congr (g₀' := fun _ : Ω => VR k r ω - W r ω) hcl] at hhit ⊢
        exact hhit
      have hmono : Monotone fun L₀ : ℕ => ⋂ L : ℕ, ⋂ (_ : max L₀ L₁ ≤ L),
          cellHit sk ρS y I gapK Bt (N : ℝ≥0) L := by
        intro a a' haa' ω hω
        refine mem_iInter₂.2 fun L hL => mem_iInter₂.1 hω L ((max_le_max_right L₁ haa').trans hL)
      calc Q (Bad ∩ Good ∩ I)
          ≤ Q (⋃ L₀ : ℕ, ⋂ L : ℕ, ⋂ (_ : max L₀ L₁ ≤ L), cellHit sk ρS y I gapK Bt (N : ℝ≥0) L) :=
            measure_mono hsub
        _ = ⨆ L₀ : ℕ, Q (⋂ L : ℕ, ⋂ (_ : max L₀ L₁ ≤ L), cellHit sk ρS y I gapK Bt (N : ℝ≥0) L) :=
            hmono.measure_iUnion
        _ ≤ ENNReal.ofReal ε * Q I := iSup_le fun L₀ =>
            (measure_mono (iInter₂_subset (max L₀ L₁) le_rfl)).trans (hL₁ _ (le_max_right _ _))
    -- the cells cover the bad set and are disjoint
    have hcover : Bad ∩ Good ⊆ ⋃ j : ℤ, Bad ∩ Good ∩ gridCell W VR ζ r k S b j := by
      rintro ω ⟨⟨σ, hcase, hgrp, hσN⟩, hg⟩
      have hcase' := hcase
      obtain ⟨h1, h2, h3, -, -, h6, -, -, -⟩ := hcase'
      have hrζ : (r : ℝ≥0∞) < ζ ω := lt_trans (ENNReal.coe_lt_coe.2 h1) h2
      obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := VR k r ω - W r ω) (sub_pos.2 h3) hb
      refine mem_iUnion.2 ⟨j, ⟨⟨σ, hcase, hgrp, hσN⟩, hg⟩, hrζ, fun j' => ?_, fun j' => ?_, ?_, ?_⟩
      · simp only [killed_of_lt hrζ]; exact hgrp j'
      · simp only [killed_of_lt hrζ]; exact h6 j'
      · simp only [killed_of_lt hrζ]; exact hj.1
      · simp only [killed_of_lt hrζ]; exact hj.2
    have hdisj : Pairwise (Function.onFun Disjoint fun j : ℤ => gridCell W VR ζ r k S b j) := by
      intro j j' hjj'
      refine Set.disjoint_left.2 fun ω hω hω' => hjj' ?_
      obtain ⟨-, -, -, a1, a2⟩ := hω
      obtain ⟨-, -, -, a1', a2'⟩ := hω'
      have hlt1 : j < j' + 1 := (zpow_lt_zpow_iff_right₀ hb).1 (lt_of_le_of_lt a1 a2')
      have hlt2 : j' < j + 1 := (zpow_lt_zpow_iff_right₀ hb).1 (lt_of_le_of_lt a1' a2)
      omega
    have hmeas : ∀ j : ℤ, MeasurableSet (gridCell W VR ζ r k S b j) := fun j =>
      𝓕.le r _ (measurableSet_gridCell hWad hVRad r k S b j)
    calc Q (Bad ∩ Good) ≤ ∑' j : ℤ, Q (Bad ∩ Good ∩ gridCell W VR ζ r k S b j) :=
          (measure_mono hcover).trans (measure_iUnion_le _)
      _ ≤ ∑' j : ℤ, ENNReal.ofReal ε * Q (gridCell W VR ζ r k S b j) := ENNReal.tsum_le_tsum hcell
      _ = ENNReal.ofReal ε * Q (⋃ j : ℤ, gridCell W VR ζ r k S b j) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hmeas]
      _ ≤ ENNReal.ofReal ε * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal ε := mul_one _
  -- the limit `cc → 1`
  have hTop := scaleTop_pos (α := α) hβ1
  have hcc : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 3)) atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h3 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
        refine h.congr fun n => ?_
        simp only [Function.comp_apply]
        push_cast
        ring_nf
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h3
    · show 1 - 1 / ((n : ℝ) + 3) < 1
      have : 0 < 1 / ((n : ℝ) + 3) := by positivity
      linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((scaleTop α β -
      scaleFn α β (1 - 1 / ((n : ℝ) + 3))) / scaleTop α β)) atTop (𝓝 0) := by
    have h := ((tendsto_scaleTop_sub_scaleFn (α := α) hβ1).comp hcc).div_const (scaleTop α β)
    rw [zero_div] at h
    simpa using ENNReal.tendsto_ofReal h
  exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le

/-- **The endpoint case never happens**, almost surely, at any rational restart time (`0 < κ < 4`). -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_noRightEndpoint [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ < 4) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, NoRightEndpoint (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) := by
  classical
  have h : ∀ᵐ ω ∂P, ∀ (q : ℚ) (k : Fin nR) (m : ℕ) (S : Finset (Fin nR)) (N : ℕ) (σ : ℝ≥0),
      EndpointCase (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) q k m σ →
        (∀ j, VR j (ratTime q) ω = VR k (ratTime q) ω ↔ j ∈ S) →
          (σ : ℝ) - ratTime q ≤ N → False := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun k => ae_all_iff.2 fun m => ae_all_iff.2 fun S =>
      ae_all_iff.2 fun N => ?_
    exact ae_not_endpointCase_group hκ hκ4 hE q k m S N
  filter_upwards [h] with ω hω
  refine noRightEndpoint_of fun q k m σ hcase => ?_
  obtain ⟨N, hN⟩ := exists_nat_ge ((σ : ℝ) - ratTime q)
  exact hω q k m (Finset.univ.filter fun j => VR j (ratTime q) ω = VR k (ratTime q) ω) N σ hcase
    (fun j => by simp) hN

end Main

/-- **The named input `EndpointExclusionStatement` holds.** -/
theorem endpointExclusionStatement : EndpointExclusionStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR Ω mΩ P hP 𝓕 W VL VR B ζ hE
  exact hE.ae_noRightEndpoint hκ hκ4

end Aux25

namespace IsIntegratedSLEEvolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Aux. lemma 25 before the lifetime** (`0 < κ < 4`): almost surely every continuous generating trace on the
available interval is injective on `{t | t < ζ}`. -/
theorem ae_injOn_lt [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      InjOn η {t | (t : ℝ≥0∞) < ζ ω} :=
  hE.ae_injOn_lt_of_endpointExclusion Aux25.endpointExclusionStatement hκ hκ4

/-- **Aux. lemma 25 when the available lifetime is unbounded** (`0 < κ < 4`): almost surely, on `ζ = ∞`, every
continuous generating trace is injective. -/
theorem ae_injOn_of_lifetime_eq_top [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω} :=
  hE.ae_injOn_of_endpointExclusion_of_lifetime_eq_top Aux25.endpointExclusionStatement hκ hκ4

end IsIntegratedSLEEvolution

end InteractingSLE
