/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeLevy

/-!
# The strip driving equation in strip time

Packet PROVE-ZHAN-A2 (Astra §3 (ii) and the target change (3.4), (3.9)–(3.11); ruling R36). For an R36 strip
evolution `Strip.IsStripSLEEvolution κ pL pR ρL ρR τ₋ …` whose strip clock is almost surely unbounded on the strip
life, there are a filtration `𝓗` and an `𝓗`-Brownian motion `B̃` such that, almost surely, for every strip time
`t ≥ 0` the chordal time `s(t)` lies in the strip life and

  `ξ_t = √κ B̃_t − Σᵢ (ρ^L_i/2)(p^L_i(t) − p^L_i) − Σⱼ (ρ^R_j/2)(p^R_j(t) − p^R_j) + ((τ₋ − τ₊)/2) t`

(`exists_stripBrownian`), where `ξ = Strip.stripDriver`, `p^{L/R}(t) = Strip.stripPoint` of the lower marks (their
strip coordinates, started at `p^{L/R}`), and `τ₊ = Strip.tauPlus κ ρL ρR τ₋` is the target charge. With the marks'
own equations `dp/dt = −coth((ξ − p)/2)` this is the strip SDE
`dξ = √κ dB̃ + Σ (ρ/2) coth((ξ − p)/2) dt + ((τ₋ − τ₊)/2) dt` of Astra's (3.4)/(3.9) (the drift of `Zhan.stripDrift_eq`);
in the integrated form above no integrability of the `coth` terms near collisions is needed.

The hypothesis "the strip clock is unbounded on the strip life" is clause (1) of `Strip.HasStripEndpoint` (strip
time is defined for all `t ≥ 0`); it is not proved here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-! ### The strip observable in strip coordinates -/

section Coords

variable {κ : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The strip observable at the chordal time `s(t)` in strip coordinates**:
`Φ = (ξ_t − t) + Σᵢ (ρᵢ/2)(pᵢ(t) − t) + Σⱼ (ρⱼ/2)(qⱼ(t) − t) + (κ/2 − 2 − τ₋) t` (the term of the end mark vanishes). -/
theorem stripMartObs_chordT_eq (hp : IsIntegratedSLEPath κ (Strip.wordXL pL) xR ρL ρR w vL vR b ζ)
    (hcl : HasUnboundedStripClock w (vL (Fin.last nL)) ζ) (t : ℝ≥0) :
    stripMartObs κ (Strip.wordXL pL) xR ρL ρR
        (stripCoordAt w vL vR (chordT w (vL (Fin.last nL)) t), b (chordT w (vL (Fin.last nL)) t)) =
      (Strip.stripDriver (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) t - t) +
      (∑ i : Fin nL, ρL i.castSucc / 2 * (Strip.stripPoint (Strip.extPath w)
        (Strip.extPath (vL (Fin.last nL))) (Strip.extPath (vL i.castSucc)) t - t)) +
      (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath w) (Strip.extPath (vL (Fin.last nL)))
        (Strip.extPath (vR j)) t - t)) +
      (κ / 2 - 2 - ρL (Fin.last nL)) * t := by
  set s := chordT w (vL (Fin.last nL)) t with hs
  have hlife := isStripLife_chordT hp hcl t
  have hct : (Strip.chordalTime (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) t).toNNReal = s := rfl
  have hW := w_eq_driftLin hp hlife.1
  have hT : (stripCoordAt w vL vR s).2.2 = t := clk_chordT hp hcl t
  rw [stripMartObs_eq, Fin.sum_univ_castSucc]
  simp only [Strip.stripDriver, Strip.stripPoint, Strip.extPath, hct]
  have hg : gapArg κ (Strip.wordXL pL) xR ρL ρR (stripCoordAt w vL vR s, b s) =
      w s - vL (Fin.last nL) s := by
    simp only [gapArg]
    rw [hs, ← hW]
    rfl
  rw [hg, hT]
  simp only [stripCoordAt, sub_self, Real.log_zero, mul_zero, add_zero, Real.log_abs]
  ring_nf

/-- The strip observable at the initial point of an R36 word: `Σ (ρ^L_i/2) p^L_i + Σ (ρ^R_j/2) p^R_j`. -/
theorem stripMartObs_stripInit_word (pR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (τm : ℝ) (ρR : Fin nR → ℝ) :
    stripMartObs κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR
        (stripInit (Strip.wordXL pL) (Strip.wordXR pR)) =
      (∑ i, ρL i / 2 * pL i) + ∑ j, ρR j / 2 * pR j := by
  rw [stripMartObs_eq, gapArg_stripInit, Fin.sum_univ_castSucc]
  simp only [stripInit, Strip.wordXL_last, Strip.wordXL_castSucc, Strip.wordRhoL_castSucc,
    Strip.wordRhoL_last, Strip.wordXR, neg_neg, Real.log_one, sub_self, Real.log_zero, mul_zero,
    add_zero, sub_neg_eq_add, sub_add_cancel, Real.log_exp, zero_add]

end Coords

/-! ### The main theorem -/

/-- **The strip driving equation in strip time** (conditional on an unbounded strip clock): the strip driver is
`√κ` times a Brownian motion of a filtration plus the integrated force terms of the lower marks and the endpoint
drift `(τ₋ − τ₊)/2`. -/
theorem exists_stripBrownian {κ : ℝ} (hκ : 0 < κ) {pL : Fin nL → ℝ} {pR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {τm : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : Strip.IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ)
    (hclock : ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL (Fin.last nL) · ω) (ζ ω)) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Strip.IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) (chordT (W · ω) (VL (Fin.last nL) · ω) t) ∧
        Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) t =
          Real.sqrt κ * B' t ω
          - (∑ i : Fin nL, ρL i / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
              (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VL i.castSucc · ω)) t - pL i))
          - (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
              (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VR j · ω)) t - pR j))
          + (τm - Strip.tauPlus κ ρL ρR τm) / 2 * t := by
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_strip hE hclock
  have h0 : stripInit (Strip.wordXL pL) (Strip.wordXR pR) ∈
      stripMartRegion κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR := by
    refine stripInit_mem_region κ _ _ _ _ (by simp) (wordXL_last_lt pL) fun j => ?_
    simp only [Strip.wordXL_last, Strip.wordXR]
    linarith [Real.exp_pos (pR j)]
  refine ⟨stripFilt hE hGm hGc hgood, stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B,
    isFilteredBrownianReal_stripBM hE hGm hGc hgood h0 hκ, ?_⟩
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω t
  have hg := hgood ω hω
  refine ⟨isStripLife_chordT hg.1 hg.2.2.2 t, ?_⟩
  have hBM : Real.sqrt κ * stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B t ω =
      stripMartObs κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR
        (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (chordT (W · ω)
          (VL (Fin.last nL) · ω) t), B (chordT (W · ω) (VL (Fin.last nL) · ω) t) ω) -
      stripMartObs κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR
        (stripInit (Strip.wordXL pL) (Strip.wordXR pR)) := by
    have hs0 : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
    simp only [stripBM, phiS, chordS, coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    field_simp
  rw [hBM, stripMartObs_chordT_eq (vL := fun i t => VL i t ω) (b := (B · ω)) hg.1 hg.2.2.2 t,
    stripMartObs_stripInit_word]
  simp only [Strip.wordRhoL_castSucc, Strip.wordRhoL_last, Strip.tauPlus]
  have e1 : ∑ i : Fin nL, ρL i / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
      (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VL i.castSucc · ω)) t - pL i) =
      (∑ i : Fin nL, ρL i / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VL i.castSucc · ω)) t - t)) +
      (∑ i : Fin nL, ρL i / 2) * t - ∑ i, ρL i / 2 * pL i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
      (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VR j · ω)) t - pR j) =
      (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VR j · ω)) t - t)) +
      (∑ j, ρR j / 2) * t - ∑ j, ρR j / 2 * pR j := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : (∑ i : Fin nL, ρL i / 2) = (∑ i, ρL i) / 2 := by rw [Finset.sum_div]
  have e4 : (∑ j, ρR j / 2) = (∑ j, ρR j) / 2 := by rw [Finset.sum_div]
  rw [e1, e2, e3, e4]
  ring

end Zhan

end InteractingSLE
