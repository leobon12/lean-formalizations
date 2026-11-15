/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalLevy

/-!
# Upper strip marks: the strip driving equation in strip time

Packet PROVE-ZHAN-A33 (Astra, *Follow-up proofs* §A.3.2, the target change "for a point on the upper strip
boundary"; ruling R36). For a chordal integrated evolution of the word `upWordXL q` (the end mark `−1`, the strip end
`−∞`, innermost; upper strip marks `−1 − e^{q_i}`, the chordal images of `q_i + iπ`, beyond it) with right (lower) marks
`xR`, whose strip clock of the end mark is almost surely unbounded on the strip life, there are a filtration `𝓗` and an
`𝓗`-Brownian motion `B̃` such that almost surely, for every strip time `t`, `s(t)` lies in the strip life and

  `ξ_t = √κ B̃_t − Σᵢ (ρ_{i+1}/2)(p_i(t) − q_i) − Σⱼ (ρ^R_j/2)(p^R_j(t) − log(1 + x^R_j)) + c t`,
  `c = ρ₀ + 3 − κ/2 + (Σᵢ ρ_{i+1} + Σⱼ ρ^R_j)/2 = (τ₋ − τ₊)/2`

(`exists_upStripBrownian`), where `ξ = Strip.stripDriver`, `p_i(t) = Strip.stripPoint` of the upper marks (the real
parts of their strip images on `ℝ + iπ`, started at `q_i`) and `p^R_j(t)` that of the right marks.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

variable {nL nR : ℕ}

section Coords

variable {κ : ℝ} {q : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The observable at the chordal time `s(t)` in strip coordinates.** -/
theorem upObs_chordT_eq (hp : IsIntegratedSLEPath κ (upWordXL q) xR ρL ρR w vL vR b ζ)
    (hcl : HasUnboundedStripClock w (vL 0) ζ) (t : ℝ≥0) :
    upObs κ (upWordXL q) xR ρL ρR (upCoordAt w vL vR (chordT w (vL 0) t), b (chordT w (vL 0) t)) =
      (Strip.stripDriver (Strip.extPath w) (Strip.extPath (vL 0)) t - t) +
      (∑ i : Fin nL, ρL i.succ / 2 * (Strip.stripPoint (Strip.extPath w) (Strip.extPath (vL 0))
        (Strip.extPath (vL i.succ)) t - t)) +
      (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath w) (Strip.extPath (vL 0))
        (Strip.extPath (vR j)) t - t)) +
      (κ / 2 - 2 - ρL 0) * t := by
  set s := chordT w (vL 0) t with hs
  have hlife := isStripLife_chordT_up hp (upWordXL_zero q) hcl t
  have hct : (Strip.chordalTime (Strip.extPath w) (Strip.extPath (vL 0)) t).toNNReal = s := rfl
  have hW := w_eq_driftLin hp hlife.1
  have hT : (upCoordAt w vL vR s).2.2 = t := clk_chordT_up hp (upWordXL_zero q) hcl t
  have hg : upGap κ (upWordXL q) xR ρL ρR (upCoordAt w vL vR s, b s) = w s - vL 0 s := by
    simp only [upGap]
    rw [hs, ← hW]
    rfl
  rw [upObs, hg, hT, Fin.sum_univ_succ]
  simp only [Strip.stripDriver, Strip.stripPoint, Strip.extPath, hct]
  simp only [upCoordAt, sub_self, Real.log_zero, mul_zero, zero_add, Real.log_abs]
  ring_nf

/-- The observable at the initial point: `Σ (ρ_{i+1}/2) q_i + Σ (ρ^R_j/2) log(1 + x^R_j)`. -/
theorem upObs_stripInit (q : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ) :
    upObs κ (upWordXL q) xR ρL ρR (stripInit (upWordXL q) xR) =
      (∑ i, ρL i.succ / 2 * q i) + ∑ j, ρR j / 2 * Real.log (1 + xR j) := by
  rw [upObs, upGap_stripInit, Fin.sum_univ_succ]
  simp only [stripInit, upWordXL_zero, upWordXL_succ, neg_neg, Real.log_one, sub_self,
    Real.log_zero, mul_zero, zero_add, add_zero, sub_neg_eq_add]
  have h1 : ∀ i : Fin nL, -1 - Real.exp (q i) + 1 = -Real.exp (q i) := fun i => by ring
  simp only [h1, Real.log_neg_eq_log, Real.log_exp]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm (xR j) 1]

end Coords

/-- **The strip driving equation in strip time, upper strip marks** (conditional on an unbounded strip clock):
the strip driver is `√κ` times a Brownian motion of a filtration plus the integrated force terms of the upper and
lower marks and the endpoint drift `(τ₋ − τ₊)/2`. -/
theorem exists_upStripBrownian {κ : ℝ} (hκ : 0 < κ) {q : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxR : ∀ j, -1 < xR j) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (upWordXL q) xR ρL ρR P 𝓕 W VL VR B ζ)
    (hclock : ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL 0 · ω) (ζ ω)) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧
      (∀ ω, Continuous (B' · ω)) ∧ (∀ ω, B' 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Strip.IsStripLife (W · ω) (VL 0 · ω) (ζ ω) (chordT (W · ω) (VL 0 · ω) t) ∧
        Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) t =
          Real.sqrt κ * B' t ω
          - (∑ i : Fin nL, ρL i.succ / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
              (Strip.extPath (VL 0 · ω)) (Strip.extPath (VL i.succ · ω)) t - q i))
          - (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
              (Strip.extPath (VL 0 · ω)) (Strip.extPath (VR j · ω)) t - Real.log (1 + xR j)))
          + (ρL 0 + 3 - κ / 2 + ((∑ i : Fin nL, ρL i.succ) + ∑ j, ρR j) / 2) * t := by
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_up hE hclock
  have h0 : stripInit (upWordXL q) xR ∈ upRegion κ (upWordXL q) xR ρL ρR := by
    refine stripInit_mem_upRegion κ _ _ _ _ (by simp) (upWordXL_succ_lt q) fun j => ?_
    simpa using hxR j
  refine ⟨upStripFilt hE hGm hGc hgood, upBM κ q xR ρL ρR G W VL VR B,
    isFilteredBrownianReal_upBM hE hGm hGc hgood h0 hκ, continuous_upBM hgood h0, upBM_zero hgood, ?_⟩
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω t
  have hg := hgood ω hω
  refine ⟨isStripLife_chordT_up hg.1 (upWordXL_zero q) hg.2.2.2 t, ?_⟩
  have hBM : Real.sqrt κ * upBM κ q xR ρL ρR G W VL VR B t ω =
      upObs κ (upWordXL q) xR ρL ρR
        (upCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (chordT (W · ω)
          (VL 0 · ω) t), B (chordT (W · ω) (VL 0 · ω) t) ω) -
      upObs κ (upWordXL q) xR ρL ρR (stripInit (upWordXL q) xR) := by
    have hs0 : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
    simp only [upBM, upPhiS, upChordS, upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    field_simp
  rw [hBM, upObs_chordT_eq (vL := fun i t => VL i t ω) (b := (B · ω)) hg.1 hg.2.2.2 t, upObs_stripInit]
  have e1 : ∑ i : Fin nL, ρL i.succ / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
      (Strip.extPath (VL 0 · ω)) (Strip.extPath (VL i.succ · ω)) t - q i) =
      (∑ i : Fin nL, ρL i.succ / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
        (Strip.extPath (VL 0 · ω)) (Strip.extPath (VL i.succ · ω)) t - t)) +
      (∑ i : Fin nL, ρL i.succ / 2) * t - ∑ i, ρL i.succ / 2 * q i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
      (Strip.extPath (VL 0 · ω)) (Strip.extPath (VR j · ω)) t - Real.log (1 + xR j)) =
      (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
        (Strip.extPath (VL 0 · ω)) (Strip.extPath (VR j · ω)) t - t)) +
      (∑ j, ρR j / 2) * t - ∑ j, ρR j / 2 * Real.log (1 + xR j) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : (∑ i : Fin nL, ρL i.succ / 2) = (∑ i : Fin nL, ρL i.succ) / 2 := by rw [Finset.sum_div]
  have e4 : (∑ j, ρR j / 2) = (∑ j, ρR j) / 2 := by rw [Finset.sum_div]
  rw [e1, e2, e3, e4]
  ring

end InteractingSLE.ZhanGT4.UpMark
