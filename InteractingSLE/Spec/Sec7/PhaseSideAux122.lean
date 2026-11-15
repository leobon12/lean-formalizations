/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMartLifeAe

/-!
# Aux. lemma 122 before the relative lifetime: the phase vanishes

Packet PROVE-PHASE. Specification §7.4, Aux. lemma 122 (`source/spec/p385-432.md` L104–L131, pp. 389–391: "Retain a
stopped Gaussian field kernel whose harmonic mean `M_t(z)` is a continuous local martingale until `z` is swallowed.
Assume the following exact boundary description […] the exposed interval raised by one common `d_t ∈ 2πχℤ` […] Then
`d_t = 0`"), Aux. lemma 125's localization (p. 397: "Stop before a fixed coordinate bound or at `ζ`, whichever occurs
first"), and Astra's follow-up 5 §3.2 (`source/external/AstraIG1/ig1_followup5.txt` L456–L483, R73: "If
`−2 < r_L, r_R < 2A − 2 = k − 6`, Aux. 122 forces zero phase").

PROVE-STRIPSYS6's `PhaseSelAdapt.aux122_adapt` selects the zero phase before a stopping time `T` for continuous
coordinates on all of `[0, ∞)`; PROVE-STRIPSYS14's `PocketMartLife.exists_aux122_stop` restarts the coordinates of a
random driven curve at a stopping time `σ` strictly before the relative lifetime, but keeps only the conditional
martingale conclusion. Here the phase conclusion is kept, and the announcing times of the coordinates
(`PocketMartLife.exists_announcing_coords`) carry it through the whole relative lifetime:

* `ae_phase_eq_zero_stop`: almost surely `d_t = 0` for `0 < t ≤ σ`, for a stopping time `σ` strictly before the
  lifetime;
* **`ae_phase_eq_zero_of_hasPhaseMeans`**: for a random driven curve with points of `ℍ` of arbitrarily large modulus
  and filled prefixes adapted to a right-continuous filtration, random time-zero marks with seeds at `0`, seed
  weights in `(−2, k − 6)`, a lattice-valued phase `d_t ∈ 2πχℤ` and Aux. lemma 122's hypotheses before the relative
  lifetime (`PocketMartLife.HasPhaseMeansBefore`), almost surely `d_t = 0` at every `0 < t < capLife`.

The phase need not be measurable or continuous: `aux122_adapt` reads it off (PS9.1) at far points. Conditional helpers
with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseSide

open MartChar PocketTraversal PhaseSel PocketMartLife Lemma71C

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

section Stop

variable {W : ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
  {d : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0}

/-- **Aux. lemma 122 for the coordinates restarted at `σ < T`: the phase is zero up to `σ`** (`aux122_adapt` with the
lifetime `σ`, as in `PocketMartLife.exists_aux122_stop`, keeping its phase conclusion): almost surely `d_t = 0` for
every `0 < t ≤ σ`. -/
theorem ae_phase_eq_zero_stop [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω})
    {Wk : ℝ≥0 → Ω → ℝ} (hWka : StronglyAdapted 𝓕 Wk)
    (hWk : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < T ω → Wk t ω = W t ω)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσT : ∀ ω, (σ ω : WithTop ℝ≥0) < T ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ σ ω → d t ω = 0 := by
  have hk0 : 0 < k := by linarith
  have hWc' : ∀ ω, Continuous (stopW W σ · ω) := continuous_stopW hWc hσT
  have hW0' : ∀ ω, stopW W σ 0 ω = 0 := fun ω => (stopW_of_le zero_le).trans (hW0 ω)
  have hWa' : StronglyAdapted 𝓕 (stopW W σ) := stronglyAdapted_stopW hWka hWk hWc hσ hσT
  have hxL0 : ∀ ω i, xL ω i ≤ 0 := fun ω i => (hxLi ω (Fin.zero_le i)).trans_eq (hseedL ω)
  have hxR0 : ∀ ω j, 0 ≤ xR ω j := fun ω j => (hseedR ω).symm.trans_le (hxRi ω (Fin.zero_le j))
  have hd' : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) ≤ (σ ω : WithTop ℝ≥0) →
      ∃ n : ℤ, stopD d σ t ω = n * phaseStep k := fun t ω ht hts => by
    have hts' : t ≤ σ ω := WithTop.coe_le_coe.1 hts
    simp only [stopD, hts', ↓reduceIte]
    exact hd t ω ht (lt_of_le_of_lt hts (hσT ω))
  obtain ⟨A, -, hAd, hAae, -⟩ := PhaseSelAdapt.aux122_adapt (P := P) (𝓕 := 𝓕)
    (T := fun ω => (σ ω : WithTop ℝ≥0)) (d := stopD d σ) hk hrL hrL' hrR hrR'
    (fun ω => by rw [geomLW_zero hWc' hW0' (hxL0 ω 0), hseedL ω])
    (fun ω => by rw [geomRW_zero hWc' hW0' (hxR0 ω 0), hseedR ω])
    (fun ω i => by rw [geomLW_zero hWc' hW0' (hxL0 ω _)]; exact hxLd ω i)
    (fun ω j => by rw [geomRW_zero hWc' hW0' (hxR0 ω _)]; exact hxRd ω j)
    hW0' hWc' hWa' (stronglyAdapted_geomLW hWa' hWc' hxLm) (stronglyAdapted_geomRW hWa' hWc' hxRm)
    (fun ω t i => geomLW_le hWc' xL ω t i) (fun ω t j => le_geomRW hWc' xR ω t j)
    (isForcePath_geomLW hWc' xL) (isForcePath_geomRW hWc' xR) (antitone_geomLW hWc' xL)
    (monotone_geomRW hWc' xR) (fun ω t => antitone_index_geomLW hWc' (hxLi ω) t)
    (fun ω t => monotone_index_geomRW hWc' (hxRi ω) t)
    (fun ω i j s t hst => geomLW_merge hWc' xL ω i j s t hst)
    (fun ω i j s t hst => geomRW_merge hWc' xR ω i j s t hst)
    (fun ω t ht i j => geom_sep hWc' xL xR ω t ht i j) hσ hd'
    (fun U hU z hz => (hasPhaseMeans_stop hk0 hWc hM hσ hσT U hU).1 z hz)
    (fun U hU => (hasPhaseMeans_stop hk0 hWc hM hσ hσT U hU).2)
  filter_upwards [hAae] with ω hω t ht htσ
  have hmem : ω ∈ A := hω (WithTop.coe_lt_coe.2 (lt_of_lt_of_le ht htσ))
  have h := (hAd ω hmem).2 t ht (WithTop.coe_le_coe.2 htσ)
  simpa only [stopD, htσ, ↓reduceIte] using h

end Stop

section Curve

variable {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {d : ℝ≥0 → Ω → ℝ}

/-- **Aux. lemma 122 before the relative lifetime: the phase vanishes** (specification pp. 389–391, with Aux. lemma
125's pre-lifetime localization, p. 397; follow-up 5 §3.2, R73). Let `γ` be a random driven curve with points of `ℍ`
of arbitrarily large modulus whose filled prefixes are adapted to a right-continuous filtration `𝓕`, with
`𝓕₀`-measurable ordered marks (seeds at `0`, the other left marks negative, the other right marks positive), seed
weights in `(−2, 2(k/2 − 2) − 2) = (−2, k − 6)`, a phase `d_t ∈ 2πχℤ` at every positive time before the lifetime, and
Aux. lemma 122's hypotheses before the lifetime for the canonical driver and the geometric force coordinates
(`HasPhaseMeansBefore`). Then almost surely `d_t = 0` at every `0 < t < capLife`. Route: the announcing times `τₘ`
of the coordinates (`exists_announcing_coords`) are stopping times strictly before the lifetime and exhaust it;
`ae_phase_eq_zero_stop` at each `τₘ`. -/
theorem ae_phase_eq_zero_of_hasPhaseMeans [IsProbabilityMeasure P] [𝓕.IsRightContinuous] (hk : 4 < k)
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR d (fun ω => capLife (γ ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → d t ω = 0 := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω =>
    (hγ ω).segDriver_spec.2.1
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => (hγ ω).segDriver_spec.1
  obtain ⟨τ, hτ, hτT, -, hτex, -, -⟩ := exists_announcing_coords hγ hunb hpre hxLm hxRm
  have h := fun m => ae_phase_eq_zero_stop (P := P) (σ := τ m) hk hrL hrL' hrR hrR' hW0 hWc
    (stronglyAdapted_killAt_segDriver hγ hpre) (fun ω t ht => killAt_segDriver_of_lt ht) hxLm hxRm hseedL
    hseedR hxLd hxRd hxLi hxRi hd hM (hτ m) (hτT m)
  filter_upwards [ae_all_iff.2 h] with ω hω t ht htT
  obtain ⟨m, hm⟩ := hτex ω t htT
  exact hω m t ht hm

end Curve

end InteractingSLE.Sec7.PhaseSide
