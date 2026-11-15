/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NqLim
import InteractingSLE.Spec.Supplement.GW2UbUnb
import InteractingSLE.Spec.ZhanGT4.Prefix
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# A first contact at the tip with a bounded clock: the glued driver is unbounded (D84, corrected)

Packet PROVE-GW2-NEARIMG2, decision D84 item (1): RELDET's `GW2Rd.TipUnbStatement` (`GW2UbUnb`).

**`TipUnbStatement` is false as stated.** Its premise "the contact point `sphereInv(x + γ τ)` is the tip `α(s)`" does
not make the relative trace tend to `∞`. When the tip is a double point of `α` (`α(s) = α(u)` for some `u < s`,
allowed for a generating trace), the fibre of `α(s)` under the boundary extension `F̄_s` of the inverse map contains a
real point `ξ ≠ 0` besides `0`. An example: `α` runs up the segment `[0, 2i]`, then along an arc to the right that
closes a loop at `i` at time `s`. The prime end of `i` on the left side of the segment is not the tip prime end, and
`F̄_s` sends a point `ξ < 0` there. Let the curve `−1/(x + γ t)` come in from the left and reach `i` at time `τ`
through that prime end, with no earlier contact. Its relative trace then tends to the finite point `−1/ξ − relBdry(x)`.
The clock is bounded, and the glued driver `cDrv` is bounded below the life, since it extends continuously
(`exists_canon_of_tendsto`). So `TipUnbStatement`'s conclusion fails. Formally, `not_tendsto_of_tipUnbStatement`
proves that `TipUnbStatement` excludes a finite relative limit at every first contact at the tip.

**Corrected statement** (`TipUnbLimStatement`, proved: `tipUnbLimStatement`): `TipUnbStatement` with the extra
premise that the relative trace has no finite limit at `τ` (by `GW2NqLim`'s dichotomy it then tends to `∞`). The case
it drops (a finite limit, possibly at the tip) is covered by `GW2NqLim.canonContactLimStatement`. So the consumer's
split is: a finite limit gives the canonical driver; otherwise the contact is at the tip (`exists_tendsto_relTr_contact`
gives a finite limit away from it), and a bounded clock gives `TipUnbLimStatement`.

* `exists_cDrv_gt_of_unbounded`: a bounded clock and an unbounded relative trace give an unbounded `cDrv`. The trace at
  the clock of `t` is the limit at `0` of the inverse map of `cDrv` (`tip_eq_c`), and if `|cDrv| ≤ B` that inverse map
  moves points by at most `6B + 6√(clock)` (`ZhanGT4.norm_fwdMapInv_sub_le_of_le`, through the chain driver).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  {τ : ℝ≥0} (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞))

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **A bounded clock and an unbounded relative trace give an unbounded glued driver below the life.** -/
theorem exists_cDrv_gt_of_unbounded {M : ℝ} (hM : ∀ v : ℝ≥0, v < τ → gClk x s (cfRec s W ζ ω) w v ≤ M)
    (hunb : ∀ R : ℝ, ∃ t : ℝ≥0, t < τ ∧ R < ‖relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x‖) (B : ℝ) :
    ∃ (u v : ℝ≥0), v < τ ∧ (u : ℝ) < gClk x s (cfRec s W ζ ω) w v ∧
      B < |cDrv x s (cfRec s W ζ ω) w τ u| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hm, -⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  set a := gClk x s (cfRec s W ζ ω) w with hadef
  set B' := max B 0 with hB'
  obtain ⟨t, ht, hbig⟩ := hunb (6 * B' + 6 * Real.sqrt M)
  obtain ⟨v, htv, hvτ⟩ := exists_between ht
  have hv0 : 0 < v := lt_of_le_of_lt zero_le htv
  have hτ0 : (0 : ℝ≥0) ∈ Iio τ := lt_of_le_of_lt zero_le ht
  have hat : 0 ≤ a t := h0 ▸ hm.monotoneOn hτ0 ht zero_le
  have hatv : a t < a v := hm ht hvτ htv
  obtain ⟨R, hRc, hR0, -, hReq⟩ := exists_chain_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv0 hvτ
  set σ : ℝ≥0 := (a t).toNNReal with hσdef
  have hσ : (σ : ℝ) = a t := Real.coe_toNNReal _ hat
  have hσv : (σ : ℝ≥0∞) < ENNReal.ofReal (a v) := by rw [ENNReal.coe_lt_ofReal, hσ]; exact hatv
  have hgen := isGeneratingTrace_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ
  have htend := hgen.tendsto_fwdMapInv_tip (continuousOn_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ)
    (cDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT) hσv
  have htip := tip_eq_c W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT htv.le hvτ
  -- the inverse map of `cDrv` at `σ` is that of the chain driver
  have hinv : fwdMapInv (fun r : ℝ => cDrv x s (cfRec s W ζ ω) w τ r.toNNReal) (σ : ℝ) =
      fwdMapInv (fun r : ℝ => R r.toNNReal) (σ : ℝ) := by
    refine InteractingSLE.fwdMapInv_eq_of_eqOn σ.coe_nonneg
      (show (σ : ℝ) < ((σ : ℝ) + a v) / 2 by linarith) fun r hr => hReq _ ?_
    rw [Real.coe_toNNReal _ hr.1]
    linarith [hr.2]
  rw [hinv] at htend
  -- the driver bound on `[0, σ]`, and the displacement bound
  have hRb : ∀ r ∈ Icc (0 : ℝ) σ, |R r.toNNReal| ≤ B' := by
    intro r hr
    have hlt : ((r.toNNReal : ℝ≥0) : ℝ) < a v := by
      rw [Real.coe_toNNReal _ hr.1]
      linarith [hr.2]
    rw [← hReq _ hlt]
    exact (hcon _ v hvτ hlt).trans (le_max_left _ _)
  have hbd : ∀ z ∈ H, ‖fwdMapInv (fun r : ℝ => R r.toNNReal) σ z - z‖ ≤ 6 * B' + 6 * Real.sqrt σ :=
    fun z hz => ZhanGT4.norm_fwdMapInv_sub_le_of_le (W := fun r : ℝ => R r.toNNReal)
      (hRc.comp continuous_real_toNNReal)
      (by simp only [Real.toNNReal_zero, hR0]) σ.coe_nonneg hRb hz
  have : (𝓝[H] (0 : ℂ)).NeBot := Restart.neBot_nhdsWithin_H_zero
  have hlim : Tendsto (fun z => fwdMapInv (fun r : ℝ => R r.toNNReal) σ z - z) (𝓝[H] 0)
      (𝓝 (RootI30.capacityTipRead x s v σ (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) - 0)) :=
    htend.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have hle := le_of_tendsto hlim.norm (eventually_nhdsWithin_of_forall hbd)
  rw [sub_zero, htip] at hle
  have hσM : Real.sqrt σ ≤ Real.sqrt M := Real.sqrt_le_sqrt (by rw [hσ]; exact hM t ht)
  linarith

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **Without a finite relative limit, a bounded clock gives an unbounded glued driver below the life.** -/
theorem exists_cDrv_gt_of_not_tendsto {M : ℝ}
    (hM : ∀ v : ℝ≥0, v < τ → gClk x s (cfRec s W ζ ω) w v ≤ M)
    (hnl : ¬ ∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) (B : ℝ) :
    ∃ (u v : ℝ≥0), v < τ ∧ (u : ℝ) < gClk x s (cfRec s W ζ ω) w v ∧
      B < |cDrv x s (cfRec s W ζ ω) w τ u| := by
  have hτ0 : 0 < τ := contact_pos' W ω hα hx harc hγ hT
  have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
  have hinf := (tendsto_or_tendsto_norm_relTr W ζ ω hα hW hW0 hζ hx harc hwc hw0 hγ hT).resolve_left hnl
  refine exists_cDrv_gt_of_unbounded W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hM (fun R => ?_) B
  obtain ⟨t, ht1, ht2⟩ := ((hinf.eventually (eventually_gt_atTop R)).and self_mem_nhdsWithin).exists
  exact ⟨t, ht2, ht1⟩

end Sample

/-- **`TipUnbStatement` corrected** (D84): with the extra premise that the relative trace has no finite limit at the
contact. The dropped case (a finite limit) is `canonContactLimStatement`. -/
def TipUnbLimStatement : Prop :=
  ∀ {Ω : Type u} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : ℝ≥0 → ℂ},
    IsGeneratingTrace (W · ω) ⊤ α → Continuous (W · ω) → W 0 ω = 0 → ζ ω = ⊤ →
    ∀ {s : ℝ≥0}, 0 < s → ∀ {x : ℝ}, 0 ≤ x → (∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) →
    ∀ {w : ℝ≥0 → ℝ}, Continuous w → w 0 = 0 → ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace w ⊤ γ → α s ≠ 0 →
    ∀ τ : ℝ≥0, firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞) →
    sphereInv (((x : ℂ) + γ τ : ℂ) : OnePoint ℂ) = ((α s : ℂ) : OnePoint ℂ) →
    (¬ ∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ)) →
    (∃ M : ℝ, ∀ v : ℝ≥0, v < τ → gClk x s (cfRec s W ζ ω) w v ≤ M) →
    ∀ B : ℝ, ∃ (u v : ℝ≥0), v < τ ∧ (u : ℝ) < gClk x s (cfRec s W ζ ω) w v ∧
      B < |cDrv x s (cfRec s W ζ ω) w τ u|

/-- **The corrected `TipUnbStatement` holds** (no inputs). -/
theorem tipUnbLimStatement : TipUnbLimStatement.{u} := by
  intro Ω W ζ ω α hα hW hW0 hζ s hs x hx harc w hwc hw0 γ hγ _ τ hT _ hnl ⟨M, hM⟩ B
  exact exists_cDrv_gt_of_not_tendsto W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hM hnl B

/-- **What `TipUnbStatement` asserts beyond the corrected form**: at every first contact at the tip the relative
trace has no finite limit. This fails when the tip is a double point reached through its other prime end (see the
module docstring), so `TipUnbStatement` is false. -/
theorem not_tendsto_of_tipUnbStatement (hTU : GW2Rd.TipUnbStatement.{u}) {Ω : Type u} (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) (hαs : α s ≠ 0) {τ : ℝ≥0}
    (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞))
    (htip : sphereInv (((x : ℂ) + γ τ : ℂ) : OnePoint ℂ) = ((α s : ℂ) : OnePoint ℂ)) :
    ¬ ∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
      relBdry (rdrv (cfRec s W ζ ω)) s x) (𝓝[<] τ) (𝓝 ℓ) := by
  rintro ⟨ℓ, hρ⟩
  obtain ⟨Wc, hWc, -, -, -, hag, M, hM⟩ :=
    exists_canon_of_tendsto W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hρ
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := M.toNNReal)).exists_bound_of_continuousOn
    hWc.continuousOn
  obtain ⟨u, v, hvτ, hu, hB⟩ := hTU W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hαs τ hT htip ⟨M, hM⟩ K
  have huM : u ≤ M.toNNReal := by
    rw [← Real.toNNReal_coe (r := u)]
    exact Real.toNNReal_le_toNNReal (hu.le.trans (hM v hvτ))
  have h := hK u ⟨zero_le, huM⟩
  rw [hag u v hvτ hu, Real.norm_eq_abs] at h
  linarith

end InteractingSLE.Theorem14.GW2Ni
