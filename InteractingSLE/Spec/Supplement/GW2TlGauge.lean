/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlRead
import InteractingSLE.Spec.Supplement.GW2GmSlit
import InteractingSLE.Spec.Zhan.ConstDriftTraceRs

/-!
# N4 item 1 in launch coordinates, part 3: the death gauge of the candidate's launch coordinates

Packet PROVE-GW2-RELDET (decision D20, option (A)). The candidate starts at the physical time `T` (the history time).
In its launch chart it is the Loewner trace of the shifted driver `W(T + ·) − W(T)`, launched at `0`. Its death is its
first entrance into the closed bad set of its launch word (`GW2Rd.ae_candidate_life_badEntrance`). For a launch word
`B w` read off the physical driver `w` up to `T`:

* `launchTr T w σ = LP.traceAt σ (Sec7.shiftNN w T)`: the launch trace at own time `σ`; `launchDist`: its distance to
  the word's bad set (`badDist`); `launchStart`: the distance of the launch point `0`;
* `launchGaugeOf`: `1` if `launchStart = 0`, else `min 1 (launchDist / launchStart)` (read causally by `evalDn`);
* **`launchGauge s κ θ B T cap`**: the gauge at relative time `t` reads the frozen path `(rec, freezeAt t path)`: the
  physical driver `physDrvR` and the own time `min cap (physTimeR − T)`. It is Borel (`measurable_launchGauge`), causal
  (`isCausal_launchGauge`, by the freezing), nonnegative;
* `launchLife`: the relative clock of the first entrance of the launch trace into the bad set, at an own time
  `≤ cap` and before the first contact; `⊤` if there is none, or if the launch point lies in the bad set;
* **`ae_launchGauge_coord`**: along EVERY relative coordinate process, almost surely on the record event, the gauge is
  continuous before the coordinates' life, positive before `launchLife` and zero at it, and `0 < launchLife` — the
  hypotheses of RELDET's capped version family (`exists_schedVersionsA_strict_gauge`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId
open Restart (BoundaryWord)

/-! ### Definitions -/

section Defs

variable (κ θ : ℝ) (B : (ℝ≥0 → ℝ) → BoundaryWord) (T cap : ℝ≥0)

/-- The launch trace of the candidate at own time `σ`, for the physical driver `w`. -/
def launchTr (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : ℂ := LP.traceAt σ (Sec7.shiftNN w T)

/-- The distance of the launch trace to the launch word's bad set. -/
def launchDist (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : ℝ := badDist κ θ (B w) (launchTr T w σ)

/-- The distance of the launch point `0` to the launch word's bad set. -/
def launchStart (w : ℝ≥0 → ℝ) : ℝ := badDist κ θ (B w) 0

/-- The normalized launch distance, read causally at the own time `σ`. -/
def launchGaugeOf (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : ℝ :=
  if launchStart κ θ B w = 0 then 1 else min 1 (max 0 (evalDn (launchDist κ θ B T w) σ) / launchStart κ θ B w)

/-- The candidate's own time at relative time `t`, capped at `cap`. -/
def ownTimeR (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℝ≥0 := min cap ((physTimeR s t p).toNNReal - T)

/-- The path frozen at `t`. -/
def frz (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : RecData × (ℝ≥0 → ℝ) := (p.1, LP.freezeAt t p.2)

/-- **The death gauge in the candidate's launch coordinates.** -/
def launchGauge (s : ℝ≥0) : GaugeReadout := fun t p =>
  launchGaugeOf κ θ B T (physDrvR s (frz t p)) (ownTimeR T cap s t (frz t p))

open scoped Classical in
/-- **The life of the launch gauge**: the relative clock of the launch trace's first entrance into the bad set at an
own time `≤ cap`, before the first contact; `⊤` otherwise (or if the launch point lies in the bad set). -/
def launchLife (W : ℝ≥0 → ℝ) (a : ℝ≥0 → ℝ) (Tc : ℝ≥0∞) : ℝ≥0∞ :=
  if launchStart κ θ B W ≠ 0 ∧ ∃ σ : ℝ≥0, σ ≤ cap ∧ launchDist κ θ B T W σ = 0 ∧ ((T + σ : ℝ≥0) : ℝ≥0∞) < Tc then
    ENNReal.ofReal (a (T + sInf {σ : ℝ≥0 | σ ≤ cap ∧ launchDist κ θ B T W σ = 0})) else ⊤

end Defs

variable {κ θ : ℝ} {B : (ℝ≥0 → ℝ) → BoundaryWord} {T cap : ℝ≥0}

/-! ### Measurability, causality, sign -/

theorem measurable_shiftNN_path (T : ℝ≥0) : Measurable fun w : ℝ≥0 → ℝ => Sec7.shiftNN w T :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem measurable_launchDist (hB : Measurable B) (σ : ℝ≥0) : Measurable fun w => launchDist κ θ B T w σ :=
  measurable_badDist_comp κ θ hB ((LP.measurable_traceAt σ).comp (measurable_shiftNN_path T))

theorem measurable_launchStart (hB : Measurable B) : Measurable fun w => launchStart κ θ B w :=
  measurable_badDist_comp κ θ hB measurable_const

theorem measurable_launchGaugeOf (hB : Measurable B) {α : Type*} [MeasurableSpace α] {w : α → ℝ≥0 → ℝ}
    (hw : Measurable w) {σ : α → ℝ≥0} (hσ : Measurable σ) :
    Measurable fun a => launchGaugeOf κ θ B T (w a) (σ a) := by
  unfold launchGaugeOf
  have hs : Measurable fun a => launchStart κ θ B (w a) := (measurable_launchStart hB).comp hw
  have he : Measurable fun a => evalDn (launchDist κ θ B T (w a)) (σ a) :=
    measurable_evalDn (p := fun a σ' => launchDist κ θ B T (w a) σ')
      (fun σ' => (measurable_launchDist hB σ').comp hw) hσ
  exact Measurable.ite (hs (measurableSet_singleton 0)) measurable_const
    (measurable_const.min ((measurable_const.max he).div hs))

theorem measurable_frz (t : ℝ≥0) : Measurable (frz t) :=
  measurable_fst.prodMk ((LP.measurable_freezeAt t).comp measurable_snd)

theorem measurable_ownTimeR (s t : ℝ≥0) : Measurable (ownTimeR T cap s t) :=
  measurable_const.min ((measurable_physTimeR s t).ennreal_toNNReal.sub measurable_const)

/-- **The launch gauge is Borel.** -/
theorem measurable_launchGauge (hB : Measurable B) (s t : ℝ≥0) :
    Measurable (launchGauge κ θ B T cap s t) :=
  measurable_launchGaugeOf hB ((measurable_physDrvR_path s).comp (measurable_frz t))
    ((measurable_ownTimeR s t).comp (measurable_frz t))

/-- **The launch gauge is causal** (it reads the path frozen at `t`). -/
theorem isCausal_launchGauge (s : ℝ≥0) : IsCausal (launchGauge κ θ B T cap s) := by
  intro t r w w' h
  simp only [launchGauge, frz, LP.freezeAt_congr h]

theorem launchStart_nonneg (w : ℝ≥0 → ℝ) : 0 ≤ launchStart κ θ B w := badDist_nonneg _ _

theorem launchGaugeOf_nonneg (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : 0 ≤ launchGaugeOf κ θ B T w σ := by
  unfold launchGaugeOf
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (div_nonneg (le_max_left _ _) (launchStart_nonneg w))

theorem launchGauge_nonneg (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ launchGauge κ θ B T cap s t p :=
  launchGaugeOf_nonneg _ _

/-! ### The launch point -/

/-- The trace of a path from `0` at time `0` is `0`. -/
theorem traceAt_zero_of {v : ℝ≥0 → ℝ} (hv0 : v 0 = 0) : LP.traceAt 0 v = 0 := by
  rw [LP.traceAt_congr (w' := fun _ => (0 : ℝ)) fun r hr => by rw [le_zero_iff.1 hr, hv0]]
  rw [LP.traceAt_eq_of_isGeneratingTrace GW2TipSystem.Gm.isGeneratingTrace_zero_slit continuousOn_const rfl
    ENNReal.coe_lt_top]
  exact GW2TipSystem.Gm.isGeneratingTrace_zero_slit.1

theorem launchTr_zero (w : ℝ≥0 → ℝ) : launchTr T w 0 = 0 :=
  traceAt_zero_of (Sec7.shiftNN_zero w T)

theorem launchDist_zero (w : ℝ≥0 → ℝ) : launchDist κ θ B T w 0 = launchStart κ θ B w := by
  unfold launchDist launchStart
  rw [launchTr_zero]

theorem evalDn_zero (p : ℝ≥0 → ℝ) : evalDn p 0 = p 0 := by
  unfold evalDn
  have h : ∀ n, dyadLo n 0 = 0 := fun n => le_zero_iff.1 (dyadLo_le n 0)
  simp only [h, limsup_const]

/-- **At own time `0` the gauge is `1`.** -/
theorem launchGaugeOf_zero (w : ℝ≥0 → ℝ) : launchGaugeOf κ θ B T w 0 = 1 := by
  unfold launchGaugeOf
  rw [evalDn_zero, launchDist_zero]
  split_ifs with h
  · rfl
  · rw [max_eq_right (launchStart_nonneg w), div_self h, min_self]

/-! ### The launch trace of a driver with a global trace -/

section Trace

variable {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

theorem continuous_shiftNN (hW : Continuous W) (T : ℝ≥0) : Continuous (Sec7.shiftNN W T) :=
  (hW.comp (continuous_const.add continuous_id)).sub continuous_const

/-- **The launch trace is the shifted trace** (`[Yua22]`, Corollary 1.3, through `Zhan.isGeneratingTrace_shiftTip`). -/
theorem launchTr_eq_shiftTip (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) (σ : ℝ≥0) :
    launchTr T W σ = Zhan.shiftTip W T σ := by
  have hg := Zhan.isGeneratingTrace_shiftTip hγ hW.continuousOn hW0 (a := T) (u := σ + 1) ENNReal.coe_lt_top
  exact LP.traceAt_eq_of_isGeneratingTrace hg (continuous_shiftNN hW T).continuousOn (Sec7.shiftNN_zero W T)
    (ENNReal.coe_lt_coe.2 (lt_add_one σ))

/-- **The launch trace is continuous.** -/
theorem continuous_launchTr (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) :
    Continuous (launchTr T W) := by
  rw [show launchTr T W = Zhan.shiftTip W T from funext (launchTr_eq_shiftTip hγ hW hW0)]
  refine continuous_iff_continuousAt.2 fun σ => ?_
  have hg := Zhan.isGeneratingTrace_shiftTip hγ hW.continuousOn hW0 (a := T) (u := σ + 1) ENNReal.coe_lt_top
  have hσ : (σ : ℝ≥0∞) < ((σ + 1 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 (lt_add_one σ)
  exact hg.2.1.continuousAt (mem_of_superset ((isOpen_lt_life _).mem_nhds hσ)
    fun t (ht : (t : ℝ≥0∞) < ((σ + 1 : ℝ≥0) : ℝ≥0∞)) => (le_of_lt ht : (t : ℝ≥0∞) ≤ ((σ + 1 : ℝ≥0) : ℝ≥0∞)))

theorem continuous_launchDist (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) :
    Continuous (launchDist κ θ B T W) :=
  (continuous_badDist (B W)).comp (continuous_launchTr hγ hW hW0)

end Trace

/-! ### The inverse clock -/

/-- **The inverse of a continuous strictly increasing clock is continuous** before the life. -/
theorem continuousOn_invClock {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    {ψ : ℝ≥0 → ℝ≥0} (hψ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (ψ t : ℝ≥0∞) < Tc ∧ a (ψ t) = t) :
    ContinuousOn ψ {t | (t : ℝ≥0∞) < L} := by
  intro t₀ ht₀
  refine ContinuousAt.continuousWithinAt ?_
  refine StrictMonoOn.continuousAt_of_image_mem_nhds (s := {t : ℝ≥0 | (t : ℝ≥0∞) < L}) ?_
    ((isOpen_lt_life L).mem_nhds ht₀) ?_
  · intro t₁ h₁ t₂ h₂ h12
    by_contra hle
    have h := ham.monotoneOn (hψ t₂ h₂).1 (hψ t₁ h₁).1 (not_lt.1 hle)
    rw [(hψ t₁ h₁).2, (hψ t₂ h₂).2] at h
    exact absurd (NNReal.coe_le_coe.1 h) (not_le.2 h12)
  · refine mem_of_superset ((isOpen_lt_life Tc).mem_nhds (hψ t₀ ht₀).1) fun t' ht' => ?_
    have h0 := (haL t' ht').1
    have hL : (((a t').toNNReal : ℝ≥0) : ℝ≥0∞) < L := (haL t' ht').2
    refine ⟨(a t').toNNReal, hL, ham.injOn (hψ _ hL).1 ht' ?_⟩
    rw [(hψ _ hL).2, Real.coe_toNNReal _ h0]

/-! ### The gauge along one sample -/

section Sample

variable {s : ℝ≥0} {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- **The gauge along one sample of relative coordinates.** With `t'` the physical time of the relative time `t`
before the life, the gauge is the normalized launch distance at the own time `min cap (t' − T)`. -/
theorem launchGauge_eq (hBc : ∀ w : ℝ≥0 → ℝ, (∀ u ≤ T, w u = W u) → B w = B W)
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ReadD.physicalTrace s (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => ReadD.physicalTrace s u p) {u | (u : ℝ≥0∞) < L})
    (hrule : ∀ Δ : ℝ≥0, (Δ : ℝ≥0∞) < Tc → timeCapRule s Δ p = ENNReal.ofReal (a Δ))
    (hruleL : ∀ Δ : ℝ≥0, ¬ (Δ : ℝ≥0∞) < Tc → L ≤ timeCapRule s Δ p)
    {t t' : ℝ≥0} (htL : (t : ℝ≥0∞) < L) (ht' : (t' : ℝ≥0∞) < Tc) (hat : a t' = t) :
    launchGauge κ θ B T cap s t p =
      if launchStart κ θ B W = 0 then 1 else min 1 (launchDist κ θ B T W (min cap (t' - T)) / launchStart κ θ B W) := by
  obtain ⟨r, w⟩ := p
  have hpT : physTimeR s t (frz t (r, w)) = t' := by
    rw [frz, physTimeR_freeze]
    exact physTimeR_eq ham hrule hruleL htL ht' hat
  have hown : ownTimeR T cap s t (frz t (r, w)) = min cap (t' - T) := by
    rw [ownTimeR, hpT, ENNReal.toNNReal_coe]
  -- the physical driver of the frozen path is the explored driver up to `t'`
  have hdrv : ∀ u ≤ t', physDrvR s (frz t (r, w)) u = W u := by
    intro u hu
    have hut : (u : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 hu).trans_lt ht'
    rw [frz, physDrvR_freeze s r w t fun ρ hρ => ?_]
    · exact physDrvR_eq hγ hW hW0 haL hread hXc hrule hut
    · have hρt : (ρ : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 (hρ.trans hu)).trans_lt ht'
      rw [hrule ρ hρt, ← ENNReal.ofReal_coe_nnreal, ← hat]
      exact ENNReal.ofReal_le_ofReal (ham.monotoneOn hρt ht' (hρ.trans hu))
  unfold launchGauge
  rw [hown]
  by_cases hT : T ≤ t'
  · have hBe : B (physDrvR s (frz t (r, w))) = B W := hBc _ fun u hu => hdrv u (hu.trans hT)
    have hst : launchStart κ θ B (physDrvR s (frz t (r, w))) = launchStart κ θ B W := by
      unfold launchStart; rw [hBe]
    have hσt : T + min cap (t' - T) ≤ t' := by
      calc T + min cap (t' - T) ≤ T + (t' - T) := add_le_add_right (min_le_right _ _) T
        _ = t' := add_tsub_cancel_of_le hT
    have hev : evalDn (launchDist κ θ B T (physDrvR s (frz t (r, w)))) (min cap (t' - T)) =
        launchDist κ θ B T W (min cap (t' - T)) := by
      rw [evalDn_congr (p' := launchDist κ θ B T W) fun σ hσ => ?_]
      · exact evalDn_eq_of_continuousWithinAt (continuous_launchDist hγ hW hW0).continuousWithinAt
      · unfold launchDist launchTr
        rw [hBe, LP.traceAt_congr (w' := Sec7.shiftNN W T) fun v hv => ?_]
        simp only [Sec7.shiftNN]
        rw [hdrv _ ((add_le_add_right (hv.trans hσ) T).trans hσt), hdrv _ (le_self_add.trans hσt)]
    have hnn : 0 ≤ launchDist κ θ B T W (min cap (t' - T)) := badDist_nonneg _ _
    unfold launchGaugeOf
    rw [hst, hev, max_eq_right hnn]
  · have h0 : t' - T = 0 := tsub_eq_zero_of_le (le_of_lt (not_le.1 hT))
    rw [h0, min_eq_right (zero_le (a := cap)), launchGaugeOf_zero, launchDist_zero]
    split_ifs with h
    · rfl
    · rw [div_self h, min_self]

end Sample

end InteractingSLE.Theorem14.GW2Rd
