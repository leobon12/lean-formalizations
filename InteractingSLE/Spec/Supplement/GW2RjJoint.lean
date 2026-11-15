/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Tip
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift
import InteractingSLE.Spec.Supplement.GW2GmJ32Data

/-!
# J32's tip is the dilated stage-1 trace of any driver matching its capacity reader (decision D33)

PROVE-GW2-ROOTX round 9, deterministic. GEOM2's `Gm.jointTip_spec` reads J32's tip through the trace of the frozen
capacity driver mapped out at the root's entry. Here the same reading for ANY driver `V` with a generating trace beyond
a level `σ` that agrees with J32's capacity reader on `[0, σ]` (for instance a root-`x` version below its cap):

* **`stage1_spec`**: the frozen driver mapped out at `A₀` is continuous, starts at `0`, and has the global Loewner trace
  `Gm.jointShiftTip V σ A₀`; it is `V(A₀ + ·) − V(A₀)` up to `σ − A₀`;
* **`jointTipRead_eq`**: `RootJ32.jointTipRead k x s L v₀ u p = k · jointShiftTip V σ A₀ (u/k²)` below `σ`;
* **`jointShiftTip_mem_H_of_sourceTip`**: a J32 tip in `ℍ` (the test's clause `γ q ∈ ℍ`) puts the stage-1 trace in `ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist.StagedLaw GW2TipSystem

variable {V : ℝ≥0 → ℝ} {B : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The stage-1 chain of a generating driver**: continuous, from `0`, with the global trace `jointShiftTip`. -/
theorem stage1_spec (hη : IsGeneratingTrace V B η) (hV : ContinuousOn V {t | (t : ℝ≥0∞) < B}) (hV0 : V 0 = 0)
    {σ : ℝ≥0} (hσB : (σ : ℝ≥0∞) < B) (A₀ : ℝ≥0) :
    Continuous (shiftDrive (Gm.frozenReal V σ) A₀) ∧ shiftDrive (Gm.frozenReal V σ) A₀ 0 = 0 ∧
      IsLoewnerTrace (shiftDrive (Gm.frozenReal V σ) A₀) (Gm.jointShiftTip V σ A₀) := by
  have hVσ : ContinuousOn V (Icc 0 σ) := hV.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans_lt hσB
  obtain ⟨η', hη', -⟩ := Gm.exists_isGeneratingTrace_frozen hVσ hV0 (hη.mono_horizon hσB.le)
  have hWc := Gm.continuous_frozenReal hVσ
  have hW0 : Gm.frozenReal V σ 0 = 0 := by simp [Gm.frozenReal, hV0]
  have hL : IsLoewnerTrace (Gm.frozenReal V σ) (fun r : ℝ => η' r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace hη'
  exact ⟨QuantumZipper.RS.continuous_shiftDrive hWc _, QuantumZipper.RS.shiftDrive_zero _ _,
    hL.isLoewnerTrace_shift hWc hW0 A₀.coe_nonneg⟩

/-- The stage-1 driver is the increment of `V` after `A₀`, below the freezing level. -/
theorem shiftDrive_frozenReal_eq {σ A₀ : ℝ≥0} (hA₀ : A₀ ≤ σ) {t : ℝ} (ht : 0 ≤ t) (htσ : (A₀ : ℝ) + t ≤ σ) :
    shiftDrive (Gm.frozenReal V σ) A₀ t = V (A₀ + t.toNNReal) - V A₀ := by
  have h1 : ((A₀ : ℝ) + t).toNNReal = A₀ + t.toNNReal := by
    have : (A₀ : ℝ) + t = ((A₀ + t.toNNReal : ℝ≥0) : ℝ) := by rw [NNReal.coe_add, Real.coe_toNNReal _ ht]
    rw [this, Real.toNNReal_coe]
  have h2 : A₀ + t.toNNReal ≤ σ := by
    rw [← h1]
    exact Real.toNNReal_le_iff_le_coe.2 htσ
  show V (min ((A₀ : ℝ) + t).toNNReal σ) - V (min (A₀ : ℝ).toNNReal σ) = _
  rw [h1, Real.toNNReal_coe, min_eq_left h2, min_eq_left hA₀]

/-- **J32's tip below the level `σ`**, for any driver `V` agreeing with J32's capacity reader on `[0, σ]`. -/
theorem jointTipRead_eq (hη : IsGeneratingTrace V B η) (hV : ContinuousOn V {t | (t : ℝ≥0∞) < B}) (hV0 : V 0 = 0)
    {σ : ℝ≥0} (hσB : (σ : ℝ≥0∞) < B) {k : ℝ≥0} (hk : 0 < k) {x : ℝ} {s L v₀ : ℝ≥0}
    {p : RecData × RecData} (hA₀σ : (RootH29.forwardCapacity x s v₀ p).toNNReal < σ)
    (hread : ∀ c : ℝ≥0, c ≤ σ → RootJ32.capacityDriverRead x s L c p = V c) {u : ℝ≥0}
    (hu : (RootH29.forwardCapacity x s v₀ p).toNNReal + u / k ^ 2 < σ) :
    RootJ32.jointTipRead k x s L v₀ u p =
      ((k : ℝ) : ℂ) * Gm.jointShiftTip V σ (RootH29.forwardCapacity x s v₀ p).toNNReal ((u / k ^ 2 : ℝ≥0) : ℝ) := by
  set A₀ := (RootH29.forwardCapacity x s v₀ p).toNNReal with hA₀def
  obtain ⟨hψc, htr, -⟩ := Gm.exists_jointShiftTip hη hV hV0 hσB hA₀σ hk
  have hJt : ∀ u' : ℝ≥0, A₀ + u' / k ^ 2 ≤ σ → ∀ r ≤ u',
      RootJ32.jointDriverRead k x s L v₀ p r = k * (V (A₀ + r / k ^ 2) - V A₀) := by
    intro u' hu' r hr
    have hr'' : A₀ + r / k ^ 2 ≤ σ :=
      le_trans ((add_le_add_iff_left A₀).2 (div_le_div_of_nonneg_right hr zero_le)) hu'
    show (1 : ℝ) * (k : ℝ) * (RootJ32.capacityDriverRead x s L (A₀ + r / k ^ 2) p -
      RootJ32.capacityDriverRead x s L A₀ p) = _
    rw [one_mul, hread _ hr'', hread _ hA₀σ.le]
  have htrace : ∀ u' : ℝ≥0, A₀ + u' / k ^ 2 ≤ σ →
      LP.traceAt u' (RootJ32.jointDriverRead k x s L v₀ p) =
        ((k : ℝ) : ℂ) * Gm.jointShiftTip V σ A₀ ((u' / k ^ 2 : ℝ≥0) : ℝ) :=
    fun u' hu' => htr _ u' hu' (hJt u' hu')
  have hψk : Continuous fun u' : ℝ≥0 => ((k : ℝ) : ℂ) * Gm.jointShiftTip V σ A₀ ((u' / k ^ 2 : ℝ≥0) : ℝ) :=
    continuous_const.mul (hψc.comp (continuous_id.div_const _))
  have hcont : ContinuousAt (fun u' => LP.traceAt u' (RootJ32.jointDriverRead k x s L v₀ p)) u := by
    have hev : ∀ᶠ u' in 𝓝 u, A₀ + u' / k ^ 2 < σ :=
      ((continuous_const.add (continuous_id.div_const _)).continuousAt (x := u)).eventually (gt_mem_nhds hu)
    refine (hψk.continuousAt (x := u)).congr ?_
    filter_upwards [hev] with u' hu'
    exact (htrace u' hu'.le).symm
  unfold RootJ32.jointTipRead RootJ32.jointTraceRead
  rw [Gm.drivingTrace_top_snd, Gm.endVal_eq_of_continuousAt hcont]
  exact htrace _ hu.le

/-- Orientation preserves `ℍ`. -/
theorem orientTip_mem_H_iff (n : ℕ) (z : ℂ) : RootJ31.orientTip n z ∈ H ↔ z ∈ H := by
  classical
  unfold RootJ31.orientTip
  by_cases hn : Even n
  · simp only [hn, ↓reduceIte]
  · simp only [hn, ↓reduceIte]
    change 0 < (-(starRingEnd ℂ) z).im ↔ 0 < z.im
    simp

/-- **A J32 tip in `ℍ` puts the stage-1 trace in `ℍ`.** -/
theorem jointShiftTip_mem_H_of_jointTipRead (hη : IsGeneratingTrace V B η)
    (hV : ContinuousOn V {t | (t : ℝ≥0∞) < B}) (hV0 : V 0 = 0) {σ : ℝ≥0} (hσB : (σ : ℝ≥0∞) < B) {k : ℝ≥0}
    (hk : 0 < k) {x : ℝ} {s L v₀ : ℝ≥0} {p : RecData × RecData}
    (hA₀σ : (RootH29.forwardCapacity x s v₀ p).toNNReal < σ)
    (hread : ∀ c : ℝ≥0, c ≤ σ → RootJ32.capacityDriverRead x s L c p = V c) {u : ℝ≥0}
    (hu : (RootH29.forwardCapacity x s v₀ p).toNNReal + u / k ^ 2 < σ) (n : ℕ)
    (htip : RootJ31.orientTip n (RootJ32.jointTipRead k x s L v₀ u p) ∈ H) :
    Gm.jointShiftTip V σ (RootH29.forwardCapacity x s v₀ p).toNNReal ((u / k ^ 2 : ℝ≥0) : ℝ) ∈ H := by
  rw [orientTip_mem_H_iff, jointTipRead_eq hη hV hV0 hσB hk hA₀σ hread hu] at htip
  change 0 < (((k : ℝ) : ℂ) * _).im at htip
  rw [Complex.im_ofReal_mul] at htip
  exact pos_of_mul_pos_right htip (NNReal.coe_nonneg k)

end InteractingSLE.Theorem14.GW2Rj
