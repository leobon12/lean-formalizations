/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataChart
import InteractingSLE.Spec.Restart.FCThresholdDriverAEMeas

/-!
# The glued-space fibre objects, III: the path facts of the restart code

Packet PROVE-AUX61-FIBDATA (piece (P) of `planning/handoffs/PROVE-AUX61-FIB.md`). For the fibre data the clearance is
read from the window `V` alone: **`clr V w = infDist w Vᶜ`** (continuous; positive exactly on an open `V` with nonempty
complement), so no boundary extension of the inverse chart is needed and the lifetime of the code is the exit time of
the capacity-time chart path from `V`.

* **`mem_goodTrace_of_fill`**: a code whose decoded path has the fillings of a continuous Loewner chain from `0` at
  every capacity time before its lifetime lies in `Aux61Fib.GoodTrace` (the decoded driver `FibCode.driver` is that
  driver before the lifetime, `Restart.FCPlumb.fcTraceDriver_eq`).
* **`pathGood_of_clr`**: `Aux61Fib.PathGood d s` for data with `d.ℓ = clr d.V`, from: `GoodTrace`, the path in `d.V`
  before the lifetime and out of it at a finite lifetime, interior points in `ℍ`, injectivity.
* **`IsPathSpec.pathGood_capPath`**: for a simple path `γ x` on `[0, U x]` (in `ℍ` at interior times) that stays in `V`
  before `U x` and leaves it at `U x`, the reading in capacity time (`capPath`, `capEnd`) satisfies all path facts;
  **`IsChartPathSpec.pathGood_rsCode`**: hence `PathGood d (rsCode …)` for the restart code.

Generic; nothing here uses Theorem 1.2/1.3 (R48).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61FibData

open Restart Aux61Fib

/-! ### The clearance of a window -/

/-- **The clearance of an open window**: the distance to its complement. -/
def clr (V : Set ℂ) (w : ℂ) : ℝ := infDist w Vᶜ

theorem continuous_clr (V : Set ℂ) : Continuous (clr V) := continuous_infDist_pt _

theorem clr_pos_iff {V : Set ℂ} (hV : IsOpen V) (hne : Vᶜ.Nonempty) {w : ℂ} : 0 < clr V w ↔ w ∈ V := by
  unfold clr
  rw [← hV.isClosed_compl.notMem_iff_infDist_pos hne]
  simp

theorem clr_eq_zero_of_notMem {V : Set ℂ} {w : ℂ} (hw : w ∉ V) : clr V w = 0 :=
  infDist_zero_of_mem hw

/-! ### Generating traces of codes -/

/-- **A code whose path has the fillings of a continuous Loewner chain is a good trace**: if a continuous `W` with
`W 0 = 0` has hull `fill(trace[0, u])` at every capacity time `u` before the lifetime, the decoded driver generates
the decoded path through the lifetime. -/
theorem mem_goodTrace_of_fill {s : FibCode} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hfill : ∀ u : ℝ≥0, (u : ℝ≥0∞) < s.life →
      QuantumZipper.fwdHull W u = fillH (FibCode.trace s '' Icc 0 u)) : s ∈ GoodTrace := by
  set w : ℝ≥0 → ℝ := fun t => W t with hw
  have hwc : Continuous w := hW.comp NNReal.continuous_coe
  have hw0 : w 0 = 0 := by simp [hw, hW0]
  have hgen : IsGeneratingTrace w s.life (FibCode.trace s) := by
    refine ⟨FibCode.trace_zero s, (FibCode.continuous_trace s).continuousOn, fun t ht => ?_⟩
    have hK : QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t = QuantumZipper.fwdHull W t :=
      YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hwc.comp continuous_real_toNNReal) hW (NNReal.coe_nonneg t)
        fun r hr => by simp [hw, Real.coe_toNNReal r hr.1]
    rw [hK, hfill t ht]
    exact isFilling_fillH (isCompact_Icc.image (FibCode.continuous_trace s))
  show IsGeneratingTrace (FibCode.driver · s) s.life (FibCode.trace s)
  refine ⟨FibCode.trace_zero s, (FibCode.continuous_trace s).continuousOn, fun t ht => ?_⟩
  have hK : QuantumZipper.fwdHull (fun r : ℝ => FibCode.driver r.toNNReal s) t = QuantumZipper.fwdHull W t := by
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ((FibCode.continuous_driver s).comp continuous_real_toNNReal) hW
      (NNReal.coe_nonneg t) fun r hr => ?_
    have hq : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < s.life :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht
    have he : FibCode.driver r.toNNReal s = w r.toNNReal :=
      FCPlumb.fcTraceDriver_eq (Γ := FibCode.trace) (U := FibCode.life) hwc hw0 hgen hq
    show FibCode.driver r.toNNReal s = W r
    rw [he]
    simp [hw, Real.coe_toNNReal r hr.1]
  rw [hK, hfill t ht]
  exact isFilling_fillH (isCompact_Icc.image (FibCode.continuous_trace s))

/-- **The path facts from the clearance of the window**: for data whose clearance is that of its (open, bounded away
from `ℂ`) window, a good trace that stays in the window before its lifetime, leaves it at a finite lifetime, is interior
at positive times before the lifetime and injective satisfies `PathGood`. -/
theorem pathGood_of_clr (d : FibData) (hℓ : d.ℓ = clr d.V) (hV : IsOpen d.V) (hne : d.Vᶜ.Nonempty)
    {s : FibCode} (hgood : s ∈ GoodTrace)
    (hin : ∀ t : ℝ≥0, (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ d.V)
    (hout : ∀ T : ℝ≥0, (T : ℝ≥0∞) = s.life → FibCode.trace s T ∉ d.V)
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → FibCode.trace s t ∈ H)
    (hinj : InjOn (FibCode.trace s) {t | (t : ℝ≥0∞) ≤ s.life}) : PathGood d s := by
  refine ⟨hgood, fun t ht => ?_, fun T hT => ?_, ?_, hH, hinj⟩
  · rw [hℓ]; exact (clr_pos_iff hV hne).2 (hin t ht)
  · rw [hℓ, clr_eq_zero_of_notMem (hout T hT)]
  · unfold RLC.exitTime
    refine (min_eq_left ?_).symm
    refine le_iInf₂ fun r hr => ?_
    by_contra hlt
    exact hr (hin r (lt_of_not_ge hlt))

/-! ### The capacity-time reading of a simple path -/

namespace IsPathSpec

variable {X : Type*} [MeasurableSpace X] {E : Set X} {γ : X → ℝ≥0 → ℂ} {U : X → ℝ≥0}
  (hs : IsPathSpec E γ U) (hclk : ∀ x ∈ E, IsClockOn (chartClock (γ x)) (U x))
include hs hclk

/-- The image of an initial capacity-time interval is the image of the corresponding original-time interval. -/
theorem image_capPath_Icc {x : X} (hx : x ∈ E) {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capEnd E γ U x) :
    capPath E γ U x '' Icc 0 u = γ x '' Icc 0 (invClock (capClock E γ U x) (U x) u) := by
  have ha := hs.isClockOn_capClock hclk hx
  have hcapL := capEnd_eq_capLife (γ := γ) (U := U) hx
  obtain ⟨hU, -, -⟩ := hs.capPath_spec hclk hx hu
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hvu : (v : ℝ≥0∞) ≤ capEnd E γ U x := (ENNReal.coe_le_coe.2 hv.2).trans hu
    obtain ⟨-, -, hve⟩ := hs.capPath_spec hclk hx hvu
    refine ⟨_, ⟨zero_le, ?_⟩, hve.symm⟩
    rw [hcapL] at hu hvu
    exact ha.strictMonoOn_invClock.monotoneOn hvu hu hv.2
  · rintro _ ⟨r, hr, rfl⟩
    have hrU : r ≤ U x := hr.2.trans hU
    have hr' : (r : ℝ≥0∞) ≤ (U x : ℝ≥0∞) := ENNReal.coe_le_coe.2 hrU
    set v := (capClock E γ U x r).toNNReal with hv
    have hvc : (v : ℝ≥0∞) ≤ capLife (capClock E γ U x) (U x : ℝ≥0∞) := ha.coe_toNNReal_le_capLife hr'
    have hinv : invClock (capClock E γ U x) (U x) v = r := ha.invClock_apply hr'
    rw [← hcapL] at hvc
    refine ⟨v, ⟨zero_le, ?_⟩, ?_⟩
    · have hmono := ha.strictMonoOn.monotoneOn hr' (ENNReal.coe_le_coe.2 hU) hr.2
      have hz := (hs.capPath_spec hclk hx hu).2.1
      rw [← hs.capClock_eq_chartClock hx hU] at hz
      rw [hz] at hmono
      rw [hv]
      exact Real.toNNReal_le_iff_le_coe.2 hmono
    · rw [(hs.capPath_spec hclk hx hvc).2.2, hinv]

/-- **The capacity-time reading of a simple path has all path facts**: for a path `γ x` on `[0, U x]` that is
injective, in `ℍ` at times in `(0, U x)`, in `ℍ̄` at `U x`, inside the open window `V` before `U x` and outside it at
`U x`, every code decoding to `capPath x` on `[0, capEnd x]` with lifetime `capEnd x` satisfies `PathGood d` for data
with `d.V = V` and `d.ℓ = clr V`. -/
theorem pathGood_capPath {x : X} (hx : x ∈ E) (hi : InjOn (γ x) (Iic (U x)))
    (hH : ∀ r : ℝ≥0, 0 < r → r < U x → γ x r ∈ H) (hUH : γ x (U x) ∈ Hbar)
    (d : FibData) (hℓ : d.ℓ = clr d.V) (hV : IsOpen d.V) (hne : d.Vᶜ.Nonempty)
    (hin : ∀ r : ℝ≥0, r < U x → γ x r ∈ d.V) (hout : γ x (U x) ∉ d.V)
    {s : FibCode} (hlife : s.life = capEnd E γ U x)
    (htr : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ capEnd E γ U x → FibCode.trace s u = capPath E γ U x u) : PathGood d s := by
  have ha := hs.isClockOn_capClock hclk hx
  have hcapL := capEnd_eq_capLife (γ := γ) (U := U) hx
  obtain ⟨-, W, hW, hW0, hWK⟩ := isClockOn_chartClock_of_injOn (hs.cont x hx) hi (hs.zero x hx) hH hUH
  -- the original time of a capacity time, and strict monotonicity
  have hspec := fun {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capEnd E γ U x) => hs.capPath_spec hclk hx hu
  have hlt : ∀ {u : ℝ≥0}, (u : ℝ≥0∞) < capEnd E γ U x → invClock (capClock E γ U x) (U x) u < U x := by
    intro u hu
    obtain ⟨hU, -, -⟩ := hspec hu.le
    refine lt_of_le_of_ne hU fun heq => ?_
    have h1 := (hspec hu.le).2.1
    rw [heq, ← hs.capClock_eq_chartClock hx le_rfl] at h1
    have h2 : capEnd E γ U x = ENNReal.ofReal (capClock E γ U x (U x)) := by simp [capEnd, hx]
    rw [h2, h1] at hu
    simp at hu
  have hpos : ∀ {u : ℝ≥0}, (u : ℝ≥0∞) ≤ capEnd E γ U x → 0 < u → 0 < invClock (capClock E γ U x) (U x) u := by
    intro u hu hu0
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h1 := (hspec hu).2.1
    rw [h0, ← hs.capClock_eq_chartClock hx zero_le, ha.zero] at h1
    exact hu0.ne' (by exact_mod_cast h1.symm)
  have hgood : s ∈ GoodTrace := by
    refine mem_goodTrace_of_fill hW hW0 fun u hu => ?_
    rw [hlife] at hu
    have hu' := hu.le
    obtain ⟨hU, hcl, -⟩ := hspec hu'
    obtain ⟨-, hK⟩ := hWK _ hU
    rw [hcl] at hK
    rw [hK, ← hs.image_capPath_Icc hclk hx hu']
    congr 1
    exact image_congr fun v hv => (htr v ((ENNReal.coe_le_coe.2 hv.2).trans hu')).symm
  refine pathGood_of_clr d hℓ hV hne hgood (fun t ht => ?_) (fun T hT => ?_) (fun t ht0 ht => ?_) ?_
  · rw [hlife] at ht
    rw [htr t ht.le, (hspec ht.le).2.2]
    exact hin _ (hlt ht)
  · rw [hlife] at hT
    obtain ⟨hU, hcl, he⟩ := hspec hT.le
    rw [htr T hT.le, he]
    -- the original time of the capacity lifetime is `U x`
    have hTU : invClock (capClock E γ U x) (U x) T = U x := by
      refine ha.strictMonoOn.injOn (ENNReal.coe_le_coe.2 hU) (show ((U x : ℝ≥0) : ℝ≥0∞) ≤ (U x : ℝ≥0∞) from le_rfl)
        ?_
      rw [hs.capClock_eq_chartClock hx hU, hcl]
      have h2 : capEnd E γ U x = ENNReal.ofReal (capClock E γ U x (U x)) := by simp [capEnd, hx]
      rw [h2] at hT
      have hnn : 0 ≤ capClock E γ U x (U x) := ha.nonneg le_rfl
      have := congrArg ENNReal.toReal hT
      rw [ENNReal.toReal_ofReal hnn] at this
      simpa using this
    rw [hTU]
    exact hout
  · rw [hlife] at ht
    rw [htr t ht.le, (hspec ht.le).2.2]
    exact hH _ (hpos ht.le ht0) (hlt ht)
  · intro u hu v hv huv
    have hu' : (u : ℝ≥0∞) ≤ capEnd E γ U x := hlife ▸ hu
    have hv' : (v : ℝ≥0∞) ≤ capEnd E γ U x := hlife ▸ hv
    rw [htr u hu', htr v hv', (hspec hu').2.2, (hspec hv').2.2] at huv
    have heq := hi (mem_Iic.2 (hspec hu').1) (mem_Iic.2 (hspec hv').1) huv
    rw [hcapL] at hu' hv'
    exact ha.strictMonoOn_invClock.injOn hu' hv' heq

end IsPathSpec

/-! ### The restart code -/

namespace IsChartPathSpec

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {U : X → ℝ≥0}
  (hs : IsChartPathSpec E c ρ U) (hclk : ∀ x ∈ E, IsClockOn (chartClock (chartPath E c ρ U x)) (U x))
include hs hclk

/-- **The path facts of the restart code**: if the chart path is simple on `[0, U x]`, interior before `U x`, and
exits the window `V = d.V` exactly at `U x`, the restart code satisfies `PathGood d`. -/
theorem pathGood_rsCode {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens} {x : X} (hx : x ∈ E)
    (hi : InjOn (chartPath E c ρ U x) (Iic (U x)))
    (hH : ∀ r : ℝ≥0, 0 < r → r < U x → chartPath E c ρ U x r ∈ H) (hUH : chartPath E c ρ U x (U x) ∈ Hbar)
    (d : FibData) (hℓ : d.ℓ = clr d.V) (hV : IsOpen d.V) (hne : d.Vᶜ.Nonempty)
    (hin : ∀ r : ℝ≥0, r < U x → chartPath E c ρ U x r ∈ d.V) (hout : chartPath E c ρ U x (U x) ∉ d.V) :
    PathGood d (rsCode E c ρ U a k h x) :=
  hs.isPathSpec.pathGood_capPath hclk hx hi hH hUH d hℓ hV hne hin hout (rsCode_life x)
    fun _ hu => rsCode_trace hs hclk x hu

end IsChartPathSpec

end InteractingSLE.Sec5.Aux61FibData
