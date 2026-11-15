/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QwHull
import InteractingSLE.Spec.Supplement.SB2QtChart
import InteractingSLE.Spec.Supplement.SB2MxChart
import InteractingSLE.Spec.Supplement.SB2MuShift
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Supplement.WalkIntFillChart
import InteractingSLE.Spec.Supplement.WalkIntCanonChart
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun

/-!
# The field after a piece, read in the hull chart of the new retained hull (step `ℓ → ℓ + 2`)

Packet REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8). Let `Y'` be the field read in the canonical
hull chart `Mo.hullChart K x₀` of a hull `K` (the chart of B's stage `ℓ`, offset at the seed). Let `e` be a regular
driver with finite lifetime and a good record `r = recOf ⊤ e` (the relative driver of B's piece `ℓ`; the first
conjunct of the single-stage law `IsStopLaw` makes the record good). Then the record field `recField κ r Y'` (the law
of `IsStopLaw`), shifted by `x₀ + W_T`, is the field read in the canonical hull chart (offset `0`) of the hull
`X = K ∪ c⁻¹(K_T)` (the old hull and the pull-back of the relative hull at the lifetime):

* `exists_model`: a normalized hull model of a chart agreeing with `Mo.hullChart K x₀` on `ℍ ∖ K` (forward map, lift),
  with inverse equal on `ℍ`;
* `recDrv`, `continuous_recDrv`, `recDrv_zero`: the record driver as a function on `ℝ`;
* **`isChartTransport_hullChart_recField`**;
* **`hull_eq_of_cofinal`**: the terminal hull identity of `SB2QwHull` in the hull chart's terms
  (`X_s = K ∪ (Mo.hullChart K x₀)⁻¹(K_s)`), and `isHPHull_stepHull`, `hcapSet_stepHull`.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.Qw

open WalkIntCanon Exist Exist.Staged Exist.StagedLaw

/-- **A normalized hull model of the canonical hull chart**: a chart agreeing with `Mo.hullChart K x₀` on `ℍ ∖ K`
(forward map and lift) and on `ℍ` (inverse), normalized, with a hull model of hull `K` and shift `x₀`. -/
theorem exists_model {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) :
    ∃ (c : Chart) (M : HullModel c), IsNormalized c ∧ M.hull = K ∧ M.shift = x₀ ∧
      IsDomainChart (H \ K) c ∧ EqOn c.1 (Mo.hullChart K x₀).1 (H \ K) ∧
      EqOn c.2.2 (Mo.hullChart K x₀).2.2 (H \ K) ∧ EqOn c.2.1 (Mo.hullChart K x₀).2.1 H := by
  obtain ⟨c₀, M₀, hn₀, hM₀⟩ := WalkIntFill.exists_normalized_hullChart hK
  set a : ℝ := x₀ - M₀.shift with ha
  have hn := hn₀.recenter a
  set M := M₀.recenter a with hMdef
  have hMh : M.hull = K := hM₀
  have hMs : M.shift = x₀ := by
    change M₀.shift + a = x₀
    rw [ha]; ring
  have hdom : ((c₀.recenter a).dom : Set ℂ) = H \ K := by rw [← hMh]; exact M.dom_eq
  have hΦ : IsDomainChart (H \ K) (c₀.recenter a) := by
    obtain ⟨L, hL, hlift⟩ := hn.derivLift
    refine ⟨hn.conformal, ?_, L, ?_, fun z hz => hlift z ?_⟩
    · rw [← hn.conformal.coe_dom]; exact hdom
    · rw [← hdom]; exact hL
    · rw [hdom]; exact hz
  have hΨ := Mo.isDomainChart_hullChart hK x₀
  have hfwd : EqOn (c₀.recenter a).1 (Mo.hullChart K x₀).1 (H \ K) := by
    intro z hz
    have hmo := (ConformalImage.isMapOut_mapOut hK).eqOn hK (hM₀ ▸ M₀.mapOut) hz
    change c₀.1 z - (a : ℂ) = ConformalImage.mapOut K z - (x₀ : ℂ)
    have hmo' : ConformalImage.mapOut K z = c₀.1 z + (M₀.shift : ℂ) := hmo
    rw [hmo', ha]
    push_cast
    ring
  have hlift : EqOn (c₀.recenter a).2.2 (Mo.hullChart K x₀).2.2 (H \ K) := by
    intro z hz
    have h1 := M₀.lift_eq_canonDerivLog hn₀ (show z ∈ H \ M₀.hull by rw [hM₀]; exact hz)
    change c₀.2.2 z = (Restart.canonDerivLog K z).im
    rw [h1, hM₀]
  have hinv : EqOn (c₀.recenter a).2.1 (Mo.hullChart K x₀).2.1 H := fun w hw => by
    have h1 := hΨ.inv_mem hw
    calc (c₀.recenter a).2.1 w = (c₀.recenter a).2.1 ((c₀.recenter a).1 ((Mo.hullChart K x₀).2.1 w)) := by
          rw [hfwd h1, hΨ.fwd_inv hw]
      _ = (Mo.hullChart K x₀).2.1 w := hΦ.inv_fwd h1
  exact ⟨c₀.recenter a, M, hn, hMh, hMs, hΦ, hfwd, hlift, hinv⟩

/-- The driver of a record as a function on `ℝ` (the driver of `recChart`). -/
def recDrv (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ → ℝ := fun x => (retOf ⊤ e).1 x.toNNReal

theorem continuous_recDrv {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf ⊤ e))) : Continuous (recDrv e) :=
  (continuous_retOf he hg).comp continuous_real_toNNReal

theorem recDrv_zero {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) : recDrv e 0 = 0 := by
  change e.1 (min ((Real.toNNReal 0 : ℝ≥0) : ℝ≥0∞) (min ⊤ e.2)).toNNReal = 0
  simp only [Real.toNNReal_zero, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
  exact he.2.1

/-- The hull after a step of the relative driver `W` for time `s`, read through the hull chart of `K`. -/
def stepHull (K : Set ℂ) (x₀ : ℝ) (W : ℝ → ℝ) (s : ℝ) : Set ℂ := K ∪ (Mo.hullChart K x₀).2.1 '' fwdHull W s

theorem stepHull_eq_model {K : Set ℂ} {x₀ : ℝ} {c : Chart} (M : HullModel c) (hn : IsNormalized c)
    (hMh : M.hull = K) (hinv : EqOn c.2.1 (Mo.hullChart K x₀).2.1 H) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) : stepHull K x₀ W s = (M.loewner hn hW hW0 hs).hull := by
  rw [loewner_hull, hMh, stepHull]
  congr 1
  exact image_congr fun z hz => (hinv ((isHPHull_fwdHull hW hs).1 hz)).symm

theorem isHPHull_stepHull {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) : IsHPHull (stepHull K x₀ W s) := by
  obtain ⟨c, M, hn, hMh, -, -, -, -, hinv⟩ := exists_model hK x₀
  rw [stepHull_eq_model M hn hMh hinv hW hW0 hs]
  exact (M.loewner hn hW hW0 hs).isHull

theorem hcapSet_stepHull {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    ConformalImage.hcapSet (stepHull K x₀ W s) = ConformalImage.hcapSet K + 2 * s := by
  obtain ⟨c, M, hn, hMh, -, -, -, -, hinv⟩ := exists_model hK x₀
  rw [stepHull_eq_model M hn hMh hinv hW hW0 hs, hcapSet_loewner_hull, hMh]

/-- **The terminal hull identity, in the hull chart's terms**: a hull `Z` with `K ⊆ Z ⊆ X_T`, containing `X_s` for a
cofinal set of times `s < T`, is `X_T`. -/
theorem hull_eq_of_cofinal {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {Z : Set ℂ} (hZ : IsHPHull Z) (hZT : Z ⊆ stepHull K x₀ W T) (hKZ : K ⊆ Z)
    (hcof : ∀ s : ℝ, 0 ≤ s → s < T → ∃ s' : ℝ, 0 ≤ s' ∧ s ≤ s' ∧ stepHull K x₀ W s' ⊆ Z) :
    Z = stepHull K x₀ W T := by
  obtain ⟨c, M, hn, hMh, -, -, -, -, hinv⟩ := exists_model hK x₀
  rw [stepHull_eq_model M hn hMh hinv hW hW0 hT] at hZT ⊢
  refine loewner_hull_eq_of_cofinal M hn hW hW0 hT hZ hZT (hMh ▸ hKZ) fun s hs hsT => ?_
  obtain ⟨s', hs', hss', hsub⟩ := hcof s hs hsT
  exact ⟨s', hs', hss', by rwa [← stepHull_eq_model M hn hMh hinv hW hW0 hs']⟩

/-- **The field after the piece in the new hull chart**: if `Y'` is `h` read in `Mo.hullChart K x₀` and the record of
the regular driver `e` (finite lifetime) is good, then the record field of `Y'`, shifted by `x₀ + W_T`, is `h` read in
`Mo.hullChart (K ∪ c⁻¹(K_T)) 0`, where `W` is the record driver and `T` the lifetime. -/
theorem isChartTransport_hullChart_recField {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {κ : ℝ}
    {h Y' : DistOn upperHalfPlaneOpens} (hY : IsChartTransport (Mo.hullChart K x₀) 1 0 (chiC κ) h Y')
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf ⊤ e))) :
    IsChartTransport (Mo.hullChart (stepHull K x₀ (recDrv e) (e.2.toNNReal : ℝ)) 0) 1 0 (chiC κ) h
      (flowField (-(x₀ + recDrv e (e.2.toNNReal : ℝ))) 0 (recField κ (recOf ⊤ e) Y')) := by
  obtain ⟨c, M, hn, hMh, hMs, hΦ, hfwd, hlift, hinv⟩ := exists_model hK x₀
  have hΨ := Mo.isDomainChart_hullChart hK x₀
  have ht₁ : IsChartTransport c 1 0 (chiC κ) h Y' := Mx.isChartTransport_of_eqOn_domain hΦ hΨ hfwd hlift hY
  have hWc := continuous_recDrv he hg
  have hW0 := recDrv_zero he
  have hT : (0 : ℝ) ≤ (e.2.toNNReal : ℝ) := NNReal.coe_nonneg _
  have hrc : recChart (recOf ⊤ e) = Chart.id.loewner (recDrv e) (e.2.toNNReal : ℝ) := by
    rw [recChart_eq_loewner he hg, min_eq_right le_top]
    rfl
  have hℓ₁ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H := by
    refine (Mu.continuousOn_lift_inv_hullChart hK x₀).congr fun w hw => ?_
    have hm := hΨ.inv_mem hw
    rw [hinv hw]
    exact hlift hm
  have ht₂ : IsChartTransport (recChart (recOf ⊤ e)) 1 0 (1 * chiC κ) Y' (recField κ (recOf ⊤ e) Y') := by
    rw [one_mul]; exact isChartTransport_recField κ _ Y'
  have hcomp := GW2JointKernel.isChartTransport_trans_sign hn.conformal (isConformal_recChart _) hℓ₁
    (continuousOn_recChart_lift _) ht₁ ht₂
  have hℓc := GW2JointKernel.continuousOn_trans_lift hn.conformal (isConformal_recChart (recOf ⊤ e)) hℓ₁
    (continuousOn_recChart_lift _)
  rw [hrc, ← Chart.loewner_eq_trans] at hcomp hℓc
  simp only [mul_one, mul_zero, add_zero, one_mul] at hcomp
  have hN := hn.loewner hWc hW0 hT
  have hfin := Qt.isChartTransport_hullChart_of_hullModel hN.conformal hN (M.loewner hn hWc hW0 hT) hℓc hcomp
  rw [← stepHull_eq_model M hn hMh hinv hWc hW0 hT] at hfin
  convert hfin using 3
  change x₀ + recDrv e _ = M.shift + recDrv e _
  rw [hMs]

end InteractingSLE.Theorem14.SB.Qw
