/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aChainWire
import InteractingSLE.Spec.Supplement.GW4LeafPiece
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Compare
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullEnd

/-!
# BR4a's infinite relative capacity: the deterministic core

Packet PROVE-T14-BR4A3. Supplement p. 610, Corollary BR4 and BR4a: "If its relative capacity had a finite limit, the
admissible integrated law and nonexplosion would bound the relative driver and hulls through that limit. But continuity
of the original prefix at its hit of `z` makes its image under `ψ` approach infinity. This contradiction gives infinite
relative capacity."

One sample, in Zhan's normalized coordinates (target `x_k > 0`, map `ψ(z) = z/(x_k − z)`): a continuous driver `w` from
`0` with a complete generating trace `γ` that reaches `x_k` at `T₀`, the target outside the earlier closed hulls. If a
continuous trace `η_c` generates a driver `w_c` on `[0, ζ_c]` and `w_c` is Zhan's retargeted driver before the new
horizon `T̃ ≤ ζ_c`, then `T̃ = ∞`: otherwise `η_c` generates the retargeted chain through `T̃` (closed interval), and
Zhan's pull-back (`PullData.isGeneratingTrace_of_lt_top`) ends the original trace at `T₀` at `ψ⁻¹(η_c(T̃)) ≠ x_k`.

* `targetChangeInv_ne_self`, `exists_fwdHull_subset_closedBall`;
* **`newHorizon_eq_top_of_code`**: the contradiction above;
* `clock_unbounded_of_newHorizon`: an infinite new horizon of BR4a's oriented target change makes `clock v` unbounded
  before the first visit (the converse half of `BR4aChain.relDrv_spec`'s clock computation);
* **`clock_unbounded_of_oriented`**: BR4a's clock statement for one sample, from the new-horizon statement for the
  oriented driver (`BR4aChain.oDrv`) at every time at which the oriented trace reaches `|v|⁻¹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open Zhan.Retarget MartChar.RealFlow BR4aChain

/-- `ψ⁻¹(y) = x_k y/(1 + y)` never equals `x_k` (with Lean's `x/0 = 0` at `y = −1`). -/
theorem targetChangeInv_ne_self {xk : ℝ} (hxk : 0 < xk) (y : ℂ) : Sec7.targetChangeInv xk y ≠ xk := by
  intro h
  unfold Sec7.targetChangeInv at h
  have hxk' : (xk : ℂ) ≠ 0 := by exact_mod_cast hxk.ne'
  by_cases hy : (1 : ℂ) + y = 0
  · rw [hy, div_zero] at h
    exact hxk' h.symm
  · rw [div_eq_iff hy] at h
    apply hxk'
    linear_combination -h

/-- The hulls of a continuous driver before a finite time lie in one closed ball. -/
theorem exists_fwdHull_subset_closedBall {w : ℝ≥0 → ℝ} (hw : Continuous w) (T₀ : ℝ≥0) :
    ∃ R : ℝ, ∀ S : ℝ≥0, (S : ℝ≥0∞) < T₀ → fwdHull (fun s : ℝ => w s.toNNReal) S ⊆ closedBall 0 R := by
  have hwc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hwc (T₀ : ℝ)).subset_closedBall 0
  refine ⟨R, fun S hS => ?_⟩
  have hST : (S : ℝ) ≤ T₀ := by exact_mod_cast (ENNReal.coe_lt_coe.1 hS).le
  exact (QuantumZipper.fwdHull_mono.1 hST).trans hR

/-- **A finite new horizon is impossible when the target is reached** (one sample). Let `w` be continuous from `0`
with a generating trace `γ` on `[0, ∞)` that is at `x_k > 0` at `T₀`, the target outside every earlier closed hull. If
`w_c` has a generating trace on `[0, ζ_c]` and agrees with Zhan's retargeted driver before the new horizon
`T̃ = sup_{S < T₀} C(S) ≤ ζ_c`, then `T̃ = ∞`. -/
theorem newHorizon_eq_top_of_code {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {xk : ℝ} (hxk : 0 < xk)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) {T₀ : ℝ≥0} (hγT : γ T₀ = xk)
    (hsep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → (xk : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t))
    {wc : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} {ηc : ℝ≥0 → ℂ} (hηc : IsGeneratingTrace wc ζc ηc)
    (hle : newHorizon xk w (fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t) T₀ ≤ ζc)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < newHorizon xk w (fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t) T₀ →
      wc t = newDrv xk w (fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t) t) :
    newHorizon xk w (fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t) T₀ = ⊤ := by
  set vk : ℝ≥0 → ℝ := fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t with hvk
  have hd : PullData w vk xk T₀ := pullData_of_notMem hw hw0 hxk hsep
  by_contra hTn
  have hη' : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T₀) ηc :=
    Sec7.IsGeneratingTrace.congr_lt (hηc.mono_horizon hle) fun t ht => (hag t ht).symm
  obtain ⟨R, hR⟩ := exists_fwdHull_subset_closedBall hw T₀
  have hp := hd.isGeneratingTrace_of_lt_top hη' hTn hR
  have heq := GW4Leaf.eqOn_of_isGeneratingTrace (hγ.mono_horizon le_top) hp hw.continuousOn hw0 T₀ le_rfl
  simp only [lt_self_iff_false, ↓reduceIte] at heq
  rw [hγT] at heq
  exact targetChangeInv_ne_self hxk _ heq

/-- **An infinite new horizon makes BR4a's clock unbounded** before `T₀`: `clock v = |v|⁻² C` there
(`BR4aChain.clock_eq_relClk`). -/
theorem clock_unbounded_of_newHorizon {w : ℝ≥0 → ℝ} {v : ℝ} (hv : v ≠ 0) {T₀ : ℝ≥0∞}
    (hd : PullData (oDrv v w) (tgt v w) (scl v) T₀) (hN : newHorizon (scl v) (oDrv v w) (tgt v w) T₀ = ⊤)
    (M : ℝ) : ∃ t : ℝ≥0, (t : ℝ≥0∞) < T₀ ∧ M ≤ BR4aPath.clock v (fun s : ℝ => w s.toNNReal) t := by
  have ha2 : 0 < scl v ^ 2 := by have := scl_pos hv; positivity
  have hlt : ENNReal.ofReal (M / scl v ^ 2) < newHorizon (scl v) (oDrv v w) (tgt v w) T₀ := by
    rw [hN]; exact ENNReal.ofReal_lt_top
  unfold newHorizon at hlt
  obtain ⟨S, hS⟩ := lt_iSup_iff.1 hlt
  obtain ⟨hST, hS'⟩ := lt_iSup_iff.1 hS
  refine ⟨S, hST, ?_⟩
  rw [clock_eq_relClk hv hd hST, relClk]
  have h1 : M / scl v ^ 2 < clk (rate (scl v) (oDrv v w) (tgt v w)) S := (ENNReal.ofReal_lt_ofReal_iff'.1 hS').1
  rw [div_lt_iff₀ ha2] at h1
  linarith

/-- The oriented driver for `v < 0` is the driver. -/
theorem oDrv_of_neg {w : ℝ≥0 → ℝ} {v : ℝ} (hv : v < 0) : oDrv v w = w := by
  funext t; simp [oDrv, sgn_of_neg hv]

/-- The oriented driver for `v > 0` is the reflected driver. -/
theorem oDrv_of_pos {w : ℝ≥0 → ℝ} {v : ℝ} (hv : 0 < v) : oDrv v w = -w := by
  funext t; simp [oDrv, sgn_of_pos hv]

/-- **The oriented trace**: `γ` for `v < 0`, `−γ̄` for `v > 0`; it generates the oriented driver and is at `|v|⁻¹`
whenever `γ` is at the pole `−1/v`. -/
theorem exists_oriented_trace {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) {v : ℝ} (hv : v ≠ 0)
    {T₀ : ℝ≥0} (hγT : γ T₀ = ((BR4aPath.pole v : ℝ) : ℂ)) :
    ∃ γo : ℝ≥0 → ℂ, IsGeneratingTrace (oDrv v w) ⊤ γo ∧ γo T₀ = scl v := by
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · refine ⟨γ, by rw [oDrv_of_neg hneg]; exact hγ, ?_⟩
    rw [hγT, pole_eq_scl_of_neg hneg]
  · refine ⟨fun t => LP.reflectC (γ t), by rw [oDrv_of_pos hpos]; exact LP.isGeneratingTrace_reflect hγ, ?_⟩
    simp only [hγT, pole_eq_neg_scl_of_pos hpos, LP.reflectC, Complex.ofReal_neg, map_neg, Complex.conj_ofReal,
      neg_neg]

/-- **BR4a's clock statement for one sample**, from the new-horizon statement for the oriented driver at every time
at which an oriented trace reaches `|v|⁻¹` with `|v|⁻¹` outside the earlier closed hulls. -/
theorem clock_unbounded_of_oriented {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {v : ℝ} (hv : v ≠ 0) (hvis : (v : ℂ) ∈ infinitySourceChart.tipSet w ⊤)
    (hN : ∀ T₀ : ℝ≥0, (∃ γo : ℝ≥0 → ℂ, IsGeneratingTrace (oDrv v w) ⊤ γo ∧ γo T₀ = scl v) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → (scl v : ℂ) ∉ closure (fwdHull (fun s : ℝ => oDrv v w s.toNNReal) t)) →
      newHorizon (scl v) (oDrv v w) (tgt v w) T₀ = ⊤) (M : ℝ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} ∧
      M ≤ BR4aPath.clock v (fun s : ℝ => w s.toNNReal) t := by
  obtain ⟨T₀, hT, hγT, -, -⟩ := BR4aPath.exists_firstTipTime_eq hγ hw hw0 hv hvis
  obtain ⟨-, -, -, hsep⟩ := exists_firstTipTime_notMem hw hw0 hγ hv hvis
  have hd := pullData_rel hw hw0 hv hsep
  rw [hT] at hd hsep ⊢
  have hN' : newHorizon (scl v) (oDrv v w) (tgt v w) T₀ = ⊤ :=
    hN T₀ (exists_oriented_trace hγ hv hγT) fun t ht => scl_notMem_closure hv (hsep t ht)
  exact clock_unbounded_of_newHorizon hv hd hN' M

end InteractingSLE.Theorem14.BR4aIn
