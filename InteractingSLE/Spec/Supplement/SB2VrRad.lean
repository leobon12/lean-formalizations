/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VqEnd
import InteractingSLE.Foundations.Loewner.ConformalImage
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Spec.Supplement.RLCG8DetRelBoundary
import InteractingSLE.Spec.Supplement.GW2SdwOutward
import InteractingSLE.Spec.Sec7.LocalExtGChart
import InteractingSLE.Spec.Exist.Determine

/-!
# Lawler's radius bound and the tip at a finite lifetime (decision D14, option b)

Packet PROVE-AUX61-NOJUMP. Decision D14 (`planning/reviews/DECISIONS-PENDING.md`): prove that if all hulls before
`T` lie in a fixed ball, then the driver is bounded before `T`.

* **`abs_le_of_fwdHull_subset`** (deterministic): if `K_t ⊆ B̄(0, R)` (`R > 0`, continuous driver from `0`), then
  `|W t| ≤ 6R`. Proof: `5R` lies off `K̄_t`, so the real flow from `5R` is alive at `t` and positive; near `5R` in
  `ℍ` the mapping-out function moves points by at most `R` ([Law05] Prop. 3.46,
  `IsMapOut.norm_sub_le_of_four_mul_le`), and the limit at `5R` is the real flow value; so
  `0 < u_t ≤ 6R − W t`. Symmetrically from `−5R`.
* **`abs_le_of_isGeneratingTrace`**: a driver continuous before a finite `T` with a generating trace continuous on
  `[0, T]` (Theorem 1.3) is bounded before `T`.
* **`tip_bad_of_isGeneratingTrace`**: an integrated SLE path with such a trace has its tip at `T` at a bad point
  (with `SB2VqEnd.tip_bad_of_bounded`); this closes D10 step 1 in the critical-escape case as well.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Vr

/-- The value at `t` of the real flow from a point `y` off the closed hull, read through the mapping-out function:
if `‖g w − w‖ ≤ R` for `w ∈ ℍ` near `y`, then `‖u_t + W t − y‖ ≤ R`. -/
theorem norm_flow_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {y t R : ℝ} (ht : 0 ≤ t) {u : ℝ → ℂ}
    (hu : IsForwardSol W (y : ℂ) t u)
    (hle : ∀ᶠ w in 𝓝[H] (y : ℂ), ‖(fwdMap W t w + W t) - w‖ ≤ R) : ‖u t + W t - y‖ ≤ R := by
  have hlim : Tendsto (fun w => (fwdMap W t w + W t) - w) (𝓝[H] (y : ℂ)) (𝓝 (u t + W t - y)) :=
    ((tendsto_fwdMap_of_isForwardSol_real hW hW0 ht hu).add tendsto_const_nhds).sub
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (y : ℂ)) (by simp)
  exact le_of_tendsto hlim.norm hle

/-- **Lawler's radius bound.** If the hull of a continuous driver from `0` at time `t` lies in `B̄(0, R)`, then
`|W t| ≤ 6R`. -/
theorem abs_le_of_fwdHull_subset {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {R t : ℝ} (hR : 0 < R)
    (ht : 0 ≤ t) (hK : fwdHull W t ⊆ closedBall (0 : ℂ) R) : |W t| ≤ 6 * R := by
  have hKH : IsHPHull (fwdHull W t) := isHPHull_fwdHull hW ht
  have hg := isMapOut_fwdMap hW hW0 ht
  have hK' : fwdHull W t ⊆ closedBall ((0 : ℝ) : ℂ) R := by simpa using hK
  -- near `±5R` the mapping-out function moves points by at most `R`
  have hnear : ∀ y : ℝ, |y| = 5 * R →
      ∀ᶠ w in 𝓝[H] (y : ℂ), ‖(fwdMap W t w + W t) - w‖ ≤ R := by
    intro y hy
    have hopen : {w : ℂ | 4 * R < ‖w‖} ∈ 𝓝 (y : ℂ) := by
      refine (isOpen_lt continuous_const continuous_norm).mem_nhds ?_
      show 4 * R < ‖(y : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, hy]
      linarith
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with w hw hwH
    refine hg.norm_sub_le_of_four_mul_le hKH hR hK' hwH ?_
    simpa using hw.le
  -- `±5R` is off the closed hull, so the real flow from it is alive at `t`
  have hoff : ∀ y : ℝ, |y| = 5 * R → (y : ℂ) ∉ closure (fwdHull W t) := by
    intro y hy hmem
    have hc : closure (fwdHull W t) ⊆ closedBall (0 : ℂ) R := closure_minimal hK isClosed_closedBall
    have h1 := mem_closedBall_zero_iff.1 (hc hmem)
    rw [Complex.norm_real, Real.norm_eq_abs, hy] at h1
    linarith
  have hy5 : |(5 * R : ℝ)| = 5 * R := abs_of_pos (by linarith)
  have hyn : |(-(5 * R) : ℝ)| = 5 * R := by rw [abs_neg, hy5]
  obtain ⟨u, hu⟩ := RLC.G8Det.alive_of_notMem_closure hW (by rw [hW0]; linarith) ht (hoff _ hy5)
  obtain ⟨v, hv⟩ := RLC.G8Det.alive_of_notMem_closure hW (by rw [hW0]; linarith) ht (hoff _ hyn)
  have hu1 := norm_flow_sub_le hW hW0 ht hu (hnear _ hy5)
  have hv1 := norm_flow_sub_le hW hW0 ht hv (hnear _ hyn)
  have hupos : 0 < (u t).re := Theorem14.GW2Sdw.re_pos_of_isForwardSol_real hW hu (by rw [hW0]; linarith)
    ⟨ht, le_rfl⟩
  have hvneg : (v t).re < 0 := Theorem14.GW2Sdw.re_neg_of_isForwardSol_real hW hv (by rw [hW0]; linarith)
    ⟨ht, le_rfl⟩
  have hre1 := (Complex.abs_re_le_norm _).trans hu1
  have hre2 := (Complex.abs_re_le_norm _).trans hv1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hre1 hre2
  rw [abs_le] at hre1 hre2 ⊢
  constructor <;> linarith [hre1.1, hre1.2, hre2.1, hre2.2]

/-- A filling of a closed set inside `B̄(0, R)` lies in `B̄(0, R)` (within `ℍ`). -/
theorem subset_closedBall_of_isFilling {K A : Set ℂ} (hKH : K ⊆ H) (hA : IsClosed A) {R : ℝ}
    (hAR : A ⊆ closedBall (0 : ℂ) R) (hK : IsFilling K A) : K ⊆ closedBall (0 : ℂ) R := by
  have hb : Bornology.IsBounded A := isBounded_closedBall.subset hAR
  have heq := (isFilling_iff_inter_H_eq_fillH hb hA).1 hK
  rw [inter_eq_left.2 hKH] at heq
  rw [heq]
  exact fillH_subset_closedBall_zero (by rw [hA.closure_eq]; exact hAR)

/-- **The driver is bounded before a finite `T`** when it is continuous before `T`, starts at `0`, and has a
generating trace continuous on `[0, T]` (Theorem 1.3's closed trace): all hulls before `T` lie in a ball containing
`γ([0, T])`, and Lawler's radius bound applies to the driver frozen after a time in `(t, T)`. -/
theorem exists_abs_le_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0} {γ : ℝ≥0 → ℂ}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w T γ) :
    ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → |w t| ≤ M := by
  have hγc : ∀ t : ℝ≥0, t ≤ T → IsCompact (γ '' Icc 0 t) := fun t htT =>
    isCompact_Icc.image_of_continuousOn (hgen.2.1.mono fun s hs => by
      show (s : ℝ≥0∞) ≤ T
      exact_mod_cast hs.2.trans htT)
  obtain ⟨r, hr⟩ := (hγc T le_rfl).isBounded.subset_closedBall (0 : ℂ)
  set R := max r 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨6 * R, fun t ht => ?_⟩
  have htT : t < T := by exact_mod_cast ht
  -- a time strictly between `t` and `T`
  obtain ⟨t', htt', ht'T⟩ := exists_between htT
  set W' : ℝ → ℝ := fun s => w (min s.toNNReal t') with hW'
  have hW'c : Continuous W' := by
    refine hw.comp_continuous (continuous_real_toNNReal.min continuous_const) fun s => ?_
    show ((min s.toNNReal t' : ℝ≥0) : ℝ≥0∞) < T
    exact_mod_cast (min_le_right _ _).trans_lt ht'T
  have hW'0 : W' 0 = 0 := by simp [hW', hw0]
  have heq : EqOn W' (fun s : ℝ => w s.toNNReal) (Icc 0 (t' : ℝ)) := fun s hs => by
    have : s.toNNReal ≤ t' := Real.toNNReal_le_iff_le_coe.2 hs.2
    simp only [hW', min_eq_left this]
  have hK : fwdHull W' t = fwdHull (fun s : ℝ => w s.toNNReal) t :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt t.2 (by exact_mod_cast htt') heq
  have hfill := hgen.2.2 t ht
  rw [← hK] at hfill
  have hsub : γ '' Icc 0 t ⊆ closedBall (0 : ℂ) R :=
    ((image_mono (Icc_subset_Icc_right htT.le)).trans hr).trans (closedBall_subset_closedBall (le_max_left _ _))
  have hKR := subset_closedBall_of_isFilling (Exist.fwdHull_subset_H t.2) (hγc t htT.le).isClosed hsub hfill
  have := abs_le_of_fwdHull_subset hW'c hW'0 hR t.2 hKR
  simpa [hW', min_eq_left htt'.le] using this

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **D10 step 1, both cases: the tip at a finite lifetime is a bad point.** An integrated SLE path with a
generating trace continuous on `[0, T]` (Theorem 1.3) and drift continuous at `T` has its tip at `T` at a bad
point; the critical-escape case of Aux. lemma 3 is excluded by the radius bound. -/
theorem tip_bad_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {β : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β T)
    (hgen : IsGeneratingTrace w T γ) (hβ : ContinuousAt β T) : Vq.IsBadPoint xL xR ρL ρR (γ T) := by
  obtain ⟨M, hM⟩ := exists_abs_le_of_isGeneratingTrace hp.2.2.2.1 hp.1 hgen
  exact Vq.tip_bad_of_bounded hT hp hgen hβ hM

/-- **D10 step 1 for a flow line, almost surely**: a flow line with a positive finite lifetime ends at a bad point of
its flow-line word (centred at its start), whether or not Aux. lemma 3's critical escape occurs. -/
theorem ae_tip_bad_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, 0 < ζ ω → ζ ω ≠ ⊤ →
      Vq.IsBadPoint (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
        (flowLineRhoR κ b jumps x θ) (η ω (ζ ω).toNNReal - x) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, hgen⟩ := hη
  filter_upwards [hcoup.1.2.2.2.2, hcoup.1.1.1.cont, hgen] with ω hp hBc hg hζ0 hζt
  obtain ⟨T, hTe⟩ : ∃ T : ℝ≥0, ζ ω = T := ⟨(ζ ω).toNNReal, (ENNReal.coe_toNNReal hζt).symm⟩
  rw [hTe] at hp hg hζ0
  rw [hTe, ENNReal.toNNReal_coe]
  exact tip_bad_of_isGeneratingTrace (by exact_mod_cast hζ0) hp hg hBc.continuousAt

end InteractingSLE.Theorem14.SB.Vr
