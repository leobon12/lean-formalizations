/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfNoThr
import InteractingSLE.Spec.ZhanGT4.Prefix
import InteractingSLE.Spec.Supplement.BHMeanReal
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# A freshly reached real tip has only the tip as boundary preimage

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). For a Loewner trace `γ` of a continuous driver `U` from
`0`, continuous on `[0, T]`, whose tip `γ T = q` is a nonzero real point off every earlier closed hull (a landing
reached for the first time), the boundary extension of the inverse map at `T` takes the value `q` only at the driving
point `0` (`eq_zero_of_extendFrom_eq_tip`). In the walk this says that a piece's landing point has a single prime end,
the image of the tip.

**Proof.** Shift at `t < T`: `f̂_T = f̂_t ∘ f̂ˢ_{T−t}` on `ℍ` (`fwdMapInv_add_shift`), `‖f̂ˢ_{T−t}(w) − w‖ ≤ δ_t :=
6 M_t + 6 √(T − t)` (`norm_fwdMapInv_sub_le_of_le`). The point `q` is alive at `t`, so the forward map `f_t` has a
limit `y_t` at `q` from `ℍ` (`tendsto_fwdMap_of_isForwardSol_real`). If `f̂_T(w) → q` as `w → x`, then
`f̂ˢ_{T−t}(w) = f_t (f̂_T w) → y_t`, so `|y_t − x| ≤ δ_t`; the same at `x = 0` (the tip). Hence `|x| ≤ 2 δ_t → 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.SB.Wf

/-- The displacement of the inverse map's boundary values from a common limit through the shifted chain. -/
theorem norm_sub_le_of_shift {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) (T - t), |QuantumZipper.RS.shiftDrive U t r| ≤ M)
    {Y : ℂ} {q : ℂ} (hY : Tendsto (fwdMap U t) (𝓝[H] q) (𝓝 Y)) {z₀ : ℂ} (hz₀ : (𝓝[H] z₀).NeBot)
    (hlim : Tendsto (fwdMapInv U T) (𝓝[H] z₀) (𝓝 q)) :
    ‖Y - z₀‖ ≤ 6 * M + 6 * Real.sqrt (T - t) := by
  set Us := QuantumZipper.RS.shiftDrive U t with hUs
  have hUsc : Continuous Us := QuantumZipper.RS.continuous_shiftDrive hU t
  have hUs0 : Us 0 = 0 := QuantumZipper.RS.shiftDrive_zero U t
  have hd : 0 ≤ T - t := by linarith
  set φ : ℂ → ℂ := fun w => fwdMapInv Us (T - t) w with hφ
  have hcomp : ∀ w ∈ H, fwdMap U t (fwdMapInv U T w) = φ w := by
    intro w hw
    have e := QuantumZipper.RS.fwdMapInv_add_shift hU hU0 ht hd hw
    rw [show t + (T - t) = T by ring] at e
    rw [e, QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 ht (QuantumZipper.RS.fwdMapInv_mem_H hUsc hUs0 hd hw)]
  have hlimH : Tendsto (fwdMapInv U T) (𝓝[H] z₀) (𝓝[H] q) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun w hw =>
      QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (ht.trans htT) hw⟩
  have hφlim : Tendsto φ (𝓝[H] z₀) (𝓝 Y) :=
    (hY.comp hlimH).congr' (eventually_nhdsWithin_of_forall fun w hw => hcomp w hw)
  have hdiff : Tendsto (fun w => ‖φ w - w‖) (𝓝[H] z₀) (𝓝 ‖Y - z₀‖) :=
    ((hφlim.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm)
  refine le_of_tendsto hdiff (eventually_nhdsWithin_of_forall fun w hw => ?_)
  exact ZhanGT4.norm_fwdMapInv_sub_le_of_le hUsc hUs0 hd hM hw

/-- **A freshly reached nonzero real tip has only the driving point as boundary preimage.** -/
theorem eq_zero_of_extendFrom_eq_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 < T)
    {γ : ℝ → ℂ} (hγ : IsLoewnerTraceLT U T γ) (hc : ContinuousOn γ (Icc 0 T)) {q : ℝ} (hq : γ T = q)
    (hq0 : q ≠ 0) (hfresh : ∀ t, 0 ≤ t → t < T → (q : ℂ) ∉ closure (fwdHull U t)) {x : ℝ}
    (hx : extendFrom H (fwdMapInv U T) x = γ T) : x = 0 := by
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hγ hU hU0 hT hc
  have htip := TraceClose.extendFrom_zero_eq hγ hU hU0 hT hc
  have hlimx : Tendsto (fwdMapInv U T) (𝓝[H] (x : ℂ)) (𝓝 (q : ℂ)) := by
    have h := hB.tendsto (show ((x : ℂ)) ∈ Hbar by simp [Hbar])
    rwa [hx, hq] at h
  have hlim0 : Tendsto (fwdMapInv U T) (𝓝[H] (0 : ℂ)) (𝓝 (q : ℂ)) := by
    have h := hB.tendsto (show ((0 : ℂ)) ∈ Hbar by simp [Hbar])
    rwa [htip, hq] at h
  have hNx : (𝓝[H] (x : ℂ)).NeBot := Theorem14.GW1P.neBot_nhdsWithin_H (by simp [Hbar])
  have hN0 : (𝓝[H] (0 : ℂ)).NeBot := Theorem14.GW1P.neBot_nhdsWithin_H (by simp [Hbar])
  -- the key estimate at every earlier time
  have key : ∀ t, 0 ≤ t → t < T → ∀ M, (∀ r ∈ Icc (0 : ℝ) (T - t), |QuantumZipper.RS.shiftDrive U t r| ≤ M) →
      |x| ≤ 2 * (6 * M + 6 * Real.sqrt (T - t)) := by
    intro t ht htT M hM
    obtain ⟨v, hv⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure hU hU0 ht (hfresh t ht htT) hq0
    have hY := tendsto_fwdMap_of_isForwardSol_real hU hU0 ht hv
    have h1 := norm_sub_le_of_shift hU hU0 ht htT.le hM hY hNx hlimx
    have h2 := norm_sub_le_of_shift hU hU0 ht htT.le hM hY hN0 hlim0
    have h3 : ‖((x : ℂ))‖ ≤ ‖v t - (x : ℂ)‖ + ‖v t - 0‖ := by
      calc ‖((x : ℂ))‖ = ‖(v t - 0) - (v t - (x : ℂ))‖ := by congr 1; ring
        _ ≤ ‖v t - 0‖ + ‖v t - (x : ℂ)‖ := norm_sub_le _ _
        _ = ‖v t - (x : ℂ)‖ + ‖v t - 0‖ := add_comm _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h3
    linarith
  -- choose the time close to `T`
  by_contra hx0
  have hxp : 0 < |x| := abs_pos.2 hx0
  set e : ℝ := |x| / 48 with he
  have he0 : 0 < e := by positivity
  obtain ⟨η₁, hη₁, hη₁U⟩ := Metric.continuous_iff.1 hU T e he0
  set d : ℝ := min (min (η₁ / 2) (T / 2)) (e ^ 2) with hd
  have hd0 : 0 < d := lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hdη : d < η₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hdT : d ≤ T / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hde : Real.sqrt d ≤ e := by
    rw [Real.sqrt_le_left he0.le]
    exact min_le_right _ _
  set t : ℝ := T - d with htdef
  have ht0 : 0 ≤ t := by linarith
  have htT : t < T := by linarith
  have hM : ∀ r ∈ Icc (0 : ℝ) (T - t), |QuantumZipper.RS.shiftDrive U t r| ≤ 2 * e := by
    intro r hr
    have hr' : r ≤ d := by have := hr.2; linarith
    have h1 : dist (t + r) T < η₁ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1]
    have h2 : dist t T < η₁ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have h1' := hη₁U (t + r) h1
    have h2' := hη₁U t h2
    rw [Real.dist_eq] at h1' h2'
    show |U (t + r) - U t| ≤ 2 * e
    calc |U (t + r) - U t| = |(U (t + r) - U T) - (U t - U T)| := by ring_nf
      _ ≤ |U (t + r) - U T| + |U t - U T| := abs_sub _ _
      _ ≤ 2 * e := by linarith
  have hk := key t ht0 htT (2 * e) hM
  have hsq : Real.sqrt (T - t) ≤ e := by rw [show T - t = d by ring]; exact hde
  have : |x| ≤ 2 * (6 * (2 * e) + 6 * e) := by
    refine hk.trans ?_
    nlinarith [hsq]
  rw [he] at this
  linarith

end InteractingSLE.Theorem14.SB.Wf
