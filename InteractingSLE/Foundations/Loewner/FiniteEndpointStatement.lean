/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Foundations.Loewner.FiniteEndpointState
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Supplement.S10B712D

/-!
# A finite continuation endpoint is original-real

Packet PROVE-ENDPOINT. Proof of the named input `Supp10.FiniteEndpointRealStatement` (supplement
§10.1, proof of Theorem 7.12D, p. 543: "a genuine finite continuation endpoint is original-real"),
and the almost-sure form of the swallowed real point used by `Theorem14.GW1FirstThresholdStatement`.

## Main results

* `Sec2.IsForcePath.notMem_H_of_isGeneratingTrace`: for one path of an integrated `SLE_κ(ρ)`
  evolution with a continuous generating trace `γ` on `[0, T]`, if at the finite positive lifetime
  `T` the state converges to a threshold state, then `γ(T) ∉ ℍ`.
* `IsIntegratedSLEEvolution.ae_notMem_H_of_isGeneratingTrace`: almost surely, a continuous
  generating trace of the evolution does not end in `ℍ` at a finite lifetime.
* `Supp10.finiteEndpointRealStatement : Supp10.FiniteEndpointRealStatement`.

## Proof

At a finite positive lifetime Aux. lemma 3 (`IsIntegratedSLEEvolution.ae_tendsto_threshold`) gives
a limit `(w₀, v₀)` of the state satisfying the threshold condition. The last member `k` of a
colliding group of weight `≤ −2` is separated from the driver before `T` and collides with it at
`T` (`IsForcePath.exists_gap_of_tendsto`), so `V^k − W` is the centred real flow of the real point
`x^k ≠ 0`, alive before `T` and tending to `0` (`IsForcePath.isForwardSol_gapR`). The driver,
extended by `w₀` after `T`, is continuous on `ℝ`; the trace generates its hulls before `T`. On the
right side `FiniteEndpoint.notMem_H_of_tendsto_fwdMap` gives `γ(T) ∉ ℍ`; the left side reduces to
it by the reflection `z ↦ −z̄`, `W ↦ −W` (`LP.fwdHull_neg`, `LP.isFilling_reflectC`). At a zero
lifetime the trace is at its real seed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Metric Filter Topology
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H fwdHull fwdMap IsForwardSol)

universe u

namespace InteractingSLE

namespace FiniteEndpoint

/-- The driver `w` extended by its limit `w₀` from time `T` on, read on `ℝ`. -/
def extDriver (w : ℝ≥0 → ℝ) (T : ℝ≥0) (w₀ : ℝ) (s : ℝ) : ℝ :=
  if s.toNNReal < T then w s.toNNReal else w₀

theorem extDriver_of_lt {w : ℝ≥0 → ℝ} {T : ℝ≥0} {w₀ s : ℝ} (hs : 0 ≤ s) (hsT : s < T) :
    extDriver w T w₀ s = w s.toNNReal := by
  have : s.toNNReal < T := by rw [Real.toNNReal_lt_iff_lt_coe hs]; exact hsT
  simp [extDriver, this]

/-- The extended driver is continuous when `w` is continuous before `T` with limit `w₀`. -/
theorem continuous_extDriver {w : ℝ≥0 → ℝ} {T : ℝ≥0} {w₀ : ℝ}
    (hw : ContinuousOn w (Iio T)) (hlim : Tendsto w (𝓝[<] T) (𝓝 w₀)) :
    Continuous (extDriver w T w₀) := by
  set E : ℝ≥0 → ℝ := fun t => if t < T then w t else w₀ with hE
  have hE' : extDriver w T w₀ = E ∘ Real.toNNReal := rfl
  rw [hE']
  refine Continuous.comp ?_ continuous_real_toNNReal
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases lt_trichotomy t T with htT | htT | htT
  · have hev : E =ᶠ[𝓝 t] w := by
      filter_upwards [isOpen_Iio.mem_nhds htT] with s hs
      simp [hE, show s < T from hs]
    exact ((hw.continuousAt (isOpen_Iio.mem_nhds htT))).congr hev.symm
  · rw [htT]
    have hET : E T = w₀ := by simp [hE]
    refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · refine continuousWithinAt_Iio_iff_Iic.1 ?_
      rw [ContinuousWithinAt, hET]
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [hE, show s < T from hs]
    · refine (continuousWithinAt_const (b := w₀)).congr (fun s hs => ?_) hET
      simp [hE, not_lt.2 (show T ≤ s from hs)]
  · have hev : E =ᶠ[𝓝 t] fun _ => w₀ := by
      filter_upwards [isOpen_Ioi.mem_nhds htT] with s hs
      simp [hE, not_lt.2 (le_of_lt (show T < s from hs))]
    exact continuousAt_const.congr hev.symm

end FiniteEndpoint

namespace Sec2

namespace IsForcePath

open FiniteEndpoint

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The trace at a finite threshold** (one path). If the state converges at the finite positive
lifetime `T = ζ` to a threshold state, a continuous generating trace `γ` of `w` on `[0, T]` does not
end in `ℍ`. -/
theorem notMem_H_of_isGeneratingTrace (h : IsForcePath xL xR ρL ρR w vL vR ζ)
    {γ : ℝ≥0 → ℂ} (htr : IsGeneratingTrace w ζ γ) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) : γ T ∉ H := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} = Iio T := by
    rw [← hζ]; exact setOf_lt_coe_eq_Iio T
  have hwc : ContinuousOn w (Iio T) := hset ▸ h.continuousOn_w
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  set U := extDriver w T w₀ with hUdef
  have hU : Continuous U := continuous_extDriver hwc hw
  have hU0 : U 0 = 0 := by rw [hUdef, extDriver_of_lt le_rfl hT']; simpa using h.w_zero
  have hUeq : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal := fun r hr hrT =>
    extDriver_of_lt hr hrT
  -- the trace read on `ℝ`
  set g : ℝ → ℂ := fun s => γ s.toNNReal with hg
  have hg0 : g 0 = 0 := by simpa [hg] using htr.1
  have hgc : ContinuousOn g (Icc 0 T) := by
    refine htr.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ
    rw [← hζ, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_iff_le_coe.2 hs.2
  have hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull U t) (g '' Icc 0 t) := by
    intro t ht
    have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by
      rw [← hζ, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht.1]; exact ht.2
    have hf := htr.2.2 t.toNNReal htT
    rw [Real.coe_toNNReal _ ht.1] at hf
    rw [hg, image_toNNReal_Icc γ ht.1,
      fwdHull_eq_of_eqOn (W := U) (W' := fun s : ℝ => w s.toNNReal) ht.1
        (show t < (t + T) / 2 by linarith [ht.2])
        (fun r hr => hUeq r hr.1 (by linarith [hr.2, ht.2]))]
    exact hf
  have hgT : g T = γ T := by simp [hg]
  rw [← hgT]
  have hm : Tendsto Real.toNNReal (𝓝[<] (T : ℝ)) (𝓝[<] T) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hT']
    exact tendsto_toNNReal_nhdsLT T
  rcases h.exists_gap_of_tendsto hT hζ hlim hthr with ⟨k, hk, hk0⟩ | ⟨k, hk, hk0⟩
  · -- right side
    have hv : Tendsto (vR k) (𝓝[<] T) (𝓝 (vR₀ k)) :=
      ((continuous_apply k).tendsto _).comp ((continuous_snd.comp continuous_snd).tendsto _ |>.comp
        hlim)
    have hy₀ : 0 < xR k := by
      have := hk 0 hT
      rwa [h.w_zero, h.vR_zero] at this
    have hsol : ∀ r : ℝ, r < T → IsForwardSol U (xR k : ℂ) r (gapR vR w k) := fun r hr =>
      h.isForwardSol_gapR hζ hk hUeq hr
    have hlim0 : Tendsto (fun r => fwdMap U r (xR k)) (𝓝[<] (T : ℝ)) (𝓝 0) := by
      have hgap : Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0) := by
        simpa [hk0] using hv.sub hw
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp (hgap.comp hm)
      rw [Complex.ofReal_zero] at h2
      refine h2.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hT'] with r hr
      exact (fwdMap_eq_of_isForwardSol hU (hsol r hr.2) ⟨hr.1.le, le_rfl⟩).symm
    exact notMem_H_of_tendsto_fwdMap hU hU0 hT' hy₀ hg0 hgc hfill
      (fun r hr => ⟨_, hsol r hr.2⟩) hlim0
  · -- left side, by reflection
    have hv : Tendsto (vL k) (𝓝[<] T) (𝓝 (vL₀ k)) :=
      ((continuous_apply k).tendsto _).comp ((continuous_fst.comp continuous_snd).tendsto _ |>.comp
        hlim)
    have hy₀ : xL k < 0 := by
      have := hk 0 hT
      rwa [h.w_zero, h.vL_zero] at this
    have hsol : ∀ r : ℝ, r < T → IsForwardSol U (xL k : ℂ) r (gapL vL w k) := fun r hr =>
      h.isForwardSol_gapL hζ hk hUeq hr
    have hU' : Continuous (fun s => -U s) := hU.neg
    have hU0' : (fun s => -U s) 0 = 0 := by simp [hU0]
    have hsol' : ∀ r ∈ Ico (0 : ℝ) T,
        ∃ u, IsForwardSol (fun s => -U s) (((-xL k : ℝ)) : ℂ) r u := fun r hr =>
      exists_isForwardSol_neg_iff.2 ⟨_, hsol r hr.2⟩
    have hlim0 : Tendsto (fun r => fwdMap (fun s => -U s) r ((-xL k : ℝ) : ℂ)) (𝓝[<] (T : ℝ))
        (𝓝 0) := by
      have hgap : Tendsto (fun t => vL k t - w t) (𝓝[<] T) (𝓝 0) := by
        simpa [hk0] using hv.sub hw
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp (hgap.comp hm)).neg
      rw [Complex.ofReal_zero, neg_zero] at h2
      refine h2.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hT'] with r hr
      rw [fwdMap_neg_real hU (hsol r hr.2) ⟨hr.1.le, le_rfl⟩,
        fwdMap_eq_of_isForwardSol hU (hsol r hr.2) ⟨hr.1.le, le_rfl⟩]
      rfl
    have hfill' : ∀ t ∈ Ico (0 : ℝ) T,
        IsFilling (fwdHull (fun s => -U s) t) ((fun s => LP.reflectC (g s)) '' Icc 0 t) := by
      intro t ht
      have h1 := LP.isFilling_reflectC (hfill t ht)
      rw [image_image] at h1
      have h2 : fwdHull (fun s => -U s) t = LP.reflectC '' fwdHull U t := LP.fwdHull_neg U t
      rw [h2]
      exact h1
    have hmain := notMem_H_of_tendsto_fwdMap hU' hU0' hT' (neg_pos.2 hy₀)
      (γ := fun s => LP.reflectC (g s)) (by simp [hg0, LP.reflectC])
      (LP.continuous_reflectC.comp_continuousOn hgc) hfill' hsol' hlim0
    exact fun hH => hmain (LP.reflectC_mem_H_iff.2 hH)

end IsForcePath

end Sec2

namespace IsIntegratedSLEEvolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **A generating trace does not end in `ℍ` at a finite lifetime** (almost surely): for `a > 0`
and a continuous generating trace `γ ω` of every driving path, almost surely `γ ω T ∉ ℍ` whenever
`T = ζ ω` is finite. -/
theorem ae_notMem_H_of_isGeneratingTrace (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (ha : 0 < a) {γ : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω → γ ω T ∉ H := by
  filter_upwards [h.ae_isIntegratedSLEPath, h.ae_tendsto_threshold ha, htr] with ω hp hth hγ T hζ
  rcases (zero_le (a := T)).lt_or_eq with hT | hT
  · obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hth T hT hζ
    exact hp.isForcePath.notMem_H_of_isGeneratingTrace hγ hT hζ hlim hthr
  · rw [← hT, hγ.1]
    intro hH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)

end IsIntegratedSLEEvolution

namespace Supp10

/-- **A genuine finite continuation endpoint is original-real** (supplement §10.1, proof of
Theorem 7.12D, p. 543): for a flow line, almost surely the value at a finite lifetime is not in
`ℍ`. -/
theorem finiteEndpointRealStatement : FiniteEndpointRealStatement.{u} := by
  intro κ hκ _ b jumps _ x θ Ω _ P _ h _ η ζ hη
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  have hae := hcoup.1.ae_notMem_H_of_isGeneratingTrace (γ := fun ω t => η ω t - x) hκ htr
  filter_upwards [hae] with ω hω T hT hH
  refine hω T hT ?_
  have : (0 : ℝ) < (η ω T - x).im := by
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hH
  exact this

end Supp10

end InteractingSLE
