import InteractingSLE.Foundations.Loewner.YuanCorollary13
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# Property (ii) of [Yua22, Theorem 1.1] for continuous Loewner traces

Packet PROVE-YUAN-M1. Y. Yuan, *Topological characterisations of Loewner traces*, Indiana Univ.
Math. J. 71 (2022), arXiv:2003.05535v4 ([Yua22]): Theorem 1.1, (i) ⇒ (ii), in the form of
`YuanCharacterisation.HasContinuousOwnFuture` (PROVE-YUAN-M23): for a continuous Loewner trace `η`
of `W`, after every prefix `η([0, s])` the future lifts continuously through the boundary extension
of `g_s⁻¹`. The lift is the shifted trace of Corollary 1.3, uncentred:
`β_s(u) = γ_s(u − s) + W(s)`.

## Main results

* `invExt_fwdHull_eq`: the extension `invExt K_s` of the inverse mapping-out function of the hull
  `K_s` is `w ↦ F̄_s(w − W(s))` on `ℍ̄` (hydrodynamic uniqueness).
* `IsLoewnerTrace.hasContinuousOwnFuture`: property (ii) on every `[0, S]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanCorollary13

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The inverse of the mapping-out function of `K_s = fwdHull W s` is `w ↦ F_s(w − W(s))` on `ℍ`
(hydrodynamic uniqueness: `mapOut K_s = f_s + W(s)`). -/
theorem invFunOn_mapOut_fwdHull_eq (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {w : ℂ} (hw : w ∈ H) :
    invFunOn (ConformalImage.mapOut (fwdHull W s)) (H \ fwdHull W s) w =
      fwdMapInv W s (w - W s) := by
  set K := fwdHull W s with hK
  have hKh : IsHPHull K := isHPHull_fwdHull hW hs
  have hg : IsMapOut K (ConformalImage.mapOut K) := ConformalImage.isMapOut_mapOut hKh
  have heq := hg.eqOn hKh (isMapOut_fwdMap hW hW0 hs)
  have hwH : w - W s ∈ H := by
    show 0 < (w - (W s : ℂ)).im
    simpa using (show 0 < w.im from hw)
  set z := fwdMapInv W s (w - W s) with hz
  have hzK : z ∈ H \ K := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hs hwH
  have hgz : ConformalImage.mapOut K z = w := by
    rw [heq hzK]
    show fwdMap W s z + (W s : ℂ) = w
    rw [hz, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs hwH]
    ring
  have hwim : w ∈ ConformalImage.mapOut K '' (H \ K) := ⟨z, hzK, hgz⟩
  exact hg.1.2.injOn (invFunOn_mem hwim) hzK ((invFunOn_eq hwim).trans hgz.symm)

/-- **The boundary extension of the inverse mapping-out function** of the hull of a Loewner trace:
`invExt K_s w = F̄_s(w − W(s))` for `w ∈ ℍ̄`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.invExt_fwdHull_eq (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ Hbar) :
    YuanCharacterisation.invExt (fwdHull W s) w =
      extendFrom H (fwdMapInv W s) (w - W s) := by
  have hwcl : w ∈ closure H := by rw [closure_H]; exact hw
  have hw' : w - W s ∈ Hbar := by
    show 0 ≤ (w - (W s : ℂ)).im
    simpa using (show 0 ≤ w.im from hw)
  have hshift : Tendsto (fun v : ℂ => v - W s) (𝓝[H] w) (𝓝[H] (w - W s)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).tendsto w).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    show 0 < (v - (W s : ℂ)).im
    simpa using (show 0 < v.im from hv)
  have hlim := ((hη.hasBdryLimits hW hW0 hs).tendsto hw').comp hshift
  refine extendFrom_eq hwcl (hlim.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (invFunOn_mapOut_fwdHull_eq hW hW0 hs hv).symm

/-- **[Yua22, Theorem 1.1, (i) ⇒ (ii)] for continuous Loewner traces**: a continuous Loewner trace
`η` of `W` has continuous own futures on every `[0, S]`; the lift after `η([0, s])` is the
uncentred shifted trace `u ↦ γ_s(u − s) + W(s)` of Corollary 1.3. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.hasContinuousOwnFuture (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (S : ℝ) :
    YuanCharacterisation.HasContinuousOwnFuture η S := by
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hcor := hη.isLoewnerTrace_shift hW hW0 hs0
  set τ := loewnerTip (shiftDrive W s) with hτ
  refine ⟨fun u => τ (u - s) + W s, ?_, fun u hu => ?_, fun u hu => ?_⟩
  · refine (hcor.2.1.comp (continuousOn_id.sub continuousOn_const) fun u hu => ?_).add
      continuousOn_const
    show 0 ≤ u - s
    linarith [hu.1]
  · have h1 := (hη.extendFrom_shift_tip hW hW0 hs0 (show 0 ≤ u - s by linarith [hu.1])).1
    show 0 ≤ (τ (u - s) + (W s : ℂ)).im
    simpa using (show 0 ≤ (τ (u - s)).im from h1)
  · have hus : 0 ≤ u - s := by linarith [hu.1]
    obtain ⟨h1, h2, -⟩ := hη.extendFrom_shift_tip hW hW0 hs0 hus
    have hβ : τ (u - s) + (W s : ℂ) ∈ Hbar := by
      show 0 ≤ (τ (u - s) + (W s : ℂ)).im
      simpa using (show 0 ≤ (τ (u - s)).im from h1)
    rw [← hη.2.2 s hs0, hη.invExt_fwdHull_eq hW hW0 hs0 hβ, add_sub_cancel_right, h2]
    congr 1
    ring

end YuanCorollary13

end InteractingSLE
