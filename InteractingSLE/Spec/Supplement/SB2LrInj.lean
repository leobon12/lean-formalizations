/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LqPhys
import InteractingSLE.Spec.Exist.StagedLaw2Real

/-!
# The one-chart injectivity input of physical aliveness, from continuity of the forward chart

Packet PROVE-T14-SB2LIFT (round 8; item 1 of handoff §R7.2). `Lk.lAlive_iff_notMem_closure_prefix` needs the boundary
map `ĝ` of the launch chart to be injective at the chart point `y = c.1 x` of a physical real point `x` beyond the
record (no other point of `ℍ̄` has boundary value `x`). This file derives that injectivity from continuity of the
forward chart at `x`:

* **`injAt_of_continuousWithinAt`** (deterministic, generic): let `g` map `ℍ` into `ℍ` with left inverse `f` on `ℍ`,
  and `ĝ` be a continuous extension of `g` to `ℍ̄`. If `x` is real, `ĝ y = x`, `f x = y`, and `f` is continuous within
  `ℍ` at `x`, then `ĝ k = ĝ y` forces `k = y` for every `k ∈ ℍ̄`. A point of `ℍ` is mapped into `ℍ`, not to the real
  `x`. A real `k` is approached by `k + i/(n+1)`, whose images under `g` tend to `x`, so their `f`-images, which are
  the points themselves, tend to `y`;
* **`continuousWithinAt_fwdMap_real`**: a Loewner forward map is continuous within `ℍ` at a real point alive at the
  stop, where it is real (`RS.fwdFlow_near_alive_real`, `im_fwdMap_ofReal`);
* **`lAlive_iff_notMem_closure_prefix_of_fwd`**: the physical aliveness criterion with the injectivity replaced by
  the continuity of the forward chart and the boundary value `ĝ (c.1 x) = x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw

variable {g ĝ f : ℂ → ℂ}

/-- The points `k + i/(n+1)` lie in `ℍ` and tend to the real point `k`. -/
theorem tendsto_add_I_div {k : ℂ} (hk : k.im = 0) :
    Tendsto (fun n : ℕ => k + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝[H] k) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h1 := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := tendsto_const_nhds (x := k) |>.add (h1.mul_const Complex.I)
    simpa using h2
  · show 0 < (k + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, hk, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, zero_add]
    exact Nat.one_div_pos_of_nat

/-- **Injectivity of the boundary map at a point where the forward chart is continuous.** -/
theorem injAt_of_continuousWithinAt (hgH : MapsTo g H H) (hfg : ∀ w ∈ H, f (g w) = w)
    (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ g H) {x y : ℂ} (hx : x.im = 0) (hyx : ĝ y = x)
    (hf : ContinuousWithinAt f H x) (hfx : f x = y) : ∀ k ∈ Hbar, ĝ k = ĝ y → k = y := by
  intro k hk hke
  rw [hyx] at hke
  by_cases hkH : k ∈ H
  · exfalso
    have h1 : g k ∈ H := hgH hkH
    rw [← hgg hkH, hke] at h1
    have : (0 : ℝ) < x.im := h1
    rw [hx] at this
    exact lt_irrefl _ this
  · have hkre : k.im = 0 := le_antisymm (not_lt.1 hkH) hk
    set z : ℕ → ℂ := fun n => k + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hzdef
    have hz := tendsto_add_I_div hkre
    have hzH : ∀ n, z n ∈ H := fun n => by
      show 0 < (k + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.add_im, hkre, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact Nat.one_div_pos_of_nat
    -- the images tend to `x` within `ℍ`
    have hgz : Tendsto (fun n => g (z n)) atTop (𝓝[H] x) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => hgH (hzH n)⟩
      have h1 := (hĝ k hk).tendsto.comp (tendsto_nhdsWithin_mono_right QuantumZipper.H_subset_Hbar hz)
      rw [hke] at h1
      exact h1.congr fun n => hgg (hzH n)
    have hfz : Tendsto (fun n => f (g (z n))) atTop (𝓝 y) := by
      rw [← hfx]
      exact hf.tendsto.comp hgz
    have hfz' : Tendsto (fun n => f (g (z n))) atTop (𝓝 k) :=
      (tendsto_nhdsWithin_iff.1 hz).1.congr fun n => (hfg _ (hzH n)).symm
    exact tendsto_nhds_unique hfz' hfz

/-- **A Loewner forward map is continuous within `ℍ` at a real point alive at the stop.** -/
theorem continuousWithinAt_fwdMap_real {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {x : ℝ}
    {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) :
    ContinuousWithinAt (fwdMap W T) H (x : ℂ) ∧ (fwdMap W T (x : ℂ)).im = 0 := by
  obtain ⟨-, hlim, -⟩ := QuantumZipper.RS.fwdFlow_near_alive_real hW hT hv
  have he : fwdMap W T (x : ℂ) = v T := fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩
  refine ⟨?_, im_fwdMap_ofReal W hT x⟩
  rw [ContinuousWithinAt, he]
  exact hlim

/-- **Physical aliveness at a launch from the continuity of the forward chart**: a real nonzero chart point
`c.1 z` of a physical real point `z` (boundary value `ĝ (c.1 z) = z`, forward chart continuous within `ℍ` at `z`), off
the old closed fill, is alive at the stop iff `z` is off the closure of the new filled prefix. -/
theorem lAlive_iff_notMem_closure_prefix_of_fwd {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤) {P P' : Set ℂ} (hcc : c.IsConformal)
    (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H) (hD : c.2.1 '' H = H \ fillH P)
    (hD' : c.2.1 '' (H \ fillH (LuM.trOf D '' Icc 0 D.2.toNNReal)) = H \ fillH P')
    (hA : IsCompact (LuM.trOf D '' Icc 0 D.2.toNNReal)) {z : ℂ} (hz : z.im = 0) (hre : (c.1 z).im = 0)
    (hne : c.1 z ≠ 0) (hyx : ĝ (c.1 z) = z) (hf : ContinuousWithinAt c.1 H z) (hy0 : z ∉ closure (fillH P)) :
    lAlive c ⊤ D z ↔ z ∉ closure (fillH P') := by
  have hinj : InjOn c.2.1 H := fun w hw w' hw' h => by rw [← hcc.2.2 w hw, h, hcc.2.2 w' hw']
  have hinjy := injAt_of_continuousWithinAt hcc.2.1 hcc.2.2 hĝ hgg hz hyx hf rfl
  have h := lAlive_iff_notMem_closure_prefix hP hfin hre hne hinj hĝ hgg hD hD' hA (by rw [hyx]; exact hy0) hinjy
  rwa [hyx] at h

end InteractingSLE.Theorem14.SB.Lk
