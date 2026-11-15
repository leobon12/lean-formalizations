/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1Connector
import InteractingSLE.Foundations.Loewner.FiniteEndpointState
import InteractingSLE.Spec.Exist.StagedLaw3Pos

/-!
# Lemma GW1: no real point beyond an open seed gap is swallowed at the lifetime (deterministic Loewner flow)

Packet PROVE-T14-GW6. The frozen `ExplState.launch` records a new **right** record whenever some real point to the
right of the right record is swallowed exactly at the end of a piece, before it looks at the left side. For the left
boundary walk (angle `π/2`) the threshold is on the left (GW1, "Reflection gives the left boundary walk"), and one must
also know that **no point right of the seed is swallowed at that moment**. Deterministic reason: the two seed marks
`0⁻`, `0⁺` separate (`V^{0,R}_t − V^{0,L}_t` is nondecreasing and positive for `t > 0`), so at a left collision the
right seed gap stays open, and every real point right of the seed stays above the right seed mark
(`Exist.StagedLaw.le_re_of_mark`); its gap is bounded below up to the lifetime, so its forward flow extends through
the lifetime.

## Main results

* `exists_isForwardSol_of_le_re`: a real point whose forward solutions on every `[0, r]`, `r < T`, keep real part
  `≥ c > 0` is alive on `[0, T]` (QuantumZipper's tamed real flow);
* `lt_of_tendsto_seeds`: at a finite positive lifetime the limits of two marks with `x^L ≤ x^R` are strictly ordered;
* `exists_isForwardSol_of_tendsto_gap`: if the gap of a right mark at `0` has a positive limit at the lifetime, every
  real point `x > 0` alive before the lifetime is alive at the lifetime;
* `continuous_launchDriver`: the stopped driver read by `ExplState.launch` is continuous when the piece's driver is
  continuous before its lifetime and left-continuous at it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol)

namespace InteractingSLE

namespace Theorem14

namespace GW1Conn

/-! ### Extension of a real forward solution through a time -/

/-- **A real point whose gap stays `≥ c > 0` before `T` is alive on `[0, T]`** (for a continuous driver): the tamed
real flow with cut-off `c` agrees with the forward solutions before `T`, stays `≥ c` up to `T` by continuity, and is
then a forward solution on `[0, T]` (`QuantumZipper.RS.isForwardSol_realTamed`). -/
theorem exists_isForwardSol_of_le_re {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) {x c : ℝ}
    (hc : 0 < c)
    (hsol : ∀ r : ℝ, 0 ≤ r → r < T → ∃ u, IsForwardSol W (x : ℂ) r u ∧ ∀ s ∈ Icc (0 : ℝ) r, c ≤ (u s).re) :
    ∃ u, IsForwardSol W (x : ℂ) T u := by
  have key : ∀ s : ℝ, 0 ≤ s → s < T → c ≤ QuantumZipper.RS.realTamed W c x s := by
    intro s hs hsT
    obtain ⟨u, hu, hle⟩ := hsol s hs hsT
    have him := QuantumZipper.im_isForwardSol_real hW hs hu
    set V : ℝ → ℝ := fun t => (u t + (W t : ℂ)).re with hVdef
    have hVe : ∀ t, V t = (u t).re + W t := fun t => by simp [hVdef]
    have hV : ∀ t ∈ Icc (0 : ℝ) s,
        HasDerivWithinAt V (QuantumZipper.RS.realVf W c t (V t)) (Icc 0 s) t := by
      intro t ht
      have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t
        (QuantumZipper.FwdHolo.hasDerivWithinAt_shift hu ht)
      have hval : QuantumZipper.RS.realVf W c t (V t) = (2 / u t).re := by
        rw [QuantumZipper.RS.realVf, hVe, add_sub_cancel_right, QuantumZipper.RS.realDrift_of_le (hle t ht)]
        have e : u t = ((u t).re : ℂ) := Complex.ext (by simp) (by simp [him t ht])
        rw [e, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
      rw [hval]
      exact h
    have hV0 : V 0 = x := by
      have h0 := (hu.2 0 ⟨le_rfl, hs⟩).2
      rw [intervalIntegral.integral_same, add_zero] at h0
      rw [hVdef]
      simp only
      rw [h0]
      simp
    have heq := QuantumZipper.RS.realTamedUnc_eq_of_sol hW hc hV0 hV s ⟨hs, le_rfl⟩
    show c ≤ QuantumZipper.RS.realTamedUnc W c x s - W s
    rw [heq, hVe]
    linarith [hle s ⟨hs, le_rfl⟩]
  have hcont := QuantumZipper.RS.continuousOn_realTamed hW hc hT.le x
  have hge : ∀ t ∈ Icc (0 : ℝ) T, c ≤ QuantumZipper.RS.realTamed W c x t := by
    intro t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · exact key t ht.1 hlt
    · rw [heq]
      have h1 : Tendsto (QuantumZipper.RS.realTamed W c x) (𝓝[Ico 0 T] T)
          (𝓝 (QuantumZipper.RS.realTamed W c x T)) :=
        (hcont T ⟨hT.le, le_rfl⟩).mono Ico_subset_Icc_self
      have hne : (𝓝[Ico (0 : ℝ) T] T).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hT.ne]
        exact ⟨hT.le, le_rfl⟩
      exact ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun s hs => key s hs.1 hs.2)
  exact ⟨_, QuantumZipper.RS.isForwardSol_realTamed hW hc hT.le hge⟩

/-! ### The marks of a force path -/

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- Times of `[0, t]` read in `ℝ≥0` lie before the lifetime. -/
theorem mapsTo_toNNReal_Icc {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    MapsTo Real.toNNReal (Icc (0 : ℝ) t) {u : ℝ≥0 | (u : ℝ≥0∞) < ζ} := fun s hs => by
  have : s.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
  exact lt_of_le_of_lt (by exact_mod_cast this) ht

/-- The reciprocal right gap `2/(V^{i,R} − W)` is integrable on `[0, t]` before the lifetime. -/
theorem intervalIntegrable_two_div_gapR (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (i : Fin nR) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have hI := (h.integrable_gapR ht i).const_mul (-2)
  have e : (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) =
      fun s : ℝ => -2 * (w s.toNNReal - vR i s.toNNReal)⁻¹ := by
    funext s
    rw [div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  rw [e]
  exact hI

/-- The reciprocal left gap `2/(V^{i,L} − W)` is integrable on `[0, t]` before the lifetime. -/
theorem intervalIntegrable_two_div_gapL (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (i : Fin nL) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have hI := (h.integrable_gapL ht i).const_mul (-2)
  have e : (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) =
      fun s : ℝ => -2 * (w s.toNNReal - vL i s.toNNReal)⁻¹ := by
    funext s
    rw [div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  rw [e]
  exact hI

/-- **The drift of a right mark is positive on a nondegenerate interval** (the gap is bounded on `[0, t]` and
positive off a null set). -/
theorem integral_two_div_gapR_pos (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (i : Fin nR) {t : ℝ≥0}
    (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < ζ) :
    0 < ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal) := by
  have hmaps := mapsTo_toNNReal_Icc ht
  have hfc : ContinuousOn (fun s : ℝ => vR i s.toNNReal - w s.toNNReal) (Icc 0 t) :=
    ((h.continuousOn_vR i).comp continuous_real_toNNReal.continuousOn hmaps).sub
      (h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  set M' : ℝ := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hnull := h.volume_collisionR i
  have hae : (fun _ : ℝ => 2 / M') ≤ᵐ[volume.restrict (Icc (0 : ℝ) t)]
      fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)] with s hs hns
    have hlt := hmaps hs
    have hle : w s.toNNReal ≤ vR i s.toNNReal := h.w_le_vR hlt i
    have hne : w s.toNNReal ≠ vR i s.toNNReal := fun he => hns ⟨hs.1, hlt, he⟩
    have hpos : 0 < vR i s.toNNReal - w s.toNNReal := sub_pos.2 (lt_of_le_of_ne hle hne)
    have hb : vR i s.toNNReal - w s.toNNReal ≤ M' :=
      ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM s hs)).trans (le_max_left _ _)
    exact div_le_div_of_nonneg_left (by norm_num) hpos hb
  have hmono := intervalIntegral.integral_mono_ae_restrict ht'.le intervalIntegrable_const
    (intervalIntegrable_two_div_gapR h i ht) hae
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have : 0 < (t : ℝ) * (2 / M') := mul_pos ht' (div_pos (by norm_num) hM'0)
  linarith

/-- **Two marks with ordered starting points separate strictly** (deterministic): at a finite positive lifetime
`T`, if `x^{L} ≤ x^{R}` for a left mark and a right mark, their limits at `T` satisfy `a < b`
(`V^R − V^L = x^R − x^L + ∫ (2/(V^R − W) − 2/(V^L − W))` has a positive and a nonnegative drift). -/
theorem lt_of_tendsto_marks (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {iL : Fin nL} {iR : Fin nR}
    (h0 : xL iL ≤ xR iR) {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {a b : ℝ}
    (hLim : Tendsto (vL iL) (𝓝[<] T) (𝓝 a)) (hRim : Tendsto (vR iR) (𝓝[<] T) (𝓝 b)) : a < b := by
  set T' : ℝ≥0 := T / 2 with hT'
  have hT'0 : 0 < T' := by rw [hT']; exact half_pos hT
  have hT'T : T' < T := by rw [hT']; exact NNReal.half_lt_self hT.ne'
  have hT'ζ : (T' : ℝ≥0∞) < ζ := by rw [← hζ]; exact_mod_cast hT'T
  set I := ∫ s in (0 : ℝ)..T', 2 / (vR iR s.toNNReal - w s.toNNReal) with hI
  have hIpos : 0 < I := integral_two_div_gapR_pos h iR hT'0 hT'ζ
  have key : ∀ t : ℝ≥0, T' ≤ t → t < T → I ≤ vR iR t - vL iL t := by
    intro t ht1 ht2
    have htζ : (t : ℝ≥0∞) < ζ := by rw [← hζ]; exact_mod_cast ht2
    have hmaps := mapsTo_toNNReal_Icc htζ
    rw [h.vR_eq htζ iR, h.vL_eq htζ iL]
    have hneg : ∫ s in (0 : ℝ)..t, 2 / (vL iL s.toNNReal - w s.toNNReal) ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) (f := fun s : ℝ =>
        -(2 / (vL iL s.toNNReal - w s.toNNReal))) (a := 0) (b := t) t.coe_nonneg fun s hs => by
          have hle : vL iL s.toNNReal ≤ w s.toNNReal := h.vL_le_w (hmaps hs) iL
          exact neg_nonneg.2 (div_nonpos_iff.2 (Or.inl ⟨by norm_num, sub_nonpos.2 hle⟩))
      rw [intervalIntegral.integral_neg] at this
      linarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_two_div_gapR h iR hT'ζ)
      (((intervalIntegrable_two_div_gapR h iR htζ).mono_set (by
        rw [uIcc_of_le (show (T' : ℝ) ≤ t by exact_mod_cast ht1), uIcc_of_le t.coe_nonneg]
        exact Icc_subset_Icc T'.coe_nonneg le_rfl)))
    have hpos2 : 0 ≤ ∫ s in (T' : ℝ)..t, 2 / (vR iR s.toNNReal - w s.toNNReal) :=
      intervalIntegral.integral_nonneg (by exact_mod_cast ht1) fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) t := ⟨T'.coe_nonneg.trans hs.1, hs.2⟩
        have hle : w s.toNNReal ≤ vR iR s.toNNReal := h.w_le_vR (hmaps hs') iR
        exact div_nonneg (by norm_num) (sub_nonneg.2 hle)
    rw [← hsplit]
    linarith
  have hlim : Tendsto (fun t => vR iR t - vL iL t) (𝓝[<] T) (𝓝 (b - a)) := hRim.sub hLim
  have hev : ∀ᶠ t in 𝓝[<] T, I ≤ vR iR t - vL iL t := by
    filter_upwards [Ioo_mem_nhdsLT hT'T] with t ht
    exact key t ht.1.le ht.2
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hle := ge_of_tendsto hlim hev
  linarith


/-- **A real point right of a right mark at `0` survives the lifetime when that mark's gap stays open**
(deterministic): at a finite positive lifetime `T`, if `V^{i,R} − W` tends to `g > 0` and the right mark `i` starts at
`0`, then every real `x > 0` that is alive on every `[0, r]`, `r < T`, for a continuous driver `U` agreeing with `W`
before `T`, is alive on `[0, T]`. Its gap stays above the mark's gap (`Exist.StagedLaw.le_re_of_mark`), hence
`≥ g/2` near `T`, and is bounded below on the rest by compactness. -/
theorem exists_isForwardSol_of_tendsto_gap (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {iR : Fin nR}
    (hx0 : xR iR = 0) {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {g : ℝ} (hg : 0 < g)
    (hlimg : Tendsto (fun t => vR iR t - w t) (𝓝[<] T) (𝓝 g)) {U : ℝ → ℝ} (hUc : Continuous U)
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {x : ℝ} (hx : 0 < x)
    (halive : ∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) : ∃ u, IsForwardSol U (x : ℂ) T u := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hU0 : U 0 = 0 := by rw [hU 0 le_rfl hT', Real.toNNReal_zero, h.w_zero]
  set d : ℝ → ℝ := fun s => vR iR s.toNNReal - w s.toNNReal with hd
  -- the right mark is a mark in the sense of `Exist.StagedLaw.IsMark` on every `[0, r]`, `r < T`
  have hmark : ∀ r : ℝ, 0 ≤ r → r < T → Exist.StagedLaw.IsMark U r 0 d := by
    intro r hr hrT
    have hrζ : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by
      rw [← hζ]; exact_mod_cast (Real.toNNReal_lt_iff_lt_coe hr).2 hrT
    have hmaps := mapsTo_toNNReal_Icc hrζ
    have hrr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr
    rw [hrr] at hmaps
    refine ⟨fun s hs => ?_, fun s hs => ?_, ?_, ?_⟩
    · have := h.w_le_vR (hmaps hs) iR
      simp only [hd]
      linarith
    · have heq := h.vR_eq (hmaps hs) iR
      rw [hx0, Real.coe_toNNReal s hs.1, zero_add] at heq
      simp only [hd]
      rw [heq, hU s hs.1 (lt_of_le_of_lt hs.2 hrT)]
      ring
    · have := intervalIntegrable_two_div_gapR h iR hrζ
      rwa [hrr] at this
    · refine measure_mono_null (fun s hs => ?_) (h.volume_collisionR iR)
      obtain ⟨hs, hs0⟩ := hs
      refine ⟨hs.1, hmaps hs, ?_⟩
      simp only [hd] at hs0
      linarith
  have hcmp : ∀ r : ℝ, 0 ≤ r → r < T → ∀ u, IsForwardSol U (x : ℂ) r u → ∀ s ∈ Icc 0 r, d s ≤ (u s).re :=
    fun r hr hrT u hu => Exist.StagedLaw.le_re_of_mark hUc hU0 hr (hmark r hr hrT) hx hu
  -- near `T` the mark's gap is at least `g/2`
  have hev : ∀ᶠ t in 𝓝[<] T, g / 2 < vR iR t - w t := hlimg.eventually (lt_mem_nhds (by linarith))
  obtain ⟨a, haT, ha⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hev
  have haT' : (a : ℝ) < T := by exact_mod_cast haT
  have hnear : ∀ s : ℝ, (a : ℝ) < s → s < T → g / 2 < d s := by
    intro s has hsT
    have hs0 : 0 ≤ s := a.coe_nonneg.trans has.le
    have hmem : s.toNNReal ∈ Ioo a T :=
      ⟨Real.lt_toNNReal_iff_coe_lt.2 has, (Real.toNNReal_lt_iff_lt_coe hs0).2 hsT⟩
    exact ha hmem
  -- away from `T`, compactness
  obtain ⟨u₀, hu₀⟩ := halive a haT'
  have hpos₀ := QuantumZipper.re_pos_isForwardSol_real hUc a.coe_nonneg hu₀ (by rw [hU0]; exact hx)
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 a.coe_nonneg)
    (Complex.continuous_re.comp_continuousOn hu₀.1)
  set m := (u₀ s₀).re with hm
  have hm0 : 0 < m := hpos₀ s₀ hs₀
  set c := min m (g / 2) with hc
  have hc0 : 0 < c := lt_min hm0 (by linarith)
  refine exists_isForwardSol_of_le_re hUc hT' hc0 fun r hr hrT => ?_
  obtain ⟨u, hu⟩ := halive r hrT
  refine ⟨u, hu, fun s hs => ?_⟩
  by_cases hsa : s ≤ a
  · have hmin' : s ≤ min r a := le_min hs.2 hsa
    have heq := QuantumZipper.ASep.isForwardSol_unique_any
      (QuantumZipper.isForwardSol_restrict hu (le_min hr a.coe_nonneg) (min_le_left _ _))
      (QuantumZipper.isForwardSol_restrict hu₀ (le_min hr a.coe_nonneg) (min_le_right _ _)) ⟨hs.1, hmin'⟩
    rw [heq]
    exact (min_le_left _ _).trans (hmin ⟨hs.1, hsa⟩)
  · have h1 := hnear s (not_le.1 hsa) (lt_of_le_of_lt hs.2 hrT)
    have h2 := hcmp r hr hrT u hu s hs
    exact (min_le_right _ _).trans (by linarith)

end Path

/-! ### The driver read by a launch -/

/-- **The stopped driver read by `ExplState.launch` is continuous** when the piece's driver is continuous before its
finite lifetime `T` and left-continuous at `T`. -/
theorem continuous_launchDriver {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {T : ℝ≥0} (hT : (T : ℝ≥0∞) = D.2)
    (hc : ContinuousOn D.1 (Iio T)) (hlim : Tendsto D.1 (𝓝[<] T) (𝓝 (D.1 T))) :
    Continuous (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) := by
  have e : (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) =
      D.1 ∘ fun r : ℝ => min r.toNNReal T := by
    funext r
    simp only [Function.comp_apply, ← hT, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  rw [e]
  have hcIic : ContinuousOn D.1 (Iic T) := by
    intro t ht
    rcases (mem_Iic.1 ht).lt_or_eq with hlt | heq
    · exact ((hc.continuousAt (isOpen_Iio.mem_nhds hlt)).continuousWithinAt)
    · rw [heq]
      exact continuousWithinAt_Iio_iff_Iic.1 hlim
  exact hcIic.comp_continuous (continuous_real_toNNReal.min continuous_const)
    fun r => mem_Iic.2 (min_le_right _ _)

/-- The stopped driver read by a launch agrees with the driver before the lifetime. -/
theorem launchDriver_eq {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {T : ℝ≥0} (hT : (T : ℝ≥0∞) = D.2) {r : ℝ} (hr : 0 ≤ r)
    (hrT : r < T) : D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal = D.1 r.toNNReal := by
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < D.2 := by
    rw [← hT, ENNReal.coe_lt_coe]; exact (Real.toNNReal_lt_iff_lt_coe hr).2 hrT
  rw [min_eq_left hlt.le, ENNReal.toNNReal_coe]

end GW1Conn

end Theorem14

end InteractingSLE
