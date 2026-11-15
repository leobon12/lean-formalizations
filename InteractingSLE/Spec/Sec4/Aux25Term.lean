/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Prob
import InteractingSLE.Foundations.Loewner.FiniteEndpointStatement
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Aux. lemma 25 at a finite terminal endpoint, and the assembled lemma

Packet PROVE-AUX25. Specification p. 125: Aux. lemma 25 holds "up to and including a continuous finite terminal
endpoint"; p. 127: "The same one-density argument includes an announced finite terminal endpoint."

At a finite positive lifetime `ζ = T` the state converges to a threshold state (Aux. lemma 3,
`IsIntegratedSLEEvolution.ae_tendsto_threshold`). The last member `k` of a colliding group of weight `≤ −2` is
separated from the driver before `T` (`Sec2.IsForcePath.exists_gap_of_tendsto`), so its gap is the centred real flow
of the real point `x^k ≠ 0`, alive before `T` and tending to `0`. Say `x^k > 0` (the other side is the reflection
`z ↦ −z̄`). The trace before `T` avoids the ray `[x^k, ∞)`: its points alive at `t` are off `closure K_t`. If the
trace at `T` also avoided the ray, the whole compact trace would stay a positive distance from it, and the ray lemma
of PROVE-ENDPOINT (`FiniteEndpoint.not_tendsto_fwdMap_of_disjoint_ray`) would contradict `G_r(x^k) → 0`. So
`η(T) = b` for a real `b ≥ x^k`, a point alive at every `t < T`, hence not on the trace before `T`.

No Carathéodory continuity of the chain at `T` is needed: the argument adapts PROVE-ENDPOINT's proof of
`FiniteEndpoint.notMem_H_of_tendsto_fwdMap` (its Steps 2–4, with the final-time case of Step 1 replaced by the
contrapositive).

## Main results

* `Aux25.exists_eq_ray_of_tendsto_fwdMap`: the trace ends on the ray of a real point swallowed at `T`;
* `Sec2.IsForcePath.trace_ne_trace_terminal`: no return at a finite threshold (one path);
* `Theorem15.aux25Statement : Theorem15.Aux25Statement` — **Aux. lemma 25**, unconditionally.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Metric Filter Topology
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H fwdHull fwdMap IsForwardSol)

universe u

namespace InteractingSLE

namespace Aux25

section Ray

variable {U : ℝ → ℝ}

/-- A continuous path on `[0, T]` from `0` whose prefixes fill the hulls before `T` is a Loewner trace before `T`. -/
theorem isLoewnerTraceLT_of_isFilling {T : ℝ} {γ : ℝ → ℂ} (hγ0 : γ 0 = 0)
    (hγc : ContinuousOn γ (Icc 0 T))
    (hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull U t) (γ '' Icc 0 t)) :
    IsLoewnerTraceLT U T γ := by
  have hcpt : ∀ t ∈ Icc (0 : ℝ) T, IsCompact (γ '' Icc 0 t) := fun t ht =>
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc le_rfl ht.2))
  refine ⟨hγ0, hγc.mono Ico_subset_Icc_self, fun t ht htT => ?_⟩
  exact (fillH_eq_iff_isFilling_of_isClosed (hcpt t ⟨ht, htT.le⟩).isBounded
    (hcpt t ⟨ht, htT.le⟩).isClosed (fun z hz => hz.1)).1 (hfill t ⟨ht, htT⟩)

/-- **The trace before `T` avoids the ray of a real point alive before `T`.** If `y₀ > 0` is alive on `[0, r]` for
every `r < T`, then no `γ(t)`, `t < T`, is a real point `b ≥ y₀` (Step 1 of
`FiniteEndpoint.notMem_H_of_tendsto_fwdMap`). -/
theorem ne_ray_of_alive (hU : Continuous U) (hU0 : U 0 = 0) {T y₀ : ℝ} (hy₀ : 0 < y₀) {γ : ℝ → ℂ}
    (htrace : IsLoewnerTraceLT U T γ)
    (halive : ∀ r ∈ Ico (0 : ℝ) T, ∃ u, IsForwardSol U (y₀ : ℂ) r u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → γ t ≠ b := by
  intro t ht b hb heq
  rcases ht.1.lt_or_eq with ht0 | ht0
  · obtain ⟨u, hu⟩ := halive t ht
    obtain ⟨v, hv⟩ : ∃ v, IsForwardSol U (b : ℂ) t v := by
      rcases hb.lt_or_eq with hlt | hlt
      · exact QuantumZipper.RS.exists_isForwardSol_of_lt hU ht.1 (by rw [hU0]; exact hy₀) hlt hu
      · exact ⟨u, hlt ▸ hu⟩
    obtain ⟨δ, hδ, hδv⟩ := exists_two_mul_le_norm_of_isForwardSol ht.1 hv
    have htip := htrace.tendsto_fwdMapInv_tip hU hU0 ht.1 ht.2
    have hcl := YuanCorollary13.mem_closure_fwdHull_of_tendsto hU hU0 ht0 htip
    rw [heq] at hcl
    have hρ : 0 < δ / Real.exp (2 / δ ^ 2 * t) := div_pos hδ (Real.exp_pos _)
    obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hcl _ hρ
    have hzb' : ‖z - (b : ℂ)‖ < δ / Real.exp (2 / δ ^ 2 * t) := by
      rw [← dist_eq_norm, dist_comm]; exact hzb
    exact not_mem_fwdHull_of_isForwardSol hU hv hδ hδv hzK.1
      ((lt_div_iff₀ (Real.exp_pos _)).1 hzb') hzK
  · rw [← ht0, htrace.1] at heq
    have := congrArg Complex.re heq
    simp only [Complex.zero_re, Complex.ofReal_re] at this
    linarith

/-- **The trace ends on the ray of a swallowed real point.** Let `γ` be continuous on `[0, T]` with `γ 0 = 0` and
`K_t = fill(γ[0, t])` for `t < T`, and let a real point `y₀ > 0` be alive on every `[0, r]`, `r < T`, with
`G_r(y₀) → 0` as `r ↑ T`. Then `γ(T)` is a real point `b ≥ y₀`. (Steps 2–4 of
`FiniteEndpoint.notMem_H_of_tendsto_fwdMap`, whose conclusion `γ(T) ∉ ℍ` this strengthens.) -/
theorem exists_eq_ray_of_tendsto_fwdMap (hU : Continuous U) (hU0 : U 0 = 0) {T y₀ : ℝ} (hT : 0 < T)
    (hy₀ : 0 < y₀) {γ : ℝ → ℂ} (hγ0 : γ 0 = 0) (hγc : ContinuousOn γ (Icc 0 T))
    (hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull U t) (γ '' Icc 0 t))
    (halive : ∀ r ∈ Ico (0 : ℝ) T, ∃ u, IsForwardSol U (y₀ : ℂ) r u)
    (hlim : Tendsto (fun r => fwdMap U r y₀) (𝓝[<] T) (𝓝 0)) :
    ∃ b : ℝ, y₀ ≤ b ∧ γ T = b := by
  by_contra hγT
  push Not at hγT
  have hcpt : ∀ t ∈ Icc (0 : ℝ) T, IsCompact (γ '' Icc 0 t) := fun t ht =>
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc le_rfl ht.2))
  have htrace : IsLoewnerTraceLT U T γ := isLoewnerTraceLT_of_isFilling hγ0 hγc hfill
  have hfillH : ∀ t ∈ Ico (0 : ℝ) T, fwdHull U t = fillH (γ '' Icc 0 t) := fun t ht =>
    htrace.2.2 t ht.1 ht.2
  -- Step 1: the trace does not meet the ray `[y₀, ∞)`
  have hstep1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → γ t ≠ b := by
    intro t ht b hb
    rcases ht.2.lt_or_eq with htT | htT
    · exact ne_ray_of_alive hU hU0 hy₀ htrace halive t ⟨ht.1, htT⟩ b hb
    · rw [htT]; exact hγT b hb
  -- Step 2: a positive distance between the trace and the ray
  set F : Set ℂ := {z | z.im = 0 ∧ y₀ ≤ z.re} with hFdef
  have hFc : IsClosed F :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hFne : F.Nonempty := ⟨(y₀ : ℂ), by rw [hFdef]; exact ⟨by simp, by simp⟩⟩
  have hnotF : ∀ t ∈ Icc (0 : ℝ) T, γ t ∉ F := fun t ht hF =>
    hstep1 t ht (γ t).re hF.2 (Complex.ext (by simp) (by simp [hF.1]))
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le)
    ((continuous_infDist_pt F).comp_continuousOn hγc)
  set d := infDist (γ t₀) F with hd
  have hdpos : 0 < d := (hFc.notMem_iff_infDist_pos hFne).1 (hnotF t₀ ht₀)
  have hdist : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → d ≤ dist (γ t) b := fun t ht b hb =>
    (hmin ht).trans (infDist_le_dist_of_mem (show (b : ℂ) ∈ F from ⟨by simp, by simpa using hb⟩))
  -- Step 3: the `d/2`-neighbourhood of the ray avoids every hull
  have hray : ∀ r ∈ Ico (0 : ℝ) T, ∀ y : ℝ, y₀ ≤ y →
      Disjoint (ball (y : ℂ) (d / 2)) (fwdHull U r) := by
    intro r hr y hy
    rw [Set.disjoint_left]
    intro z hzb hzK
    rw [hfillH r hr] at hzK
    have hAc : closure (γ '' Icc 0 r) = γ '' Icc 0 r :=
      (hcpt r (Ico_subset_Icc_self hr)).isClosed.closure_eq
    set C : Set ℂ := (ball (y : ℂ) (d / 2) ∩ H) ∪ {w | y ≤ w.re ∧ 0 < w.im ∧ w.im < d / 2}
      with hC
    have hzC : z ∈ C := Or.inl ⟨hzb, hzK.1⟩
    have hp1 : (⟨y, d / 4⟩ : ℂ) ∈ ball (y : ℂ) (d / 2) ∩ H := by
      refine ⟨?_, show (0 : ℝ) < d / 4 by positivity⟩
      rw [mem_ball, dist_eq_norm]
      refine FiniteEndpoint.norm_lt_of_abs_re_add_abs_im_lt ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_self,
        abs_zero, sub_zero, zero_add]
      rw [abs_of_pos (by positivity)]
      linarith
    have hp2 : (⟨y, d / 4⟩ : ℂ) ∈ {w : ℂ | y ≤ w.re ∧ 0 < w.im ∧ w.im < d / 2} :=
      ⟨le_rfl, show (0 : ℝ) < d / 4 by positivity, show d / 4 < d / 2 by linarith⟩
    have hCpre : IsPreconnected C :=
      IsPreconnected.union _ hp1 hp2
        ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
        ((convex_halfSpace_re_ge y).inter ((convex_halfSpace_im_gt 0).inter
          (convex_halfSpace_im_lt (d / 2)))).isPreconnected
    have hCsub : C ⊆ H \ closure (γ '' Icc 0 r) := by
      intro w hw
      have hwH : w ∈ H := by
        rcases hw with hw | hw
        · exact hw.2
        · exact hw.2.1
      refine ⟨hwH, ?_⟩
      rw [hAc]
      rintro ⟨t, ht, rfl⟩
      have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hr.2.le⟩
      rcases hw with hw | hw
      · have := hdist t htT y hy
        have hw1 := hw.1
        rw [mem_ball] at hw1
        linarith
      · have := hdist t htT (γ t).re (hy.trans hw.1)
        have hle : dist (γ t) ((γ t).re : ℂ) < d / 2 := by
          rw [dist_eq_norm]
          refine FiniteEndpoint.norm_lt_of_abs_re_add_abs_im_lt ?_
          simp only [Complex.sub_re, Complex.ofReal_re, sub_self, abs_zero, Complex.sub_im,
            Complex.ofReal_im, sub_zero, zero_add]
          rw [abs_of_pos hw.2.1]
          exact hw.2.2
        linarith
    have hCunb : ¬ Bornology.IsBounded C := by
      intro hb
      obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hb
      have hw : (⟨max y (R + 1), d / 4⟩ : ℂ) ∈ C :=
        Or.inr ⟨le_max_left _ _, show (0 : ℝ) < d / 4 by positivity,
          show d / 4 < d / 2 by linarith⟩
      have h1 := hR _ hw
      have h2 := Complex.abs_re_le_norm (⟨max y (R + 1), d / 4⟩ : ℂ)
      have h3 : R + 1 ≤ |(⟨max y (R + 1), d / 4⟩ : ℂ).re| :=
        (le_max_right _ _).trans (le_abs_self _)
      linarith
    rcases hzK.2 with hzA | hbdd
    · exact (hCsub hzC).2 hzA
    · exact hCunb (hbdd.subset (hCpre.subset_connectedComponentIn hzC hCsub))
  -- Step 4: the ray lemma
  exact FiniteEndpoint.not_tendsto_fwdMap_of_disjoint_ray hU hU0 hT hy₀ (half_pos hdpos) hray halive hlim

/-- **No return at the swallowing time.** Under the hypotheses of `exists_eq_ray_of_tendsto_fwdMap`, `γ(T)` is not
a point of `γ([0, T))`. -/
theorem ne_of_tendsto_fwdMap (hU : Continuous U) (hU0 : U 0 = 0) {T y₀ : ℝ} (hT : 0 < T)
    (hy₀ : 0 < y₀) {γ : ℝ → ℂ} (hγ0 : γ 0 = 0) (hγc : ContinuousOn γ (Icc 0 T))
    (hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull U t) (γ '' Icc 0 t))
    (halive : ∀ r ∈ Ico (0 : ℝ) T, ∃ u, IsForwardSol U (y₀ : ℂ) r u)
    (hlim : Tendsto (fun r => fwdMap U r y₀) (𝓝[<] T) (𝓝 0)) :
    ∀ s ∈ Ico (0 : ℝ) T, γ s ≠ γ T := by
  obtain ⟨b, hb, hγT⟩ := exists_eq_ray_of_tendsto_fwdMap hU hU0 hT hy₀ hγ0 hγc hfill halive hlim
  intro s hs heq
  rw [hγT] at heq
  exact ne_ray_of_alive hU hU0 hy₀ (isLoewnerTraceLT_of_isFilling hγ0 hγc hfill) halive s hs b hb heq

end Ray

end Aux25

/-! ### One path at a finite threshold -/

namespace Sec2

namespace IsForcePath

open FiniteEndpoint

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **No return at a finite threshold** (one path). If the state converges at the finite positive lifetime
`T = ζ` to a threshold state, a continuous generating trace `γ` of `w` on `[0, T]` does not return at `T` to a point
it visited before `T`. (The setup is that of `IsForcePath.notMem_H_of_isGeneratingTrace`.) -/
theorem trace_ne_trace_terminal (h : IsForcePath xL xR ρL ρR w vL vR ζ)
    {γ : ℝ≥0 → ℂ} (htr : IsGeneratingTrace w ζ γ) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {s : ℝ≥0} (hsT : s < T) :
    γ s ≠ γ T := by
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
  have hgs : g s = γ s := by simp [hg]
  have hsI : (s : ℝ) ∈ Ico (0 : ℝ) T := ⟨s.coe_nonneg, NNReal.coe_lt_coe.2 hsT⟩
  rw [← hgT, ← hgs]
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
    exact Aux25.ne_of_tendsto_fwdMap hU hU0 hT' hy₀ hg0 hgc hfill
      (fun r hr => ⟨_, hsol r hr.2⟩) hlim0 s hsI
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
    have hmain := Aux25.ne_of_tendsto_fwdMap hU' hU0' hT' (neg_pos.2 hy₀)
      (γ := fun s => LP.reflectC (g s)) (by simp [hg0, LP.reflectC])
      (LP.continuous_reflectC.comp_continuousOn hgc) hfill' hsol' hlim0 s hsI
    exact fun he => hmain (by simp only [he])

end IsForcePath

end Sec2

/-! ### Assembly -/

namespace Theorem15

/-- **Aux. lemma 25** (Specification p. 125, `0 < κ < 4`): for an ordered force word, almost surely every continuous
generating trace on the available interval is injective on `{t | t ≤ ζ}`. Before the lifetime this is
`IsIntegratedSLEEvolution.ae_injOn_lt`; at a finite positive lifetime the state converges to a threshold state
(Aux. lemma 3) and `Sec2.IsForcePath.trace_ne_trace_terminal` excludes a return at `ζ`. -/
theorem aux25Statement : Aux25Statement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR _ Ω mΩ P _ 𝓕 W VL VR B ζ hE
  filter_upwards [hE.ae_injOn_lt hκ hκ4, hE.ae_tendsto_threshold hκ, hE.ae_isIntegratedSLEPath]
    with ω hinj hthr hpath
  intro η hη
  have hlt := hinj η hη
  induction hζ : ζ ω using ENNReal.recTopCoe with
  | top =>
    intro s _ t _ hst
    exact hlt (by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_top)
      (by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_top) hst
  | coe T =>
    intro s hs t ht hst
    rw [mem_ofPred_eq, ENNReal.coe_le_coe] at hs ht
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
    · have hs0 : s = 0 := le_antisymm (by rw [hT0]; exact hs) zero_le
      have ht0 : t = 0 := le_antisymm (by rw [hT0]; exact ht) zero_le
      rw [hs0, ht0]
    obtain ⟨w₀, vL₀, vR₀, hlim, hthrT⟩ := hthr T hT0 hζ.symm
    have hne := fun {r : ℝ≥0} (hr : r < T) =>
      hpath.isForcePath.trace_ne_trace_terminal hη hT0 hζ.symm hlim hthrT hr
    rcases hs.lt_or_eq with hsT | hsT <;> rcases ht.lt_or_eq with htT | htT
    · exact hlt (by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_coe.2 hsT)
        (by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_coe.2 htT) hst
    · exact absurd (htT ▸ hst) (hne hsT)
    · exact absurd (hsT ▸ hst.symm) (hne htT)
    · rw [hsT, htT]

end Theorem15

end InteractingSLE
