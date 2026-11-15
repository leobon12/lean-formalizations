/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux41RG

/-!
# The first-exit prime-end lemma for paths (an input of Aux. lemma 36)

Specification §6.2, **Aux.** lemma 36 (`source/spec/p193-240.md` L36–L78, p. 195): "Map `D_T` to the
half-plane using its original target at infinity. The first-exit prime-end lemma continuously lifts
the two incoming subarcs to simple arcs, ending at real points `q₁, q₂`." The same lifting is used
in Aux. lemma 34 (`source/spec/p145-192.md` L893) and in the fixed-chart geometry of the
ZTip-elimination note (ruling R41, §1.1, "its current incoming subarcs lift simply in the `g_r`
chart, from `z_r = g_r(x_C)` to `q₁, q₂ ∈ ℝ`").

For a continuous Loewner trace with continuous driver, the active domain at time `r` is
`D_r = ℍ \ K_r` and its mapping-out function is `g_r = fwdMap W r` (centred). If a path runs in
`D_r` on `[c, u)` and its endpoint `α(u)` is not in `D_r`, then `g_r ∘ α` converges, as `v ↑ u`,
to a
real point `q` with `f̄_r(q) = α(u)`.

## Proof

`β = g_r ∘ α` is continuous on `[c, u)` and bounded near `u` (`f_r` moves points by a bounded
amount). Every cluster point `ξ` of `β` at `u` lies in `ℍ̄` with `f̄_r(ξ) = α(u)`, hence is real
(`f̄_r(ℍ) = D_r ∌ α(u)`). Two distinct real cluster points `ξ₁ < ξ₂` are impossible: pick `m`
between
them with `f̄_r(m) ≠ α(u)` (no fibre of `f̄_r` contains an interval); the vertical ray over `m` is
mapped at a positive distance `r₀` from `α(u)` (PROVE-YUAN-M1's ray lemma), while `β` crosses that
ray (intermediate value theorem on `Re β`) at times where `|α(v) − α(u)| < r₀`. A bounded map with a
unique cluster point converges.

## Main result

* `exists_tendsto_lift`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The first-exit prime-end lemma for paths.** Let `α` be continuous on `[c, u]` (`c < u`), with
`α([c, u)) ⊆ D_r = ℍ \ K_r` and `α(u) ∉ D_r`. Then `g_r(α(v))` converges, as `v ↑ u`, to a real
point `q` with `f̄_r(q) = α(u)`. -/
theorem exists_tendsto_lift (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r c u : ℝ} (hr : 0 ≤ r) (hcu : c < u) {α : ℝ → ℂ} (hα : ContinuousOn α (Icc c u))
    (hαD : ∀ v ∈ Ico c u, α v ∈ H \ fwdHull W r) (hαu : α u ∉ H \ fwdHull W r) :
    ∃ q : ℝ, trMap W 0 r q = α u ∧
      Tendsto (fun v => fwdMap W r (α v)) (𝓝[<] u) (𝓝 (q : ℂ)) := by
  set β : ℝ → ℂ := fun v => fwdMap W r (α v) with hβ
  set F := trMap W 0 r with hF
  have hFeq : F = extendFrom H (fwdMapInv W r) := YuanSimpleApprox.trMap_zero_left hW0 r
  obtain ⟨hFd, hFc, hFi, hFR⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl hr
  have himg := trMap_zero_image_H hW hW0 hr
  -- the lift on `[c, u)`
  have hβH : ∀ v ∈ Ico c u, β v ∈ H := fun v hv =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hαD v hv)
  have hFβ : ∀ v ∈ Ico c u, F (β v) = α v := by
    intro v hv
    rw [hF, YuanSimpleApprox.trMap_eq_fwdMapInv hW hr (hβH v hv),
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero,
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr (hαD v hv)]
  have hβc : ContinuousOn β (Ico c u) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.comp
      (hα.mono Ico_subset_Icc_self) fun v hv => hαD v hv
  -- the filter
  set l : Filter ℝ := 𝓝[<] u with hl
  have hlIco : ∀ᶠ v in l, v ∈ Ico c u := by
    filter_upwards [Ioo_mem_nhdsLT hcu] with v hv using ⟨hv.1.le, hv.2⟩
  have hαlim : Tendsto α l (𝓝 (α u)) :=
    ((hα u ⟨hcu.le, le_rfl⟩).tendsto.mono_left (nhdsWithin_mono _ fun v hv =>
      ⟨hv.1.le, hv.2.le⟩)).mono_left (nhdsWithin_le_of_mem (Ioo_mem_nhdsLT hcu))
  have hFβlim : Tendsto (fun v => F (β v)) l (𝓝 (α u)) :=
    hαlim.congr' (by filter_upwards [hlIco] with v hv using (hFβ v hv).symm)
  -- boundedness
  obtain ⟨C₀, hC₀⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hr
  have hαB : ∀ᶠ v in l, ‖α v‖ ≤ ‖α u‖ + 1 := by
    have := hαlim.eventually (Metric.closedBall_mem_nhds (α u) one_pos)
    filter_upwards [this] with v hv
    have h1 := norm_le_norm_add_norm_sub' (α v) (α u)
    rw [dist_eq_norm] at hv
    linarith
  set Rb := ‖α u‖ + 1 + |C₀| with hRb
  have hβB : ∀ᶠ v in l, β v ∈ closedBall (0 : ℂ) Rb ∩ Hbar := by
    filter_upwards [hlIco, hαB] with v hv hvB
    refine ⟨?_, H_subset_Hbar (hβH v hv)⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hC₀ (β v) (hβH v hv)
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr (hαD v hv)] at h1
    have h2 := norm_le_norm_add_norm_sub' (β v) (α v)
    rw [norm_sub_rev] at h1
    linarith [le_abs_self C₀]
  have hK : IsCompact (closedBall (0 : ℂ) Rb ∩ Hbar) :=
    (isCompact_closedBall 0 Rb).inter_right isClosed_Hbar
  have hlne : l.NeBot := nhdsLT_neBot u
  -- cluster points are real points of the fibre
  have hclu : ∀ ξ, MapClusterPt ξ l β → ξ ∈ Hbar → F ξ = α u ∧ ξ.im = 0 := by
    intro ξ hξ hξH
    have hFξ : F ξ = α u := eq_of_mapClusterPt hFc
      (by filter_upwards [hlIco] with v hv using H_subset_Hbar (hβH v hv)) hFβlim hξH hξ
    refine ⟨hFξ, ?_⟩
    by_contra him
    have hξH' : ξ ∈ H := lt_of_le_of_ne hξH (Ne.symm him)
    exact hαu (by rw [← hFξ, ← himg]; exact ⟨ξ, hξH', rfl⟩)
  obtain ⟨ξ, hξK, hξ⟩ := hK.exists_mapClusterPt (f := l) (u := β)
    (by rw [le_principal_iff]; exact hβB)
  obtain ⟨hFξ, hξim⟩ := hclu ξ hξ hξK.2
  -- uniqueness of the cluster point
  have huniq : ∀ ξ' ∈ closedBall (0 : ℂ) Rb ∩ Hbar, MapClusterPt ξ' l β → ξ' = ξ := by
    intro ξ' hξ'K hξ'
    obtain ⟨-, hξ'im⟩ := hclu ξ' hξ' hξ'K.2
    by_contra hne
    have hre : ξ'.re ≠ ξ.re := fun h => hne (Complex.ext h (by rw [hξ'im, hξim]))
    -- name the two real cluster points `x₁ < x₂`
    obtain ⟨x₁, x₂, hx₁₂, hc₁, hc₂⟩ : ∃ x₁ x₂ : ℂ, x₁.re < x₂.re ∧ MapClusterPt x₁ l β ∧
        MapClusterPt x₂ l β := by
      rcases lt_or_gt_of_ne hre with h | h
      · exact ⟨ξ', ξ, h, hξ', hξ⟩
      · exact ⟨ξ, ξ', h, hξ, hξ'⟩
    obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hFd hFc hFi hx₁₂ (α u)
    have hzH : ∀ w ∈ H, extendFrom H (fwdMapInv W r) w ≠ α u := by
      intro w hw h
      rw [← hFeq] at h
      exact hαu (by rw [← h, ← himg]; exact ⟨w, hw, rfl⟩)
    obtain ⟨r₀, hr₀, hray⟩ := hη.exists_pos_lt_dist_ray hW hW0 hr hzH (by rw [← hFeq]; exact hFm)
    -- near `u`, `β` avoids the ray over `m`
    have hnear : ∀ᶠ v in l, v ∈ Ico c u ∧ dist (α v) (α u) < r₀ :=
      hlIco.and (hαlim.eventually (Metric.ball_mem_nhds _ hr₀))
    obtain ⟨v₀, hv₀u, hv₀⟩ : ∃ v₀ < u, ∀ v ∈ Ioo v₀ u, v ∈ Ico c u ∧ dist (α v) (α u) < r₀ := by
      obtain ⟨v₀, hv₀u, hv₀⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hnear
      exact ⟨v₀, hv₀u, fun v hv => hv₀ hv⟩
    have havoid : ∀ v ∈ Ioo v₀ u, (β v).re ≠ m := by
      intro v hv hvm
      obtain ⟨hvI, hvd⟩ := hv₀ v hv
      have := hray (β v) (H_subset_Hbar (hβH v hvI)) hvm
      rw [← hFeq, hFβ v hvI] at this
      linarith
    -- `β` comes close to both `x₁` and `x₂` after `v₀`
    have hev : ∀ᶠ v in l, v ∈ Ioo v₀ u := Ioo_mem_nhdsLT hv₀u
    obtain ⟨v₁, hv₁β, hv₁⟩ := ((hc₁.frequently (Metric.ball_mem_nhds x₁
      (show 0 < m - x₁.re by linarith [hm.1]))).and_eventually hev).exists
    obtain ⟨v₂, hv₂β, hv₂⟩ := ((hc₂.frequently (Metric.ball_mem_nhds x₂
      (show 0 < x₂.re - m by linarith [hm.2]))).and_eventually hev).exists
    have hre₁ : (β v₁).re < m := by
      have h := abs_re_le_norm (β v₁ - x₁)
      rw [dist_eq_norm] at hv₁β
      rw [sub_re] at h
      have := (abs_lt.1 (lt_of_le_of_lt h hv₁β)).2
      linarith
    have hre₂ : m < (β v₂).re := by
      have h := abs_re_le_norm (β v₂ - x₂)
      rw [dist_eq_norm] at hv₂β
      rw [sub_re] at h
      have := (abs_lt.1 (lt_of_le_of_lt h hv₂β)).1
      linarith
    -- intermediate value theorem for `Re β` between `v₁` and `v₂`
    have hsub : uIcc v₁ v₂ ⊆ Ioo v₀ u := by
      rcases le_total v₁ v₂ with h | h
      · rw [uIcc_of_le h]; exact fun v hv => ⟨hv₁.1.trans_le hv.1, hv.2.trans_lt hv₂.2⟩
      · rw [uIcc_of_ge h]; exact fun v hv => ⟨hv₂.1.trans_le hv.1, hv.2.trans_lt hv₁.2⟩
    have hrec : ContinuousOn (fun v => (β v).re) (uIcc v₁ v₂) :=
      Complex.continuous_re.comp_continuousOn (hβc.mono fun v hv =>
        ⟨(hv₀ v (hsub hv)).1.1, (hsub hv).2⟩)
    have hmem : m ∈ uIcc (β v₁).re (β v₂).re := by
      rw [uIcc_of_le (hre₁.trans hre₂).le]; exact ⟨hre₁.le, hre₂.le⟩
    obtain ⟨v, hv, hvm⟩ := intermediate_value_uIcc hrec hmem
    exact havoid v (hsub hv) hvm
  have hlim := hK.tendsto_nhds_of_unique_mapClusterPt hβB huniq
  refine ⟨ξ.re, ?_, ?_⟩
  · have hξr : (ξ.re : ℂ) = ξ := Complex.ext (by simp) (by simp [hξim])
    rw [hξr]; exact hFξ
  · have hξr : (ξ.re : ℂ) = ξ := Complex.ext (by simp) (by simp [hξim])
    rw [hξr]; exact hlim

end InteractingSLE.Sec6
