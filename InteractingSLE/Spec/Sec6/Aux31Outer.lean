/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40InfJordan

/-!
# Aux. lemma 30 in the half-plane chart: the boundary extension on a locally connected subdomain

Specification §6.2, **Aux.** lemma 30 (`source/spec/p145-192.md` L736–L749, pp. 181–182):
"Let `O` be a simply connected plane domain and let `f : 𝔻 → O` have a continuous extension to
`𝔻̄` … If `E ⊂ O` is a Jordan domain in the sphere, then `g = f⁻¹` restricted to `E` extends
continuously and injectively to `Ē`."

Here `O = D_s = ℍ \ K_s` is the active domain of a continuous Loewner trace, `f = f̄_s` its inverse
mapping-out function (continuous on `ℍ̄`, the boundary theorem for a continuous Loewner trace), and
`g = g_s`. The proof is the source's: a boundary fibre of `f̄_s` is totally disconnected
(`exists_ne_of_injOn`; the ray lemma), the cluster set of `g_s` along nested connected relative
neighbourhoods is connected, hence a single point. We state it for any `A ⊆ D_s` which is locally
connected at its boundary points (`IsLocConnWithin`), and prove this property for Jordan domains
(`isLocConnWithin_of_jordan`, from the Schoenflies disc chart) and for their images under the real
Möbius map `ψ_p` (`isLocConnWithin_of_psiMap`), which covers Jordan domains in the sphere through
`∞`.

## Main results

* `exists_tendsto_fwdMap_of_locConn`: the boundary limit of `g_s` along a locally connected
  approach;
* `exists_bdryExt_fwdMap` (**Aux. lemma 30, half-plane form**): `g_s|A` extends continuously and
  injectively to `Ā`, with `f̄_s ∘ G = id` on `Ā`, real values at the boundary points of `D_s`;
* `isLocConnWithin_of_jordan`, `isLocConnWithin_of_psiMap`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

/-- `A` is **locally connected at `z` from within**: `z` has arbitrarily small preconnected relative
neighbourhoods in `A`. -/
def IsLocConnWithin (A : Set ℂ) (z : ℂ) : Prop :=
  ∀ ε > 0, ∃ A' ⊆ A ∩ ball z ε, IsPreconnected A' ∧ A' ∈ 𝓝[A] z

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The boundary limit of `g_s` along a locally connected approach** (the core of Aux. lemma 30):
if `A ⊆ D_s` is locally connected at a boundary point `p ∉ D_s` of `A`, then `g_s(z)` converges as
`z → p` within `A`, to a real point `q` with `f̄_s(q) = p`. -/
theorem exists_tendsto_fwdMap_of_locConn (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {A : Set ℂ} (hAD : A ⊆ H \ fwdHull W s) {p : ℂ}
    (hpA : p ∈ closure A) (hpD : p ∉ H \ fwdHull W s) (hloc : IsLocConnWithin A p) :
    ∃ q : ℝ, trMap W 0 s q = p ∧ Tendsto (fwdMap W s) (𝓝[A] p) (𝓝 (q : ℂ)) := by
  set β : ℂ → ℂ := fwdMap W s with hβ
  set F := trMap W 0 s with hF
  have hFeq : F = extendFrom H (fwdMapInv W s) := YuanSimpleApprox.trMap_zero_left hW0 s
  obtain ⟨hFd, hFc, hFi, -⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl hs
  have himg := trMap_zero_image_H hW hW0 hs
  have hβH : ∀ z ∈ A, β z ∈ H := fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hAD hz)
  have hFβ : ∀ z ∈ A, F (β z) = z := by
    intro z hz
    rw [hF, YuanSimpleApprox.trMap_eq_fwdMapInv hW hs (hβH z hz),
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero,
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (hAD hz)]
  have hβc : ContinuousOn β A :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn.mono hAD
  set l : Filter ℂ := 𝓝[A] p with hl
  have hlne : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpA
  have hlA : ∀ᶠ z in l, z ∈ A := self_mem_nhdsWithin
  have hlim : Tendsto (fun z : ℂ => z) l (𝓝 p) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hFβlim : Tendsto (fun z => F (β z)) l (𝓝 p) :=
    hlim.congr' (by filter_upwards [hlA] with z hz using (hFβ z hz).symm)
  -- boundedness
  obtain ⟨C₀, hC₀⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hs
  have hzB : ∀ᶠ z in l, ‖z‖ ≤ ‖p‖ + 1 := by
    filter_upwards [hlim.eventually (Metric.closedBall_mem_nhds p one_pos)] with z hz
    have h1 := norm_le_norm_add_norm_sub' z p
    rw [dist_eq_norm] at hz
    linarith
  set Rb := ‖p‖ + 1 + |C₀| with hRb
  have hβB : ∀ᶠ z in l, β z ∈ closedBall (0 : ℂ) Rb ∩ Hbar := by
    filter_upwards [hlA, hzB] with z hz hzb
    refine ⟨?_, QuantumZipper.H_subset_Hbar (hβH z hz)⟩
    rw [mem_closedBall_zero_iff]
    have h1 := hC₀ (β z) (hβH z hz)
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (hAD hz)] at h1
    have h2 := norm_le_norm_add_norm_sub' (β z) z
    rw [norm_sub_rev] at h1
    linarith [le_abs_self C₀]
  have hK : IsCompact (closedBall (0 : ℂ) Rb ∩ Hbar) :=
    (isCompact_closedBall 0 Rb).inter_right QuantumZipper.isClosed_Hbar
  -- cluster points are real points of the fibre
  have hclu : ∀ ξ, MapClusterPt ξ l β → ξ ∈ Hbar → F ξ = p ∧ ξ.im = 0 := by
    intro ξ hξ hξH
    have hFξ : F ξ = p := eq_of_mapClusterPt hFc
      (by filter_upwards [hlA] with z hz using QuantumZipper.H_subset_Hbar (hβH z hz)) hFβlim
      hξH hξ
    refine ⟨hFξ, ?_⟩
    by_contra him
    have hξH' : ξ ∈ H := lt_of_le_of_ne hξH (Ne.symm him)
    exact hpD (by rw [← hFξ, ← himg]; exact ⟨ξ, hξH', rfl⟩)
  obtain ⟨ξ, hξK, hξ⟩ := hK.exists_mapClusterPt (f := l) (u := β)
    (by rw [le_principal_iff]; exact hβB)
  obtain ⟨hFξ, hξim⟩ := hclu ξ hξ hξK.2
  -- uniqueness of the cluster point
  have huniq : ∀ ξ' ∈ closedBall (0 : ℂ) Rb ∩ Hbar, MapClusterPt ξ' l β → ξ' = ξ := by
    intro ξ' hξ'K hξ'
    obtain ⟨-, hξ'im⟩ := hclu ξ' hξ' hξ'K.2
    by_contra hne
    have hre : ξ'.re ≠ ξ.re := fun h => hne (Complex.ext h (by rw [hξ'im, hξim]))
    obtain ⟨x₁, x₂, hx₁₂, hc₁, hc₂⟩ : ∃ x₁ x₂ : ℂ, x₁.re < x₂.re ∧ MapClusterPt x₁ l β ∧
        MapClusterPt x₂ l β := by
      rcases lt_or_gt_of_ne hre with h | h
      · exact ⟨ξ', ξ, h, hξ', hξ⟩
      · exact ⟨ξ, ξ', h, hξ, hξ'⟩
    obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hFd hFc hFi hx₁₂ p
    have hzH : ∀ w ∈ H, extendFrom H (fwdMapInv W s) w ≠ p := by
      intro w hw h
      rw [← hFeq] at h
      exact hpD (by rw [← h, ← himg]; exact ⟨w, hw, rfl⟩)
    obtain ⟨r₀, hr₀, hray⟩ := hη.exists_pos_lt_dist_ray hW hW0 hs hzH (by rw [← hFeq]; exact hFm)
    -- a small connected neighbourhood, whose lift must cross the ray over `m`
    obtain ⟨A', hA'sub, hA'pre, hA'l⟩ := hloc r₀ hr₀
    obtain ⟨z₁, hz₁β, hz₁⟩ := ((hc₁.frequently (Metric.ball_mem_nhds x₁
      (show 0 < m - x₁.re by linarith [hm.1]))).and_eventually hA'l).exists
    obtain ⟨z₂, hz₂β, hz₂⟩ := ((hc₂.frequently (Metric.ball_mem_nhds x₂
      (show 0 < x₂.re - m by linarith [hm.2]))).and_eventually hA'l).exists
    have hre₁ : (β z₁).re < m := by
      have h := abs_re_le_norm (β z₁ - x₁)
      rw [dist_eq_norm] at hz₁β
      rw [sub_re] at h
      have := (abs_lt.1 (lt_of_le_of_lt h hz₁β)).2
      linarith
    have hre₂ : m < (β z₂).re := by
      have h := abs_re_le_norm (β z₂ - x₂)
      rw [dist_eq_norm] at hz₂β
      rw [sub_re] at h
      have := (abs_lt.1 (lt_of_le_of_lt h hz₂β)).1
      linarith
    have hpre : IsPreconnected ((fun z => (β z).re) '' A') :=
      hA'pre.image _ (Complex.continuous_re.comp_continuousOn
        (hβc.mono fun z hz => (hA'sub hz).1))
    obtain ⟨z, hzA', hzm⟩ := hpre.Icc_subset ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
      ⟨hre₁.le, hre₂.le⟩
    have hzA := (hA'sub hzA').1
    have := hray (β z) (QuantumZipper.H_subset_Hbar (hβH z hzA)) hzm
    rw [← hFeq, hFβ z hzA] at this
    exact absurd (mem_ball.1 (hA'sub hzA').2) (not_lt.2 this.le)
  have hlim' := hK.tendsto_nhds_of_unique_mapClusterPt hβB huniq
  have hξr : (ξ.re : ℂ) = ξ := Complex.ext (by simp) (by simp [hξim])
  exact ⟨ξ.re, by rw [hξr]; exact hFξ, by rw [hξr]; exact hlim'⟩

/-- **Aux. lemma 30, half-plane form.** Let `A ⊆ D_s` be locally connected at each of its boundary
points outside `D_s`. Then `g_s|A` extends to a continuous injective `G` on `Ā` with values in
`ℍ̄`, `f̄_s(G(z)) = z` on `Ā`, `G = g_s` on `Ā ∩ D_s`, and `G` real at the points of `Ā \ D_s`. -/
theorem exists_bdryExt_fwdMap (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {A : Set ℂ} (hAD : A ⊆ H \ fwdHull W s)
    (hloc : ∀ p ∈ closure A, p ∉ H \ fwdHull W s → IsLocConnWithin A p) :
    ∃ G : ℂ → ℂ, ContinuousOn G (closure A) ∧ InjOn G (closure A) ∧
      MapsTo G (closure A) Hbar ∧ (∀ z ∈ closure A, trMap W 0 s (G z) = z) ∧
      (∀ z ∈ closure A, z ∈ H \ fwdHull W s → G z = fwdMap W s z) ∧
      ∀ z ∈ closure A, z ∉ H \ fwdHull W s → (G z).im = 0 := by
  set D := H \ fwdHull W s with hDdef
  have hDo : IsOpen D := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs
  have hgc : ContinuousOn (fwdMap W s) D :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn
  have himg := trMap_zero_image_H hW hW0 hs
  obtain ⟨-, hFc, -, -⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl hs
  have hFg : ∀ z ∈ D, trMap W 0 s (fwdMap W s z) = z := fun z hz => by
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hz),
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero,
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs hz]
  -- the limits
  have hlim : ∀ z ∈ closure A, ∃ y, Tendsto (fwdMap W s) (𝓝[A] z) (𝓝 y) := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact ⟨_, ((hgc z hzD).continuousAt (hDo.mem_nhds hzD)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · obtain ⟨q, -, hq⟩ := exists_tendsto_fwdMap_of_locConn hη hW hW0 hs hAD hz hzD
        (hloc z hz hzD)
      exact ⟨_, hq⟩
  set G := extendFrom A (fwdMap W s) with hGdef
  have hGlim : ∀ z ∈ closure A, Tendsto (fwdMap W s) (𝓝[A] z) (𝓝 (G z)) := fun z hz => by
    have : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
    exact tendsto_extendFrom (hlim z hz)
  have hGH : ∀ z ∈ closure A, G z ∈ Hbar := fun z hz => by
    have : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
    exact QuantumZipper.isClosed_Hbar.mem_of_tendsto (hGlim z hz)
      (by filter_upwards [self_mem_nhdsWithin] with w hw using
        QuantumZipper.H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hAD hw)))
  have hFG : ∀ z ∈ closure A, trMap W 0 s (G z) = z := by
    intro z hz
    have hne : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
    have h1 : Tendsto (fun w => trMap W 0 s (fwdMap W s w)) (𝓝[A] z) (𝓝 (trMap W 0 s (G z))) :=
      (hFc _ (hGH z hz)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hGlim z hz, by
        filter_upwards [self_mem_nhdsWithin] with w hw using
          QuantumZipper.H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hAD hw))⟩)
    have h2 : Tendsto (fun w => trMap W 0 s (fwdMap W s w)) (𝓝[A] z) (𝓝 z) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (by
        filter_upwards [self_mem_nhdsWithin] with w hw using (hFg w (hAD hw)).symm)
    exact tendsto_nhds_unique h1 h2
  refine ⟨G, continuousOn_extendFrom subset_rfl hlim, fun z hz z' hz' h => ?_, hGH, hFG,
    fun z hz hzD => ?_, fun z hz hzD => ?_⟩
  · rw [← hFG z hz, ← hFG z' hz', h]
  · exact extendFrom_eq hz (((hgc z hzD).continuousAt (hDo.mem_nhds hzD)).tendsto.mono_left
      nhdsWithin_le_nhds)
  · by_contra him
    have hGH' : G z ∈ H := lt_of_le_of_ne (hGH z hz) (Ne.symm him)
    exact hzD (by rw [← hFG z hz, hDdef, ← himg]; exact ⟨G z, hGH', rfl⟩)

/-- **A Jordan domain is locally connected at every point of its closure** (from the Schoenflies
disc chart: images of `𝔻 ∩ ball(w, δ)`). -/
theorem isLocConnWithin_of_jordan {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {p : ℂ}
    (hp : p ∈ Γᶜ) (hb : IsBounded (connectedComponentIn Γᶜ p)) {z : ℂ}
    (hz : z ∈ closure (connectedComponentIn Γᶜ p)) :
    IsLocConnWithin (connectedComponentIn Γᶜ p) z := by
  obtain ⟨φ, χ, hφc, hχc, -, hφχ, hχcl, hχD, -, hφball, -, -, -, -⟩ := exists_discChart hΓ hp hb
  set D := connectedComponentIn Γᶜ p with hDdef
  intro ε hε
  set w := χ z with hw
  have hwB : w ∈ closedBall (0 : ℂ) 1 := hχcl hz
  obtain ⟨δ, hδ, hφδ⟩ := Metric.continuousWithinAt_iff.1 (hφc w hwB) ε hε
  have hφw : φ w = z := hφχ z hz
  refine ⟨φ '' (ball 0 1 ∩ ball w δ), fun y hy => ?_, ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := hy
    refine ⟨hφball ▸ mem_image_of_mem φ hv.1, ?_⟩
    rw [mem_ball, ← hφw]
    exact hφδ (ball_subset_closedBall hv.1) hv.2
  · exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected.image _
      (hφc.mono fun v hv => ball_subset_closedBall hv.1)
  · have h1 : χ ⁻¹' ball w δ ∈ 𝓝[D] z :=
      nhdsWithin_mono _ subset_closure ((hχc z hz).preimage_mem_nhdsWithin (ball_mem_nhds w hδ))
    filter_upwards [h1, self_mem_nhdsWithin] with y hy hyD
    exact ⟨χ y, ⟨hχD hyD, hy⟩, hφχ y (subset_closure hyD)⟩

/-- **Local connectivity transfers through `ψ_p`** (`p ∉ Ē`): if `ψ_p(E)` is locally connected at
`ψ_p(z)`, then `E` is locally connected at `z`. -/
theorem isLocConnWithin_of_psiMap {E : Set ℂ} {p : ℝ} (hpE : (p : ℂ) ∉ closure E) {z : ℂ}
    (hz : z ∈ closure E) (h : IsLocConnWithin (psiMap p '' E) (psiMap p z)) :
    IsLocConnWithin E z := by
  have hzp : z ≠ p := fun h' => hpE (h' ▸ hz)
  have hψz : psiMap p z ≠ 0 := fun h' => hzp (psiMap_eq_zero_iff.1 h')
  have hinvc : ContinuousAt (psiMapInv p) (psiMap p z) :=
    continuousOn_psiMapInv.continuousAt (isOpen_compl_singleton.mem_nhds hψz)
  have hψc : ContinuousAt (psiMap p) z :=
    continuousOn_psiMap.continuousAt (isOpen_compl_singleton.mem_nhds hzp)
  intro ε hε
  obtain ⟨ε', hε', hε'z⟩ := Metric.continuousAt_iff.1 hinvc ε hε
  rw [psiMapInv_psiMap] at hε'z
  obtain ⟨A'', hA''sub, hA''pre, hA''l⟩ := h ε' hε'
  have hA''0 : A'' ⊆ {(0 : ℂ)}ᶜ := by
    intro ζ hζ h0
    obtain ⟨y, hy, hye⟩ := (hA''sub hζ).1
    rw [mem_singleton_iff.1 h0] at hye
    exact hpE (psiMap_eq_zero_iff.1 hye ▸ subset_closure hy)
  refine ⟨psiMapInv p '' A'', ?_, hA''pre.image _ (continuousOn_psiMapInv.mono hA''0), ?_⟩
  · rintro _ ⟨ζ, hζ, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (hA''sub hζ).1
    refine ⟨by rw [psiMapInv_psiMap]; exact hy, ?_⟩
    rw [mem_ball]
    exact hε'z (mem_ball.1 (hA''sub hζ).2)
  · have h1 : Tendsto (psiMap p) (𝓝[E] z) (𝓝[psiMap p '' E] (psiMap p z)) :=
      tendsto_nhdsWithin_iff.2 ⟨hψc.tendsto.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun y hy => mem_image_of_mem _ hy⟩
    filter_upwards [h1 hA''l] with y hy
    exact ⟨psiMap p y, hy, psiMapInv_psiMap y⟩

end InteractingSLE.Sec6
