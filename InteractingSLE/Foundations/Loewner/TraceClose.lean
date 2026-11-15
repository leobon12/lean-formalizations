import InteractingSLE.Foundations.Loewner.YuanCorollary13Tip
import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Spec.Dimension.TraceBridge
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Closing a Loewner trace at its horizon

Packet PROVE-TRACECLOSE. Let `W` be a continuous driver with `W 0 = 0`, `σ > 0`, and let `η` be a
continuous path on `[0, σ]` that generates the chain before `σ`: `η 0 = 0` and
`K_t = fill(η[0, t])` for `0 ≤ t < σ` (`IsLoewnerTraceLT W σ η`). Then `η` also generates the chain
at `σ` itself, with its tip there:

* `fwdHull_eq_fillH_of_isLoewnerTraceLT`: `K_σ = fill(η[0, σ])`;
* `tendsto_fwdMapInv_tip_of_isLoewnerTraceLT`: `F_σ(w) → η(σ)` as `w → 0` in `ℍ`.

The landed tip lemma `IsLoewnerTraceLT.tendsto_fwdMapInv_tip` uses the trace *after* the time in
question; at the horizon only the past is available.

## Proof

* **Hull.** `ℍ \ K_σ` is connected, unbounded and misses `η[0, σ]` (its points in `ℍ` before `σ` lie in
  `K_t ⊆ K_σ`, and `K_σ` is relatively closed in `ℍ`), so `fill(η[0, σ]) ⊆ K_σ`; both have half-plane
  capacity `2σ` (`hcap(fill) ≥ hcap(K_t) = 2t` for `t < σ`), and capacity is strictly monotone.
* **Boundary extension.** `F_σ` extends continuously to `ℍ̄` (Carathéodory–Torhorst,
  `exists_continuousOn_extension_of_path_of_tendsto`); let `p` be its value at `0`.
* **Cluster points of the shifted chain lie on its hull** (`mem_closure_fwdHull_of_tendsto_seq`): if
  `F_r(z_n) → c` along `z_n → 0` in `ℍ`, then `c ∈ closure K_r`. Off the hull, the centred Schwarz
  reflection of `G_r` vanishes at `c` and is not locally constant, so by the open mapping theorem `F_r`
  has the full limit `c` at `0`, and `YuanCorollary13.mem_closure_fwdHull_of_tendsto` applies.
* **The tip lies on the recent trace.** Fix `s < σ` and suppose `p ∉ η[s, σ]`; take `ε` with
  `B(p, 2ε) ∩ η[s, σ] = ∅`. With `F''` the inverse map of the chain shifted by `s`, at time `σ − s`,
  `F_σ = F_s ∘ F''` (`RS.fwdMapInv_add_shift`). A cluster point `c` of `F''(i/(n+1))` satisfies
  `F̄_s(c) = p` and `c ∈ closure K''`. By continuity of `F̄_s` at `c`, `F_s` maps a half-disc
  `S = B(c, κ) ∩ ℍ` into `B(p, 2ε) ∩ (ℍ \ K_s) ⊆ ℍ \ η[0, σ]`; `F_s(S)` is connected and meets
  `ℍ \ K_σ` (at the points `F_σ(i/(n+1))`), the unbounded component of `ℍ \ η[0, σ]`, so it lies in it.
  But a point of `S ∩ K''` is sent by `F_s` into `K_σ`. Hence `B(c, κ)` misses `K''`, a contradiction.
* Letting `s ↑ σ`, `p = η(σ)` by continuity of `η` at `σ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace TraceClose

/-! ### Cluster points of the inverse map at the driving point -/

section Cluster

variable {U : ℝ → ℝ}

/-- **Cluster points of `F_r` at the driving point lie in the closure of the hull.** If `r > 0`,
`z_n → 0` in `ℍ` and `F_r(z_n) → c`, then `c ∈ closure K_r` (the sequential form of
`YuanCorollary13.mem_closure_fwdHull_of_tendsto`, which assumes the full limit). -/
theorem mem_closure_fwdHull_of_tendsto_seq (hU : Continuous U) (hU0 : U 0 = 0) {r : ℝ}
    (hr : 0 < r) {z : ℕ → ℂ} (hzH : ∀ n, z n ∈ H) (hz0 : Tendsto z atTop (𝓝 0)) {c : ℂ}
    (hc : Tendsto (fun n => fwdMapInv U r (z n)) atTop (𝓝 c)) : c ∈ closure (fwdHull U r) := by
  have hFH : ∀ n, fwdMapInv U r (z n) ∈ H := fun n =>
    QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hr.le (hzH n)
  have hGF : ∀ n, fwdMap U r (fwdMapInv U r (z n)) = z n := fun n =>
    QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hr.le (hzH n)
  have hcH : c ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hc (Eventually.of_forall hFH)
  by_contra hcK
  by_cases hcH' : c ∈ H
  · -- an interior cluster point would be a point of `ℍ \ K_r` mapped to `0`
    have hcD : c ∈ H \ fwdHull U r := ⟨hcH', fun h => hcK (subset_closure h)⟩
    have hopen : IsOpen (H \ fwdHull U r) := (isHPHull_fwdHull hU hr.le).isOpen
    have hcont : ContinuousAt (fwdMap U r) c :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hU hr.le).differentiableAt
        (hopen.mem_nhds hcD)).continuousAt
    have heq : fwdMap U r c = 0 := by
      refine tendsto_nhds_unique (hcont.tendsto.comp hc) ?_
      simpa only [Function.comp_def, hGF] using hz0
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hr.le hcD
    rw [heq] at this
    exact lt_irrefl 0 (show (0 : ℝ) < (0 : ℂ).im from this)
  -- a real cluster point with a hull-free neighbourhood
  have hc0 : c.im = 0 := le_antisymm (not_lt.1 hcH') hcH
  set y := c.re with hy
  have hcy : c = (y : ℂ) := InteractingSLE.eq_ofReal_re_of_im_eq_zero hc0
  obtain ⟨κ, hκ, hκsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl c hcK
  have hdr : Disjoint (ball (y : ℂ) κ) (fwdHull U r) := by
    rw [← hcy]
    exact Set.disjoint_left.2 fun w hw hwK => hκsub hw (subset_closure hwK)
  obtain ⟨K, hKd, hKeq, hKc, hKr, hKt⟩ :=
    YuanCorollary13.exists_centred_reflection hU hU0 hr.le hdr
  have hyb : (y : ℂ) ∈ ball (y : ℂ) (κ / 2) := mem_ball_self (by positivity)
  have hbD : ∀ w ∈ ball (y : ℂ) (κ / 2), w ∈ H → w ∈ H \ fwdHull U r := fun w hw hwH =>
    ⟨hwH, fun h => Set.disjoint_left.1 hdr (ball_subset_ball (by linarith) hw) h⟩
  -- `K y = 0`
  rw [hcy] at hc
  have hFS : Tendsto (fun n => fwdMapInv U r (z n)) atTop
      (𝓝[ball (y : ℂ) (κ / 2) ∩ H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc, ?_⟩
    filter_upwards [hc (isOpen_ball.mem_nhds hyb)] with n hn
    exact ⟨hn, hFH n⟩
  have hKy : K y = 0 := by
    refine tendsto_nhds_unique ((hKt y hyb (by simp)).comp hFS) ?_
    simpa only [Function.comp_def, hGF] using hz0
  -- `K` is not locally constant at `y`
  have hKa : AnalyticAt ℂ K (y : ℂ) := hKd.analyticAt (isOpen_ball.mem_nhds hyb)
  have hnc : ¬ ∀ᶠ w in 𝓝 (y : ℂ), K w = K y := by
    intro h
    have hne : (𝓝[H] (y : ℂ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
      exact hcy ▸ hcH
    have h1 : ∀ᶠ w in 𝓝[H] (y : ℂ), K w = K y := h.filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ w in 𝓝[H] (y : ℂ), w ∈ ball (y : ℂ) (κ / 2) :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hyb)
    have h3 : ∀ᶠ w in 𝓝[H] (y : ℂ), w ∈ H := self_mem_nhdsWithin
    obtain ⟨w, hw, hwH, hwb⟩ := (h1.and (h3.and h2)).exists
    rw [hKy, hKeq ⟨hwb, hwH⟩] at hw
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hr.le (hbD w hwb hwH)
    rw [hw] at this
    exact lt_irrefl 0 (show (0 : ℝ) < (0 : ℂ).im from this)
  have hmap : 𝓝 (K y) ≤ map K (𝓝 (y : ℂ)) :=
    hKa.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
  rw [hKy] at hmap
  -- hence `F_r(w) → y` as `w → 0` in `ℍ`
  have htend : Tendsto (fwdMapInv U r) (𝓝[H] 0) (𝓝 (y : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < min ε (κ / 2) := lt_min hε (by positivity)
    have hball : K '' ball (y : ℂ) (min ε (κ / 2)) ∈ 𝓝 (0 : ℂ) :=
      hmap (image_mem_map (ball_mem_nhds _ hε'))
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with w hw hwH
    obtain ⟨ζ, hζ, hKζ⟩ := hw
    have hζb : ζ ∈ ball (y : ℂ) (κ / 2) := ball_subset_ball (min_le_right _ _) hζ
    have hwH' : (0 : ℝ) < w.im := hwH
    have hζH : 0 < ζ.im := by
      by_cases h0 : ζ.im = 0
      · have := hKr ζ hζb h0
        rw [hKζ] at this
        linarith
      · exact ((YuanCorollary13.im_pos_of_centred_reflection hU hr.le hdr hKeq hKc hζb
          h0).1).2 (hKζ ▸ hwH)
    have hGζ : fwdMap U r ζ = w := (hKeq ⟨hζb, hζH⟩).symm.trans hKζ
    rw [← hGζ, QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hr.le (hbD ζ hζb hζH)]
    exact lt_of_lt_of_le (mem_ball.1 hζ) (min_le_left _ _)
  exact hcK (hcy ▸ YuanCorollary13.mem_closure_fwdHull_of_tendsto hU hU0 hr htend)

end Cluster

/-! ### Strict monotonicity of half-plane capacity -/

/-- A hull inside another one with at least its capacity is equal to it (`hcap` is strictly
monotone: `hcap(B) = hcap(g_A(B \ A)) + hcap(A)` and only the empty hull has capacity `0`). -/
theorem eq_of_subset_of_hcap_le {A B : HPHull} (hAB : A.1 ⊆ B.1) (h : B.hcap ≤ A.hcap) :
    A.1 = B.1 := by
  obtain ⟨g, hg⟩ := A.2.exists_isMapOut
  have he := HPHull.hcap_eq_add hAB hg
  set C : HPHull := ⟨g '' (B.1 \ A.1), hg.isHPHull_image A.2 B.2 hAB⟩ with hC
  have hC0 : C.hcap = 0 := le_antisymm (by linarith) C.hcap_nonneg
  have hCe : C.1 = ∅ := (C.hcap_eq_zero_iff).1 hC0
  refine Subset.antisymm hAB fun z hz => ?_
  by_contra hzA
  have hmem : g z ∈ C.1 := ⟨z, ⟨hz, hzA⟩, rfl⟩
  rw [hCe] at hmem
  exact hmem

/-! ### The hull at the horizon -/

section Hull

variable {W : ℝ → ℝ} {σ : ℝ} {η : ℝ → ℂ}

/-- The points of the path in `ℍ` lie in the hull at the horizon (before `σ` they lie in `K_t ⊆ K_σ`;
`K_σ` is relatively closed in `ℍ`). -/
theorem mem_fwdHull_of_mem_H (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W) (hσ : 0 < σ)
    (hησ : ContinuousOn η (Icc 0 σ)) {u : ℝ} (hu : u ∈ Icc 0 σ) (huH : η u ∈ H) :
    η u ∈ fwdHull W σ := by
  have hlt : ∀ v ∈ Ico 0 σ, η v ∈ H → η v ∈ fwdHull W σ := fun v hv hvH => by
    have h1 : η v ∈ fwdHull W v := by
      rw [hη.2.2 v hv.1 hv.2]
      exact mem_fillH_of_mem_closure hvH (subset_closure ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩)
    exact fwdHull_mono' hv.2.le h1
  rcases hu.2.lt_or_eq with h | h
  · exact hlt u ⟨hu.1, h⟩ huH
  rw [h] at huH ⊢
  by_contra hn
  have hopen : IsOpen (H \ fwdHull W σ) := (isHPHull_fwdHull hW hσ.le).isOpen
  have hev : ∀ᶠ v in 𝓝[Icc 0 σ] σ, η v ∈ H \ fwdHull W σ :=
    (hησ σ ⟨hσ.le, le_rfl⟩) (hopen.mem_nhds ⟨huH, hn⟩)
  have hne : (𝓝[Ico 0 σ] σ).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hσ]; infer_instance
  have hev' : ∀ᶠ v in 𝓝[Ico 0 σ] σ, η v ∈ H \ fwdHull W σ ∧ v ∈ Ico 0 σ :=
    (hev.filter_mono (nhdsWithin_mono _ Ico_subset_Icc_self)).and self_mem_nhdsWithin
  obtain ⟨v, hv, hvI⟩ := hev'.exists
  exact hv.2 (hlt v hvI hv.1)

/-- **The hull at the horizon is the filling of the closed trace**: `K_σ = fill(η[0, σ])`. -/
theorem fwdHull_eq_fillH_of_isLoewnerTraceLT (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) :
    fwdHull W σ = fillH (η '' Icc 0 σ) := by
  set A := η '' Icc 0 σ with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hησ
  have hAH : IsHPHull (fillH A) := by
    refine isHPHull_fillH_of_isPreconnected hAc.isBounded ?_
    refine IsPreconnected.union (η 0) ⟨0, ⟨le_rfl, hσ.le⟩, rfl⟩ ?_
      (isPreconnected_Icc.image _ hησ) isPreconnected_lowerHalf
    show (η 0).im ≤ 0
    rw [hη.1, zero_im]
  have hKH : IsHPHull (fwdHull W σ) := isHPHull_fwdHull hW hσ.le
  -- `fill(η[0, σ]) ⊆ K_σ`
  have hsub : fillH A ⊆ fwdHull W σ := by
    have h1 : H \ fwdHull W σ ⊆ H \ fillH A := by
      refine subset_H_diff_fillH_of_isPreconnected hAc.isBounded
        (QuantumZipper.RS.isPreconnected_compl_fwdHull hW hW0 hσ.le) ?_ ?_
      · rintro z ⟨hzH, hzK⟩
        refine ⟨hzH, fun hzA => hzK ?_⟩
        rw [hAc.isClosed.closure_eq] at hzA
        obtain ⟨u, hu, rfl⟩ := hzA
        exact mem_fwdHull_of_mem_H hη hW hσ hησ hu hzH
      · intro hb
        refine not_isBounded_setOf_lt_im 0 ((hb.union hKH.2.1).subset fun z hz => ?_)
        by_cases h : z ∈ fwdHull W σ
        · exact Or.inr h
        · exact Or.inl ⟨hz, h⟩
    intro z hz
    by_contra hzK
    exact (h1 ⟨hAH.1 hz, hzK⟩).2 hz
  -- `hcap(fill(η[0, σ])) ≥ 2σ = hcap(K_σ)`
  have hge : ∀ t : ℝ, 0 ≤ t → t < σ → 2 * t ≤ HPHull.hcap ⟨fillH A, hAH⟩ := by
    intro t ht htσ
    rw [← hcap_fwdHull hW hW0 ht]
    refine HPHull.hcap_mono ?_
    show fwdHull W t ⊆ fillH A
    rw [hη.2.2 t ht htσ]
    exact fillH_mono (image_mono (Icc_subset_Icc_right htσ.le))
  have hcap : HPHull.hcap ⟨fwdHull W σ, hKH⟩ ≤ HPHull.hcap ⟨fillH A, hAH⟩ := by
    rw [hcap_fwdHull hW hW0 hσ.le]
    by_contra hlt
    push Not at hlt
    have h0 := HPHull.hcap_nonneg ⟨fillH A, hAH⟩
    set c := HPHull.hcap ⟨fillH A, hAH⟩
    have := hge ((c / 2 + σ) / 2) (by positivity) (by linarith)
    linarith
  exact (eq_of_subset_of_hcap_le (A := ⟨fillH A, hAH⟩) (B := ⟨fwdHull W σ, hKH⟩) hsub hcap).symm

end Hull

/-! ### The tip at the horizon -/

section Tip

variable {W : ℝ → ℝ} {σ : ℝ} {η : ℝ → ℂ}

/-- **Boundary extension at the horizon**: `F_σ` has a limit at every point of `ℍ̄`
(Carathéodory–Torhorst for the path complement `ℍ \ fill(η[0, σ]) = ℍ \ K_σ`). -/
theorem hasBdryLimits_of_isLoewnerTraceLT (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) :
    HasBdryLimits (fwdMapInv W σ) := by
  set γ : ℝ → ℂ := fun s => clipH (η s) with hγ
  have hγc : ContinuousOn γ (Icc 0 σ) := continuous_clipH.comp_continuousOn hησ
  have hγH : MapsTo γ (Icc 0 σ) Hbar := fun s _ => clipH_mem_Hbar _
  have hAc : IsCompact (η '' Icc 0 σ) := isCompact_Icc.image_of_continuousOn hησ
  have hfill : fillH (γ '' Icc 0 σ) = fwdHull W σ := by
    rw [fwdHull_eq_fillH_of_isLoewnerTraceLT hη hW hW0 hσ hησ]
    apply fillH_congr
    have hc1 : IsCompact (γ '' Icc 0 σ) := isCompact_Icc.image_of_continuousOn hγc
    rw [hc1.isClosed.closure_eq, hAc.isClosed.closure_eq]
    rw [show γ '' Icc 0 σ = clipH '' (η '' Icc 0 σ) from (image_image clipH η _).symm]
    exact image_clipH_inter_H _
  have hψ : IsConformalBijection (fwdMapInv W σ) H (H \ fillH (γ '' Icc 0 σ)) := by
    rw [hfill]; exact isConformalBijection_fwdMapInv hW hW0 hσ.le
  obtain ⟨F, hFeq, hFc, -, -⟩ := exists_continuousOn_extension_of_path_of_tendsto hγc hγH hψ
    (tendsto_fwdMapInv_cobounded hW hW0 hσ.le)
  intro x hx
  refine ⟨F x, ?_⟩
  have h1 : Tendsto F (𝓝[H] x) (𝓝 (F x)) := (hFc x hx).mono H_subset_Hbar
  exact h1.congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)

/-- **The tip at the horizon lies on the recent trace**: for `0 ≤ s < σ`, the boundary value
`F̄_σ(0)` lies in `η([s, σ])`. -/
theorem extendFrom_zero_mem_image (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) {s : ℝ} (hs : 0 ≤ s)
    (hsσ : s < σ) : extendFrom H (fwdMapInv W σ) 0 ∈ η '' Icc s σ := by
  set p := extendFrom H (fwdMapInv W σ) 0 with hp
  have hlim : Tendsto (fwdMapInv W σ) (𝓝[H] 0) (𝓝 p) :=
    (hasBdryLimits_of_isLoewnerTraceLT hη hW hW0 hσ hησ).tendsto zero_mem_Hbar
  have hAc : IsClosed (η '' Icc s σ) :=
    (isCompact_Icc.image_of_continuousOn (hησ.mono (Icc_subset_Icc_left hs))).isClosed
  by_contra hpA
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 hAc.isOpen_compl p hpA
  -- the chain shifted by `s`, at time `u = σ − s`
  set V := shiftDrive W s with hV
  have hVc : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW s
  have hV0 : V 0 = 0 := QuantumZipper.RS.shiftDrive_zero W s
  set u := σ - s with hu
  have hu0 : 0 < u := sub_pos.2 hsσ
  have hsu : s + u = σ := by rw [hu]; ring
  -- the points `z n = i/(n+1)` and a convergent subsequence of their `F''`-images
  set z : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hz
  have hzH : ∀ n, z n ∈ H := fun n => QuantumZipper.RS.mul_I_mem_H (by positivity)
  have hz0 : Tendsto z atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hz] using h1.mul_const I
  have hFH' : ∀ n, fwdMapInv V u (z n) ∈ H := fun n =>
    QuantumZipper.RS.fwdMapInv_mem_H hVc hV0 hu0.le (hzH n)
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hVc hV0 hu0.le
  have hbdd : ∀ n, fwdMapInv V u (z n) ∈ closedBall (0 : ℂ) (C + 1) := fun n => by
    rw [mem_closedBall_zero_iff]
    have h1 := hC (z n) (hzH n)
    have h2 : ‖z n‖ ≤ 1 := by
      rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [norm_le_norm_add_norm_sub' (fwdMapInv V u (z n)) (z n)]
  obtain ⟨c, -, φ, hφ, hcφ⟩ := tendsto_subseq_of_bounded isBounded_closedBall hbdd
  have hz'0 : Tendsto (z ∘ φ) atTop (𝓝 0) := hz0.comp hφ.tendsto_atTop
  have hcK : c ∈ closure (fwdHull V u) :=
    mem_closure_fwdHull_of_tendsto_seq hVc hV0 hu0 (fun n => hzH (φ n)) hz'0 hcφ
  have hcH : c ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hcφ (Eventually.of_forall fun n => hFH' (φ n))
  -- `F̄_s` is continuous on `ℍ̄` and `F̄_s(c) = p`
  have hFsc : ContinuousOn (extendFrom H (fwdMapInv W s)) Hbar :=
    (hη.hasBdryLimits hW hW0 hs hsσ).continuousOn
  have hFsH : ∀ w ∈ H, extendFrom H (fwdMapInv W s) w = fwdMapInv W s w := fun w hw =>
    extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hs) hw
  have hcomp : ∀ w ∈ H, fwdMapInv W σ w = fwdMapInv W s (fwdMapInv V u w) := fun w hw => by
    rw [← hsu]; exact QuantumZipper.RS.fwdMapInv_add_shift hW hW0 hs hu0.le hw
  have hpc : extendFrom H (fwdMapInv W s) c = p := by
    have h1 : Tendsto (fun n => fwdMapInv W σ (z (φ n))) atTop (𝓝 p) :=
      hlim.comp (tendsto_nhdsWithin_iff.2 ⟨hz'0, Eventually.of_forall fun n => hzH (φ n)⟩)
    have h2 : Tendsto (fun n => extendFrom H (fwdMapInv W s) (fwdMapInv V u (z (φ n)))) atTop
        (𝓝 (extendFrom H (fwdMapInv W s) c)) :=
      (hFsc c hcH).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hcφ, Eventually.of_forall fun n => H_subset_Hbar (hFH' (φ n))⟩)
    refine tendsto_nhds_unique h2 (h1.congr fun n => ?_)
    rw [hcomp _ (hzH _), hFsH _ (hFH' _)]
  -- a half-disc `S` about `c` is mapped by `F_s` into `B(p, ε)`
  obtain ⟨κ, hκ, hκF⟩ := Metric.continuousWithinAt_iff.1 (hFsc c hcH) ε hε
  set S := ball c κ ∩ H with hS
  have hSc : IsPreconnected S := ((convex_ball c κ).inter convex_H).isPreconnected
  set P := η '' Icc 0 σ with hP
  have hFS : MapsTo (fwdMapInv W s) S (H \ P) := by
    intro w hw
    have hwD := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hs hw.2
    refine ⟨hwD.1, ?_⟩
    rintro ⟨v, hv, hvw⟩
    rcases le_or_gt v s with hvs | hvs
    · apply hwD.2
      rw [hη.2.2 s hs hsσ, ← hvw]
      exact mem_fillH_of_mem_closure (hvw ▸ hwD.1) (subset_closure ⟨v, ⟨hv.1, hvs⟩, rfl⟩)
    · have hd := hκF (H_subset_Hbar hw.2) hw.1
      rw [hpc, hFsH w hw.2, ← hvw] at hd
      exact hεA (mem_ball.2 hd) ⟨v, ⟨hvs.le, hv.2⟩, rfl⟩
  have hFSc : IsPreconnected (fwdMapInv W s '' S) :=
    hSc.image _ ((continuousOn_fwdMapInv hW hW0 hs).mono inter_subset_right)
  -- `ℍ \ K_σ` is the unbounded component of `ℍ \ η[0, σ]`
  have hPc : IsCompact P := isCompact_Icc.image_of_continuousOn hησ
  obtain ⟨R, hR, hPR⟩ := exists_closure_subset_ball hPc.isBounded
  have hD : H \ fwdHull W σ = connectedComponentIn (H \ P) (((R + 1 : ℝ) : ℂ) * I) := by
    rw [fwdHull_eq_fillH_of_isLoewnerTraceLT hη hW hW0 hσ hησ, H_diff_fillH hR hPR,
      hPc.isClosed.closure_eq]
  -- `F_s(S)` meets `ℍ \ K_σ`, hence lies in it
  have hev : ∀ᶠ n in atTop, fwdMapInv V u (z (φ n)) ∈ S := by
    filter_upwards [hcφ (isOpen_ball.mem_nhds (mem_ball_self hκ))] with n hn
    exact ⟨hn, hFH' _⟩
  obtain ⟨n, hn⟩ := hev.exists
  have hnD : fwdMapInv W s (fwdMapInv V u (z (φ n))) ∈ H \ fwdHull W σ := by
    rw [← hcomp _ (hzH _)]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hσ.le (hzH _)
  have hsubD : fwdMapInv W s '' S ⊆ H \ fwdHull W σ := by
    rw [hD] at hnD ⊢
    rw [connectedComponentIn_eq hnD]
    exact hFSc.subset_connectedComponentIn ⟨_, hn, rfl⟩ hFS.image_subset
  -- so the ball about `c` misses the shifted hull
  have hSK : Disjoint (ball c κ) (fwdHull V u) := by
    refine Set.disjoint_left.2 fun w hwb hwK => ?_
    have hwH : w ∈ H := (isHPHull_fwdHull hVc hu0.le).1 hwK
    have hFw := hsubD ⟨w, ⟨hwb, hwH⟩, rfl⟩
    obtain ⟨w', hw'H, hw'⟩ := (isConformalBijection_fwdMapInv hW hW0 hσ.le).2.surjOn hFw
    rw [hcomp w' hw'H] at hw'
    have hww : fwdMapInv V u w' = w := (isConformalBijection_fwdMapInv hW hW0 hs).2.injOn
      (QuantumZipper.RS.fwdMapInv_mem_H hVc hV0 hu0.le hw'H) hwH hw'
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hVc hV0 hu0.le hw'H).2 (hww ▸ hwK)
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hcK (ball c κ) isOpen_ball (mem_ball_self hκ)
  exact Set.disjoint_left.1 hSK hw1 hw2

/-- **The boundary value of `F̄_σ` at the driving point is the endpoint of the trace.** -/
theorem extendFrom_zero_eq (hη : IsLoewnerTraceLT W σ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) :
    extendFrom H (fwdMapInv W σ) 0 = η σ := by
  set p := extendFrom H (fwdMapInv W σ) 0 with hp
  have h : ∀ n : ℕ, ∃ v ∈ Icc (σ - σ / ((n : ℝ) + 1)) σ, η v = p := fun n => by
    have hd : 0 < σ / ((n : ℝ) + 1) := by positivity
    have hd' : σ / ((n : ℝ) + 1) ≤ σ := div_le_self hσ.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    obtain ⟨v, hv, hvp⟩ := extendFrom_zero_mem_image hη hW hW0 hσ hησ (s := σ - σ / ((n : ℝ) + 1))
      (by linarith) (by linarith)
    exact ⟨v, hv, hvp⟩
  choose v hv hvp using h
  have hlow : Tendsto (fun n : ℕ => σ - σ / ((n : ℝ) + 1)) atTop (𝓝 σ) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul σ
    rw [mul_zero] at h1
    have h2 := (tendsto_const_nhds (x := σ)).sub h1
    rw [sub_zero] at h2
    refine h2.congr fun n => ?_
    rw [mul_one_div]
  have hvt : Tendsto v atTop (𝓝[Icc 0 σ] σ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le hlow
      tendsto_const_nhds (fun n => (hv n).1) (fun n => (hv n).2), Eventually.of_forall fun n => ?_⟩
    refine ⟨le_trans ?_ (hv n).1, (hv n).2⟩
    have hd' : σ / ((n : ℝ) + 1) ≤ σ := div_le_self hσ.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    linarith
  have h1 := (hησ σ ⟨hσ.le, le_rfl⟩).tendsto.comp hvt
  have h2 : (η ∘ v) = fun _ => p := funext fun n => hvp n
  rw [h2] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

/-- **The tip at the horizon**: `F_σ(w) → η(σ)` as `w → 0` in `ℍ`. -/
theorem tendsto_fwdMapInv_tip_of_isLoewnerTraceLT (hη : IsLoewnerTraceLT W σ η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 < σ) (hησ : ContinuousOn η (Icc 0 σ)) :
    Tendsto (fwdMapInv W σ) (𝓝[H] 0) (𝓝 (η σ)) := by
  have h := (hasBdryLimits_of_isLoewnerTraceLT hη hW hW0 hσ hησ).tendsto zero_mem_Hbar
  rwa [extendFrom_zero_eq hη hW hW0 hσ hησ] at h

end Tip

end TraceClose

end InteractingSLE
