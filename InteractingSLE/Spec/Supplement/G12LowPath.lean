/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowLim
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Supplement.G12RemSwallow

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the picture at a first visit (pathwise)

Packet PROVE-G12C. Supplement §7.9, proof of Lemma G12 ("Suppose first that there is a final time interval with no
original-real contact before `τ` … The outward height has cumulative weight `S_j > d_*`. The strengthened G4 excludes
this endpoint."). One path of an integrated `SLE_κ(ρ)` evolution with a continuous injective generating trace; a right
mark `y = x_{j₀}`, the last right mark `x_k ∈ (0, y)` below it, and cumulative weight `S' = Σ_{x_i < y} ρ_i ≤ −2`.
At the first visit `t₀` of `y`:

* the inner gap `V^k − W` is positive on `[0, t₀)` (`gap_pos_of_first_visit`): a collision of `V^k` with the driver
  before `t₀` is a continuation threshold (the marks below `y` carry weight `S' ≤ −2`; `y` itself is not yet
  swallowed, `G12RemSwallow.trace_ne_of_gap_eq_zero`);
* there is a final contact-free interval before `t₀` (GB7a's first real contact after a rational time `p`: a contact
  in `(x_k, y)` would make `V^k` meet the driver, a contact beyond `y` would make `V^y` meet it; both are excluded by
  the positivity of the gaps before `t₀`), no mark meets the driver on it, and in the chart at a rational `q` the drift
  difference to the two-mark reference has bounded energy (`GB7a.exists_energy_bound_of_restart`: the weights between
  the driver and the target are those of the marks below `y` minus `S'`, summing to `0`).

Hence the picture `LowPic` holds at some rational `q` up to `t₀` (`lowPic_of_first_visit`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open GB7a

variable {nL nR : ℕ} {Ω : Type*} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {k j₀ : Fin nR} {S : ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {η : ℝ≥0 → ℂ}

/-- The collided marks at a collision of the last mark below `y`: exactly the marks below `y`. -/
theorem filter_collided_eq (h : Sec2.IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω)) (hord : IsOrderedForceWord xL xR)
    (hnext : ∀ j, xR j < xR j₀ → xR j ≤ xR k) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω)
    (hk : VR k t ω = W t ω) (hu : W t ω < VR j₀ t ω) :
    univ.filter (fun j => VR j t ω = W t ω) = univ.filter (fun j => xR j < xR j₀) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    by_contra hjy
    push Not at hjy
    -- `x_j ≥ y`: `V^j ≥ V^{j₀} > W`
    have hle : VR j₀ t ω ≤ VR j t ω := by
      rcases hjy.lt_or_eq with hlt | heq
      · exact h.monotone_vR ht (not_lt.1 fun hji => absurd hlt (not_lt.2 (hord.2.2.1 hji.le)))
      · exact (G12.eq_of_forceEq_right h heq ht).le
    linarith
  · intro hj
    have hjk := hnext j hj
    have hle : VR j t ω ≤ VR k t ω := by
      rcases hjk.lt_or_eq with hlt | heq
      · exact h.monotone_vR ht (not_lt.1 fun hkj => absurd hlt (not_lt.2 (hord.2.2.1 hkj.le)))
      · exact (G12.eq_of_forceEq_right h heq ht).le
    exact le_antisymm (hle.trans hk.le) (h.w_le_vR ht j)

/-- **Before the first visit the inner gap is positive** (for `S' ≤ −2`). -/
theorem gap_pos_of_first_visit (h : Sec2.IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω)) (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace (W · ω) (ζ ω) η)
    (hkjx : xR k < xR j₀) (hnext : ∀ j, xR j < xR j₀ → xR j ≤ xR k)
    (hS : ∑ i ∈ univ.filter (fun i => xR i < xR j₀), ρR i ≤ -2) {t₀ : ℝ≥0} (ht₀ζ : (t₀ : ℝ≥0∞) ≤ ζ ω)
    (hvis : η t₀ = xR j₀) (hfirst : ∀ s < t₀, η s ≠ xR j₀) :
    (∀ t < t₀, W t ω < VR j₀ t ω) ∧ ∀ t < t₀, W t ω < VR k t ω := by
  have hy : 0 < xR j₀ := lt_of_le_of_lt (hord.2.2.2 k) hkjx
  have hltζ : ∀ s : ℝ≥0, s < t₀ → (s : ℝ≥0∞) < ζ ω := fun s hs =>
    (ENNReal.coe_lt_coe.2 hs).trans_le ht₀ζ
  have hu : ∀ t < t₀, W t ω < VR j₀ t ω := by
    intro s hs
    refine lt_of_le_of_ne (h.w_le_vR (hltζ s hs) j₀) fun he => ?_
    exact G12.trace_ne_of_gap_eq_zero h hη hy (hltζ s hs) he.symm
      (fun s' hs' => hfirst s' (lt_of_le_of_lt hs' hs)) t₀ ht₀ζ hvis
  refine ⟨hu, fun t ht => lt_of_le_of_ne (h.w_le_vR (hltζ t ht) k) fun he => ?_⟩
  have hthr := h.not_threshold (hltζ t ht)
  apply hthr
  right
  rw [filter_collided_eq h hord hnext (hltζ t ht) he.symm (hu t ht)]
  exact hS

/-- **The picture at the first visit (one path).** With a continuous generating trace injective up to the lifetime and
the convergence of the state at a finite positive lifetime (Aux. lemma 3), at the first visit `t₀` of the mark
`y = x_{j₀}` (last mark below it `x_k ≥ 0`, `S' = Σ_{x_i < y} ρ_i ≤ −2`, reference weight `S = S'` at `k`), the picture
`LowPic` holds at some rational restart time `q ∈ (0, t₀)` up to `t₀`. -/
theorem lowPic_of_first_visit (hκ : 0 < κ) (h : Sec2.IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω)) (hord : IsOrderedForceWord xL xR)
    (hη : IsGeneratingTrace (W · ω) (ζ ω) η) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω})
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hkjx : xR k < xR j₀) (hnext : ∀ j, xR j < xR j₀ → xR j ≤ xR k)
    (hSdef : S = ∑ i ∈ univ.filter (fun i => xR i < xR j₀), ρR i) (hS : S ≤ -2)
    {t₀ : ℝ≥0} (ht₀ζ : (t₀ : ℝ≥0∞) ≤ ζ ω) (hvis : η t₀ = xR j₀) (hfirst : ∀ s < t₀, η s ≠ xR j₀) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < t₀ ∧ ∃ C : ℕ,
      LowPic κ ρL xR ρR k j₀ S W VL VR ζ (q : ℝ).toNNReal C ω t₀ := by
  set w : ℝ≥0 → ℝ := (W · ω) with hwdef
  set vL : Fin nL → ℝ≥0 → ℝ := fun i t => VL i t ω with hvLdef
  set vR : Fin nR → ℝ≥0 → ℝ := fun j t => VR j t ω with hvRdef
  have hwc := h.continuousOn_w
  have hw0 := h.w_zero
  have hxk : 0 ≤ xR k := hord.2.2.2 k
  have hy0 : 0 < xR j₀ := lt_of_le_of_lt hxk hkjx
  obtain ⟨hupos, hopos⟩ := gap_pos_of_first_visit h hord hη hkjx hnext (hSdef ▸ hS) ht₀ζ hvis hfirst
  have hltζ₀ : ∀ s : ℝ≥0, s < t₀ → (s : ℝ≥0∞) < ζ ω := fun s hs =>
    (ENNReal.coe_lt_coe.2 hs).trans_le ht₀ζ
  have hy : xR j₀ ∈ Ioo (xR k) (xR j₀ + 1) := ⟨hkjx, by linarith⟩
  obtain ⟨p, T, y', hp0, hpT, hTt₀, hy', hηT, hH⟩ := exists_firstContact hη hwc hw0 hxk ht₀ζ hy hvis
  have hTζ : (T : ℝ≥0∞) ≤ ζ ω := (ENNReal.coe_le_coe.2 hTt₀).trans ht₀ζ
  have hT0 : 0 < T := NNReal.coe_pos.1 (hp0.trans hpT)
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hpT
  have hq0 : 0 < (q : ℝ) := hp0.trans hpq
  have hqN : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  obtain ⟨U, hU, hU0, hUw, hlimV⟩ := exists_driver h hTζ hT0 hlimζ
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR : IsLoewnerTraceLT U T ηR := isLoewnerTraceLT_of_agree hη hTζ hUw
  have hltζ : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ ω := fun t ht =>
    (ENNReal.coe_lt_coe.2 ht).trans_le hTζ
  set ûR : Fin nR → ℝ → ℝ := fun j r => vR j r.toNNReal - w r.toNNReal with hûR
  set ûL : Fin nL → ℝ → ℝ := fun i r => vL i r.toNNReal - w r.toNNReal with hûL
  have pkgR := fun j (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => centredPkg hwc (h.continuousOn_vR j)
    (fun t ht => h.integrable_gapR ht j) (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hTζ hUw hs0 hsT
  have pkgL := fun i (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => centredPkg hwc (h.continuousOn_vL i)
    (fun t ht => h.integrable_gapL ht i) (fun t ht => h.vL_eq ht i) (h.volume_collisionL i) hTζ hUw hs0 hsT
  -- no force coordinate meets the driver on `[p, T)`
  have hoffR : ∀ t : ℝ≥0, (p : ℝ) ≤ t → t < T → ∀ j, w t ≠ vR j t := by
    intro t hpt htT j heq
    have htT' : (t : ℝ) < T := NNReal.coe_lt_coe.2 htT
    obtain ⟨hc, hue, hi, hn⟩ := pkgR j t t.coe_nonneg htT'
    obtain ⟨x, hx, -, -⟩ := hηR.exists_tip_real_of_collision_right hU hU0 t.coe_nonneg htT' hc
      (fun s hs => sub_nonneg.2 (h.w_le_vR (hltζ _ (lt_of_le_of_lt
        (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2) htT)) j)) hue hi hn
      (by simp [heq])
    have hHt := hH t hpt htT
    have : (η t).im = 0 := by
      have hx' : η t = x := by simpa [hηRdef] using hx
      rw [hx', Complex.ofReal_im]
    exact absurd this (ne_of_gt hHt)
  have hoffL : ∀ t : ℝ≥0, (p : ℝ) ≤ t → t < T → ∀ i, w t ≠ vL i t := by
    intro t hpt htT i heq
    have htT' : (t : ℝ) < T := NNReal.coe_lt_coe.2 htT
    obtain ⟨hc, hue, hi, hn⟩ := pkgL i t t.coe_nonneg htT'
    obtain ⟨x, hx, -, -⟩ := hηR.exists_tip_real_of_collision_left hU hU0 t.coe_nonneg htT' hc
      (fun s hs => sub_nonpos.2 (h.vL_le_w (hltζ _ (lt_of_le_of_lt
        (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2) htT)) i)) hue hi hn
      (by simp [heq])
    have hHt := hH t hpt htT
    have : (η t).im = 0 := by
      have hx' : η t = x := by simpa [hηRdef] using hx
      rw [hx', Complex.ofReal_im]
    exact absurd this (ne_of_gt hHt)
  have hy'0 : 0 < y' := lt_of_le_of_lt hxk hy'.1
  have hqT' : (q : ℝ) < T := hqT
  -- the trace on `(q, T)`
  have hHR : ∀ s ∈ Ioo (q : ℝ) T, ηR s ∈ H := fun s hs => by
    have hs0 : 0 ≤ s := (hq0.trans hs.1).le
    refine hH s.toNNReal ?_ ?_
    · rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.2
  have hmemζ : ∀ r : ℝ, r ≤ T → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := fun r hr =>
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr)).trans hTζ
  have hinjR : ∀ s ∈ Ioo (q : ℝ) T, ηR s ∉ ηR '' Icc 0 q := by
    rintro s hs ⟨r, hr, hrs⟩
    have hrs' := hinj (hmemζ r (hr.2.trans hqT'.le)) (hmemζ s hs.2.le) hrs
    have hs0 : 0 ≤ s := (hq0.trans hs.1).le
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrs'
    simp only [Real.coe_toNNReal _ hr.1, Real.coe_toNNReal _ hs0] at this
    linarith [hr.2, hs.1]
  have hyq : (y' : ℂ) ∉ ηR '' Icc 0 q := by
    rintro ⟨r, hr, hry⟩
    rw [← hηT] at hry
    have hrT := hinj (hmemζ r (hr.2.trans hqT'.le)) hTζ hry
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrT
    simp only [Real.coe_toNNReal _ hr.1] at this
    linarith [hr.2]
  have hlimR : Tendsto ηR (𝓝[<] (T : ℝ)) (𝓝 (y' : ℂ)) := by
    rw [← hηT]
    exact tendsto_comp_toNNReal hη hTζ hT0
  -- the limit point is alive at `q`; order of the right marks in the chart
  obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart hηR hU hU0 hq0.le hqT' hHR hinjR hy'0.ne' hlimR hyq
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_re_of_isForwardSol hU hU0 hy'0 hq0.le hv
  have hV : 0 < (v q).re := hc₁.trans_le (hc₁le q ⟨hq0.le, le_rfl⟩)
  have hsT : ∀ s : ℝ, 0 ≤ s → s < T → s.toNNReal < T := fun s hs0 hsT => by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hsT
  have hnnR : ∀ j, ∀ s : ℝ, 0 ≤ s → s < T → 0 ≤ ûR j s := fun j s hs0 hsT' =>
    sub_nonneg.2 (h.w_le_vR (hltζ _ (hsT s hs0 hsT')) j)
  have hnpL : ∀ i, ∀ s : ℝ, 0 ≤ s → s < T → ûL i s ≤ 0 := fun i s hs0 hsT' =>
    sub_nonpos.2 (h.vL_le_w (hltζ _ (hsT s hs0 hsT')) i)
  have hneR : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ûR j s ≠ 0 := by
    intro j s hs h0
    have hs0 : 0 ≤ s := hq0.le.trans hs.1
    refine hoffR s.toNNReal (by rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]) (hsT s hs0 hs.2) j ?_
    simp only [hûR] at h0
    linarith
  have hneL : ∀ i, ∀ s ∈ Ico (q : ℝ) T, ûL i s ≠ 0 := by
    intro i s hs h0
    have hs0 : 0 ≤ s := hq0.le.trans hs.1
    refine hoffL s.toNNReal (by rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]) (hsT s hs0 hs.2) i ?_
    simp only [hûL] at h0
    linarith
  have hûR0 : ∀ j, ûR j 0 = xR j := fun j => by simp [hûR, vR, w, h.vR_zero j, h.w_zero]
  have hpkgq := fun j => pkgR j q hq0.le hqT'
  have hlo : ∀ j, xR j < y' → ûR j q < (v q).re := fun j hj =>
    lt_re_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1 (by rw [hûR0]; exact hj)
  have hhi : ∀ j, y' < xR j → (v q).re < ûR j q := fun j hj =>
    re_lt_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1 (hpkgq j).2.2.1 (hpkgq j).2.2.2
      (by rw [hûR0]; exact hj)
  have rpkgR := fun j (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgR j s (hq0.le.trans hs.1) hs.2)
  have rpkgL := fun i (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgL i s (hq0.le.trans hs.1) hs.2)
  -- a mark between the driver and the limit point collides with the driver at `T`
  have hcoll : ∀ j, xR j < y' → Tendsto (fun t => vR j t - w t) (𝓝[<] T) (𝓝 0) := by
    intro j hj
    obtain ⟨L, hL⟩ := hlimV j
    have hL0 : L = 0 :=
      eq_zero_of_tendsto_restart hηR hU hU0 hq0.le hqT' hHR hy'0 hlimR hv (u := ûR j)
        (fun s hs => ⟨(rpkgR j s hs).1, (rpkgR j s hs).2.1, (rpkgR j s hs).2.2.1⟩)
        (fun s hs => lt_of_le_of_ne (hnnR j s (hq0.le.trans hs.1) hs.2) (hneR j s hs).symm)
        (hlo j hj).le (tendsto_comp_toNNReal' hT0 hL)
    rwa [hL0] at hL
  -- before `t₀` a gap that collides at `T` contradicts its positivity
  have hnotlt : ¬ T < t₀ → T = t₀ := fun hn => le_antisymm hTt₀ (not_lt.1 hn)
  have hcontr : ∀ j, (∀ t < t₀, w t < vR j t) → T < t₀ → xR j < y' → False := by
    intro j hpos hTlt hj
    have hc : ContinuousAt (fun t => vR j t - w t) T :=
      ((h.continuousOn_vR j).sub hwc).continuousAt
        ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds ((ENNReal.coe_lt_coe.2 hTlt).trans_le ht₀ζ))
    have hne : (𝓝[<] T).NeBot := Sec2.IsForcePath.neBot_nhdsLT hT0
    have h1 := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) (hcoll j hj)
    have h2 := hpos T hTlt
    linarith
  -- the first real contact is the visit of `y`
  have hTeq : T = t₀ ∧ y' = xR j₀ := by
    rcases lt_trichotomy y' (xR j₀) with hlt | heq | hgt
    · have hTlt : T < t₀ := by
        by_contra hn
        have := hnotlt hn
        rw [this, hvis] at hηT
        have := congrArg Complex.re hηT
        simp only [Complex.ofReal_re] at this
        linarith
      exact (hcontr k hopos hTlt hy'.1).elim
    · refine ⟨?_, heq⟩
      by_contra hn
      have hTlt : T < t₀ := lt_of_le_of_ne hTt₀ hn
      exact hfirst T hTlt (by rw [hηT, heq])
    · have hTlt : T < t₀ := by
        by_contra hn
        have := hnotlt hn
        rw [this, hvis] at hηT
        have := congrArg Complex.re hηT
        simp only [Complex.ofReal_re] at this
        linarith
      exact (hcontr j₀ hupos hTlt hgt).elim
  obtain ⟨hTt, hy'y⟩ := hTeq
  subst hTt
  subst hy'y
  -- the energy bound: weights between the driver and the target sum to `S' − S = 0`
  set c : Fin nL ⊕ Fin nR → ℝ := Sum.elim ρL (fun j => ρR j - lowRefW xR ρR k j₀ S j) with hc
  set û : Fin nL ⊕ Fin nR → ℝ → ℝ := Sum.elim ûL (fun j => if xR j = xR j₀ then ûR k else ûR j) with hû
  have hpkg : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ContinuousOn (û j) (Icc q s) ∧
      ∀ s₁ ∈ Icc (q : ℝ) s, ∀ s₂ ∈ Icc (q : ℝ) s, s₁ ≤ s₂ →
        û j s₂ - û j s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / û j r := by
    rintro (i | j) s hs
    · exact ⟨(rpkgL i s hs).1, (rpkgL i s hs).2.1⟩
    · by_cases hj : xR j = xR j₀
      · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]
        exact ⟨(rpkgR k s hs).1, (rpkgR k s hs).2.1⟩
      · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]
        exact ⟨(rpkgR j s hs).1, (rpkgR j s hs).2.1⟩
  have hne : ∀ j, ∀ s ∈ Ico (q : ℝ) T, û j s ≠ 0 := by
    rintro (i | j) s hs
    · exact hneL i s hs
    · by_cases hj : xR j = xR j₀
      · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]; exact hneR k s hs
      · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]; exact hneR j s hs
  have hûLq : ∀ i, ûL i q < 0 := fun i =>
    lt_of_le_of_ne (hnpL i q hq0.le hqT') (hneL i q ⟨le_rfl, hqT'⟩)
  have hûRq : ∀ j, 0 < ûR j q := fun j =>
    lt_of_le_of_ne (hnnR j q hq0.le hqT') (hneR j q ⟨le_rfl, hqT'⟩).symm
  have hsep : ∀ j, û j q ≠ (v q).re := by
    rintro (i | j)
    · exact ((hûLq i).trans hV).ne
    · by_cases hj : xR j = xR j₀
      · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]; exact (hlo k hkjx).ne
      · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]
        rcases lt_or_gt_of_ne hj with hlt | hgt
        · exact (hlo j hlt).ne
        · exact (hhi j hgt).ne'
  have hright : ∀ j : Fin nR, (0 < û (Sum.inr j) q ∧ û (Sum.inr j) q < (v q).re) ↔ xR j ≤ xR j₀ := by
    intro j
    by_cases hj : xR j = xR j₀
    · simp only [hû, Sum.elim_inr, hj, ↓reduceIte, le_refl, iff_true]
      exact ⟨hûRq k, hlo k hkjx⟩
    · simp only [hû, Sum.elim_inr, hj, ↓reduceIte]
      constructor
      · rintro ⟨-, h2⟩
        by_contra hjy
        exact absurd (hhi j (not_le.1 hjy)) (not_lt.2 h2.le)
      · intro hjy
        exact ⟨hûRq j, hlo j (lt_of_le_of_ne hjy hj)⟩
  have hcore : ∑ j ∈ univ.filter (fun j => 0 < û j q ∧ û j q < (v q).re), c j = 0 := by
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have hleft : ∑ i : Fin nL, (if 0 < û (Sum.inl i) q ∧ û (Sum.inl i) q < (v q).re
        then c (Sum.inl i) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun hh => absurd hh.1 (not_lt.2 (hûLq i).le)
    rw [hleft, zero_add]
    simp_rw [hright]
    rw [← Finset.sum_filter]
    simp only [hc, Sum.elim_inr]
    -- split `x_j ≤ y` into `x_j < y` and the group of `y`
    have hsplit : univ.filter (fun j => xR j ≤ xR j₀) =
        univ.filter (fun j => xR j < xR j₀) ∪ univ.filter (fun j => xR j = xR j₀) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, le_iff_lt_or_eq]
    have hdisj : Disjoint (univ.filter (fun j => xR j < xR j₀)) (univ.filter (fun j => xR j = xR j₀)) :=
      Finset.disjoint_filter.2 fun j _ h1 h2 => h1.ne h2
    rw [hsplit, Finset.sum_union hdisj]
    have hgrp : ∑ j ∈ univ.filter (fun j => xR j = xR j₀), (ρR j - lowRefW xR ρR k j₀ S j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : xR j = xR j₀ := (Finset.mem_filter.1 hj).2
      have hjk : j ≠ k := fun hjk => by rw [hjk] at hj'; exact hkjx.ne hj'
      simp only [lowRefW, hjk, hj', ↓reduceIte, zero_add, sub_self]
    have hnear : ∑ j ∈ univ.filter (fun j => xR j < xR j₀), (ρR j - lowRefW xR ρR k j₀ S j) = 0 := by
      rw [Finset.sum_sub_distrib, ← hSdef]
      have : ∑ j ∈ univ.filter (fun j => xR j < xR j₀), lowRefW xR ρR k j₀ S j = S := by
        have e : ∀ j ∈ univ.filter (fun j => xR j < xR j₀), lowRefW xR ρR k j₀ S j = if j = k then S else 0 :=
          fun j hj => by
            have hj' : xR j ≠ xR j₀ := (Finset.mem_filter.1 hj).2.ne
            simp only [lowRefW, hj', ↓reduceIte, add_zero]
        rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
        simp [hkjx]
      rw [this, sub_self]
    rw [hgrp, hnear, add_zero]
  obtain ⟨Cb, hCb⟩ := exists_energy_bound_of_restart hηR hU hU0 hq0.le hqT' hHR hinjR hy0 hlimR hv
    û c hpkg hne hsep hcore
  refine ⟨q, hq0, hqT', ⌈Cb / κ⌉₊, ?_, ht₀ζ, fun t ht => hopos t ht, fun t hqt ht => ?_, fun t hqt ht => ?_⟩
  · rw [← NNReal.coe_lt_coe, hqN]; exact hqT'
  · have hqt' : (p : ℝ) ≤ t := by
      have : (q : ℝ) ≤ t := by rw [← hqN]; exact NNReal.coe_le_coe.2 hqt
      linarith
    exact ⟨fun i => hoffL t hqt' ht i, fun j => hoffR t hqt' ht j⟩
  · have hqt' : (q : ℝ) ≤ t := by rw [← hqN]; exact NNReal.coe_le_coe.2 hqt
    have hb := hCb t ⟨hqt', NNReal.coe_lt_coe.2 ht⟩
    have hgrp0 : ∀ j, xR j = xR j₀ → ρR j - lowRefW xR ρR k j₀ S j = 0 := fun j hj => by
      have hjk : j ≠ k := fun hjk => by rw [hjk] at hj; exact hkjx.ne hj
      simp only [lowRefW, hjk, hj, ↓reduceIte, zero_add, sub_self]
    have key : ∀ s : ℝ, ∑ x, c x / û x s = -lowD ρL xR ρR k j₀ S W VL VR ω s := fun s => by
      rw [Fintype.sum_sum_type]
      simp only [hc, hû, Sum.elim_inl, Sum.elim_inr]
      unfold lowD
      rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        show ρL i / (VL i s.toNNReal ω - W s.toNNReal ω) = -(ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
        rw [← neg_sub (W s.toNNReal ω), div_neg]
      · refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : xR j = xR j₀
        · rw [hgrp0 j hj, zero_div, zero_div, neg_zero]
        · simp only [hj, ↓reduceIte]
          show (ρR j - lowRefW xR ρR k j₀ S j) / (VR j s.toNNReal ω - W s.toNNReal ω) =
            -((ρR j - lowRefW xR ρR k j₀ S j) / (W s.toNNReal ω - VR j s.toNNReal ω))
          rw [← neg_sub (W s.toNNReal ω), div_neg]
    have heq : ∫ s in (q : ℝ)..t, (∑ j, c j / û j s) ^ 2 =
        ∫ s in ((q : ℝ).toNNReal : ℝ)..t, lowD ρL xR ρR k j₀ S W VL VR ω s ^ 2 := by
      rw [hqN]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [key s, neg_sq]
    have hκC : Cb ≤ κ * (⌈Cb / κ⌉₊ : ℝ) := by
      have := Nat.le_ceil (Cb / κ)
      rw [div_le_iff₀ hκ] at this
      linarith
    rw [← heq]
    exact hb.trans hκC

end G12Low

end Supp7

end InteractingSLE
