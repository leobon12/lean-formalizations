/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GB7aAbove4Merge
import InteractingSLE.Spec.Sec5.CfAvoidLeftQHit

/-!
# GB7a's pathwise half above `κ = 4`: the comparison picture from a visit

Packet PROVE-CFBARRIER2. PROVE-GB7A3's `GB7a.rightCmpPath_of_visit` without injectivity of the trace (Aux. lemma 25,
true only for `κ ≤ 4`). For one path of an integrated `SLE_κ(ρ)` evolution with a continuous generating trace:

* `rightCmpPath_of_fresh`: **the chart route.** At a visit `η(T) = y ∈ (x_k, a')` that is the first visit of `y`,
  with the trace in `ℍ` on `[p, T)`, the comparison picture holds at a rational `q ∈ (p, T)`: the proof of
  `GB7a.rightCmpPath_of_visit`, with the chart lemmas of `GB7aAbove4Chart.lean` (the limit point is alive at `q` because
  it is off the prefix; the energy bound with an asymmetric seed core, since the trace after `q` may touch its past);
* `rightCmpPath_of_visit_any`: **the comparison picture from any visit** (every `κ > 0`, no injectivity). Let `T₁` be
  the first visit of `[y₀, ∞)`, `y₀ ∈ (x_k, a')` a visited point. Its point `X₁` is in `[y₀, a')`: otherwise `y₀`,
  swallowed at `T₁` without being visited, would be alive at `T₁` because it is visited later
  (`exists_isForwardSol_at_restart_of_notMem`). If the trace is in `ℍ` on some `[p, T₁)`, the chart route applies.
  Otherwise real contacts accumulate at `T₁`; their values tend to `X₁` from below, and the first visits of `[c, ∞)`
  for two of them, `c ∈ (x_k, y₀)`, are two collisions `σ₁ < σ₂ < T₁` of the mark `k` (`CfAvoidLeftQ.vR_eq_w_of_off`),
  at which every mark at or left of `x_k` is merged: the merged-group route (`rightCmpPath_of_merged`) applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5.GB7aAbove4

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open GB7a

section Fresh

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The comparison picture at a fresh visit with the trace in `ℍ` before it** (one path, no injectivity). -/
theorem rightCmpPath_of_fresh (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nR} {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ) {y' : ℝ} (hy' : y' ∈ Ioo (xR k) a') (hηT : η T = y')
    (hfresh : ∀ s : ℝ≥0, s < T → η s ≠ y') {p : ℝ≥0} (hpT : p < T)
    (hH : ∀ s : ℝ≥0, (p : ℝ) ≤ s → s < T → η s ∈ H) :
    ∃ q : ℚ, RightCmpPath ρL ρR w vL vR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal := by
  have hwc := h.continuousOn_w
  have hxk : 0 ≤ xR k := hord.2.2.2 k
  have hT0 : 0 < T := lt_of_le_of_lt zero_le hpT
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 hpT)
  have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt p.coe_nonneg hpq
  have hqN : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  obtain ⟨U, hU, hU0, hUw, hlimV⟩ := exists_driver h hTζ hT0 hlimζ
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR : IsLoewnerTraceLT U T ηR := isLoewnerTraceLT_of_agree hη hTζ hUw
  have hltζ : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht =>
    (ENNReal.coe_lt_coe.2 ht).trans_le hTζ
  -- the centred force coordinates and their packages on `[0, s]`, `s < T`
  set ûR : Fin nR → ℝ → ℝ := fun j r => vR j r.toNNReal - w r.toNNReal with hûR
  set ûL : Fin nL → ℝ → ℝ := fun i r => vL i r.toNNReal - w r.toNNReal with hûL
  have pkgR := fun j (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => centredPkg hwc (h.continuousOn_vR j)
    (fun t ht => h.integrable_gapR ht j) (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hTζ hUw hs0 hsT
  have pkgL := fun i (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => centredPkg hwc (h.continuousOn_vL i)
    (fun t ht => h.integrable_gapL ht i) (fun t ht => h.vL_eq ht i) (h.volume_collisionL i) hTζ hUw hs0 hsT
  -- (2) no force coordinate meets the driver on `[p, T)`
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
  have hyq : (y' : ℂ) ∉ ηR '' Icc 0 q := by
    rintro ⟨r, hr, hry⟩
    refine hfresh r.toNNReal ?_ hry
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1]
    exact hr.2.trans_lt hqT'
  have hlimR : Tendsto ηR (𝓝[<] (T : ℝ)) (𝓝 (y' : ℂ)) := by
    rw [← hηT]
    exact tendsto_comp_toNNReal hη hTζ hT0
  -- (3) the limit point is alive at `q`; strict order of the right marks
  obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart_of_notMem hηR hU hU0 hq0.le hqT' hy'0.ne' hlimR hyq
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
  have hûR0 : ∀ j, ûR j 0 = xR j := fun j => by simp [hûR, h.vR_zero j, h.w_zero]
  have hpkgq := fun j => pkgR j q hq0.le hqT'
  have hlo : ∀ j, xR j ≤ xR k → ûR j q < (v q).re := fun j hj =>
    lt_re_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1
      (by rw [hûR0]; linarith [hy'.1])
  have hhi : ∀ j, xR k < xR j → (v q).re < ûR j q := fun j hj =>
    re_lt_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1 (hpkgq j).2.2.1 (hpkgq j).2.2.2
      (by rw [hûR0]; linarith [hnext j hj, hy'.2])
  -- packages on `[q, s]`
  have rpkgR := fun j (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgR j s (hq0.le.trans hs.1) hs.2)
  have rpkgL := fun i (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgL i s (hq0.le.trans hs.1) hs.2)
  -- (4) collision of `k` at `T`
  obtain ⟨L, hL⟩ := hlimV k
  have hL0 : L = 0 :=
    eq_zero_of_tendsto_restart hηR hU hU0 hq0.le hqT' hHR hy'0 hlimR hv (u := ûR k)
      (fun s hs => ⟨(rpkgR k s hs).1, (rpkgR k s hs).2.1, (rpkgR k s hs).2.2.1⟩)
      (fun s hs => lt_of_le_of_ne (hnnR k s (hq0.le.trans hs.1) hs.2) (hneR k s hs).symm)
      (hlo k le_rfl).le (tendsto_comp_toNNReal' hT0 hL)
  -- (5) the energy bound
  set S := ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i with hS
  set c : Fin nL ⊕ Fin nR → ℝ := Sum.elim ρL (fun j => ρR j - refWeightR k none S j) with hc
  set û : Fin nL ⊕ Fin nR → ℝ → ℝ := Sum.elim ûL ûR with hû
  have hpkg : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ContinuousOn (û j) (Icc q s) ∧
      ∀ s₁ ∈ Icc (q : ℝ) s, ∀ s₂ ∈ Icc (q : ℝ) s, s₁ ≤ s₂ →
        û j s₂ - û j s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / û j r := by
    rintro (i | j) s hs
    · exact ⟨(rpkgL i s hs).1, (rpkgL i s hs).2.1⟩
    · exact ⟨(rpkgR j s hs).1, (rpkgR j s hs).2.1⟩
  have hne : ∀ j, ∀ s ∈ Ico (q : ℝ) T, û j s ≠ 0 := by
    rintro (i | j) s hs
    exacts [hneL i s hs, hneR j s hs]
  have hûLq : ∀ i, ûL i q < 0 := fun i =>
    lt_of_le_of_ne (hnpL i q hq0.le hqT') (hneL i q ⟨le_rfl, hqT'⟩)
  have hûRq : ∀ j, 0 < ûR j q := fun j =>
    lt_of_le_of_ne (hnnR j q hq0.le hqT') (hneR j q ⟨le_rfl, hqT'⟩).symm
  have hsep : ∀ j, û j q ≠ (v q).re := by
    rintro (i | j)
    · exact ((hûLq i).trans hV).ne
    · rcases le_or_gt (xR j) (xR k) with hj | hj
      · exact (hlo j hj).ne
      · exact (hhi j hj).ne'
  have hright : ∀ j : Fin nR, (0 < û (Sum.inr j) q ∧ û (Sum.inr j) q < (v q).re) ↔ xR j ≤ xR k := by
    intro j
    constructor
    · rintro ⟨-, h2⟩
      by_contra hj
      exact absurd (hhi j (not_le.1 hj)) (not_lt.2 h2.le)
    · intro hj
      exact ⟨hûRq j, hlo j hj⟩
  have hcore : ∑ j ∈ univ.filter (fun j => 0 < û j q ∧ û j q < (v q).re), c j = 0 := by
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have hleft : ∑ i : Fin nL, (if 0 < û (Sum.inl i) q ∧ û (Sum.inl i) q < (v q).re
        then c (Sum.inl i) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun hh => absurd hh.1 (not_lt.2 (hûLq i).le)
    rw [hleft, zero_add]
    simp_rw [hright]
    rw [← Finset.sum_filter]
    simp only [hc, Sum.elim_inr]
    rw [Finset.sum_sub_distrib]
    have href : ∑ j ∈ univ.filter (fun j => xR j ≤ xR k), refWeightR k none S j = S := by
      simp only [refWeightR, reduceCtorEq, ite_false, sub_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [href, sub_self]
  obtain ⟨C, hC⟩ := exists_energy_bound_of_restart_above4 hηR hU hU0 hq0.le hqT' hHR hlimR hyq hv
    û c hpkg hne hsep (k := Sum.inr k) (hûRq k) (hlo k le_rfl) hcore
  have hqt : ∀ t : ℝ≥0, (q : ℝ).toNNReal ≤ t → (q : ℝ) ≤ t := fun t ht => by
    rw [← hqN]; exact NNReal.coe_le_coe.2 ht
  refine ⟨q, T, by rw [← NNReal.coe_lt_coe, hqN]; exact hqT', hTζ, fun t hqt' htT =>
    ⟨fun i _ => hoffL t (by linarith [hqt t hqt']) htT i,
      fun j _ => hoffR t (by linarith [hqt t hqt']) htT j⟩, ⟨C, fun t hqt' htT => ?_⟩, ?_⟩
  · have hb := hC t ⟨hqt t hqt', NNReal.coe_lt_coe.2 htT⟩
    rw [hqN]
    refine le_of_eq_of_le (intervalIntegral.integral_congr fun s _ => ?_) hb
    simp only [Fintype.sum_sum_type, hû, hc, Sum.elim_inl, Sum.elim_inr, hûL, hûR]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_div, ← div_neg, neg_sub]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← neg_sub (ρR j), ← neg_sub (vR j s.toNNReal), neg_div_neg_eq]
  · rw [← hL0]
    exact hL

end Fresh


/-! ### The comparison picture from any visit -/

section Any

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The comparison picture from a visit, without injectivity** (one path of an integrated `SLE_a(ρ)` path; every
parameter). If the trace visits `(x_k, a')`, where `a'` is at most the next right mark after `x_k`, then
`RightCmpPath` holds at some rational restart time, for the comparison weight `S = ∑_{xᵢ ≤ x_k} ρᵢ`. -/
theorem rightCmpPath_of_visit_any (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nR} {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo (xR k) a', η t = y) :
    ∃ q : ℚ, RightCmpPath ρL ρR w vL vR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal := by
  have h := hp.isForcePath
  obtain ⟨t₀, ht₀, y₀, hy₀, he₀⟩ := hvis
  have hxk : 0 ≤ xR k := hord.2.2.2 k
  have hy₀0 : 0 < y₀ := lt_of_le_of_lt hxk hy₀.1
  have hcont : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → ContinuousOn η (Icc 0 t) := fun t ht =>
    hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans ht
  -- the first visit of `[y₀, ∞)`
  obtain ⟨T₁, hT₁0, hT₁t₀, X₁, hX₁, hηT₁, hoff₁⟩ := exists_first_visit_le (hcont t₀ ht₀) hη.1 hy₀0 le_rfl he₀
  have hT₁ζ : (T₁ : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hT₁t₀).trans ht₀
  -- (1) its point lies before `a'`
  have hX₁a : X₁ < a' := by
    by_contra hge
    push Not at hge
    have hT₁lt : T₁ < t₀ := lt_of_le_of_ne hT₁t₀ fun he => by
      rw [he, he₀] at hηT₁
      have := Complex.ofReal_injective hηT₁
      linarith [hy₀.2]
    obtain ⟨U, hU, hU0, hUw, -⟩ := exists_driver h ht₀ (hT₁0.trans hT₁lt) hlimζ
    set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
    have hηR : IsLoewnerTraceLT U t₀ ηR := isLoewnerTraceLT_of_agree hη ht₀ hUw
    have hlim : Tendsto ηR (𝓝[<] (t₀ : ℝ)) (𝓝 (y₀ : ℂ)) := by
      rw [← he₀]
      exact tendsto_comp_toNNReal hη ht₀ (hT₁0.trans hT₁lt)
    have hyq : (y₀ : ℂ) ∉ ηR '' Icc 0 (T₁ : ℝ) := by
      rintro ⟨r, hr, hry⟩
      have hrT : r.toNNReal ≤ T₁ := Real.toNNReal_le_iff_le_coe.2 hr.2
      rcases hrT.lt_or_eq with hlt | heq
      · exact hoff₁ _ hlt y₀ le_rfl hry
      · have hry' : η r.toNNReal = y₀ := hry
        rw [heq, hηT₁] at hry'
        have := Complex.ofReal_injective hry'
        linarith [hy₀.2]
    obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart_of_notMem hηR hU hU0 T₁.coe_nonneg
      (NNReal.coe_lt_coe.2 hT₁lt) hy₀0.ne' hlim hyq
    obtain ⟨v', hv'⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hU T₁.coe_nonneg (by rw [hU0]; exact hy₀0)
      (show y₀ < X₁ by linarith [hy₀.2]) hv
    exact trace_ne_of_isForwardSol hηR hU hU0 ⟨T₁.coe_nonneg, NNReal.coe_lt_coe.2 hT₁lt⟩ hv'
      (by simp [hηRdef, hηT₁])
  have hX₁I : X₁ ∈ Ioo (xR k) a' := ⟨lt_of_lt_of_le hy₀.1 hX₁, hX₁a⟩
  have hfresh : ∀ s : ℝ≥0, s < T₁ → η s ≠ X₁ := fun s hs => hoff₁ s hs X₁ hX₁
  by_cases hA : ∃ p : ℝ≥0, p < T₁ ∧ ∀ s : ℝ≥0, (p : ℝ) ≤ s → s < T₁ → (η s).im ≠ 0
  · -- (2) the trace is in `ℍ` before `T₁`: the chart route
    obtain ⟨p, hpT, hpH⟩ := hA
    refine rightCmpPath_of_fresh h hord hη hlimζ hnext hT₁ζ hX₁I hηT₁ hfresh hpT fun s hps hsT => ?_
    have hbar := Sec7.IsGeneratingTrace.mem_Hbar hη h.continuousOn_w h.w_zero
      ((ENNReal.coe_le_coe.2 hsT.le).trans hT₁ζ)
    exact lt_of_le_of_ne hbar (Ne.symm (hpH s hps hsT))
  · -- (3) real contacts accumulate at `T₁`: the merged-group route
    push Not at hA
    have hnear : ∀ ε > 0, ∃ s : ℝ≥0, s < T₁ ∧ (η s).im = 0 ∧ |(η s).re - X₁| < ε := by
      intro ε hε
      obtain ⟨δ, hδ, hδη⟩ := Metric.continuousWithinAt_iff.1 (hη.2.1 T₁ hT₁ζ) ε hε
      set p : ℝ≥0 := ((T₁ : ℝ) - δ / 2).toNNReal with hpdef
      have hpT : p < T₁ := by
        rw [← NNReal.coe_lt_coe, hpdef, Real.coe_toNNReal']
        exact max_lt (by linarith) (NNReal.coe_pos.2 hT₁0)
      obtain ⟨s, hps, hsT, hs0⟩ := hA p hpT
      have hps' : (T₁ : ℝ) - δ / 2 ≤ s := (Real.le_coe_toNNReal _).trans hps
      have hd : dist s T₁ < δ := by
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hsT.le))]
        linarith
      have h1 := hδη ((ENNReal.coe_le_coe.2 hsT.le).trans hT₁ζ) hd
      rw [hηT₁, Complex.dist_eq] at h1
      refine ⟨s, hsT, hs0, lt_of_le_of_lt ?_ h1⟩
      have := Complex.abs_re_le_norm (η s - X₁)
      simpa using this
    have hcol : ∀ s : ℝ≥0, s < T₁ → (η s).im = 0 → xR k < (η s).re →
        ∃ σ : ℝ≥0, σ ≤ s ∧ ∃ X : ℝ, (η s).re ≤ X ∧ η σ = X ∧ X < y₀ ∧
          (∀ s' : ℝ≥0, s' < σ → ∀ r : ℝ, (η s).re ≤ r → η s' ≠ r) ∧ (∀ j, xR j ≤ X → vR j σ = w σ) := by
      intro s hsT hs0 hsk
      have hc0 : 0 < (η s).re := lt_of_le_of_lt hxk hsk
      have hηs : η s = ((η s).re : ℂ) := Complex.ext (by simp) (by simp [hs0])
      have hsζ : (s : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hsT.le).trans hT₁ζ
      obtain ⟨σ, hσ0, hσs, X, hX, hησ, hoffσ⟩ := exists_first_visit_le (hcont s hsζ) hη.1 hc0 le_rfl hηs
      have hσT : σ < T₁ := hσs.trans_lt hsT
      have hXy : X < y₀ := by
        by_contra hge
        push Not at hge
        exact hoff₁ σ hσT X hge hησ
      refine ⟨σ, hσs, X, hX, hησ, hXy, hoffσ, fun j hj => ?_⟩
      exact CfAvoidLeftQ.vR_eq_w_of_off hp hη hσ0 ((ENNReal.coe_lt_coe.2 hσT).trans_le hT₁ζ)
        (hc0.trans_le hX) hησ (fun t ht s' hs' r hr => hoffσ s' (hs'.trans_lt ht) r (hX.trans hr)) hj
    -- the first collision `σ₁`
    obtain ⟨s₁, hs₁T, hs₁0, hs₁X⟩ := hnear (X₁ - xR k) (by linarith [hX₁I.1])
    have hs₁k : xR k < (η s₁).re := by linarith [neg_abs_le ((η s₁).re - X₁)]
    obtain ⟨σ₁, hσ₁s, Y₁, hY₁, hησ₁, hY₁y, hoffσ₁, hm₁⟩ := hcol s₁ hs₁T hs₁0 hs₁k
    -- a second collision `σ₂ > σ₁`
    obtain ⟨s₂, hs₂T, hs₂0, hs₂X⟩ := hnear (X₁ - Y₁) (by linarith)
    have hs₂Y : Y₁ < (η s₂).re := by linarith [neg_abs_le ((η s₂).re - X₁)]
    obtain ⟨σ₂, hσ₂s, Y₂, hY₂, hησ₂, hY₂y, -, hm₂⟩ := hcol s₂ hs₂T hs₂0 (by linarith)
    have hσ₁₂ : σ₁ < σ₂ := by
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hlt | heq
      · exact hoffσ₁ σ₂ hlt Y₂ (by linarith) hησ₂
      · rw [heq, hησ₁] at hησ₂
        have := Complex.ofReal_injective hησ₂
        linarith
    have hσ₂T : σ₂ < T₁ := hσ₂s.trans_lt hs₂T
    have hY₁0 : 0 < Y₁ := by linarith
    refine rightCmpPath_of_merged h hord hη hnext hσ₁₂ ((ENNReal.coe_lt_coe.2 hσ₂T).trans_le hT₁ζ)
      (fun j hj => hm₁ j (hj.trans (by linarith))) (hm₂ k (by linarith)) hY₁0 hησ₁
      (fun s hs r hr => hoff₁ s (hs.trans_lt hσ₂T) r (by linarith [hy₀.2]))

end Any

end Sec5.GB7aAbove4

end InteractingSLE
