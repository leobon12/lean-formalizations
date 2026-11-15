/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfJunction

/-!
# The junction barrier: the pathwise half

Packet PROVE-CFBARRIER2. For one path of an integrated `SLE_κ(ρ)` evolution with a continuous generating trace (no
injectivity): a visit of a right mark position `x_k > 0`, when the trace visits neither the interval `(x_{k'}, x_k)`
before it (`x_{k'}` the previous distinct mark position) nor `(x_k, a')` after it, produces the comparison picture
`CfJunction.GenCmpPath` for the junction reference weights (`junctionWeight`) and the repelled mark `k'` at a rational
restart time:

* `genCmpPath_of_junction_fresh`: the chart route at the first visit of `x_k`, with the trace in `ℍ` before it (the
  proof of `GB7aAbove4.rightCmpPath_of_fresh`; the marks at `x_k` sit at the chart target and carry comparison weight
  `0`, so they are left out of the cutoff configuration);
* `genCmpPath_of_junction_visit`: the visit of `x_k` is the first visit of `[x_k, ∞)`, approached from `ℍ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5.CfJunction

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open GB7a GB7aAbove4

section Fresh

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The junction comparison picture at a fresh visit of the junction with the trace in `ℍ` before it.** -/
theorem genCmpPath_of_junction_fresh (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k' k : Fin nR} (hk'k : xR k' < xR k) (hprev : ∀ j, xR j < xR k → xR j ≤ xR k')
    {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ) (hηT : η T = xR k)
    (hfresh : ∀ s : ℝ≥0, s < T → η s ≠ xR k) {p : ℝ≥0} (hpT : p < T)
    (hH : ∀ s : ℝ≥0, (p : ℝ) ≤ s → s < T → η s ∈ H) :
    ∃ q : ℚ, GenCmpPath ρL ρR (junctionWeight xR ρR k' k (∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i))
      w vL vR ζ k' (q : ℝ).toNNReal := by
  classical
  set y' : ℝ := xR k with hy'def
  have hwc := h.continuousOn_w
  have hxk : 0 ≤ xR k' := hord.2.2.2 k'
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
  have hy'0 : 0 < y' := lt_of_le_of_lt hxk hk'k
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
  have hlo : ∀ j, xR j < xR k → ûR j q < (v q).re := fun j hj =>
    lt_re_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1
      (by rw [hûR0]; exact hj)
  have hhi : ∀ j, xR k < xR j → (v q).re < ûR j q := fun j hj =>
    re_lt_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hqT')) (hpkgq j).2.1 (hpkgq j).2.2.1 (hpkgq j).2.2.2
      (by rw [hûR0]; exact hj)
  -- packages on `[q, s]`
  have rpkgR := fun j (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgR j s (hq0.le.trans hs.1) hs.2)
  have rpkgL := fun i (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl (pkgL i s (hq0.le.trans hs.1) hs.2)
  -- (4) collision of `k'` at `T`
  obtain ⟨L, hL⟩ := hlimV k'
  have hL0 : L = 0 :=
    eq_zero_of_tendsto_restart hηR hU hU0 hq0.le hqT' hHR hy'0 hlimR hv (u := ûR k')
      (fun s hs => ⟨(rpkgR k' s hs).1, (rpkgR k' s hs).2.1, (rpkgR k' s hs).2.2.1⟩)
      (fun s hs => lt_of_le_of_ne (hnnR k' s (hq0.le.trans hs.1) hs.2) (hneR k' s hs).symm)
      (hlo k' hk'k).le (tendsto_comp_toNNReal' hT0 hL)
  -- (5) the energy bound: the marks at the junction position carry comparison weight `0`
  set S' := ∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i with hS'
  set ρ' := junctionWeight xR ρR k' k S' with hρ'
  have hρ'G : ∀ j, xR j = xR k → ρ' j = ρR j := fun j hj => by
    have hjk' : j ≠ k' := fun he => by rw [he] at hj; exact hk'k.ne hj
    simp [hρ', junctionWeight, hjk', hj]
  have hρ'off : ∀ j, xR j ≠ xR k → ρ' j = if j = k' then S' else 0 := fun j hj => by
    simp [hρ', junctionWeight, hj]
  have hk'ne : xR k' ≠ xR k := hk'k.ne
  set c : Fin nL ⊕ {j : Fin nR // xR j ≠ xR k} → ℝ := Sum.elim ρL (fun j => ρR j.1 - ρ' j.1) with hc
  set û : Fin nL ⊕ {j : Fin nR // xR j ≠ xR k} → ℝ → ℝ := Sum.elim ûL (fun j => ûR j.1) with hû
  have hpkg : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ContinuousOn (û j) (Icc q s) ∧
      ∀ s₁ ∈ Icc (q : ℝ) s, ∀ s₂ ∈ Icc (q : ℝ) s, s₁ ≤ s₂ →
        û j s₂ - û j s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / û j r := by
    rintro (i | j) s hs
    · exact ⟨(rpkgL i s hs).1, (rpkgL i s hs).2.1⟩
    · exact ⟨(rpkgR j.1 s hs).1, (rpkgR j.1 s hs).2.1⟩
  have hne : ∀ j, ∀ s ∈ Ico (q : ℝ) T, û j s ≠ 0 := by
    rintro (i | j) s hs
    exacts [hneL i s hs, hneR j.1 s hs]
  have hûLq : ∀ i, ûL i q < 0 := fun i =>
    lt_of_le_of_ne (hnpL i q hq0.le hqT') (hneL i q ⟨le_rfl, hqT'⟩)
  have hûRq : ∀ j, 0 < ûR j q := fun j =>
    lt_of_le_of_ne (hnnR j q hq0.le hqT') (hneR j q ⟨le_rfl, hqT'⟩).symm
  have hsep : ∀ j, û j q ≠ (v q).re := by
    rintro (i | j)
    · exact ((hûLq i).trans hV).ne
    · rcases lt_or_gt_of_ne j.2 with hj | hj
      · exact (hlo j.1 hj).ne
      · exact (hhi j.1 hj).ne'
  have hright : ∀ j : {j : Fin nR // xR j ≠ xR k},
      (0 < û (Sum.inr j) q ∧ û (Sum.inr j) q < (v q).re) ↔ xR j.1 < xR k := by
    intro j
    constructor
    · rintro ⟨-, h2⟩
      rcases lt_or_gt_of_ne j.2 with hj | hj
      · exact hj
      · exact absurd (hhi j.1 hj) (not_lt.2 h2.le)
    · intro hj
      exact ⟨hûRq j.1, hlo j.1 hj⟩
  have hcore : ∑ j ∈ univ.filter (fun j => 0 < û j q ∧ û j q < (v q).re), c j = 0 := by
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have hleft : ∑ i : Fin nL, (if 0 < û (Sum.inl i) q ∧ û (Sum.inl i) q < (v q).re
        then c (Sum.inl i) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun hh => absurd hh.1 (not_lt.2 (hûLq i).le)
    rw [hleft, zero_add]
    simp_rw [hright]
    simp only [hc, Sum.elim_inr]
    have hsub := Fintype.sum_subtype_add_sum_subtype (fun j : Fin nR => xR j ≠ xR k)
      (fun j => if xR j < xR k then ρR j - ρ' j else 0)
    have hz : ∑ j : {j : Fin nR // ¬ xR j ≠ xR k}, (if xR j.1 < xR k then ρR j.1 - ρ' j.1 else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        have : xR j.1 = xR k := not_not.1 j.2
        simp [this]
    rw [hz, add_zero] at hsub
    rw [hsub, ← Finset.sum_filter, Finset.sum_sub_distrib]
    have hfilt : univ.filter (fun j => xR j < xR k) = univ.filter (fun j => xR j ≤ xR k') :=
      Finset.filter_congr fun j _ => ⟨hprev j, fun h => h.trans_lt hk'k⟩
    rw [hfilt, ← hS']
    have href : ∑ j ∈ univ.filter (fun j => xR j ≤ xR k'), ρ' j = S' := by
      rw [Finset.sum_congr rfl fun j hj => hρ'off j fun he =>
        absurd ((Finset.mem_filter.1 hj).2.trans_lt hk'k) (by rw [he]; exact lt_irrefl _)]
      rw [Finset.sum_ite_eq']
      simp
    rw [href, sub_self]
  obtain ⟨C, hC⟩ := exists_energy_bound_of_restart_above4 hηR hU hU0 hq0.le hqT' hHR hlimR hyq hv
    û c hpkg hne hsep (k := Sum.inr ⟨k', hk'ne⟩) (hûRq k') (hlo k' hk'k) hcore
  have hqt : ∀ t : ℝ≥0, (q : ℝ).toNNReal ≤ t → (q : ℝ) ≤ t := fun t ht => by
    rw [← hqN]; exact NNReal.coe_le_coe.2 ht
  refine ⟨q, T, by rw [← NNReal.coe_lt_coe, hqN]; exact hqT', hTζ, fun t hqt' htT =>
    ⟨fun i _ => hoffL t (by linarith [hqt t hqt']) htT i,
      fun j _ => hoffR t (by linarith [hqt t hqt']) htT j⟩, ⟨C, fun t hqt' htT => ?_⟩, ?_⟩
  · have hb := hC t ⟨hqt t hqt', NNReal.coe_lt_coe.2 htT⟩
    rw [hqN]
    refine le_of_eq_of_le (intervalIntegral.integral_congr fun s _ => ?_) hb
    show _ = (∑ j : Fin nL ⊕ {j : Fin nR // xR j ≠ xR k}, c j / û j s) ^ 2
    rw [Fintype.sum_sum_type]
    simp only [hû, hc, Sum.elim_inl, Sum.elim_inr, hûL, hûR]
    congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_div, ← div_neg, neg_sub]
    · rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin nR => xR j ≠ xR k)]
      have hz : ∑ j : {j : Fin nR // ¬ xR j ≠ xR k},
          (ρ' j.1 - ρR j.1) / (w s.toNNReal - vR j.1 s.toNNReal) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hρ'G j.1 (not_not.1 j.2), sub_self, zero_div]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← neg_sub (ρR j.1), ← neg_sub (vR j.1 s.toNNReal), neg_div_neg_eq]
  · rw [← hL0]
    exact hL

end Fresh

/-! ### The visit of a junction -/

section Visit

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The junction comparison picture from a visit** (one path, no injectivity): if the trace visits the right mark
position `x_k` but never the interval `(x_{k'}, x_k)` before it, `GenCmpPath` holds for the junction reference at some
rational restart time. -/
theorem genCmpPath_of_junction_visit (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k' k : Fin nR} (hk'k : xR k' < xR k) (hprev : ∀ j, xR j < xR k → xR j ≤ xR k')
    (hIL : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → ∀ y ∈ Ioo (xR k') (xR k), η t ≠ y)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ η t = xR k) :
    ∃ q : ℚ, GenCmpPath ρL ρR (junctionWeight xR ρR k' k (∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i))
      w vL vR ζ k' (q : ℝ).toNNReal := by
  have h := hp.isForcePath
  obtain ⟨t₀, ht₀, he₀⟩ := hvis
  have hxk0 : 0 < xR k := lt_of_le_of_lt (hord.2.2.2 k') hk'k
  have hcont : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → ContinuousOn η (Icc 0 t) := fun t ht =>
    hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans ht
  obtain ⟨T₁, hT₁0, hT₁t₀, X₁, hX₁, hηT₁, hoff₁⟩ := exists_first_visit_le (hcont t₀ ht₀) hη.1 hxk0 le_rfl he₀
  have hT₁ζ : (T₁ : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hT₁t₀).trans ht₀
  -- (1) the first visit of `[x_k, ∞)` is at `x_k`
  have hX₁k : X₁ = xR k := by
    by_contra hne
    have hgt : xR k < X₁ := lt_of_le_of_ne hX₁ (Ne.symm hne)
    have hT₁lt : T₁ < t₀ := lt_of_le_of_ne hT₁t₀ fun he => by
      rw [he, he₀] at hηT₁
      exact hne (Complex.ofReal_injective hηT₁).symm
    obtain ⟨U, hU, hU0, hUw, -⟩ := exists_driver h ht₀ (hT₁0.trans hT₁lt) hlimζ
    set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
    have hηR : IsLoewnerTraceLT U t₀ ηR := isLoewnerTraceLT_of_agree hη ht₀ hUw
    have hlim : Tendsto ηR (𝓝[<] (t₀ : ℝ)) (𝓝 (xR k : ℂ)) := by
      rw [← he₀]
      exact tendsto_comp_toNNReal hη ht₀ (hT₁0.trans hT₁lt)
    have hyq : (xR k : ℂ) ∉ ηR '' Icc 0 (T₁ : ℝ) := by
      rintro ⟨r, hr, hry⟩
      have hrT : r.toNNReal ≤ T₁ := Real.toNNReal_le_iff_le_coe.2 hr.2
      rcases hrT.lt_or_eq with hlt | heq
      · exact hoff₁ _ hlt (xR k) le_rfl hry
      · have hry' : η r.toNNReal = xR k := hry
        rw [heq, hηT₁] at hry'
        exact hne (Complex.ofReal_injective hry')
    obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart_of_notMem hηR hU hU0 T₁.coe_nonneg
      (NNReal.coe_lt_coe.2 hT₁lt) hxk0.ne' hlim hyq
    obtain ⟨v', hv'⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hU T₁.coe_nonneg (by rw [hU0]; exact hxk0)
      hgt hv
    exact trace_ne_of_isForwardSol hηR hU hU0 ⟨T₁.coe_nonneg, NNReal.coe_lt_coe.2 hT₁lt⟩ hv'
      (by simp [hηRdef, hηT₁])
  rw [hX₁k] at hηT₁
  -- (2) the trace is in `ℍ` just before `T₁` (real contacts there would visit `(x_{k'}, x_k)`)
  have hA : ∃ p : ℝ≥0, p < T₁ ∧ ∀ s : ℝ≥0, (p : ℝ) ≤ s → s < T₁ → (η s).im ≠ 0 := by
    by_contra hA
    push Not at hA
    obtain ⟨δ, hδ, hδη⟩ := Metric.continuousWithinAt_iff.1 (hη.2.1 T₁ hT₁ζ) (xR k - xR k') (by linarith)
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
    have hre : |(η s).re - xR k| < xR k - xR k' :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (η s - xR k)) h1
    have hηs : η s = ((η s).re : ℂ) := Complex.ext (by simp) (by simp [hs0])
    have hlt : (η s).re < xR k := by
      by_contra hge
      push Not at hge
      exact hoff₁ s hsT _ hge hηs
    exact hIL s ((ENNReal.coe_le_coe.2 hsT.le).trans hT₁ζ) _
      ⟨by linarith [neg_abs_le ((η s).re - xR k)], hlt⟩ hηs
  obtain ⟨p, hpT, hpH⟩ := hA
  refine genCmpPath_of_junction_fresh h hord hη hlimζ hk'k hprev hT₁ζ hηT₁
    (fun s hs => hoff₁ s hs (xR k) le_rfl) hpT fun s hps hsT => ?_
  have hbar := Sec7.IsGeneratingTrace.mem_Hbar hη h.continuousOn_w h.w_zero
    ((ENNReal.coe_le_coe.2 hsT.le).trans hT₁ζ)
  exact lt_of_le_of_ne hbar (Ne.symm (hpH s hps hsT))

end Visit

/-! ### The junction barrier -/

section Barrier

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The junction barrier, right side, every `κ > 0`.** Let `x_k` be a right mark position with previous distinct
right mark position `x_{k'} < x_k`. If the cumulative weights `S' = ∑_{xᵢ ≤ x_{k'}} ρᵢ` and `S = ∑_{xᵢ ≤ x_k} ρᵢ` are
both at least `κ/2 − 2` (both adjacent intervals are GB7a barriers), almost surely the trace never visits `x_k`. -/
theorem ae_trace_ne_junction_right (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k' k : Fin nR} (hk'k : xR k' < xR k)
    (hprev : ∀ j, xR j < xR k → xR j ≤ xR k')
    (h1 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i)
    (h2 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xR k := by
  set ρ' := junctionWeight xR ρR k' k (∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i) with hρ'
  have hIL := GB7aAbove4.gb7aEvol_right_any hκ hord hE hη (k := k') (a' := xR k)
    (fun j hj => by
      by_contra hlt
      push Not at hlt
      exact absurd (hprev j hlt) (not_le.2 hj)) h1
  have hin : ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ η ω t = xR k) →
      ∃ q : ℚ, GenCmpPath ρL ρR ρ' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) k'
        (q : ℝ).toNNReal := by
    filter_upwards [hE.ae_tendsto_threshold hκ, hE.2.2.2.2, hη, hIL] with ω h2' h3 h4 h5 hvis
    exact genCmpPath_of_junction_visit h3 hord h4
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2' T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hk'k hprev h5 hvis
  have hnull : P (⋃ q : ℚ, {ω | GenCmpPath ρL ρR ρ' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (ζ ω) k' (q : ℝ).toNNReal}) = 0 :=
    measure_iUnion_null fun q => measure_genCmp_eq_zero hκ hE (ae_junction_drift_ge hord hE hk'k hprev h1 h2) _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, he⟩))

/-- **The junction barrier with its two arcs, right side**: under the hypotheses of `ae_trace_ne_junction_right`, with
`a'` at most the next right mark position after `x_k`, almost surely the trace avoids the whole interval
`(x_{k'}, a')`. -/
theorem ae_trace_notMem_junction_right (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k' k : Fin nR} (hk'k : xR k' < xR k)
    (hprev : ∀ j, xR j < xR k → xR j ≤ xR k') {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (h1 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k'), ρR i)
    (h2 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (xR k') a', η ω t ≠ y := by
  have hIL := GB7aAbove4.gb7aEvol_right_any hκ hord hE hη (k := k') (a' := xR k)
    (fun j hj => by
      by_contra hlt
      push Not at hlt
      exact absurd (hprev j hlt) (not_le.2 hj)) h1
  have hIR := GB7aAbove4.gb7aEvol_right_any hκ hord hE hη (k := k) hnext h2
  filter_upwards [hIL, hIR, ae_trace_ne_junction_right hκ hord hE hη hk'k hprev h1 h2]
    with ω hL hR hJ t ht y hy
  rcases lt_trichotomy y (xR k) with hlt | heq | hgt
  · exact hL t ht y ⟨hy.1, hlt⟩
  · rw [heq]; exact hJ t ht
  · exact hR t ht y ⟨hgt, hy.2⟩

/-- **The junction barrier, left side** (the reflected evolution and trace `−η̄`): for a left mark position `x_k` with
previous distinct left mark position `x_{k'} > x_k`, if `∑_{xᵢ ≥ x_{k'}} ρᵢ` and `∑_{xᵢ ≥ x_k} ρᵢ` are both at least
`κ/2 − 2`, almost surely the trace never visits `x_k`. -/
theorem ae_trace_ne_junction_left (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k' k : Fin nL} (hk'k : xL k < xL k')
    (hprev : ∀ j, xL k < xL j → xL k' ≤ xL j)
    (h1 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xL k' ≤ xL i), ρL i)
    (h2 : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xL k := by
  have hER := IsIntegratedSLEEvolution.reflect hE
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω hω
    exact LP.isGeneratingTrace_reflect hω
  have e1 : univ.filter (fun i => (-xL) i ≤ (-xL) k') = univ.filter (fun i => xL k' ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  have e2 : univ.filter (fun i => (-xL) i ≤ (-xL) k) = univ.filter (fun i => xL k ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  have hJ := ae_trace_ne_junction_right hκ (GB7a.isOrderedForceWord_reflect hord) hER hη' (k' := k') (k := k)
    (by simp only [Pi.neg_apply, neg_lt_neg_iff]; exact hk'k)
    (fun j hj => by
      simp only [Pi.neg_apply, neg_lt_neg_iff, neg_le_neg_iff] at hj ⊢
      exact hprev j hj)
    (by rw [e1]; exact h1) (by rw [e2]; exact h2)
  filter_upwards [hJ] with ω hω t ht he
  refine hω t ht ?_
  rw [he]
  simp [LP.reflectC]

end Barrier

end Sec5.CfJunction

end InteractingSLE
