/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Sec2.Assembly2UpTo

/-!
# GB7a's deterministic comparison for a stopped local solution

This is the landed `GB7aCmpPath` argument with `IsSLEPathUpTo` in place
of `IsForcePath`. Its two maximality fields were never used: the continuous
driver and gap limits use only continuity before the stop and the state limit
at it. Every geometric and energy estimate is reused from the landed proof.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal
namespace InteractingSLE.Sec5.Aux61R45
open GB7a
open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {b w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- Continuous driver and finite gap limits for a local solution. -/
theorem exists_driver_upTo (h : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ)
    (hT0 : 0 < T)
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) :
    ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ (∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) ∧
      ∀ j, ∃ L : ℝ, Tendsto (fun t => vR j t - w t) (𝓝[<] T) (𝓝 L) := by
  rcases hTζ.lt_or_eq with hlt | heq
  · obtain ⟨t₂, hTt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hlt
    have ht₂0 : 0 ≤ t₂ := T.coe_nonneg.trans hTt₂.le
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    refine ⟨frozenDrive w t₂, continuous_frozenDrive_of_lt h.continuousOn_w ht₂ζ, ?_,
      fun s hs0 hsT => frozenDrive_eq ⟨hs0, hsT.le.trans hTt₂.le⟩, fun j => ⟨vR j T - w T, ?_⟩⟩
    · rw [frozenDrive_eq ⟨le_rfl, ht₂0⟩]
      simpa using h.w_zero
    · have hc := ((h.continuousOn_vR j).sub h.continuousOn_w).continuousAt (hopen.mem_nhds hlt)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · obtain ⟨w₀, vL₀, vR₀, hl⟩ := hlimζ T hT0 heq
    have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hl
    have hwc : ContinuousOn w (Iio T) := h.continuousOn_w.mono fun t ht => by
      show (t : ℝ≥0∞) < ζ
      rw [← heq]
      exact ENNReal.coe_lt_coe.2 ht
    refine ⟨FiniteEndpoint.extDriver w T w₀, FiniteEndpoint.continuous_extDriver hwc hw, ?_,
      fun s hs0 hsT => FiniteEndpoint.extDriver_of_lt hs0 hsT, fun j => ⟨vR₀ j - w₀, ?_⟩⟩
    · rw [FiniteEndpoint.extDriver_of_lt le_rfl (NNReal.coe_pos.2 hT0)]
      simpa using h.w_zero
    · have hv : Tendsto (fun t => vR j t) (𝓝[<] T) (𝓝 (vR₀ j)) :=
        (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hl
      exact hv.sub hw

/-- A right interval visit gives the GB7a comparison picture, including a terminal visit. -/
theorem rightCmpPath_of_visit_upTo (h : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nR} {a' : ℝ} (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo (xR k) a', η t = y) :
    ∃ q : ℚ, RightCmpPath ρL ρR w vL vR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal := by
  obtain ⟨t₀, ht₀, y, hy, he⟩ := hvis
  have hwc := h.continuousOn_w
  have hw0 := h.w_zero
  have hxk : 0 ≤ xR k := hord.2.2.2 k
  obtain ⟨p, T, y', hp0, hpT, hTt₀, hy', hηT, hH⟩ := exists_firstContact hη hwc hw0 hxk ht₀ hy he
  have hTζ : (T : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hTt₀).trans ht₀
  have hT0 : 0 < T := NNReal.coe_pos.1 (hp0.trans hpT)
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hpT
  have hq0 : 0 < (q : ℝ) := hp0.trans hpq
  have hqN : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  obtain ⟨U, hU, hU0, hUw, hlimV⟩ := exists_driver_upTo h hTζ hT0 hlimζ
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
  have hmemζ : ∀ r : ℝ, r ≤ T → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun r hr =>
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
  -- (3) the limit point is alive at `q`; strict order of the right marks
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
  obtain ⟨C, hC⟩ := exists_energy_bound_of_restart hηR hU hU0 hq0.le hqT' hHR hinjR hy'0 hlimR hv
    û c hpkg hne hsep hcore
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

/-- The reflected, left-hand version. -/
theorem leftCmpPath_of_visit_upTo (h : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nL} {a : ℝ} (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo a (xL k), η t = y) :
    ∃ q : ℚ, RightCmpPath ρR ρL (fun t => -w t) (fun i t => -vR i t) (fun i t => -vL i t) ζ k none
      (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal := by
  have hinj' : InjOn (fun t => LP.reflectC (η t)) {t | (t : ℝ≥0∞) ≤ ζ} := fun s hs t ht hst => by
    have := congrArg LP.reflectC hst
    simp only [LP.reflectC_reflectC] at this
    exact hinj hs ht this
  have hlim' : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nR → ℝ) (vR₀ : Fin nL → ℝ),
      Tendsto (fun t => ((-w) t, fun i => (fun i => -vR i) i t, fun i => (fun i => -vL i) i t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) := by
    intro T hT hζ
    obtain ⟨w₀, vL₀, vR₀, hl⟩ := hlimζ T hT hζ
    refine ⟨-w₀, -vR₀, -vL₀, ?_⟩
    have hc : Continuous fun z : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => (-z.1, -z.2.2, -z.2.1) := by
      fun_prop
    exact (hc.tendsto _).comp hl
  have hvis' : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo ((-xL) k) (-a), LP.reflectC (η t) = y := by
    obtain ⟨t, ht, y, hy, he⟩ := hvis
    refine ⟨t, ht, -y, ⟨by simp only [Pi.neg_apply]; linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
    rw [he]
    simp [LP.reflectC]
  have hnext' : ∀ j, (-xL) k < (-xL) j → -a ≤ (-xL) j := fun j hj => by
    simp only [Pi.neg_apply, neg_lt_neg_iff] at hj
    simp only [Pi.neg_apply, neg_le_neg_iff]
    exact hnext j hj
  obtain ⟨q, hq⟩ := rightCmpPath_of_visit_upTo h.reflect (isOrderedForceWord_reflect hord)
    (LP.isGeneratingTrace_reflect hη) hinj' hlim' hnext' hvis'
  have e : univ.filter (fun i => (-xL) i ≤ (-xL) k) = univ.filter (fun i => xL k ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  rw [e] at hq
  exact ⟨q, hq⟩


end InteractingSLE.Sec5.Aux61R45
