/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcModel
import InteractingSLE.Spec.Sec7.ReverseArcSep
import InteractingSLE.Spec.Sec7.ReverseArcExpose

/-!
# Aux. lemma 69, the side: the joint unbounded domain sees the right side of the first trace

Packet PROVE-LEMMA76B (specification §7.2, Aux. lemma 69, p. 273: "The side incident to `D` is the right side of `α₁`
and the left side of `α₂`"). In the chart of the first trace (centred at its seed `0`, `IsChart`), every approach to a
non-tip trace point `α(s) ∈ ℍ` from the joint unbounded domain `D = ℍ \ fill(α([0, q]) ∪ β([0, σ]))` has a positive
chart limit, when the second path `β` (seed `x₂ < 0`) reaches the interior tip `α(q) = β(σ)` without meeting
`α([0, q])` before.

## Proof

The chart limit `y` exists and is real and nonzero (`IsChart.cluster`). Suppose `y < 0`.

* The prefix `β([0, σ))` is free for `A = α([0, q])` (otherwise it is trapped, but its points near the interior tip
  lie in the unbounded domain of `A`: the tip property of `α` and the slit lemma).
* Let `t*` be the last real time of `β` before `σ` and `x* = β(t*)`, a free real point of `A`. Then `x* < 0`: if
  `x* > 0`, the separation lemma (`isTrappedAt_of_isPreconnected`) traps the seed `0` by `β([0, t*])`, hence all of
  `A`, in particular the tip `β(σ)`, which the tip property of `β` frees.
* Let `c` be the chart value at `x*` (`IsChart.free_real`). If `c < y`, the chart curve `f ∘ β` on `[t*, σ]`, from `c`
  to `0` (the tip, `IsChart.tendsto_tip`), traps `y` (separation lemma in the chart); but the chart image of `D`, a
  connected unbounded set off that curve, contains the approach.
* If `y < c`, the chart boundary arc `Φ([y, c − δ/2])`, a connected subset of `A ∪ ℝ` from `α(s)` to a real point left
  of `x*` avoiding `x*`, forces a real point of `A` left of `x*`; with the seed `0 ∈ A` right of `x*`, the separation
  lemma traps `x*` by `A`, which is free.

## Main results

* `ReverseArc.IsChart.tendsto_tip`, `ReverseArc.IsChart.eq_of_inv_eq`, `ReverseArc.IsChart.im_nonneg_inv`;
* **`ReverseArc.exists_pos_tendsto`**: the positive chart limit.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart

namespace ReverseArc

variable {η : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ}

/-- The trace point `η(s)`, `s ≤ q`, is in the filling of the stopped trace. -/
theorem mem_fillH_of_mem_H {s : ℝ≥0} (hs : s ≤ q) (hsH : η s ∈ H) : η s ∈ fillH (η '' Icc 0 q) :=
  ⟨hsH, Or.inl (subset_closure ⟨s, ⟨zero_le, hs⟩, rfl⟩)⟩

/-- Boundary values lie in the closed half-plane. -/
theorem IsChart.inv_mem_Hbar (hch : IsChart η q f Φ) {w : ℂ} (hw : w ∈ Hbar) : Φ w ∈ Hbar := by
  have hcl : Hbar = closure H := (closure_H).symm
  have hneb : (𝓝[H] w).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, ← hcl]; exact hw
  have hlim : Tendsto Φ (𝓝[H] w) (𝓝 (Φ w)) := ((hch.inv_cont w hw).mono H_subset_Hbar).tendsto
  have hc : IsClosed Hbar := by rw [hcl]; exact isClosed_closure
  exact hc.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun v hv => H_subset_Hbar (hch.inv_mem hv).1)

/-- **The tip.** If the tip `η(q)` is interior, the chart tends to `0` at it (from `ℍ \ K`). -/
theorem IsChart.tendsto_tip (hch : IsChart η q f Φ) (htip : η q ∈ H) :
    Tendsto f (𝓝[H \ fillH (η '' Icc 0 q)] (η q)) (𝓝 0) := by
  rw [tendsto_iff_ultrafilter]
  intro V hV
  obtain ⟨y, hyH, hfy, hΦy⟩ := hch.cluster V (η q) hV
  have hqK : η q ∈ fillH (η '' Icc 0 q) := mem_fillH_of_mem_H le_rfl htip
  have hyim : y.im = 0 := le_antisymm (not_lt.1 fun hpos => (hch.inv_mem hpos).2 (hΦy ▸ hqK)) hyH
  have hyeq : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyim])
  rw [hyeq] at hΦy hfy
  rw [hch.tip_fibre htip y.re hΦy, ofReal_zero] at hfy
  exact hfy

/-- **The chart value of a free real point is its only preimage**: if `f → c` at the real point `x` from `ℍ`, then
`Φ(t) = x` forces `t = c`. -/
theorem IsChart.eq_of_inv_eq (hch : IsChart η q f Φ) {x c t : ℝ} (hfc : Tendsto f (𝓝[H] (x : ℂ)) (𝓝 (c : ℂ)))
    (ht : Φ t = x) : t = c := by
  set φ : ℝ → ℂ := fun e => (t : ℂ) + (e : ℂ) * I with hφ
  have hφH : ∀ e : ℝ, 0 < e → φ e ∈ H := fun e he => by
    show 0 < (φ e).im
    simp [hφ, he]
  have hφt : Tendsto φ (𝓝[>] 0) (𝓝[H] (t : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun e he => hφH e he⟩
    have : Tendsto φ (𝓝 0) (𝓝 (φ 0)) := by
      have hc : Continuous φ := by fun_prop
      exact hc.tendsto 0
    simpa [hφ] using this.mono_left nhdsWithin_le_nhds
  have htH : (t : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im; simp
  have hΦφ : Tendsto (fun e => Φ (φ e)) (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun e he => (hch.inv_mem (hφH e he)).1⟩
    rw [← ht]
    exact ((hch.inv_cont _ htH).mono H_subset_Hbar).tendsto.comp hφt
  have h1 : Tendsto (fun e => f (Φ (φ e))) (𝓝[>] 0) (𝓝 (c : ℂ)) := hfc.comp hΦφ
  have h2 : Tendsto (fun e => f (Φ (φ e))) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
    refine (tendsto_nhds_of_tendsto_nhdsWithin hφt).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    exact (hch.f_inv _ (hφH e he)).symm
  exact_mod_cast tendsto_nhds_unique h2 h1

/-- **Aux. lemma 69, the side, in the chart of the first trace** (centred at its seed `0`): an approach to the non-tip
trace point `α(s) ∈ ℍ` from the joint unbounded domain has a positive chart limit. -/
theorem exists_pos_tendsto {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₂ : ℝ} (hp₁ : IsPathGood α ζ₁ 0)
    (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < 0) {q σ : ℝ≥0} {f Φ : ℂ → ℂ} (hch : IsChart α q f Φ)
    (hq : (q : ℝ≥0∞) ≤ ζ₁) (htip : α q ∈ H) (hσ : (σ : ℝ≥0∞) ≤ ζ₂) (hβσ : β σ = α q)
    (hdisj : ∀ t < σ, β t ∉ α '' Icc 0 q) {s : ℝ≥0} (hsq : s < q) (hsH : α s ∈ H)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q ∪ β '' Icc 0 σ)] (α s)) :
    ∃ y : ℝ, 0 < y ∧ Tendsto f U (𝓝 (y : ℂ)) := by
  set A := α '' Icc 0 q with hAdef
  set B := β '' Icc 0 σ with hBdef
  have hAc : IsCompact A := IsPathGood.isCompact_image hp₁ hq
  have hBc : IsCompact B := IsPathGood.isCompact_image hp₂ hσ
  have hc₁ : ContinuousOn α (Icc 0 q) := IsPathGood.continuousOn_Icc hp₁ hq
  have hβc : ContinuousOn β (Icc 0 σ) := IsPathGood.continuousOn_Icc hp₂ hσ
  have hApc : IsPreconnected A := isPreconnected_Icc.image _ hc₁
  have hAim : ∀ w ∈ A, 0 ≤ w.im := by
    rintro _ ⟨t, ht, rfl⟩; exact IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 ht.2).trans hq)
  have hα0 : α 0 = ((0 : ℝ) : ℂ) := IsPathGood.zero hp₁
  have h0A : ((0 : ℝ) : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, hα0⟩
  have hβ0 : β 0 = x₂ := IsPathGood.zero hp₂
  -- the chart limit
  have hUA : (U : Filter ℂ) ≤ 𝓝[H \ fillH A] (α s) :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_left)))
  obtain ⟨y₀, hy₀H, hfy, hΦy⟩ := hch.cluster U (α s) hUA
  have hsK : α s ∈ fillH A := mem_fillH_of_mem_H hsq.le hsH
  have hy₀im : y₀.im = 0 := le_antisymm (not_lt.1 fun hpos => (hch.inv_mem hpos).2 (hΦy ▸ hsK)) hy₀H
  set y := y₀.re with hydef
  have hy₀eq : y₀ = (y : ℂ) := Complex.ext (by simp [hydef]) (by simp [hy₀im])
  rw [hy₀eq] at hfy hΦy
  have hsζ : (s : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hsq.le).trans hq
  have hyne : y ≠ 0 := by
    intro h0
    rw [h0, ofReal_zero, hch.tip] at hΦy
    exact absurd (hp₁.1 hq hsζ hΦy) (ne_of_gt hsq)
  refine ⟨y, lt_of_le_of_ne (not_lt.1 fun hyneg => ?_) (Ne.symm hyne), hfy⟩
  -- the second prefix before the tip
  have hσ0 : 0 < σ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hβ0] at hβσ
    have : (α q).im = 0 := by rw [← hβσ]; simp
    exact absurd htip (by rw [show α q ∈ H ↔ 0 < (α q).im from Iff.rfl, this]; exact lt_irrefl 0)
  have hX : β '' Ico 0 σ ⊆ {w | 0 ≤ w.im} \ A := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2.le).trans hσ), hdisj t ht.2⟩
  have hnottr : ¬ ∀ w ∈ β '' Ico 0 σ, IsTrappedAt A w := by
    intro htr
    -- an interior final piece `α([u, q]) ⊆ ℍ`
    have hIcc : Icc (0 : ℝ≥0) q = Iic q := by ext t; simp
    have hmem : α ⁻¹' H ∈ 𝓝[Iic q] q := by
      rw [← hIcc]
      exact hc₁ q ⟨zero_le, le_rfl⟩ (QuantumZipper.isOpen_H.mem_nhds htip)
    obtain ⟨l, hl, hlsub⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' (lt_of_le_of_lt zero_le hsq)).1 hmem
    obtain ⟨u, hlu, huq⟩ := exists_between (show l < q from hl)
    have hslit : α '' Icc u q ⊆ H := by
      rintro _ ⟨t, ht, rfl⟩
      exact hlsub ⟨hlu.trans_le ht.1, ht.2⟩
    obtain ⟨ε, hε, hball⟩ := exists_ball_of_isFreeAt (IsPathGood.isFreeAt_of_lt hp₁ huq hq)
    have hIcc₂ : Icc (0 : ℝ≥0) σ = Iic σ := by ext t; simp
    have hmem₂ : β ⁻¹' (ball (α q) ε ∩ H) ∈ 𝓝[Iic σ] σ := by
      rw [← hIcc₂]
      refine hβc σ ⟨zero_le, le_rfl⟩ ?_
      rw [hβσ]
      exact (isOpen_ball.inter QuantumZipper.isOpen_H).mem_nhds ⟨mem_ball_self hε, htip⟩
    obtain ⟨l₂, hl₂, hl₂sub⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' hσ0).1 hmem₂
    obtain ⟨t, hlt, htσ⟩ := exists_between (show l₂ < σ from hl₂)
    obtain ⟨htb, htH⟩ := hl₂sub ⟨hlt, htσ.le⟩
    have hz := hball _ htb htH
    have hz' := IsPathGood.mem_H_diff_fillH_of_slit hp₁ huq hq hslit hz (hdisj t htσ)
    exact (htr _ ⟨t, ⟨zero_le, htσ⟩, rfl⟩).notMem hz'
  have hfr : ∀ w ∈ β '' Ico 0 σ, IsFreeAt A w :=
    (isFreeAt_or_isTrappedAt_of_isPreconnected hAc.isClosed
      (isPreconnected_Ico.image _ (hβc.mono Ico_subset_Icc_self)) hX).resolve_right hnottr
  -- the last real time before the tip
  set T := Icc 0 σ ∩ β ⁻¹' Hᶜ with hTdef
  have hTc : IsClosed T := hβc.preimage_isClosed_of_isClosed isClosed_Icc QuantumZipper.isOpen_H.isClosed_compl
  have h0T : (0 : ℝ≥0) ∈ T := ⟨⟨le_rfl, zero_le⟩, fun h => by
    have : (β 0).im = 0 := by rw [hβ0]; simp
    exact absurd h (by rw [show β 0 ∈ H ↔ 0 < (β 0).im from Iff.rfl, this]; exact lt_irrefl 0)⟩
  have hTb : BddAbove T := ⟨σ, fun t ht => ht.1.2⟩
  set ts := sSup T with htsdef
  have hts : ts ∈ T := hTc.csSup_mem ⟨0, h0T⟩ hTb
  have htsσ : ts < σ := lt_of_le_of_ne hts.1.2 fun h => hts.2 (by rw [h, hβσ]; exact htip)
  have hafter : ∀ t, ts < t → t ≤ σ → β t ∈ H := fun t h1 h2 => by
    by_contra hn
    exact absurd (le_csSup hTb ⟨⟨zero_le, h2⟩, hn⟩) (not_le.2 h1)
  have htsζ : (ts : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 htsσ.le).trans hσ
  have hxsim : (β ts).im = 0 := IsPathGood.im_eq_zero hp₂ htsζ hts.2
  set xs := (β ts).re with hxsdef
  have hβts : β ts = (xs : ℂ) := Complex.ext (by simp [hxsdef]) (by simp [hxsim])
  have hxsfree : IsFreeAt A (xs : ℂ) := hβts ▸ hfr _ ⟨ts, ⟨zero_le, htsσ⟩, rfl⟩
  have hxsA : (xs : ℂ) ∉ A := hβts ▸ hdisj ts htsσ
  have hβD : ∀ t, ts < t → t < σ → β t ∈ H \ fillH A := fun t h1 h2 =>
    mem_H_diff_fillH_of_isFreeAt (hfr _ ⟨t, ⟨zero_le, h2⟩, rfl⟩) (hafter t h1 h2.le)
  -- the real point is left of the seed
  have hxs : xs < 0 := by
    rcases lt_trichotomy xs 0 with h | h | h
    · exact h
    · exact absurd (by rw [h]; exact h0A) hxsA
    exfalso
    set K' := β '' Icc 0 ts with hK'def
    have hK'c : IsCompact K' := IsPathGood.isCompact_image hp₂ htsζ
    have hK'pc : IsPreconnected K' := isPreconnected_Icc.image _ (hβc.mono (Icc_subset_Icc_right htsσ.le))
    have hK'im : ∀ w ∈ K', 0 ≤ w.im := by
      rintro _ ⟨t, ht, rfl⟩; exact IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans htsζ)
    have hdK' : ∀ w ∈ K', w ∉ A := by
      rintro _ ⟨t, ht, rfl⟩; exact hdisj t (ht.2.trans_lt htsσ)
    have htrap0 := isTrappedAt_of_isPreconnected hK'c hK'pc hK'im (u := x₂) (v := xs)
      ⟨0, ⟨le_rfl, zero_le⟩, hβ0⟩ ⟨ts, ⟨zero_le, le_rfl⟩, hβts⟩ hx h (fun h' => hdK' _ h' h0A)
    have hAK' : A ⊆ {w | 0 ≤ w.im} \ K' := fun w hw => ⟨hAim w hw, fun h' => hdK' w h' hw⟩
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hK'c.isClosed hApc hAK' with hall | hall
    · exact (hall _ h0A).not_isTrappedAt (by simp) htrap0
    · have h1 := hall (α q) ⟨q, ⟨zero_le, le_rfl⟩, rfl⟩
      have h2 := IsPathGood.isFreeAt_of_lt hp₂ htsσ hσ
      rw [hβσ] at h2
      exact h2.not_isTrappedAt (hAim _ ⟨q, ⟨zero_le, le_rfl⟩, rfl⟩) h1
  -- the chart value of the real point
  obtain ⟨c, hfc, hΦc, δ, hδ, hleft⟩ := hch.free_real xs hxsfree
  have hsH' : 0 < (α s).im := hsH
  have hcy : c ≠ y := by
    intro h
    rw [← h, hΦc] at hΦy
    have : (α s).im = 0 := by rw [← hΦy]; simp
    linarith
  rcases lt_or_gt_of_ne hcy with hcy | hyc
  · -- `c < y`: the chart curve `f ∘ β` on `[t*, σ]` traps `y`
    set b : ℝ≥0 → ℂ := fun t => if t ≤ ts then (c : ℂ) else if t < σ then f (β t) else 0 with hbdef
    have hbI : ∀ t, ts < t → t < σ → b t = f (β t) := fun t h1 h2 => by
      simp [hbdef, not_le.2 h1, h2]
    have hβcI : ∀ t ∈ Icc (0 : ℝ≥0) σ, ContinuousWithinAt β (Icc 0 σ) t := hβc
    have hbc : ContinuousOn b (Icc ts σ) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h1 | h1
      · -- at `t*`
        subst h1
        have hIo : Iio σ ∈ 𝓝 ts := isOpen_Iio.mem_nhds htsσ
        rw [← continuousWithinAt_inter hIo]
        have he : Icc ts σ ∩ Iio σ = insert ts (Ioo ts σ) := by
          ext t'; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_insert_iff, mem_Ioo]
          constructor
          · rintro ⟨⟨h1, -⟩, h2⟩; rcases eq_or_lt_of_le h1 with h | h
            · exact Or.inl h.symm
            · exact Or.inr ⟨h, h2⟩
          · rintro (h | ⟨h1, h2⟩)
            · subst h; exact ⟨⟨le_rfl, htsσ.le⟩, htsσ⟩
            · exact ⟨⟨h1.le, h2.le⟩, h2⟩
        rw [he, continuousWithinAt_insert_self]
        have hbt : b ts = (c : ℂ) := by simp [hbdef]
        show Tendsto b (𝓝[Ioo ts σ] ts) (𝓝 (b ts))
        rw [hbt]
        have hβt : Tendsto β (𝓝[Ioo ts σ] ts) (𝓝[H] (xs : ℂ)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => hafter t ht.1 ht.2.le⟩
          rw [← hβts]
          exact (hβcI ts ⟨zero_le, htsσ.le⟩).tendsto.mono_left
            (nhdsWithin_mono _ fun t ht => ⟨zero_le, ht.2.le⟩)
        exact (hfc.comp hβt).congr' (eventually_nhdsWithin_of_forall fun t ht => (hbI t ht.1 ht.2).symm)
      rcases eq_or_lt_of_le ht.2 with h2 | h2
      · -- at the tip `σ`
        subst h2
        have hIo : Ioi ts ∈ 𝓝 t := isOpen_Ioi.mem_nhds h1
        rw [← continuousWithinAt_inter hIo]
        have he : Icc ts t ∩ Ioi ts = insert t (Ioo ts t) := by
          ext t'; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_insert_iff, mem_Ioo]
          constructor
          · rintro ⟨⟨-, h2⟩, h1⟩; rcases eq_or_lt_of_le h2 with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h1, h⟩
          · rintro (h | ⟨h1, h2⟩)
            · subst h; exact ⟨⟨h1.le, le_rfl⟩, h1⟩
            · exact ⟨⟨h1.le, h2.le⟩, h1⟩
        rw [he, continuousWithinAt_insert_self]
        have hbt : b t = 0 := by simp [hbdef, not_le.2 h1]
        show Tendsto b (𝓝[Ioo ts t] t) (𝓝 (b t))
        rw [hbt]
        have hβt : Tendsto β (𝓝[Ioo ts t] t) (𝓝[H \ fillH A] (α q)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t' ht' => hβD t' ht'.1 ht'.2⟩
          rw [← hβσ]
          exact (hβcI t ⟨zero_le, le_rfl⟩).tendsto.mono_left
            (nhdsWithin_mono _ fun t' ht' => ⟨zero_le, ht'.2.le⟩)
        exact ((hch.tendsto_tip htip).comp hβt).congr'
          (eventually_nhdsWithin_of_forall fun t' ht' => (hbI t' ht'.1 ht'.2).symm)
      · -- inside
        have hn : Ioo ts σ ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨h1, h2⟩
        have hβat : ContinuousAt β t :=
          (hβcI t ⟨zero_le, h2.le⟩).continuousAt (Icc_mem_nhds (lt_of_le_of_lt zero_le h1) h2)
        have hfat : ContinuousAt f (β t) :=
          (hch.cont _ (hβD t h1 h2)).continuousAt
            ((isOpen_H_diff_fillH hAc.isBounded).mem_nhds (hβD t h1 h2))
        refine (ContinuousAt.continuousWithinAt ?_)
        exact (hfat.comp hβat).congr (eventually_of_mem hn fun t' ht' => (hbI t' ht'.1 ht'.2).symm)
    set K := b '' Icc ts σ with hKdef
    have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hbc
    have hKpc : IsPreconnected K := isPreconnected_Icc.image _ hbc
    have hbval : ∀ t, b t = (c : ℂ) ∨ (ts < t ∧ t < σ ∧ b t = f (β t)) ∨ b t = 0 := fun t => by
      by_cases h1 : t ≤ ts
      · left; simp [hbdef, h1]
      by_cases h2 : t < σ
      · right; left; exact ⟨not_le.1 h1, h2, hbI t (not_le.1 h1) h2⟩
      · right; right; simp [hbdef, h1, h2]
    have hKim : ∀ w ∈ K, 0 ≤ w.im := by
      rintro _ ⟨t, -, rfl⟩
      rcases hbval t with h | ⟨h1, h2, h⟩ | h
      · rw [h]; simp
      · rw [h]; exact (hch.maps (hβD t h1 h2)).le
      · rw [h]; simp
    have hcK : (c : ℂ) ∈ K := ⟨ts, ⟨le_rfl, htsσ.le⟩, by simp [hbdef]⟩
    have h0K : ((0 : ℝ) : ℂ) ∈ K := ⟨σ, ⟨htsσ.le, le_rfl⟩, by
      simp [hbdef, not_le.2 htsσ]⟩
    have hyK : (y : ℂ) ∉ K := by
      rintro ⟨t, -, hte⟩
      rcases hbval t with h | ⟨h1, h2, h⟩ | h
      · rw [h] at hte; exact hcy.ne (by exact_mod_cast hte)
      · rw [h] at hte
        have := hch.maps (hβD t h1 h2)
        rw [hte] at this
        have h0 : (0 : ℝ) < ((y : ℝ) : ℂ).im := this
        simp at h0
      · rw [h] at hte; exact hyne (by exact_mod_cast hte.symm)
    obtain ⟨ε', hε', hdisj'⟩ := isTrappedAt_of_isPreconnected hKc hKpc hKim hcK h0K hcy hyneg hyK
    -- the chart image of the joint unbounded domain avoids the curve
    have hABc : IsCompact (A ∪ B) := hAc.union hBc
    set D := H \ fillH (A ∪ B) with hDdef
    have hDpc : IsPreconnected D := HalfPlaneSep.isPreconnected_H_diff_fillH hABc.isClosed hABc.isBounded
    have hDu : ¬ IsBounded D := HalfPlaneSep.not_isBounded_H_diff_fillH hABc.isClosed hABc.isBounded
    have hDA : D ⊆ H \ fillH A := sdiff_subset_sdiff_right (fillH_mono subset_union_left)
    have hfDpc : IsPreconnected (f '' D) := hDpc.image f (hch.cont.mono hDA)
    have hfDu : ¬ IsBounded (f '' D) := by
      intro hb
      obtain ⟨C, hC⟩ := hch.bdd
      obtain ⟨R, hR⟩ := hb.subset_closedBall 0
      refine hDu ((isBounded_closedBall (x := (0 : ℂ)) (r := R + C)).subset fun z hz => ?_)
      have h1 := hR ⟨z, hz, rfl⟩
      rw [mem_closedBall_zero_iff] at h1 ⊢
      have h2 := hC z (hDA hz)
      have h3 : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
        have := norm_sub_le (f z) (f z - z)
        rwa [sub_sub_cancel] at this
      linarith
    have hfDK : f '' D ⊆ H \ K := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨hch.maps (hDA hz), fun hmem => ?_⟩
      obtain ⟨t, ht, hte⟩ := hmem
      have hfz : 0 < (f z).im := hch.maps (hDA hz)
      rcases hbval t with h | ⟨h1, h2, h⟩ | h
      · rw [h] at hte; rw [← hte] at hfz; simp at hfz
      · rw [h] at hte
        have hzβ := hch.injOn (hβD t h1 h2) (hDA hz) hte
        apply hz.2
        exact ⟨hz.1, Or.inl (subset_closure (Or.inr ⟨t, ⟨zero_le, h2.le⟩, hzβ⟩))⟩
      · rw [h] at hte; rw [← hte] at hfz; simp at hfz
    have hsub := subset_H_diff_fillH_of_not_isBounded hKc.isClosed hfDpc hfDu hfDK
    have hev1 : ∀ᶠ z in (U : Filter ℂ), f z ∈ ball (y : ℂ) ε' := hfy (ball_mem_nhds _ hε')
    have hev2 : ∀ᶠ z in (U : Filter ℂ), z ∈ D := hU self_mem_nhdsWithin
    obtain ⟨z, hz1, hz2⟩ := (hev1.and hev2).exists
    exact Set.disjoint_left.1 hdisj' hz1 (hsub ⟨z, hz2, rfl⟩)
  · -- `y < c`: a real point of `A` left of `x*`, so `A` traps `x*`
    have hyδ : y ≤ c - δ := by
      by_contra h
      obtain ⟨x', -, hx'⟩ := hleft y ⟨not_le.1 h, hyc⟩
      rw [hΦy] at hx'
      have : (α s).im = 0 := by rw [hx']; simp
      linarith
    set c' := c - δ / 2 with hc'def
    obtain ⟨x'', hx''lt, hΦc'⟩ := hleft c' ⟨by rw [hc'def]; linarith, by rw [hc'def]; linarith⟩
    have hyc' : y < c' := by rw [hc'def]; linarith
    have hRH : ∀ t : ℝ, (t : ℂ) ∈ Hbar := fun t => by show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im; simp
    set S := Φ '' ((fun t : ℝ => (t : ℂ)) '' Icc y c') with hSdef
    have hSpc : IsPreconnected S :=
      (isPreconnected_Icc.image _ continuous_ofReal.continuousOn).image Φ
        (hch.inv_cont.mono (by rintro _ ⟨t, -, rfl⟩; exact hRH t))
    have hSsub : ∀ w ∈ S, w ∈ A ∨ w.im = 0 := by
      rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
      by_cases hH : Φ t ∈ H
      · exact Or.inl (hch.bdry t hH)
      · exact Or.inr (le_antisymm (not_lt.1 hH) (hch.inv_mem_Hbar (hRH t)))
    have hxsS : (xs : ℂ) ∉ S := by
      rintro ⟨_, ⟨t, ht, rfl⟩, hte⟩
      have := hch.eq_of_inv_eq hfc hte
      rw [this] at ht
      linarith [ht.2]
    have hreal : ∃ x' : ℝ, x' < xs ∧ (x' : ℂ) ∈ A := by
      by_contra hno
      push Not at hno
      set U₁ : Set ℂ := {w | w.re < xs} ∩ Aᶜ with hU₁
      set U₂ : Set ℂ := ({w : ℂ | w.im = 0} ∩ {w | w.re ≤ xs})ᶜ with hU₂
      have hU₁o : IsOpen U₁ := (isOpen_lt continuous_re continuous_const).inter hAc.isClosed.isOpen_compl
      have hU₂o : IsOpen U₂ := ((isClosed_eq continuous_im continuous_const).inter
        (isClosed_le continuous_re continuous_const)).isOpen_compl
      have hcover : S ⊆ U₁ ∪ U₂ := by
        intro w hw
        by_cases hray : w ∈ {w : ℂ | w.im = 0} ∩ {w | w.re ≤ xs}
        · left
          have hwim : w.im = 0 := hray.1
          have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hwim])
          have hlt : w.re < xs := lt_of_le_of_ne hray.2 fun h => hxsS (by rw [hwr, h] at hw; exact hw)
          refine ⟨hlt, fun hA => hno w.re hlt ?_⟩
          rw [← hwr]; exact hA
        · exact Or.inr hray
      have h1 : (S ∩ U₁).Nonempty := by
        refine ⟨Φ c', ⟨_, ⟨c', ⟨hyc'.le, le_rfl⟩, rfl⟩, rfl⟩, ?_⟩
        rw [hΦc']
        exact ⟨by simpa using (hx''lt.trans_le le_rfl), hno x'' hx''lt⟩
      have h2 : (S ∩ U₂).Nonempty := by
        refine ⟨Φ y, ⟨_, ⟨y, ⟨le_rfl, hyc'.le⟩, rfl⟩, rfl⟩, ?_⟩
        rw [hΦy]
        rintro ⟨him, -⟩
        have : (α s).im = 0 := him
        linarith
      obtain ⟨w, hwS, hw1, hw2⟩ := hSpc U₁ U₂ hU₁o hU₂o hcover h1 h2
      rcases hSsub w hwS with hA | him
      · exact hw1.2 hA
      · exact hw2 ⟨him, show w.re ≤ xs from le_of_lt hw1.1⟩
    obtain ⟨x', hx'lt, hx'A⟩ := hreal
    exact hxsfree.not_isTrappedAt (by simp)
      (isTrappedAt_of_isPreconnected hAc hApc hAim hx'A h0A hx'lt hxs hxsA)

end ReverseArc

end Sec7

end InteractingSLE
