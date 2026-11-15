/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Supplement.RLCDG2a

/-!
# The continuation-threshold half of Lemma 5.1: no visit before the lifetime at cumulative weight `≤ −2`

Packet PROVE-RLC-E. `RLC.ThresholdVisitStatement` (PROVE-RLC-D, `RLCDG2a.lean`) is the threshold half of Lemma 5.1
of Astra's shortcut note (R52): a flow line does not visit, strictly before its lifetime, an open boundary interval
on one side of the seed whose cumulative weight is `≤ −2`.

**Pathwise argument** (`RLC.exists_merge_of_visit_right`). Let the trace visit `(x_k, a')` (`a'` at most the next
right mark) at a time `t₀ < ζ`. As in GB7a's pathwise half (`GB7a.rightCmpPath_of_visit`), take the first real
contact `T ≤ t₀` after an interior rational time `p` (`GB7a.exists_firstContact`): `η(T) = y' ∈ (x_k, a')` and
`η ∈ ℍ` on `[p, T)`. Now `T < ζ`, so the driving state is continuous at `T` and a continuous driver agrees with `w`
on `[0, T₂]` for some `T₂ ∈ (T, ζ)`. Then:

1. every right mark `j` with `x_j ≤ x_k` collides with the driver at `T`: in the chart at a rational `q ∈ (p, T)`
   the mark sits below the real flow of `y'` (`GB7a.lt_re_of_centred`), and its gap tends to `0` at `T`
   (`GB7a.eq_zero_of_tendsto_restart`);
2. no right mark `j` with `x_j > x_k` collides at `T`: at a right collision the tip `η(T)` is a real point
   `≥ x_j ≥ a'` (`IsLoewnerTraceLT.exists_tip_real_of_collision_right`, with the horizon `T₂ > T`), but
   `η(T) = y' < a'`.

So the right group merged with the driver at `T` is exactly `{j : x_j ≤ x_k}`, whose weight is the cumulative
weight; if it is `≤ −2`, the threshold condition holds at `T < ζ`, contrary to the lifetime's definition
(`not_threshold`). The left side is the right side of the reflected path.

Main results:

* `RLC.exists_merge_of_visit_right`, `RLC.not_visit_right`, `RLC.not_visit_left` (one path);
* **`RLC.thresholdVisitStatement : RLC.ThresholdVisitStatement`** (the named input of PROVE-RLC-D, now a theorem);
* **`RLC.ae_admissible_of_visit'`**: Lemma 5.1 of the note (R52), unconditional.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace RLC

open GB7a

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The merged right group at the first contact (one path).** If the trace visits `(x_k, a')` strictly before the
lifetime, where `a'` is at most the next right mark after `x_k`, there is a time `T < ζ` at which the right marks
merged with the driver are exactly those at or left of `x_k`. -/
theorem exists_merge_of_visit_right (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) {k : Fin nR} {a' : ℝ}
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ ∃ y ∈ Ioo (xR k) a', η t = y) :
    ∃ T : ℝ≥0, (T : ℝ≥0∞) < ζ ∧ ∀ j, vR j T = w T ↔ xR j ≤ xR k := by
  obtain ⟨t₀, ht₀, y, hy, he⟩ := hvis
  have hwc := h.continuousOn_w
  have hxk : 0 ≤ xR k := hord.2.2.2 k
  obtain ⟨p, T, y', hp0, hpT, hTt₀, hy', hηT, hH⟩ :=
    exists_firstContact hη hwc h.w_zero hxk ht₀.le hy he
  have hTζ : (T : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 hTt₀).trans_lt ht₀
  have hT0 : 0 < T := NNReal.coe_pos.1 (hp0.trans hpT)
  -- a horizon `T₂ ∈ (T, ζ)` and a continuous driver agreeing with `w` up to it
  obtain ⟨T₂, hTT₂e, hT₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTζ
  have hTT₂ : (T : ℝ) < T₂ := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hTT₂e)
  set U : ℝ → ℝ := frozenDrive w T₂ with hUdef
  have hU : Continuous U :=
    continuous_frozenDrive_of_lt hwc (by rw [ENNReal.ofReal_coe_nnreal]; exact hT₂ζ)
  have hUw₂ : ∀ s : ℝ, 0 ≤ s → s < T₂ → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, hs.le⟩
  have hU0 : U 0 = 0 := by
    rw [hUw₂ 0 le_rfl (hT0.trans_le (NNReal.coe_le_coe.2 (ENNReal.coe_lt_coe.1 hTT₂e).le)),
      Real.toNNReal_zero, h.w_zero]
  have hUw : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal := fun s hs0 hs =>
    hUw₂ s hs0 (hs.trans hTT₂)
  set ηR : ℝ → ℂ := fun s => η s.toNNReal with hηRdef
  have hηR : IsLoewnerTraceLT U T ηR := isLoewnerTraceLT_of_agree hη hTζ.le hUw
  have hηR₂ : IsLoewnerTraceLT U T₂ ηR := isLoewnerTraceLT_of_agree hη hT₂ζ.le hUw₂
  have hltζ : ∀ t : ℝ≥0, (t : ℝ) < T₂ → (t : ℝ≥0∞) < ζ := fun t ht =>
    (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ht)).trans hT₂ζ
  -- the centred right force coordinates and their packages on `[0, s]`, `s < T₂`
  set ûR : Fin nR → ℝ → ℝ := fun j r => vR j r.toNNReal - w r.toNNReal with hûR
  have pkgR := fun j (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T₂) => centredPkg hwc (h.continuousOn_vR j)
    (fun t ht => h.integrable_gapR ht j) (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hT₂ζ.le hUw₂
    hs0 hsT
  have hnnR : ∀ j, ∀ s : ℝ, 0 ≤ s → s < T₂ → 0 ≤ ûR j s := fun j s hs0 hsT => by
    refine sub_nonneg.2 (h.w_le_vR (hltζ _ ?_) j)
    rwa [Real.coe_toNNReal _ hs0]
  -- no right force coordinate meets the driver on `[p, T)` (the tip would be real)
  have hoffR : ∀ t : ℝ≥0, (p : ℝ) ≤ t → t < T → ∀ j, w t ≠ vR j t := by
    intro t hpt htT j heq
    have htT' : (t : ℝ) < T := NNReal.coe_lt_coe.2 htT
    obtain ⟨hc, hue, hi, hn⟩ := pkgR j t t.coe_nonneg (htT'.trans hTT₂)
    obtain ⟨x, hx, -, -⟩ := hηR.exists_tip_real_of_collision_right hU hU0 t.coe_nonneg htT' hc
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt (htT'.trans hTT₂))) hue hi hn (by simp [heq])
    have hHt := hH t hpt htT
    have : (η t).im = 0 := by
      have hx' : η t = x := by simpa [hηRdef] using hx
      rw [hx', Complex.ofReal_im]
    exact absurd this (ne_of_gt hHt)
  have hy'0 : 0 < y' := lt_of_le_of_lt hxk hy'.1
  -- the chart at a rational time `q ∈ (p, T)`
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hpT
  have hq0 : 0 < (q : ℝ) := hp0.trans hpq
  have hqT' : (q : ℝ) < T := hqT
  have hHR : ∀ s ∈ Ioo (q : ℝ) T, ηR s ∈ H := fun s hs => by
    have hs0 : 0 ≤ s := (hq0.trans hs.1).le
    refine hH s.toNNReal ?_ ?_
    · rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.2
  have hmemζ : ∀ r : ℝ, r ≤ T → ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun r hr =>
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr)).trans hTζ.le
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
    have hrT := hinj (hmemζ r (hr.2.trans hqT'.le)) hTζ.le hry
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hrT
    simp only [Real.coe_toNNReal _ hr.1] at this
    linarith [hr.2]
  have hlimR : Tendsto ηR (𝓝[<] (T : ℝ)) (𝓝 (y' : ℂ)) := by
    rw [← hηT]
    exact tendsto_comp_toNNReal hη hTζ.le hT0
  obtain ⟨v, hv⟩ := exists_isForwardSol_at_restart hηR hU hU0 hq0.le hqT' hHR hinjR hy'0.ne' hlimR hyq
  have hsT : ∀ s : ℝ, 0 ≤ s → s < T → s.toNNReal < T := fun s hs0 hsT => by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hsT
  have hneR : ∀ j, ∀ s ∈ Ico (q : ℝ) T, ûR j s ≠ 0 := by
    intro j s hs h0
    have hs0 : 0 ≤ s := hq0.le.trans hs.1
    refine hoffR s.toNNReal (by rw [Real.coe_toNNReal _ hs0]; linarith [hs.1]) (hsT s hs0 hs.2) j ?_
    simp only [hûR] at h0
    linarith
  have hûR0 : ∀ j, ûR j 0 = xR j := fun j => by simp [hûR, h.vR_zero j, h.w_zero]
  have hpkgq := fun j => pkgR j q hq0.le (hqT'.trans hTT₂)
  have hlo : ∀ j, xR j ≤ xR k → ûR j q < (v q).re := fun j hj =>
    lt_re_of_centred hU hU0 hy'0 hq0.le hv (hpkgq j).1
      (fun s hs => hnnR j s hs.1 ((hs.2.trans_lt hqT').trans hTT₂)) (hpkgq j).2.1
      (by rw [hûR0]; linarith [hy'.1])
  have rpkgR := fun j (s : ℝ) (hs : s ∈ Ico (q : ℝ) T) =>
    Aux25.centred_restrict (W := U) hq0.le hs.1 le_rfl
      (pkgR j s (hq0.le.trans hs.1) (hs.2.trans hTT₂))
  -- the value of a centred coordinate at `T`
  have hûRT : ∀ j, ûR j T = vR j T - w T := fun j => by simp only [hûR, Real.toNNReal_coe]
  refine ⟨T, hTζ, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · -- a colliding mark puts the tip at a real point `≥ x_j`; the tip is `y' < a'`
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hc, hue, hi, hn⟩ := pkgR j T T.coe_nonneg hTT₂
    obtain ⟨x, hx, hx0, -⟩ := hηR₂.exists_tip_real_of_collision_right hU hU0 T.coe_nonneg hTT₂ hc
      (fun s hs => hnnR j s hs.1 (hs.2.trans_lt hTT₂)) hue hi hn (by simp only [Real.toNNReal_coe, hj, sub_self])
    have hxT : η T = x := by simpa [hηRdef] using hx
    rw [hηT] at hxT
    have hxy : y' = x := Complex.ofReal_injective hxT
    simp only [Real.toNNReal_zero, h.vR_zero j, h.w_zero, sub_zero] at hx0
    linarith [hnext j hlt, hy'.2]
  · -- a mark at or left of `x_k` collides at `T`
    have hTs : (T : ℝ) < ((T : ℝ) + T₂) / 2 := by linarith
    have hsT₂ : ((T : ℝ) + T₂) / 2 < T₂ := by linarith
    have hcont := (pkgR j (((T : ℝ) + T₂) / 2) (by positivity) hsT₂).1
    have hL : Tendsto (ûR j) (𝓝[<] (T : ℝ)) (𝓝 (ûR j T)) :=
      (hcont.continuousAt (Icc_mem_nhds (NNReal.coe_pos.2 hT0) hTs)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hL0 := eq_zero_of_tendsto_restart hηR hU hU0 hq0.le hqT' hHR hy'0 hlimR hv (u := ûR j)
      (fun s hs => ⟨(rpkgR j s hs).1, (rpkgR j s hs).2.1, (rpkgR j s hs).2.2.1⟩)
      (fun s hs => lt_of_le_of_ne (hnnR j s (hq0.le.trans hs.1) (hs.2.trans hTT₂)) (hneR j s hs).symm)
      (hlo j hj).le hL
    rw [hûRT] at hL0
    linarith

/-- **No visit before the lifetime at cumulative weight `≤ −2`, right side (one path).** -/
theorem not_visit_right (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) {k : Fin nR} {a' : ℝ}
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i ≤ -2) :
    ¬ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ ∃ y ∈ Ioo (xR k) a', η t = y := by
  intro hvis
  obtain ⟨T, hTζ, hiff⟩ := exists_merge_of_visit_right h hord hη hinj hnext hvis
  refine h.not_threshold hTζ (Or.inr ?_)
  have e : univ.filter (fun i => vR i T = w T) = univ.filter (fun i => xR i ≤ xR k) :=
    Finset.filter_congr fun i _ => hiff i
  show (∑ i ∈ univ.filter (fun i => vR i T = w T), ρR i) ≤ -2
  rw [e]
  exact hS

/-- **No visit before the lifetime at cumulative weight `≤ −2`, left side (one path)**: the right side for the
reflected path and the reflected trace `−η̄`. -/
theorem not_visit_left (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) {k : Fin nL} {a : ℝ}
    (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hS : ∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i ≤ -2) :
    ¬ ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ ∃ y ∈ Ioo a (xL k), η t = y := by
  rintro ⟨t, ht, y, hy, he⟩
  have hinj' : InjOn (fun t => LP.reflectC (η t)) {t | (t : ℝ≥0∞) ≤ ζ} := fun s hs t ht hst => by
    have := congrArg LP.reflectC hst
    simp only [LP.reflectC_reflectC] at this
    exact hinj hs ht this
  have hnext' : ∀ j, (-xL) k < (-xL) j → -a ≤ (-xL) j := fun j hj => by
    simp only [Pi.neg_apply, neg_lt_neg_iff] at hj
    simp only [Pi.neg_apply, neg_le_neg_iff]
    exact hnext j hj
  have e : univ.filter (fun i => (-xL) i ≤ (-xL) k) = univ.filter (fun i => xL k ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  refine not_visit_right h.reflect (isOrderedForceWord_reflect hord) (LP.isGeneratingTrace_reflect hη) hinj'
    hnext' (by rw [e]; exact hS) ⟨t, ht, -y, ⟨?_, ?_⟩, ?_⟩
  · simp only [Pi.neg_apply]; linarith [hy.2]
  · linarith [hy.1]
  · rw [he]
    simp [LP.reflectC]

end Path

/-- **The continuation-threshold half of Lemma 5.1** (`RLC.ThresholdVisitStatement`, the named input of
PROVE-RLC-D): for the angle-`θ` flow line from `x`, an open interval `(a, a')` on one side of the seed with constant
data `v` and cumulative weight `≤ −2` is not visited strictly before the lifetime. -/
theorem thresholdVisitStatement : ThresholdVisitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ a a' v hv Ω _ P _ h _ η ζ hη
  obtain ⟨_h', 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hη
  have hord := Theorem15.isOrderedForceWord_flowLine b jumps x
  have hE := hcpl.1
  have hinj := Theorem15.aux25Statement κ hκ hκ4 _ _ _ _ hord P 𝓕 W VL VR B ζ hE
  have hpath := hE.2.2.2.2
  have key : ∀ ω t (y : ℝ), η ω t = y → η ω t - x = ((y - x : ℝ) : ℂ) := fun ω t y he => by
    rw [he]
    push_cast
    ring
  refine ⟨fun hxa hS => ?_, fun hax hS => ?_⟩
  · rcases le_or_gt a' a with haa | haa
    · exact ae_of_all _ fun ω t _ y hy => absurd (hy.1.trans hy.2) (not_lt.2 haa)
    obtain ⟨k, hka, hnext, hsum⟩ := Supp8.exists_mark_right hκ hb θ hxa haa hv
    filter_upwards [hinj, hpath, htr] with ω h1 h3 h4 t ht y hy he
    exact not_visit_right h3.isForcePath hord h4 (h1 _ h4) (k := k) (a' := a' - x) hnext
      (by rw [hsum]; exact hS) ⟨t, ht, y - x, ⟨by linarith [hy.1], by linarith [hy.2]⟩, key ω t y he⟩
  · rcases le_or_gt a' a with haa | haa
    · exact ae_of_all _ fun ω t _ y hy => absurd (hy.1.trans hy.2) (not_lt.2 haa)
    obtain ⟨k, hka, hnext, hsum⟩ := Supp8.exists_mark_left hκ hb θ hax haa hv
    filter_upwards [hinj, hpath, htr] with ω h1 h3 h4 t ht y hy he
    exact not_visit_left h3.isForcePath hord h4 (h1 _ h4) (k := k) (a := a - x) hnext
      (by rw [hsum]; exact hS) ⟨t, ht, y - x, ⟨by linarith [hy.1], by linarith [hy.2]⟩, key ω t y he⟩

/-- **Lemma 5.1 of the shortcut note (R52), unconditional**: `ae_admissible_of_visit` with the threshold half proved.
Almost surely, if either flow visits the middle interval `(a, a')` of height `C` strictly before its lifetime, then
`−λ − θ₂χ < C < λ − θ₁χ`. -/
theorem ae_admissible_of_visit' {κ θ₁ θ₂ W : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ₁ < θ₂) {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {a a' C : ℝ}
    (ha : 0 ≤ a) (ha' : a' ≤ W) (hcC : ∀ y ∈ Ioo a a', y ∉ J → c y = C)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData P H c J)
    (Γ₁ Γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞) (h₁ : IsFlowLine κ c J W θ₁ P H Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ P H Γ₂ U₂) :
    ∀ᵐ ω ∂P, ((∃ t : ℝ≥0, (t : ℝ≥0∞) < U₁ ω ∧ ∃ y ∈ Ioo a a', Γ₁ ω t = y) ∨
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < U₂ ω ∧ ∃ y ∈ Ioo a a', Γ₂ ω t = y)) →
      -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ :=
  ae_admissible_of_visit thresholdVisitStatement hκ hκ4 hθ hc ha ha' hcC P H hH Γ₁ Γ₂ U₁ U₂ h₁ h₂

end RLC

end InteractingSLE
