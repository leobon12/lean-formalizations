/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxChart
import InteractingSLE.Spec.Supplement.SB2MtDrv
import InteractingSLE.Spec.ZhanGT4.A1MargClock
import InteractingSLE.Spec.Sec7.Lemma71Capacity
import InteractingSLE.Spec.Supplement.SB2FinConfig

/-!
# Identification of drivers through hulls: the topological core

Packet PROVE-SB2-LCMEAN, round 14 (item 4: identification with `EL`). The relative stage driver `EL j` and the
canonical driver of the matched B-stage are both determined by their hulls, and the two hull families are images of
B's piece under charts of the retained complement that differ by a real translation. Generic facts:

* `diff_eq_of_frontier`: if `ℍ ∖ K₁ ⊆ ℍ ∖ K₂`, the complement `ℍ ∖ K₂` is preconnected, `ℍ ∖ K₁` is open and
  nonempty, and every frontier point of `K₁` in `ℍ` lies in `K₂`, then `ℍ ∖ K₁ = ℍ ∖ K₂`;
* `eq_of_diff_eq`: two subsets of `ℍ` with the same complement in `ℍ` are equal;
* **`eq_of_frontier_subset_hull`**: two `ℍ`-hulls each containing the other's frontier points in `ℍ` are equal. This is
  how two chains of the same piece (`FinRel.IsSB2RelChain`'s frontier and inclusion clauses) meet;
* **`time_eq_of_fwdHull_eq_add_const`**: Loewner hulls equal up to a real translation have the same time (half-plane
  capacity `2t`, translation invariant);
* **`eqOn_of_fwdHull_eq_add_const_clock`**: if, along two clocks, the hulls of `W₂` are those of `W₁` translated by `d`
  on `[0, S₀]`, the first clock continuous from `0`, then the clocks agree, `d = 0`, and `W₁ = W₂` up to the time
  reached (`Mt.eqOn_of_fwdHull_eq_add_const` and the intermediate value theorem);
* **`fwdHull_eq_add_of_chains`**: two relative chains (`FinRel.IsSB2RelChain`) of the same piece over the same
  retained set, in two domain charts of its complement that differ by a real translation `d`, have hulls that differ
  by `d` at every `s` (frontier and inclusion clauses, `eq_of_frontier_subset_hull`);
* **`eqOn_of_chains`**: their drivers agree up to the clock time at `S₀`, and the clocks agree;
* `fillH_start_subset`, **`tL_eq_of_chains`**: two such chains start at the same time of the piece (before its start
  the piece lies in the retained fill, after it the hull grows).

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mx

/-- **Equal complements from the frontier clause.** -/
theorem diff_eq_of_frontier {K₁ K₂ : Set ℂ} (ho₁ : IsOpen (H \ K₁)) (hc₂ : IsPreconnected (H \ K₂))
    (hne : (H \ K₁).Nonempty) (h12 : H \ K₁ ⊆ H \ K₂)
    (hfr : frontier K₁ ∩ H ⊆ K₂) : H \ K₁ = H \ K₂ := by
  refine Subset.antisymm h12 ?_
  have hsub : H \ K₂ ⊆ (H \ K₁) ∪ interior K₁ := by
    rintro z ⟨hzH, hzK₂⟩
    by_cases hz₁ : z ∈ K₁
    · right
      by_contra hint
      exact hzK₂ (hfr ⟨⟨subset_closure hz₁, hint⟩, hzH⟩)
    · exact Or.inl ⟨hzH, hz₁⟩
  have hdisj : Disjoint (H \ K₁) (interior K₁) :=
    Set.disjoint_left.2 fun z hz hzi => hz.2 (interior_subset hzi)
  have hmeet : ((H \ K₂) ∩ (H \ K₁)).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, h12 hz, hz⟩
  exact hc₂.subset_left_of_subset_union ho₁ isOpen_interior hdisj hsub hmeet

/-- Two subsets of `ℍ` with the same complement in `ℍ` are equal. -/
theorem eq_of_diff_eq {K₁ K₂ : Set ℂ} (h₁ : K₁ ⊆ H) (h₂ : K₂ ⊆ H) (h : H \ K₁ = H \ K₂) : K₁ = K₂ := by
  ext z
  constructor
  · intro hz
    by_contra hz₂
    have : z ∈ H \ K₂ := ⟨h₁ hz, hz₂⟩
    rw [← h] at this
    exact this.2 hz
  · intro hz
    by_contra hz₁
    have : z ∈ H \ K₁ := ⟨h₂ hz, hz₁⟩
    rw [h] at this
    exact this.2 hz

/-- **Two `ℍ`-hulls each containing the other's frontier points in `ℍ` are equal.** -/
theorem eq_of_frontier_subset_hull {K₁ K₂ : Set ℂ} (hA₁ : IsHPHull K₁) (hA₂ : IsHPHull K₂)
    (hf₁ : frontier K₁ ∩ H ⊆ K₂) (hf₂ : frontier K₂ ∩ H ⊆ K₁) : K₁ = K₂ := by
  obtain ⟨R, hR⟩ := (hA₁.2.1.union hA₂.2.1).subset_ball 0
  set z₀ : ℂ := ((|R| + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀H : z₀ ∈ H := by
    show 0 < z₀.im
    simp only [hz₀, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  have hz₀K : z₀ ∉ K₁ ∪ K₂ := by
    intro hz
    have h1 := hR hz
    rw [Metric.mem_ball, dist_zero_right, hz₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < |R| + 1)] at h1
    linarith [le_abs_self R]
  have hz₁ : z₀ ∈ H \ K₁ := ⟨hz₀H, fun h => hz₀K (Or.inl h)⟩
  have hz₂ : z₀ ∈ H \ K₂ := ⟨hz₀H, fun h => hz₀K (Or.inr h)⟩
  have hpc : ∀ {A : Set ℂ}, IsHPHull A → IsPreconnected (H \ A) := fun hA =>
    hA.2.2.2.isPathConnected.isConnected.isPreconnected
  have hsub : ∀ {A B : Set ℂ}, IsHPHull A → IsHPHull B → frontier A ∩ H ⊆ B → z₀ ∈ H \ A → z₀ ∈ H \ B →
      H \ B ⊆ H \ A := by
    intro A B hA hB hf hzA hzB
    have hcov : H \ B ⊆ (H \ A) ∪ interior A := by
      rintro z ⟨hzH, hzB'⟩
      by_cases hzA' : z ∈ A
      · right
        by_contra hint
        exact hzB' (hf ⟨⟨subset_closure hzA', hint⟩, hzH⟩)
      · exact Or.inl ⟨hzH, hzA'⟩
    have hdisj : Disjoint (H \ A) (interior A) :=
      Set.disjoint_left.2 fun z hz hzi => hz.2 (interior_subset hzi)
    exact (hpc hB).subset_left_of_subset_union hA.2.2.1 isOpen_interior hdisj hcov ⟨z₀, hzB, hzA⟩
  exact eq_of_diff_eq hA₁.1 hA₂.1
    (Subset.antisymm (hsub hA₂ hA₁ hf₂ hz₂ hz₁) (hsub hA₁ hA₂ hf₁ hz₁ hz₂))

/-- **Loewner hulls equal up to a real translation have the same time.** -/
theorem time_eq_of_fwdHull_eq_add_const {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (hW₁0 : W₁ 0 = 0) (hW₂0 : W₂ 0 = 0) {t₁ t₂ d : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h : QuantumZipper.fwdHull W₂ t₂ = (fun z : ℂ => z + d) '' QuantumZipper.fwdHull W₁ t₁) : t₁ = t₂ := by
  have h1 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW₁ hW₁0 ht₁ rfl
  have h2 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW₂ hW₂0 ht₂ h
  have e : (fun z : ℂ => z + d) '' QuantumZipper.fwdHull W₁ t₁ =
      (fun z : ℂ => z - ((-d : ℝ) : ℂ)) '' QuantumZipper.fwdHull W₁ t₁ :=
    image_congr fun z _ => by push_cast; ring
  rw [e, ZhanGT4.A1Marg.hcapSet_image_sub, h1] at h2
  linarith

/-- **Drivers from translated hulls along clocks.** -/
theorem eqOn_of_fwdHull_eq_add_const_clock {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (hW₁0 : W₁ 0 = 0) (hW₂0 : W₂ 0 = 0) {τ₁ τ₂ : ℝ → ℝ} {S₀ d : ℝ} (hS₀ : 0 ≤ S₀)
    (hτ₁c : ContinuousOn τ₁ (Icc 0 S₀)) (hτ₁0 : τ₁ 0 = 0) (hpos : 0 < τ₁ S₀)
    (hτ₁ : ∀ s ∈ Icc 0 S₀, 0 ≤ τ₁ s) (hτ₂ : ∀ s ∈ Icc 0 S₀, 0 ≤ τ₂ s)
    (h : ∀ s ∈ Icc 0 S₀,
      QuantumZipper.fwdHull W₂ (τ₂ s) = (fun z : ℂ => z + d) '' QuantumZipper.fwdHull W₁ (τ₁ s)) :
    (∀ s ∈ Icc 0 S₀, τ₁ s = τ₂ s) ∧ d = 0 ∧ EqOn W₁ W₂ (Icc 0 (τ₁ S₀)) := by
  have hτ : ∀ s ∈ Icc 0 S₀, τ₁ s = τ₂ s := fun s hs =>
    time_eq_of_fwdHull_eq_add_const hW₁ hW₂ hW₁0 hW₂0 (hτ₁ s hs) (hτ₂ s hs) (h s hs)
  have hall : ∀ r ∈ Icc 0 (τ₁ S₀),
      QuantumZipper.fwdHull W₂ r = (fun z : ℂ => z + d) '' QuantumZipper.fwdHull W₁ r := by
    intro r hr
    have hivt := intermediate_value_Icc hS₀ hτ₁c
    rw [hτ₁0] at hivt
    obtain ⟨s, hs, rfl⟩ := hivt hr
    have := h s hs
    rwa [← hτ s hs] at this
  obtain ⟨hd, heq⟩ := Mt.eqOn_of_fwdHull_eq_add_const hW₁ hW₂ hW₁0 hW₂0 hpos hall
  exact ⟨hτ, hd, heq⟩

open Sec7.Lemma71C in
/-- **Two relative chains of the same piece, in charts differing by a real translation, have translated hulls.** -/
theorem fwdHull_eq_add_of_chains {A : Set ℂ} {cR cC : Chart} {β' γR γC : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ d : ℝ}
    {WR WC : ℝ → ℝ} {ηR ηC : ℝ → ℂ} (hdR : IsDomainChart (H \ A) cR) (hdC : IsDomainChart (H \ A) cC)
    (hfill : ∀ z ∈ H \ A, z ∉ fillH A) (hfwd : ∀ z ∈ H \ A, cC.1 z = cR.1 z + d)
    (hR : FinRel.IsSB2RelChain A cR β' γR tL S₀ WR ηR) (hC : FinRel.IsSB2RelChain A cC β' γC tL S₀ WC ηC)
    {s : ℝ} (hs : s ∈ Icc 0 S₀) :
    QuantumZipper.fwdHull WC (capClock (fun r : ℝ => γC r.toNNReal) s) =
      (fun z : ℂ => z + d) '' QuantumZipper.fwdHull WR (capClock (fun r : ℝ => γR r.toNNReal) s) := by
  obtain ⟨hWRc, -, -, -, -, -, hRs⟩ := hR
  obtain ⟨hWCc, -, -, -, -, -, hCs⟩ := hC
  obtain ⟨hR0, -, -, hRin, hRfr⟩ := hRs s hs
  obtain ⟨hC0, -, -, hCin, hCfr⟩ := hCs s hs
  have hAR : IsHPHull ((fun z : ℂ => z + d) '' QuantumZipper.fwdHull WR (capClock (fun r : ℝ => γR r.toNNReal) s)) := by
    rw [← ConformalImageFull.fwdHull_add_const]
    exact isHPHull_fwdHull (hWRc.add continuous_const) hR0
  have hAC : IsHPHull (QuantumZipper.fwdHull WC (capClock (fun r : ℝ => γC r.toNNReal) s)) :=
    isHPHull_fwdHull hWCc hC0
  have himg : ∀ K : Set ℂ, (fun z : ℂ => z + d) '' K = Homeomorph.addRight (d : ℂ) '' K := fun K => rfl
  refine eq_of_frontier_subset_hull hAC hAR ?_ ?_
  · rintro y ⟨hy, hyH⟩
    have hzD : cC.2.1 y ∈ H \ A := hdC.inv_mem hyH
    have hyz : cC.1 (cC.2.1 y) = y := hdC.fwd_inv hyH
    have hzF := hCfr (cC.2.1 y) ⟨hzD.1, hfill _ hzD⟩ (by rw [hyz]; exact hy)
    refine ⟨cR.1 (cC.2.1 y), hRin _ hzF (hfill _ hzD), ?_⟩
    show cR.1 (cC.2.1 y) + d = y
    rw [← hfwd _ hzD, hyz]
  · rintro y ⟨hy, hyH⟩
    rw [himg, ← (Homeomorph.addRight (d : ℂ)).image_frontier] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwH : w ∈ H := by
      have : (w + (d : ℂ)).im = w.im := by simp
      show 0 < w.im
      rw [← this]
      exact hyH
    have hzD : cR.2.1 w ∈ H \ A := hdR.inv_mem hwH
    have hwz : cR.1 (cR.2.1 w) = w := hdR.fwd_inv hwH
    have hzF := hRfr (cR.2.1 w) ⟨hzD.1, hfill _ hzD⟩ (by rw [hwz]; exact hw)
    have h1 := hCin _ hzF (hfill _ hzD)
    rw [hfwd _ hzD, hwz] at h1
    exact h1

open Sec7.Lemma71C in
/-- **Two relative chains of the same piece, in charts differing by a real translation, have the same driver** up to
the clock time at `S₀`; the clocks agree and the translation is `0`. -/
theorem eqOn_of_chains {A : Set ℂ} {cR cC : Chart} {β' γR γC : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ d : ℝ}
    {WR WC : ℝ → ℝ} {ηR ηC : ℝ → ℂ} (hdR : IsDomainChart (H \ A) cR) (hdC : IsDomainChart (H \ A) cC)
    (hfill : ∀ z ∈ H \ A, z ∉ fillH A) (hfwd : ∀ z ∈ H \ A, cC.1 z = cR.1 z + d) (hS₀ : 0 < S₀)
    (hR : FinRel.IsSB2RelChain A cR β' γR tL S₀ WR ηR) (hC : FinRel.IsSB2RelChain A cC β' γC tL S₀ WC ηC) :
    (∀ s ∈ Icc 0 S₀, capClock (fun r : ℝ => γR r.toNNReal) s = capClock (fun r : ℝ => γC r.toNNReal) s) ∧ d = 0 ∧
      EqOn WR WC (Icc 0 (capClock (fun r : ℝ => γR r.toNNReal) S₀)) := by
  have hR' := hR
  have hC' := hC
  obtain ⟨hWRc, hWR0, -, hR0, hRmono, hRcont, hRs⟩ := hR'
  obtain ⟨hWCc, hWC0, -, -, -, -, hCs⟩ := hC'
  have hpos : 0 < capClock (fun r : ℝ => γR r.toNNReal) S₀ := by
    have := hRmono ⟨le_rfl, hS₀.le⟩ ⟨hS₀.le, le_rfl⟩ hS₀
    rwa [hR0] at this
  exact eqOn_of_fwdHull_eq_add_const_clock hWRc hWCc hWR0 hWC0 hS₀.le hRcont hR0 hpos
    (fun s hs => (hRs s hs).1) (fun s hs => (hCs s hs).1)
    (fun s hs => fwdHull_eq_add_of_chains hdR hdC hfill hfwd hR hC hs)

open Sec7.Lemma71C in
/-- In a relative chain, the piece up to the chain's start lies in the retained fill (the hull at clock `0` is
empty). -/
theorem fillH_start_subset {A : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {W : ℝ → ℝ}
    {η : ℝ → ℂ} (hS₀ : 0 ≤ S₀) (hC : FinRel.IsSB2RelChain A c β' γ tL S₀ W η) :
    fillH (β' '' Icc 0 tL) ⊆ fillH A := by
  obtain ⟨hWc, -, -, h0, -, -, hs⟩ := hC
  obtain ⟨-, -, -, hin, -⟩ := hs 0 ⟨le_rfl, hS₀⟩
  intro z hz
  by_contra hzA
  have h1 := hin z (by simpa using hz) hzA
  rw [h0, QuantumZipper.RS.fwdHull_zero_eq_empty hWc] at h1
  exact h1

open Sec7.Lemma71C in
/-- One direction of `tL_eq_of_chains`. -/
theorem le_tL_of_chains {A : Set ℂ} {cR cC : Chart} {β' γR γC : ℝ≥0 → ℂ} {tL tL' : ℝ≥0} {S₀ S₀' : ℝ}
    {WR WC : ℝ → ℝ} {ηR ηC : ℝ → ℂ} (hdR : IsDomainChart (H \ A) cR) (hfill : ∀ z ∈ H \ A, z ∉ fillH A)
    (hS₀ : 0 < S₀) (hS₀' : 0 ≤ S₀') (hR : FinRel.IsSB2RelChain A cR β' γR tL S₀ WR ηR)
    (hC : FinRel.IsSB2RelChain A cC β' γC tL' S₀' WC ηC) : tL' ≤ tL := by
  by_contra hlt
  rw [not_le] at hlt
  have hstart := fillH_start_subset hS₀' hC
  obtain ⟨hWRc, hWR0, -, hR0, hRmono, -, hRs⟩ := hR
  set s : ℝ := min S₀ ((tL' : ℝ) - tL) with hsdef
  have hspos : 0 < s := lt_min hS₀ (sub_pos.2 (NNReal.coe_lt_coe.2 hlt))
  have hsI : s ∈ Icc 0 S₀ := ⟨hspos.le, min_le_left _ _⟩
  have hle : tL + s.toNNReal ≤ tL' := by
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hspos.le]
    linarith [min_le_right S₀ ((tL' : ℝ) - tL)]
  have hcap : 0 < capClock (fun r : ℝ => γR r.toNNReal) s := by
    have := hRmono ⟨le_rfl, hS₀.le⟩ hsI hspos
    rwa [hR0] at this
  obtain ⟨hcap0, -, -, -, hRfr⟩ := hRs s hsI
  set K := QuantumZipper.fwdHull WR (capClock (fun r : ℝ => γR r.toNNReal) s) with hKdef
  have hK : IsHPHull K := isHPHull_fwdHull hWRc hcap0
  have hne : K.Nonempty := QuantumZipper.RS.fwdHull_nonempty_of_pos hWRc hWR0 hcap
  have hfr : ∀ y ∈ H, y ∉ frontier K := by
    intro y hyH hy
    have hzD : cR.2.1 y ∈ H \ A := hdR.inv_mem hyH
    have hyz : cR.1 (cR.2.1 y) = y := hdR.fwd_inv hyH
    have hzF := hRfr (cR.2.1 y) ⟨hzD.1, hfill _ hzD⟩ (by rw [hyz]; exact hy)
    have hzA : cR.2.1 y ∈ fillH A :=
      hstart (fillH_mono (image_mono (Icc_subset_Icc le_rfl hle)) hzF)
    exact hfill _ hzD hzA
  -- `K` would be clopen in the connected `ℍ`, hence all of `ℍ`, which is unbounded
  have hcov : H ⊆ interior K ∪ (H \ K) := by
    intro z hzH
    by_cases hzK : z ∈ K
    · left
      by_contra hint
      exact hfr z hzH ⟨subset_closure hzK, hint⟩
    · exact Or.inr ⟨hzH, hzK⟩
  have hdisj : Disjoint (interior K) (H \ K) :=
    Set.disjoint_left.2 fun z hzi hz => hz.2 (interior_subset hzi)
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀i : z₀ ∈ interior K := by
    by_contra hzi
    exact hfr z₀ (hK.1 hz₀) ⟨subset_closure hz₀, hzi⟩
  have hHK : H ⊆ interior K :=
    (convex_halfSpace_im_gt 0).isPreconnected.subset_left_of_subset_union isOpen_interior hK.2.2.1 hdisj hcov
      ⟨z₀, hK.1 hz₀, hz₀i⟩
  obtain ⟨R, hR⟩ := hK.2.1.subset_ball 0
  have hzH : ((|R| + 1 : ℝ) : ℂ) * Complex.I ∈ H := by
    show 0 < (((|R| + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  have h1 := hR (interior_subset (hHK hzH))
  rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < |R| + 1)] at h1
  linarith [le_abs_self R]

/-- **Two relative chains of the same piece start at the same time.** -/
theorem tL_eq_of_chains {A : Set ℂ} {cR cC : Chart} {β' γR γC : ℝ≥0 → ℂ} {tL tL' : ℝ≥0} {S₀ S₀' : ℝ}
    {WR WC : ℝ → ℝ} {ηR ηC : ℝ → ℂ} (hdR : IsDomainChart (H \ A) cR) (hdC : IsDomainChart (H \ A) cC)
    (hfill : ∀ z ∈ H \ A, z ∉ fillH A) (hS₀ : 0 < S₀) (hS₀' : 0 < S₀')
    (hR : FinRel.IsSB2RelChain A cR β' γR tL S₀ WR ηR) (hC : FinRel.IsSB2RelChain A cC β' γC tL' S₀' WC ηC) :
    tL = tL' :=
  le_antisymm (le_tL_of_chains hdC hfill hS₀' hS₀.le hC hR) (le_tL_of_chains hdR hfill hS₀ hS₀'.le hR hC)

end InteractingSLE.Theorem14.SB.Mx
