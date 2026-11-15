/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcSign
import InteractingSLE.Spec.Sec7.ReverseArcLift
import InteractingSLE.Spec.Sec7.Aux70Select

/-!
# The chart geometry of a stopped reverse common arc (Aux. lemmas 69 and 57), at interior tips

Packet PROVE-LEMMA76B (specification §7.2, Aux. lemma 69, p. 273, and the proof of Aux. lemma 70, p. 275). This file
proves the conclusion of the named input `Sec7.ReverseArcChartStatement` (`Aux70.lean`) under the additional hypotheses
that both stopped tips `α(q₁)`, `β(q₂)` are interior (`reverseArcChart_of_mem_H`):

* the common arc is exposed to the joint unbounded domain `D` (`ReverseArc.mem_closure_H_diff_fillH`); an ultrafilter
  `U` converging to `α(s₀)` inside `D` is the approach;
* along `U` the first chart tends to a positive real and the second to a negative one (`exists_pos_tendsto_phys`,
  `exists_neg_tendsto_phys`: Aux. lemma 69's "right side of `α₁`, left side of `α₂`");
* the half-disc of each chart at its limit is mapped into `D` (`exists_ball_notMem_of_approach`), so the transition
  hull of each chart to the joint chart misses a ball about the limit, and Aux. lemma 57 (`tendsto_im_sub_of_le`) makes
  each derivative-argument lift agree with the joint one along `U`.

The interior-tip hypotheses are what the fresh-tip uniqueness (Lemma 1.1 of the singleton-tip elimination note) and the
slit lemma need; `exists_rat_reverseArc_mem_H` (`ReverseArcAux70.lean`) selects the rational stops with
interior tips, and `aux70Statement_of_sideHeight` (`ReverseArcAux70.lean`) assembles Aux. lemma 70 without the geometric
input.
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

/-! ### The physical chart of a trace from a real seed -/

section Phys

variable {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}

/-- The physical filling is the translate of the centred one. -/
theorem fillH_image_eq (x : ℝ) (q : ℝ≥0) :
    fillH (α '' Icc 0 q) = (fun z => z + (x : ℂ)) '' fillH ((fun t => α t - x) '' Icc 0 q) := by
  rw [← fillH_image_add, image_image]
  congr 1
  exact image_congr fun t _ => by ring

theorem mem_H_diff_fillH_phys_iff (x : ℝ) (q : ℝ≥0) (z : ℂ) :
    z ∈ H \ fillH (α '' Icc 0 q) ↔ z - x ∈ H \ fillH ((fun t => α t - x) '' Icc 0 q) := by
  rw [fillH_image_eq x q, mem_H_diff_image_add_iff]

/-- **The physical chart of a simple frozen trace from `x`**: the hull `fill α([0, q])` is a compact `ℍ`-hull, mapped
out by `z ↦ f_q(z − x) + κ`, with canonical logarithm `z ↦ log f_q′(z − x)`. -/
theorem exists_physChart (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hq : (q : ℝ≥0∞) < ζ) :
    ∃ κ : ℝ, IsHPHull (fillH (α '' Icc 0 q)) ∧
      IsMapOut (fillH (α '' Icc 0 q))
        (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) ∧
      IsCanonicalDerivLog (fillH (α '' Icc 0 q))
        (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ)
        (fun z => QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)) := by
  obtain ⟨Wg, γ, T', hqT', hWgc, hWg0, hγ, hWeq, hγeq⟩ := exists_global_model hg hWc hW0 hq
  have hq0' : (0 : ℝ) ≤ q := NNReal.coe_nonneg q
  have hf : QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q = QuantumZipper.fwdMap Wg q := funext fun z =>
    fwdMap_eq_of_eqOn hq0' fun r hr => (hWeq r ⟨hr.1, hr.2.trans hqT'.le⟩).symm
  have hL : QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q = QuantumZipper.logDerivFwd Wg q := funext fun z =>
    Ito.logDerivFwd_congr_of_eqOn (fun r hr => (hWeq r ⟨hr.1, hr.2.trans hqT'.le⟩).symm) hq0' le_rfl
  have himg : γ '' Icc 0 (q : ℝ) = (fun t => α t - x) '' Icc 0 q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hqT'.le⟩),
      image_toNNReal_Icc (fun t => α t - x) hq0', Real.toNNReal_coe]
  have hK : QuantumZipper.fwdHull Wg q = fillH ((fun t => α t - x) '' Icc 0 q) := by rw [hγ.2.2 q hq0', himg]
  have hKfill : fillH (α '' Icc 0 q) = (fun z => z + (x : ℂ)) '' QuantumZipper.fwdHull Wg q := by
    rw [hK]; exact fillH_image_eq x q
  refine ⟨Wg q + x, ?_, ?_, ?_⟩
  · rw [hKfill]
    have h := (isHPHull_fwdHull hWgc hq0').image_affHomeo (r := 1) (x := x) one_pos
    have hfn : ⇑(affHomeo 1 one_pos x) = fun z : ℂ => z + x := by
      funext z; exact ConformalImageFull.affHomeo_one_apply x z
    rwa [hfn] at h
  · rw [hKfill, hf]
    have h := isMapOut_translate (isMapOut_fwdMap hWgc hWg0 hq0') x
    convert h using 2 with z
    push_cast; ring
  · rw [hKfill, hf, hL]
    have h := isCanonicalDerivLog_translate (isCanonicalDerivLog_logDerivFwd hWgc hWg0 hq0') x
    convert h using 2 with z
    push_cast; ring

/-- **The physical inverse chart**: `Φ(w) = F̄_q(w) + x` inverts `z ↦ f_q(z − x)` between `ℍ \ fill α([0, q])` and `ℍ`
and is continuous on `ℍ̄`. -/
theorem exists_physInv (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) :
    ∃ Φ : ℂ → ℂ, ContinuousOn Φ Hbar ∧ MapsTo Φ H (H \ fillH (α '' Icc 0 q)) ∧
      (∀ w ∈ H, QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (Φ w - x) = w) ∧
      (∀ z ∈ H \ fillH (α '' Icc 0 q), Φ (QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) = z) ∧
      MapsTo (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) (H \ fillH (α '' Icc 0 q)) H := by
  have hinj' : InjOn (fun t => α t - x) {t | (t : ℝ≥0∞) ≤ ζ} := fun a ha b hb hab =>
    hinj ha hb (sub_left_injective hab)
  have hch := isChart hg hWc hW0 hinj' hq hq0
  refine ⟨fun w => extendFrom H (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) q) w + x,
    hch.inv_cont.add continuousOn_const, fun w hw => ?_, fun w hw => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rw [mem_H_diff_fillH_phys_iff x q, add_sub_cancel_right]
    exact hch.inv_mem hw
  · rw [add_sub_cancel_right]
    exact hch.f_inv w hw
  · show extendFrom H _ _ + _ = z
    rw [hch.inv_f _ ((mem_H_diff_fillH_phys_iff x q z).1 hz), sub_add_cancel]
  · exact hch.maps ((mem_H_diff_fillH_phys_iff x q z).1 hz)

end Phys

/-! ### The half-disc of a chart at the approach -/

/-- **The half-disc lemma.** Let `f` map `ℍ \ fill A` into `ℍ` with an inverse `Φ` continuous on `ℍ̄`, `A ⊆ Γ` closed,
and let the approach `U` to `z₀` from the unbounded domain of `Γ` have `f → y` (`y` real), where near `z₀` the set `Γ`
is contained in `A`. Then for small `ε`, no point of `fill Γ \ fill A` is mapped into `B(y, ε)`: the `Φ`-image of the
half-disc is a connected set off `Γ` meeting the unbounded domain. -/
theorem exists_ball_notMem_of_approach {Γ A : Set ℂ} (hΓ : IsClosed Γ) (hAΓ : A ⊆ Γ) {f Φ : ℂ → ℂ}
    (hmaps : MapsTo f (H \ fillH A) H) (hΦc : ContinuousOn Φ Hbar) (hΦH : MapsTo Φ H (H \ fillH A))
    (hinv : ∀ z ∈ H \ fillH A, Φ (f z) = z) {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hloc : Γ ∩ ball z₀ r ⊆ A)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH Γ] z₀) {y : ℝ} (hfU : Tendsto f U (𝓝 (y : ℂ))) :
    ∃ ε > 0, ∀ z ∈ H \ fillH A, z ∈ fillH Γ → f z ∉ ball (y : ℂ) ε := by
  have hDA : H \ fillH Γ ⊆ H \ fillH A := sdiff_subset_sdiff_right (fillH_mono hAΓ)
  have hyH : (y : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im; simp
  -- `Φ(y) = z₀`
  have hev : ∀ᶠ z in (U : Filter ℂ), z ∈ H \ fillH Γ := hU self_mem_nhdsWithin
  have hfH : Tendsto f U (𝓝[Hbar] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hfU, hev.mono fun z hz => H_subset_Hbar (hmaps (hDA hz))⟩
  have h1 : Tendsto (fun z => Φ (f z)) U (𝓝 (Φ y)) := (hΦc _ hyH).tendsto.comp hfH
  have h2 : Tendsto (fun z => Φ (f z)) U (𝓝 z₀) :=
    (tendsto_nhds_of_tendsto_nhdsWithin hU).congr' (hev.mono fun z hz => (hinv z (hDA hz)).symm)
  have hΦy : Φ y = z₀ := tendsto_nhds_unique h1 h2
  -- the half-disc maps near `z₀`
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1 ((hΦc _ hyH) (hΦy ▸ ball_mem_nhds z₀ hr))
  set V := ball (y : ℂ) ε ∩ H with hV
  have hVpc : IsPreconnected V :=
    ((convex_ball _ _).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
  have hΦV : Φ '' V ⊆ H \ Γ := by
    rintro _ ⟨w, ⟨hwb, hwH⟩, rfl⟩
    have hm := hΦH hwH
    refine ⟨hm.1, fun hΓw => hm.2 ?_⟩
    have hb : Φ w ∈ ball z₀ r := by
      have := hεsub ⟨hwb, H_subset_Hbar hwH⟩
      rwa [mem_preimage, hΦy] at this
    exact ⟨hm.1, Or.inl (subset_closure (hloc ⟨hΓw, hb⟩))⟩
  -- it meets the unbounded domain
  have hev2 : ∀ᶠ z in (U : Filter ℂ), f z ∈ ball (y : ℂ) ε := hfU (ball_mem_nhds _ hε)
  obtain ⟨z₁, hz₁D, hz₁b⟩ := (hev.and hev2).exists
  have hz₁V : z₁ ∈ Φ '' V := ⟨f z₁, ⟨hz₁b, hmaps (hDA hz₁D)⟩, hinv z₁ (hDA hz₁D)⟩
  have hΦVD : Φ '' V ⊆ H \ fillH Γ :=
    (hVpc.image Φ (hΦc.mono fun w hw => H_subset_Hbar hw.2)).subset_connectedComponentIn hz₁V hΦV |>.trans
      (connectedComponentIn_subset_H_diff_fillH hΓ hz₁D)
  refine ⟨ε, hε, fun z hz hzΓ hzb => ?_⟩
  have := hΦVD ⟨f z, ⟨hzb, hmaps hz⟩, hinv z hz⟩
  exact this.2 hzΓ

/-! ### The chart geometry of the reverse arc -/

/-- **The conclusion of `ReverseArcChartStatement` when both stopped tips are interior** (Aux. lemma 69 and Aux. lemma
57): some point `α(s)` of the open common arc is approached from the joint unbounded domain along a nontrivial filter on
which the first chart tends to a positive real, the second to a negative real, and the two derivative-argument lifts
differ by a quantity tending to `0`. -/
theorem reverseArcChart_of_mem_H (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ) (hx : x₂ < x₁) (W₁ W₂ : ℝ≥0 → ℝ) (ζ₁ ζ₂ : ℝ≥0∞)
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hW₁c : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW₁0 : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hW₂c : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW₂0 : W₂ 0 = 0)
    (hi₁ : InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (q₁ q₂ σ₁ σ₂ s₀ : ℝ≥0) (f : ℝ≥0 → ℝ≥0) (hq₁ : (q₁ : ℝ≥0∞) < ζ₁) (hq₂ : (q₂ : ℝ≥0∞) < ζ₂)
    (hσs : σ₁ < s₀) (hsq : s₀ < q₁) (hσ₂q : σ₂ < q₂) (hfc : ContinuousOn f (Icc σ₁ q₁))
    (hfa : StrictAntiOn f (Icc σ₁ q₁)) (hfσ : f σ₁ = q₂) (hfq : f q₁ = σ₂) (hfeq : ∀ s ∈ Icc σ₁ q₁, β (f s) = α s)
    (hover : α '' Icc 0 q₁ ∩ β '' Icc 0 q₂ ⊆ α '' Icc σ₁ q₁) (hs₀H : α s₀ ∈ H) (htip₁ : α q₁ ∈ H)
    (htip₂ : β q₂ ∈ H) :
    ∃ s ∈ Ioo σ₁ q₁, α s ∈ H ∧ ∃ F : Filter ℂ, F.NeBot ∧
      F ≤ 𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] (α s) ∧ ∃ y₁ y₂ : ℝ, 0 < y₁ ∧ y₂ < 0 ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)) F (𝓝 (y₁ : ℂ)) ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)) F (𝓝 (y₂ : ℂ)) ∧
      Tendsto (fun z => (QuantumZipper.logDerivFwd (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)).im -
        (QuantumZipper.logDerivFwd (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)).im) F (𝓝 0) := by
  have hp₁ : IsPathGood α ζ₁ x₁ := ⟨hi₁, W₁, hW₁c, hW₁0, hg₁⟩
  have hp₂ : IsPathGood β ζ₂ x₂ := ⟨hi₂, W₂, hW₂c, hW₂0, hg₂⟩
  have hσq : σ₁ ≤ q₁ := (hσs.trans hsq).le
  have hβ0 : β 0 = x₂ := IsPathGood.zero hp₂
  have hβσ : β σ₂ = α q₁ := by rw [← hfq]; exact hfeq q₁ ⟨hσq, le_rfl⟩
  have hασ : α σ₁ = β q₂ := by rw [← hfσ]; exact (hfeq σ₁ ⟨le_rfl, hσq⟩).symm
  have hσ₂pos : 0 < σ₂ := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, hβ0] at hβσ
    have : (α q₁).im = 0 := by rw [← hβσ]; simp
    exact absurd htip₁ (by rw [show α q₁ ∈ H ↔ 0 < (α q₁).im from Iff.rfl, this]; exact lt_irrefl 0)
  have hs₀I : s₀ ∈ Ioo σ₁ q₁ := ⟨hσs, hsq⟩
  have hc₁ := IsPathGood.continuousOn_Icc hp₁ hq₁.le
  have hc₂ := IsPathGood.continuousOn_Icc hp₂ hq₂.le
  have hj₁ := IsPathGood.injOn_Icc hp₁ hq₁.le
  have hj₂ := IsPathGood.injOn_Icc hp₂ hq₂.le
  set A := α '' Icc 0 q₁ with hAdef
  set B := β '' Icc 0 q₂ with hBdef
  -- the approach
  have hcl := mem_closure_H_diff_fillH hp₁ hp₂ hx hq₁.le hq₂.le hσ₂pos hσ₂q.le hσq hfc hfa hfσ hfq hfeq hover hs₀I
    hs₀H
  have hneb : (𝓝[H \ fillH (A ∪ B)] (α s₀)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  set U := Ultrafilter.of (𝓝[H \ fillH (A ∪ B)] (α s₀)) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (A ∪ B)] (α s₀) := Ultrafilter.of_le _
  -- the first chart: positive
  have hΓ₁ : A ∪ B = A ∪ β '' Icc 0 σ₂ := union_eq hσ₂q.le hσq hfc hfa hfσ hfq hfeq
  have hdisj₁ : ∀ t < σ₂, β t ∉ A := by
    rintro t ht ⟨u, hu, hue⟩
    obtain ⟨huI, hfu⟩ := eq_of_mem_both hj₁ hj₂ hσq hfa hfσ hfeq hover hu.2 (ht.le.trans hσ₂q.le) hue
    have : σ₂ ≤ t := by rw [← hfu, ← hfq]; exact hfa.antitoneOn huI ⟨hσq, le_rfl⟩ huI.2
    exact absurd ht (not_lt.2 this)
  obtain ⟨y₁, hy₁, hf₁⟩ := exists_pos_tendsto_phys hp₁ hp₂ hx hg₁ hW₁c hW₁0 hq₁ htip₁
    ((ENNReal.coe_le_coe.2 hσ₂q.le).trans hq₂.le) hβσ hdisj₁ hsq hs₀H U (hΓ₁ ▸ hU)
  -- the second chart: negative
  have hΓ₂ : A ∪ B = B ∪ α '' Icc 0 σ₁ := by
    have hsplit : A = α '' Icc 0 σ₁ ∪ α '' Icc σ₁ q₁ := by
      rw [hAdef, ← image_union, Icc_union_Icc_eq_Icc zero_le hσq]
    have hsub : α '' Icc σ₁ q₁ ⊆ B := by
      rw [← image_Icc_eq hσq hfc hfa hfσ hfq hfeq]
      exact image_mono (Icc_subset_Icc_left zero_le)
    rw [hsplit, union_assoc, union_eq_right.2 hsub, union_comm]
  have hdisj₂ : ∀ t < σ₁, α t ∉ B := by
    rintro t ht ⟨u, hu, hue⟩
    obtain ⟨htI, -⟩ := eq_of_mem_both hj₁ hj₂ hσq hfa hfσ hfeq hover (ht.le.trans hσq) hu.2 hue.symm
    exact absurd htI.1 (not_le.2 ht)
  have hfs : f s₀ < q₂ := hfσ ▸ hfa ⟨le_rfl, hσq⟩ ⟨hσs.le, hsq.le⟩ hσs
  have hβfs : β (f s₀) = α s₀ := hfeq s₀ ⟨hσs.le, hsq.le⟩
  obtain ⟨y₂, hy₂, hf₂⟩ := exists_neg_tendsto_phys hp₁ hp₂ hx hg₂ hW₂c hW₂0 hq₂ htip₂
    ((ENNReal.coe_le_coe.2 hσq).trans hq₁.le) hασ hdisj₂ hfs (hβfs ▸ hs₀H) U (by rw [hβfs, ← hΓ₂]; exact hU)
  -- the lifts
  have hABc : IsCompact (A ∪ B) := (IsPathGood.isCompact_image hp₁ hq₁.le).union (IsPathGood.isCompact_image hp₂ hq₂.le)
  have hKΓ : IsHPHull (fillH (A ∪ B)) := by
    refine isHPHull_fillH_of_isPreconnected hABc.isBounded ?_
    have hApc : IsPreconnected A := isPreconnected_Icc.image _ hc₁
    have hBpc : IsPreconnected B := isPreconnected_Icc.image _ hc₂
    have hlow : IsPreconnected {z : ℂ | z.im ≤ 0} := isPreconnected_lowerHalf
    have hx₁ : (x₁ : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₁⟩
    have hx₂ : (x₂ : ℂ) ∈ B := ⟨0, ⟨le_rfl, zero_le⟩, hβ0⟩
    have h1 := hApc.union (x₁ : ℂ) hx₁ (show (x₁ : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp) hlow
    have h2 := h1.union (x₂ : ℂ) (Or.inr (show (x₂ : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)) hx₂ hBpc
    rwa [union_right_comm] at h2
  set gK := ConformalImage.mapOut (fillH (A ∪ B)) with hgKdef
  have hgK : IsMapOut (fillH (A ∪ B)) gK := ConformalImage.isMapOut_mapOut hKΓ
  obtain ⟨LK, hLK⟩ := exists_isCanonicalDerivLog hKΓ hgK
  have hF : (U : Filter ℂ) ≤ 𝓟 (H \ fillH (A ∪ B)) := hU.trans inf_le_right
  obtain ⟨ρ, hρ, hagree⟩ := local_agree_of_reverseArc hc₁ hc₂ hj₁ hj₂ le_rfl le_rfl hfc hfa hfσ hfq hfeq hover hs₀I
  -- a chart and its lift
  have hlift : ∀ {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0} {y : ℝ},
      IsGeneratingTrace W ζ (fun t => γ t - x) → ContinuousOn W {s | (s : ℝ≥0∞) < ζ} → W 0 = 0 →
      InjOn γ {t | (t : ℝ≥0∞) ≤ ζ} → (q : ℝ≥0∞) < ζ → 0 < q → γ '' Icc 0 q ⊆ A ∪ B →
      (A ∪ B) ∩ ball (α s₀) ρ ⊆ γ '' Icc 0 q →
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ)) →
      Tendsto (fun z => (LK z).im - (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) U
        (𝓝 0) := by
    intro γ ζ x W q y hg hWc hW0 hi hq hq0 hsub hloc hfy
    obtain ⟨κ, hK, hgm, hL⟩ := exists_physChart hg hWc hW0 hq
    obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ := exists_physInv hg hWc hW0 hi hq hq0
    obtain ⟨ε, hε, hno⟩ := exists_ball_notMem_of_approach hABc.isClosed hsub hmaps hΦc hΦH hinv hρ hloc U hU hfy
    have hd : Disjoint (ball (((y + κ : ℝ)) : ℂ) ε)
        ((fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) '' (fillH (A ∪ B) \
          fillH (γ '' Icc 0 q))) := by
      rw [Set.disjoint_left]
      rintro w hwb ⟨z, ⟨hzK, hzA⟩, rfl⟩
      refine hno z ⟨hzK.1, hzA⟩ hzK ?_
      rw [mem_ball, dist_eq_norm] at hwb ⊢
      convert hwb using 2
      push_cast; ring
    have hq' : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) U
        (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := hfy.add_const (κ : ℂ)
        convert this using 2
        push_cast; ring
      · filter_upwards [hF (mem_principal_self _)] with z hz
        exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
    exact tendsto_im_sub_of_le hK hKΓ (fillH_mono hsub) hgm hgK hL hLK hF hε hd hq'
  have hloc₁ : (A ∪ B) ∩ ball (α s₀) ρ ⊆ A := by
    rintro z ⟨hz | hz, hzb⟩
    · exact hz
    · have : z ∈ B ∩ ball (α s₀) ρ := ⟨hz, hzb⟩
      rw [← hagree] at this
      exact this.1
  have hloc₂ : (A ∪ B) ∩ ball (α s₀) ρ ⊆ B := by
    rintro z ⟨hz | hz, hzb⟩
    · have : z ∈ A ∩ ball (α s₀) ρ := ⟨hz, hzb⟩
      rw [hagree] at this
      exact this.1
    · exact hz
  have hq₁0 : 0 < q₁ := lt_of_le_of_lt zero_le hsq
  have hq₂0 : 0 < q₂ := lt_of_le_of_lt zero_le hσ₂q
  have hl₁ := hlift hg₁ hW₁c hW₁0 hi₁ hq₁ hq₁0 subset_union_left hloc₁ hf₁
  have hl₂ := hlift hg₂ hW₂c hW₂0 hi₂ hq₂ hq₂0 subset_union_right hloc₂ hf₂
  refine ⟨s₀, hs₀I, hs₀H, U, inferInstance, hU, y₁, y₂, hy₁, hy₂, hf₁, hf₂, ?_⟩
  have := hl₂.sub hl₁
  rw [sub_zero] at this
  refine this.congr fun z => ?_
  ring

end ReverseArc

end Sec7

end InteractingSLE
