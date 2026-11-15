/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Sec7.ContinuityProbCollision

/-!
# §7.3: joining Loewner traces through the extended inverse map of a finite prefix

Packet PROVE-SEC7-C3. Every §7.3 continuation step ends the same way (Aux. lemma 99, p. 344: "A finite
continuous Loewner prefix has a locally connected active boundary, so its inverse map extends continuously
to the real line; it joins this new trace to the terminal tip and fixes infinity"; Aux. lemma 106, p. 354;
Aux. lemma 103 "the resulting traces join at their tips"; the revised induction, p. 380). This file proves
that deterministic step.

* `exists_extension_of_fwdHull_eq`: if `K_a = fill(γ[0, a])` for a curve `γ` continuous on `[0, a]`, then
  `F_a = g_a⁻¹` (centred) extends continuously to `ℍ̄` and maps no real point into `ℍ \ K_a`.
* `fwdHull_add_eq_fillH_union`: **hull composition.** If moreover the chain driven by the shifted driver
  `W(a + ·) − W(a)` has `K'_u = fill(B)` for a compact `B ⊆ ℍ̄`, then `K_{a+u} = fill(A ∪ F̄_a(B))`.
* `IsLoewnerTraceLT.mem_Hbar`: a generating trace never enters the open lower half-plane (strict growth
  of hulls), so the frozen transience `‖η t‖ → ∞` survives the join.
* `IsGeneratingTraceIcc`: a generating trace on the closed interval `[0, σ]`, with the hull and the tip at
  `σ`; `IsGeneratingTrace.isGeneratingTraceIcc` (any `σ` before the horizon).
* `IsGeneratingTraceIcc.join`: **the join.** A trace on `[0, σ]` (closed form) and a generating trace of
  the shifted driver on `[0, T₂]` give a generating trace on `[0, σ + T₂]`; transience is transferred.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Sec7

section Real

variable {W : ℝ → ℝ}

/-- **Boundary extension of `F_a` from the hull at `a` alone.** If `K_a = fill(γ[0, a])` for a curve `γ`
continuous on `[0, a]`, the centred inverse map `F_a` extends continuously to `ℍ̄` and maps no real point
into `ℍ \ K_a` (the proof of `IsLoewnerTraceLT.exists_extension`, which uses only the hull at `a`). -/
theorem exists_extension_of_fwdHull_eq (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 a)) (hK : fwdHull W a = fillH (γ '' Icc 0 a)) :
    ∃ F : ℂ → ℂ, EqOn F (fwdMapInv W a) H ∧ ContinuousOn F Hbar ∧
      ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W a := by
  set γ' : ℝ → ℂ := fun s => clipH (γ s) with hγ'
  have hγc : ContinuousOn γ' (Icc 0 a) := continuous_clipH.comp_continuousOn hγ
  have hγH : MapsTo γ' (Icc 0 a) Hbar := fun s _ => clipH_mem_Hbar _
  have hcpt : IsCompact (γ '' Icc 0 a) := isCompact_Icc.image_of_continuousOn hγ
  have hfill : fillH (γ' '' Icc 0 a) = fwdHull W a := by
    rw [hK]
    apply fillH_congr
    have hc1 : IsCompact (γ' '' Icc 0 a) := isCompact_Icc.image_of_continuousOn hγc
    rw [hc1.isClosed.closure_eq, hcpt.isClosed.closure_eq]
    rw [show γ' '' Icc 0 a = clipH '' (γ '' Icc 0 a) from (image_image clipH γ _).symm]
    exact image_clipH_inter_H _
  have hψ : IsConformalBijection (fwdMapInv W a) H (H \ fillH (γ' '' Icc 0 a)) := by
    rw [hfill]; exact isConformalBijection_fwdMapInv hW hW0 ha
  obtain ⟨F, hFeq, hFc, hFfr, -⟩ := exists_continuousOn_extension_of_path_of_tendsto hγc hγH hψ
    (tendsto_fwdMapInv_cobounded hW hW0 ha)
  refine ⟨F, hFeq, hFc, fun x hx hFx => ?_⟩
  have hxH : x ∈ Hbar \ H := ⟨mem_Hbar_of_im_eq_zero hx, fun h => by
    have : 0 < x.im := h
    rw [hx] at this; exact lt_irrefl 0 this⟩
  have hfr := hFfr hxH
  rw [hfill, (isHPHull_fwdHull hW ha).isOpen.frontier_eq] at hfr
  exact hfr.2 hFx

/-- The boundary extension `F̄_a = extendFrom ℍ F_a` under the hypotheses of
`exists_extension_of_fwdHull_eq`: it agrees with `F_a` on `ℍ`, is continuous on `ℍ̄`, maps no real point
into `ℍ \ K_a`, and stays within a bounded distance of the identity on `ℍ̄`. -/
theorem extendFrom_fwdMapInv_props (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 a)) (hK : fwdHull W a = fillH (γ '' Icc 0 a)) :
    EqOn (extendFrom H (fwdMapInv W a)) (fwdMapInv W a) H ∧
      ContinuousOn (extendFrom H (fwdMapInv W a)) Hbar ∧
      (∀ x : ℂ, x.im = 0 → extendFrom H (fwdMapInv W a) x ∉ H \ fwdHull W a) ∧
      ∃ C : ℝ, ∀ y ∈ Hbar, ‖extendFrom H (fwdMapInv W a) y - y‖ ≤ C := by
  obtain ⟨F, hFeq, hFc, hFR⟩ := exists_extension_of_fwdHull_eq hW hW0 ha hγ hK
  have hext : ∀ y ∈ Hbar, extendFrom H (fwdMapInv W a) y = F y := by
    intro y hy
    have h1 : Tendsto (fwdMapInv W a) (𝓝[H] y) (𝓝 (F y)) :=
      ((hFc y hy).mono H_subset_Hbar).congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)
    exact extendFrom_eq (by rw [closure_H]; exact hy) h1
  have hEqHbar : EqOn (extendFrom H (fwdMapInv W a)) F Hbar := fun y hy => hext y hy
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ha
  refine ⟨fun y hy => (hext y (H_subset_Hbar hy)).trans (hFeq hy), hFc.congr hEqHbar,
    fun x hx => by rw [hext x (mem_Hbar_of_im_eq_zero hx)]; exact hFR x hx, C, fun y hy => ?_⟩
  -- the bound passes to `ℍ̄` by density of `ℍ`
  rw [hext y hy]
  have hcl : y ∈ closure H := by rw [closure_H]; exact hy
  have hlim : Tendsto (fun z => ‖F z - z‖) (𝓝[H] y) (𝓝 ‖F y - y‖) :=
    (((hFc y hy).mono H_subset_Hbar).tendsto.sub
      (continuous_id.continuousWithinAt.tendsto)).norm
  have : (𝓝[H] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [hFeq hz]
  exact hC z hz

/-- **Hull composition through the extended inverse map.** Let `K_a = fill(A)` with `A` compact, and let
the chain driven by the shifted driver `V = W(a + ·) − W(a)` have `K'_u = fill(B)` for a compact `B ⊆ ℍ̄`.
If the extension `F̄_a` of `F_a` is continuous on `ℍ̄` and maps no real point into `ℍ \ K_a`, then
`K_{a+u} = fill(A ∪ F̄_a(B))`. (Domain Markov property `F_{a+u} = F_a ∘ F'_u`; `F_a` carries the unbounded
component of `ℍ \ B` onto the unbounded component of `ℍ \ (A ∪ F̄_a(B))`.) -/
theorem fwdHull_add_eq_fillH_union (hW : Continuous W) (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a)
    (hu : 0 ≤ u) {A B : Set ℂ} (hA : IsCompact A) (hKa : fwdHull W a = fillH A) (hB : IsCompact B)
    (hBH : B ⊆ Hbar) (hKB : fwdHull (shiftDrive W a) u = fillH B)
    (hFeq : EqOn (extendFrom H (fwdMapInv W a)) (fwdMapInv W a) H)
    (hFc : ContinuousOn (extendFrom H (fwdMapInv W a)) Hbar)
    (hFR : ∀ x : ℂ, x.im = 0 → extendFrom H (fwdMapInv W a) x ∉ H \ fwdHull W a) :
    fwdHull W (a + u) = fillH (A ∪ extendFrom H (fwdMapInv W a) '' B) := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : V 0 = 0 := shiftDrive_zero W a
  set F := fwdMapInv W a with hFdef
  set Fb := extendFrom H F with hFbdef
  set C := A ∪ Fb '' B with hCdef
  set Da := H \ fwdHull W a with hDa
  have hau : 0 ≤ a + u := add_nonneg ha hu
  have hcb := isConformalBijection_fwdMapInv hW hW0 ha
  have hgF : ∀ w ∈ H, fwdMap W a (F w) = w := fun w hw =>
    QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ha hw
  have hFg : ∀ z ∈ Da, F (fwdMap W a z) = z := fun z hz =>
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ha hz
  have hgH : MapsTo (fwdMap W a) Da H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha
  have hFDa : ∀ w ∈ H, F w ∈ Da := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha hw
  have hFinj : InjOn F H := hcb.2.injOn
  have hCc : IsCompact C := hA.union (hB.image_of_continuousOn (hFc.mono hBH))
  have hCb := hCc.isBounded
  have hBb := hB.isBounded
  have hstep1 : H \ fwdHull W (a + u) = F '' (H \ fwdHull V u) := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hV hV0 hu,
      ← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hau, image_image]
    refine image_congr fun w hw => ?_
    rw [QuantumZipper.RS.fwdMapInv_add_shift hW hW0 ha hu hw]
  rw [hKB] at hstep1
  have hAsub : ∀ z ∈ A, z ∈ H → z ∈ fwdHull W a := fun z hzA hzH => by
    rw [hKa]; exact ⟨hzH, Or.inl (subset_closure hzA)⟩
  have hCsub : ∀ z ∈ C, z ∈ H → z ∈ fillH C := fun z hz hzH =>
    ⟨hzH, Or.inl (subset_closure hz)⟩
  obtain ⟨CF, hCF⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ha
  obtain ⟨Ma, -, hMa⟩ := exists_abs_le_of_continuous hW a
  have hgdisp : ∀ z ∈ Da, ‖fwdMap W a z - z‖ ≤ 24 * Ma + 8 * Real.sqrt a := fun z hz =>
    norm_fwdMap_sub_self_le hW hW0 ha hMa hz ⟨ha, le_rfl⟩
  have hgcont : ContinuousOn (fwdMap W a) Da :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ha).continuousOn
  have hpc : ∀ S : Set ℂ, Bornology.IsBounded S → IsPreconnected (H \ fillH S) := fun S hS => by
    obtain ⟨R, hR', hSR⟩ := exists_closure_subset_ball hS
    rw [H_diff_fillH hR' hSR]
    exact isPreconnected_connectedComponentIn
  have hsub1 : F '' (H \ fillH B) ⊆ H \ fillH C := by
    apply subset_H_diff_fillH_of_isPreconnected hCb
    · exact (hpc B hBb).image _ ((continuousOn_fwdMapInv hW hW0 ha).mono fun x hx => hx.1)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨(hFDa x hx.1).1, fun hxC => ?_⟩
      rw [hCc.isClosed.closure_eq] at hxC
      rcases hxC with hxA | ⟨b, hbB, hb⟩
      · exact (hFDa x hx.1).2 (hAsub _ hxA (hFDa x hx.1).1)
      · by_cases hbH : b ∈ H
        · rw [hFeq hbH] at hb
          have hbx : b = x := hFinj hbH hx.1 hb
          exact hx.2 ⟨hx.1, Or.inl (subset_closure (hbx ▸ hbB))⟩
        · have h0 : b.im = 0 := le_antisymm (not_lt.1 hbH) (hBH hbB)
          exact hFR b h0 (hb ▸ hFDa x hx.1)
    · exact not_isBounded_image_of_norm_sub_le (not_isBounded_H_diff_fillH hBb)
        fun x hx => hCF x hx.1
  have hCDa : H \ fillH C ⊆ Da := fun z hz =>
    ⟨hz.1, fun hzK => hz.2 (fillH_mono subset_union_left (hKa ▸ hzK))⟩
  have himgsub : fwdMap W a '' (H \ fillH C) ⊆ H \ fillH B := by
    apply subset_H_diff_fillH_of_isPreconnected hBb
    · exact (hpc C hCb).image _ (hgcont.mono hCDa)
    · rintro _ ⟨y, hy, rfl⟩
      have hyD := hCDa hy
      have hgyH := hgH hyD
      refine ⟨hgyH, fun hyB => ?_⟩
      rw [hB.isClosed.closure_eq] at hyB
      have hFb : Fb (fwdMap W a y) = y := by rw [hFeq hgyH, hFg y hyD]
      exact hy.2 (hCsub y (Or.inr ⟨_, hyB, hFb⟩) hy.1)
    · exact not_isBounded_image_of_norm_sub_le (not_isBounded_H_diff_fillH hCb)
        fun z hz => hgdisp z (hCDa hz)
  have hsub2 : H \ fillH C ⊆ F '' (H \ fillH B) := fun z hz =>
    ⟨fwdMap W a z, himgsub ⟨z, hz, rfl⟩, hFg z (hCDa hz)⟩
  have hfin : H \ fwdHull W (a + u) = H \ fillH C := by
    rw [hstep1]; exact Subset.antisymm hsub1 hsub2
  ext z
  by_cases hzH : z ∈ H
  · constructor
    · intro hz
      by_contra hn
      have h1 : z ∈ H \ fillH C := ⟨hzH, hn⟩
      rw [← hfin] at h1
      exact h1.2 hz
    · intro hz
      by_contra hn
      have h1 : z ∈ H \ fwdHull W (a + u) := ⟨hzH, hn⟩
      rw [hfin] at h1
      exact h1.2 hz
  · exact ⟨fun hz => absurd ((QuantumZipper.fwdHull_mono (W := W)).2 _ hz) hzH,
      fun hz => absurd (fillH_subset_H _ hz) hzH⟩

/-- **A Loewner trace never enters the open lower half-plane.** Points below `ℝ` do not change the
filling, so an excursion of `η` below `ℝ` on a time interval would freeze the hulls, contradicting strict
growth (`fwdHull_ne_of_lt`). -/
theorem IsLoewnerTraceLT.mem_Hbar {T : ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) : η t ∈ Hbar := by
  by_contra hn
  have hneg : (η t).im < 0 := not_le.1 hn
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuousWithinAt_iff.1 (hη.2.1 t ⟨ht, htT⟩) (-(η t).im)
    (by linarith)
  set δ' := min (δ / 2) ((T - t) / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδ'δ : δ' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ'T : t + δ' < T := by linarith [min_le_right (δ / 2) ((T - t) / 2)]
  have hbelow : ∀ s ∈ Icc t (t + δ'), (η s).im < 0 := by
    intro s hs
    have hsT : s ∈ Ico 0 T := ⟨ht.trans hs.1, lt_of_le_of_lt hs.2 hδ'T⟩
    have hd : dist s t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have h1 := hδη hsT hd
    rw [dist_eq_norm] at h1
    have h2 : |(η s).im - (η t).im| < -(η t).im := by
      rw [← sub_im]
      exact lt_of_le_of_lt (abs_im_le_norm _) h1
    have h3 := (abs_lt.1 h2).2
    linarith
  have htt' : t < t + δ' := by linarith
  apply fwdHull_ne_of_lt hW hW0 ht htt'
  rw [hη.2.2 t ht htT, hη.2.2 (t + δ') (by linarith) hδ'T]
  apply fillH_congr
  rw [(hη.isCompact_image htT).isClosed.closure_eq, (hη.isCompact_image hδ'T).isClosed.closure_eq]
  ext z
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hzH⟩
    exact ⟨⟨s, ⟨hs.1, hs.2.trans htt'.le⟩, rfl⟩, hzH⟩
  · rintro ⟨⟨s, hs, rfl⟩, hzH⟩
    refine ⟨⟨s, ⟨hs.1, ?_⟩, rfl⟩, hzH⟩
    by_contra hst
    have := hbelow s ⟨(not_le.1 hst).le, hs.2⟩
    exact absurd hzH (not_lt.2 this.le)

end Real

section Frozen

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The frozen generating trace lies in `ℍ̄`** on its closed horizon `[0, T]` (driver continuous
before `T`). -/
theorem IsGeneratingTrace.mem_Hbar (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ T) : η t ∈ Hbar := by
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → η s ∈ Hbar := by
    intro s hs
    obtain ⟨t₂, hst₂, ht₂T⟩ := exists_real_btwn_of_lt hs
    have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg s).trans hst₂.le
    have h := IsLoewnerTraceLT.mem_Hbar (hη.isLoewnerTraceLT ht₂T) (continuous_frozenDrive_of_lt hw ht₂T)
      (by rw [frozenDrive_zero ht₂, hw0]) (NNReal.coe_nonneg s) hst₂
    simpa using h
  rcases ht.lt_or_eq with h | h
  · exact hlt t h
  · rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hη.1]; exact mem_Hbar_of_im_eq_zero (by simp)
    · have hc : ContinuousWithinAt η (Iio t) t :=
        (hη.2.1 t ht).mono fun s hs => (ENNReal.coe_le_coe.2 (le_of_lt hs)).trans ht
      have hcl : t ∈ closure (Iio t) := by
        rw [closure_Iio' ⟨0, pos_iff_ne_zero.2 h0⟩]
        exact (le_refl t : t ∈ Iic t)
      refine closure_minimal ?_ QuantumZipper.isClosed_Hbar (hc.mem_closure_image hcl)
      rintro _ ⟨s, hs, rfl⟩
      exact hlt s (h ▸ ENNReal.coe_lt_coe.2 hs)

/-- `η` **generates the Loewner chain driven by `w` on the closed interval `[0, σ]`, with its tip at
`σ`**: `η` is a generating trace on `[0, σ]` (the frozen `IsGeneratingTrace`, which asserts the hulls only
before `σ`), the hull at `σ` itself is the filling of `η([0, σ])`, and `F_σ(z) → η(σ)` as `z → 0` in `ℍ`.
This is "the trace is continuous up to and including" a time at which the chain is still defined
(Aux. lemma 99, p. 340), the form a continuation step needs. -/
def IsGeneratingTraceIcc (w : ℝ≥0 → ℝ) (σ : ℝ≥0) (η : ℝ≥0 → ℂ) : Prop :=
  IsGeneratingTrace w σ η ∧
    IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) σ) (η '' Icc 0 σ) ∧
    Tendsto (fwdMapInv (fun s : ℝ => w s.toNNReal) σ) (𝓝[H] 0) (𝓝 (η σ))

/-- A generating trace on `[0, T]` generates the chain on every closed `[0, σ]`, `σ < T`, with its tip. -/
theorem IsGeneratingTrace.isGeneratingTraceIcc (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {σ : ℝ≥0}
    (hσ : (σ : ℝ≥0∞) < T) : IsGeneratingTraceIcc w σ η :=
  ⟨hη.mono_horizon hσ.le, hη.2.2 σ hσ, hη.tendsto_fwdMapInv_tip hw hw0 hσ⟩

/-- The shifted driver `s ↦ w(σ + s) − w(σ)` on `ℝ≥0` (the driver of the restarted chain). -/
def shiftNN (w : ℝ≥0 → ℝ) (σ : ℝ≥0) (s : ℝ≥0) : ℝ := w (σ + s) - w σ

theorem shiftNN_zero (w : ℝ≥0 → ℝ) (σ : ℝ≥0) : shiftNN w σ 0 = 0 := by
  simp [shiftNN]

theorem continuousOn_shiftNN {T₂ : ℝ≥0∞} {σ : ℝ≥0}
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < σ + T₂}) :
    ContinuousOn (shiftNN w σ) {s | (s : ℝ≥0∞) < T₂} := by
  have h1 : ContinuousOn (fun s : ℝ≥0 => w (σ + s)) {s | (s : ℝ≥0∞) < T₂} :=
    hw.comp (continuous_const.add continuous_id).continuousOn fun s hs => by
      show ((σ + s : ℝ≥0) : ℝ≥0∞) < σ + T₂
      rw [ENNReal.coe_add]
      exact ENNReal.add_lt_add_left ENNReal.coe_ne_top hs
  exact h1.sub continuousOn_const

/-- **The joined path**: `η₁` on `[0, σ]`, then `F̄_σ(η₂(t − σ))`, where `F̄_σ` is the boundary extension of
the centred inverse map `F_σ` of the chain driven by `w`. -/
def joinTrace (w : ℝ≥0 → ℝ) (σ : ℝ≥0) (η₁ η₂ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  if t ≤ σ then η₁ t else extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) σ) (η₂ (t - σ))

theorem joinTrace_of_le {σ : ℝ≥0} {η₁ η₂ : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : t ≤ σ) :
    joinTrace w σ η₁ η₂ t = η₁ t := by
  simp only [joinTrace, ht, ↓reduceIte]

theorem joinTrace_of_lt {σ : ℝ≥0} {η₁ η₂ : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : σ < t) :
    joinTrace w σ η₁ η₂ t =
      extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) σ) (η₂ (t - σ)) := by
  simp only [joinTrace, not_le.2 ht, ↓reduceIte]

/-- The extension data of `F̄_σ` used by the join, read through the frozen driver `frozenDrive w t₂` for
some `t₂ > σ` (continuous on `ℝ`). -/
theorem IsGeneratingTraceIcc.extend_props {σ : ℝ≥0} {η₁ : ℝ≥0 → ℂ} (h₁ : IsGeneratingTraceIcc w σ η₁)
    {t₂ : ℝ} (hσt₂ : (σ : ℝ) < t₂) (hwc : Continuous (frozenDrive w t₂)) (hw0 : w 0 = 0) :
    fwdMapInv (fun s : ℝ => w s.toNNReal) σ = fwdMapInv (frozenDrive w t₂) σ ∧
      fwdHull (frozenDrive w t₂) σ = fillH ((fun s : ℝ => η₁ s.toNNReal) '' Icc 0 σ) ∧
      EqOn (extendFrom H (fwdMapInv (frozenDrive w t₂) σ)) (fwdMapInv (frozenDrive w t₂) σ) H ∧
      ContinuousOn (extendFrom H (fwdMapInv (frozenDrive w t₂) σ)) Hbar ∧
      (∀ x : ℂ, x.im = 0 →
        extendFrom H (fwdMapInv (frozenDrive w t₂) σ) x ∉ H \ fwdHull (frozenDrive w t₂) σ) ∧
      (∃ C : ℝ, ∀ y ∈ Hbar, ‖extendFrom H (fwdMapInv (frozenDrive w t₂) σ) y - y‖ ≤ C) ∧
      extendFrom H (fwdMapInv (frozenDrive w t₂) σ) 0 = η₁ σ := by
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg σ).trans hσt₂.le
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, w r.toNNReal = frozenDrive w t₂ r := fun r hr =>
    (frozenDrive_eq hr).symm
  have hF : fwdMapInv (fun s : ℝ => w s.toNNReal) σ = fwdMapInv (frozenDrive w t₂) σ :=
    fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg σ) hσt₂ heq
  have hK0 : fwdHull (fun s : ℝ => w s.toNNReal) σ = fwdHull (frozenDrive w t₂) σ :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg σ) hσt₂ heq
  have hA : IsCompact (η₁ '' Icc 0 σ) := isCompact_Icc.image_of_continuousOn
    (h₁.1.2.1.mono fun r hr => ENNReal.coe_le_coe.2 hr.2)
  have hfill : fwdHull (fun s : ℝ => w s.toNNReal) σ = fillH (η₁ '' Icc 0 σ) :=
    (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).1 h₁.2.1
  have hK : fwdHull (frozenDrive w t₂) σ = fillH ((fun s : ℝ => η₁ s.toNNReal) '' Icc 0 σ) := by
    rw [← hK0, hfill, image_toNNReal_Icc η₁ (NNReal.coe_nonneg σ), Real.toNNReal_coe]
  have hγ : ContinuousOn (fun s : ℝ => η₁ s.toNNReal) (Icc 0 σ) :=
    h₁.1.2.1.comp continuous_real_toNNReal.continuousOn fun r hr => by
      show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ σ
      exact ENNReal.coe_le_coe.2 (by simpa using Real.toNNReal_le_toNNReal hr.2)
  obtain ⟨h1, h2, h3, h4⟩ := extendFrom_fwdMapInv_props hwc (by rw [frozenDrive_zero ht₂, hw0])
    (NNReal.coe_nonneg σ) hγ hK
  refine ⟨hF, hK, h1, h2, h3, h4, ?_⟩
  have htend := h₁.2.2
  rw [hF] at htend
  exact extendFrom_eq (by rw [closure_H]; exact mem_Hbar_of_im_eq_zero (z := 0) (by simp)) htend

/-- The hulls of the joined path after the junction time `σ` (the main step of
`IsGeneratingTraceIcc.join`): for `σ < t < σ + T₂`, `K_t = fill(η₁[0, σ] ∪ F̄_σ(η₂[0, t − σ]))`. -/
theorem IsGeneratingTraceIcc.isFilling_join_of_lt {σ : ℝ≥0} {T₂ : ℝ≥0∞} {η₁ η₂ : ℝ≥0 → ℂ}
    (h₁ : IsGeneratingTraceIcc w σ η₁) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < σ + T₂})
    (hw0 : w 0 = 0) (h₂ : IsGeneratingTrace (shiftNN w σ) T₂ η₂)
    (hη₂H : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ T₂ → η₂ v ∈ Hbar)
    (hafter : ∀ t : ℝ≥0, σ ≤ t → joinTrace w σ η₁ η₂ t =
      extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) σ) (η₂ (t - σ)))
    (hcont : ContinuousOn (joinTrace w σ η₁ η₂) {t | (t : ℝ≥0∞) ≤ σ + T₂})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < σ + T₂) (hts : σ < t) :
    IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) t) (joinTrace w σ η₁ η₂ '' Icc 0 t) := by
  set Fb := extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) σ) with hFb
  set u : ℝ≥0 := t - σ with hu
  have htu : t = σ + u := (add_tsub_cancel_of_le hts.le).symm
  have huT : (u : ℝ≥0∞) < T₂ := by
    have h : ((σ + u : ℝ≥0) : ℝ≥0∞) < σ + T₂ := htu ▸ ht
    rw [ENNReal.coe_add] at h
    exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 h
  obtain ⟨t₃, htt₃, ht₃T⟩ := exists_real_btwn_of_lt ht
  have hwc₃ := continuous_frozenDrive_of_lt hw ht₃T
  have htR : (t : ℝ) = σ + u := by rw [htu, NNReal.coe_add]
  have hσt₃ : (σ : ℝ) < t₃ := by
    have : (σ : ℝ) < t := by exact_mod_cast hts
    linarith
  have ht₃ : 0 ≤ t₃ := (NNReal.coe_nonneg σ).trans hσt₃.le
  obtain ⟨hF₃, hK₃, hFeq₃, hFc₃, hFR₃, -, -⟩ := h₁.extend_props hσt₃ hwc₃ hw0
  have hu₃ : (u : ℝ) < t₃ - σ := by linarith
  have hshift : ∀ r ∈ Icc (0 : ℝ) (t₃ - σ),
      shiftDrive (frozenDrive w t₃) σ r = shiftNN w σ r.toNNReal := by
    intro r hr
    simp only [shiftDrive]
    rw [frozenDrive_eq ⟨by linarith [hr.1, NNReal.coe_nonneg σ], by linarith [hr.2]⟩,
      frozenDrive_eq ⟨NNReal.coe_nonneg σ, hσt₃.le⟩, Real.toNNReal_add (NNReal.coe_nonneg σ) hr.1,
      Real.toNNReal_coe]
    rfl
  have hBc : IsCompact (η₂ '' Icc 0 u) := isCompact_Icc.image_of_continuousOn
    (h₂.2.1.mono fun v hv => (ENNReal.coe_le_coe.2 hv.2).trans huT.le)
  have hK₂ : fwdHull (shiftDrive (frozenDrive w t₃) σ) u = fillH (η₂ '' Icc 0 u) := by
    rw [fwdHull_eq_of_eqOn (W' := fun s : ℝ => shiftNN w σ s.toNNReal) (NNReal.coe_nonneg u) hu₃
      hshift]
    exact (fillH_eq_iff_isFilling_of_isClosed hBc.isBounded hBc.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).1 (h₂.2.2 u huT)
  have hAc : IsCompact ((fun s : ℝ => η₁ s.toNNReal) '' Icc 0 σ) := by
    rw [image_toNNReal_Icc η₁ (NNReal.coe_nonneg σ), Real.toNNReal_coe]
    exact isCompact_Icc.image_of_continuousOn
      (h₁.1.2.1.mono fun r hr => ENNReal.coe_le_coe.2 hr.2)
  have hBH : η₂ '' Icc 0 u ⊆ Hbar := by
    rintro _ ⟨v, hv, rfl⟩
    exact hη₂H v ((ENNReal.coe_le_coe.2 hv.2).trans huT.le)
  have hcore := fwdHull_add_eq_fillH_union hwc₃ (by rw [frozenDrive_zero ht₃, hw0])
    (NNReal.coe_nonneg σ) (NNReal.coe_nonneg u) hAc hK₃ hBc hBH hK₂ hFeq₃ hFc₃ hFR₃
  have hFb₃ : extendFrom H (fwdMapInv (frozenDrive w t₃) σ) = Fb := by rw [hFb, hF₃]
  rw [hFb₃, image_toNNReal_Icc η₁ (NNReal.coe_nonneg σ), Real.toNNReal_coe, ← htR] at hcore
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (frozenDrive w t₃) t :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg t) htt₃ fun r hr => (frozenDrive_eq hr).symm
  have hset : joinTrace w σ η₁ η₂ '' Icc 0 t = η₁ '' Icc 0 σ ∪ Fb '' (η₂ '' Icc 0 u) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      rcases le_or_gt s σ with h | h
      · exact Or.inl ⟨s, ⟨zero_le, h⟩, (joinTrace_of_le h).symm⟩
      · exact Or.inr ⟨η₂ (s - σ), ⟨s - σ, ⟨zero_le, tsub_le_tsub_right hs.2 σ⟩, rfl⟩,
          (joinTrace_of_lt h).symm⟩
    · rintro (⟨s, hs, rfl⟩ | ⟨_, ⟨v, hv, rfl⟩, rfl⟩)
      · exact ⟨s, ⟨zero_le, hs.2.trans hts.le⟩, joinTrace_of_le hs.2⟩
      · refine ⟨σ + v, ⟨zero_le, ?_⟩, ?_⟩
        · rw [htu]; exact add_le_add_right hv.2 σ
        · rw [hafter _ le_self_add, add_tsub_cancel_left]
  have hJc : IsCompact (joinTrace w σ η₁ η₂ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn
    (hcont.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht.le)
  rw [hK]
  refine (fillH_eq_iff_isFilling_of_isClosed hJc.isBounded hJc.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).2 ?_
  rw [hset]
  exact hcore

/-- **The join of Loewner traces.** If `η₁` generates the chain driven by `w` on the closed interval
`[0, σ]` with its tip at `σ` (`IsGeneratingTraceIcc`), and `η₂` is a generating trace on `[0, T₂]` of the
shifted driver `w(σ + ·) − w(σ)`, then the joined path (`η₁` on `[0, σ]`, then `F̄_σ ∘ η₂(· − σ)`) is a
generating trace of `w` on `[0, σ + T₂]`. When `T₂ = ∞` and `‖η₂‖ → ∞`, also `‖joined‖ → ∞` (`F̄_σ` stays
within a bounded distance of the identity on `ℍ̄`, and `η₂` stays in `ℍ̄`). The driver need only be
continuous before `σ + T₂`. -/
theorem IsGeneratingTraceIcc.join {σ : ℝ≥0} {T₂ : ℝ≥0∞} {η₁ η₂ : ℝ≥0 → ℂ}
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < σ + T₂}) (hw0 : w 0 = 0)
    (h₁ : IsGeneratingTraceIcc w σ η₁) (h₂ : IsGeneratingTrace (shiftNN w σ) T₂ η₂) :
    IsGeneratingTrace w (σ + T₂) (joinTrace w σ η₁ η₂) ∧
      (T₂ = ⊤ → Tendsto (fun t => ‖η₂ t‖) atTop atTop →
        Tendsto (fun t => ‖joinTrace w σ η₁ η₂ t‖) atTop atTop) := by
  rcases eq_or_ne T₂ 0 with hT0 | hT0
  · subst hT0
    refine ⟨?_, fun h => absurd h ENNReal.zero_ne_top⟩
    rw [add_zero]
    refine ⟨by rw [joinTrace_of_le zero_le]; exact h₁.1.1,
      h₁.1.2.1.congr fun t ht => joinTrace_of_le (ENNReal.coe_le_coe.1 ht), fun t ht => ?_⟩
    have hts : t ≤ σ := (ENNReal.coe_lt_coe.1 ht).le
    rw [image_congr fun s hs => joinTrace_of_le (hs.2.trans hts)]
    exact h₁.1.2.2 t ht
  have hσlt : (σ : ℝ≥0∞) < σ + T₂ := ENNReal.lt_add_right ENNReal.coe_ne_top hT0
  have hwv := continuousOn_shiftNN hw
  have hw0' := shiftNN_zero w σ
  obtain ⟨t₂, hσt₂, ht₂T⟩ := exists_real_btwn_of_lt hσlt
  have hwc₂ := continuous_frozenDrive_of_lt hw ht₂T
  obtain ⟨hF, -, -, hFc, -, ⟨C, hC⟩, htip⟩ := h₁.extend_props hσt₂ hwc₂ hw0
  set Fb := extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) σ) with hFb
  have hFb' : Fb = extendFrom H (fwdMapInv (frozenDrive w t₂) σ) := by rw [hFb, hF]
  have hη₂H : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ T₂ → η₂ v ∈ Hbar := fun v hv =>
    IsGeneratingTrace.mem_Hbar h₂ hwv hw0' hv
  have hafter : ∀ t : ℝ≥0, σ ≤ t → joinTrace w σ η₁ η₂ t = Fb (η₂ (t - σ)) := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · exact joinTrace_of_lt h
    · subst h
      rw [joinTrace_of_le le_rfl, tsub_self, h₂.1, hFb', htip]
  have hFbH : ContinuousOn Fb Hbar := hFb' ▸ hFc
  have hCb : ∀ y ∈ Hbar, ‖Fb y - y‖ ≤ C := hFb' ▸ hC
  -- continuity on the closed horizon
  have hcont : ContinuousOn (joinTrace w σ η₁ η₂) {t | (t : ℝ≥0∞) ≤ σ + T₂} := by
    have hS₁ : ContinuousOn (joinTrace w σ η₁ η₂) (Iic σ) :=
      (h₁.1.2.1.mono fun t ht => ENNReal.coe_le_coe.2 ht).congr fun t ht => joinTrace_of_le ht
    set S₂ := {t : ℝ≥0 | σ ≤ t ∧ (t : ℝ≥0∞) ≤ σ + T₂} with hS₂def
    have hmaps : MapsTo (fun t : ℝ≥0 => t - σ) S₂ {v | (v : ℝ≥0∞) ≤ T₂} := by
      intro t ht
      show ((t - σ : ℝ≥0) : ℝ≥0∞) ≤ T₂
      rw [ENNReal.coe_sub]
      exact tsub_le_iff_left.2 ht.2
    have hc₂ : ContinuousOn (fun t : ℝ≥0 => η₂ (t - σ)) S₂ :=
      h₂.2.1.comp (continuous_id.sub continuous_const).continuousOn hmaps
    have hS₂ : ContinuousOn (joinTrace w σ η₁ η₂) S₂ :=
      (hFbH.comp hc₂ fun t ht => hη₂H _ (hmaps ht)).congr fun t ht => hafter t ht.1
    have hcl₂ : IsClosed S₂ := (isClosed_le continuous_const continuous_id).inter
      (isClosed_le ENNReal.continuous_coe continuous_const)
    refine (hS₁.union_of_isClosed hS₂ isClosed_Iic hcl₂).mono fun t ht => ?_
    rcases le_total t σ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, ht⟩
  -- the hulls
  have hhull : ∀ t : ℝ≥0, (t : ℝ≥0∞) < σ + T₂ →
      IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) t) (joinTrace w σ η₁ η₂ '' Icc 0 t) := by
    intro t ht
    rcases le_or_gt t σ with hts | hts
    · rw [image_congr fun s hs => joinTrace_of_le (hs.2.trans hts)]
      rcases hts.lt_or_eq with h | h
      · exact h₁.1.2.2 t (ENNReal.coe_lt_coe.2 h)
      · subst h; exact h₁.2.1
    · exact h₁.isFilling_join_of_lt hw hw0 h₂ hη₂H hafter hcont ht hts
  refine ⟨⟨by rw [joinTrace_of_le zero_le]; exact h₁.1.1, hcont, hhull⟩, fun hT hlim => ?_⟩
  have hsh : Tendsto (fun t : ℝ≥0 => t - σ) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b + σ, fun t ht => le_tsub_of_add_le_right ht⟩
  have h1 := tendsto_atTop_add_const_right atTop (-C) (hlim.comp hsh)
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop σ] with t ht
  rw [hafter t ht]
  have h3 := hCb _ (hη₂H (t - σ) (by rw [hT]; exact le_top))
  have h4 := norm_sub_norm_le (η₂ (t - σ)) (Fb (η₂ (t - σ)))
  rw [norm_sub_rev] at h4
  show ‖η₂ (t - σ)‖ + -C ≤ ‖Fb (η₂ (t - σ))‖
  linarith

end Frozen

end Sec7

end InteractingSLE
