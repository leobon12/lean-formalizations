/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3Exhaust
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# A.2, part 3: pulling the image accumulation back to the small tip

Packet PROVE-ZHAN-A2P3. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L563–L596; R38, R53): "Infinite half-plane capacity forces an
unbounded sequence of trace points … Under `R⁻¹`, this makes `w` a subsequential limit of the original image trace.
Pulling back through the continuous inverse map of the simple small prefix puts its tip in `S`."

Fix the small prefix at a deterministic time `q < ζ₁`, with hydrodynamic map `g_q = physMap y w₁ q` and tip image
`y + w₁(q)`. This file proves the pull-back step:

* `mem_closure_of_mem_closure_physMap` (pathwise): if a set `A ⊂ ℍ` disjoint from the small hull has `g_q`-images
  accumulating at the tip image `x₁ + w₁(q)`, then the tip `η(q) + x₁` lies in the closure of `A`. Proof: the
  centred inverse `F_q = fwdMapInv` tends to `η(q)` at `0` (`IsGeneratingTrace.tendsto_fwdMapInv_tip`, the
  continuous boundary extension of the inverse map of a curve-generated hull) and inverts `fwdMap` off the hull.
* `LargeAccumG3Statement`, `LargeAccumEightStatement` (per time, not proved here): almost surely on `{q < ζ₁}`,
  the `g_q`-images of the large hulls before contact accumulate at the tip image;
* **`tipInHullG3Statement_of_largeAccum`**, **`tipInHullEightStatement_of_largeAccum`**: the per-time statements of
  `A2Part3Exhaust` from these (the large hulls before contact lie in the strip life and miss the small hull);
* `ImageTipG3Statement`, `ImageTipEightStatement` (per time, not proved here): in the chart of the conditional
  image law at `q` (A.1 L183–L187), the image hulls before the image contact time `ζ'` accumulate at the image `w`
  of the small tip — the content of L563–L594 (maximality up to contact, retargeting `w` to `∞`, high-force
  noncollision, infinite capacity);
* **`largeAccumG3Statement_of_imageTip`**, **`largeAccumEightStatement_of_imageTip`**: the large-hull form from the
  image-chart form, through the hull identity of `IsImageChainUpTo` (`g_q(K₂(s)) = K'(clk s)` before contact) and the
  conditional image law of `IsA2DualPair` at the constant stopping time `q`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-! ### The pull-back through the inverse map -/

theorem mem_H_sub_ofReal {z : ℂ} (hz : z ∈ H) (x : ℝ) : z - x ∈ H := by
  have h : 0 < z.im := hz
  show 0 < (z - x).im
  simpa using h

/-- **Pull-back through the continuous inverse map** (L593–L594). Let `η` generate the small driver `w₁` up to `ζ₁`
and `q < ζ₁`. If `A ⊂ ℍ` misses the small hull at `q` (translated by `x₁`) and the hydrodynamic images
`g_q(A)` accumulate at the tip image `x₁ + w₁(q)`, then `η(q) + x₁` lies in the closure of `A`. -/
theorem mem_closure_of_mem_closure_physMap {x₁ : ℝ} {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ₁) (hw : ContinuousOn w₁ {s | (s : ℝ≥0∞) < ζ₁}) (hw0 : w₁ 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w₁ ζ₁ η) {A : Set ℂ} (hAH : A ⊆ H)
    (hA : Disjoint A (physHull x₁ (Strip.extPath w₁) q))
    (hacc : (x₁ : ℂ) + (w₁ q : ℂ) ∈ closure (physMap x₁ (Strip.extPath w₁) q '' A)) :
    η q + x₁ ∈ closure A := by
  obtain ⟨t₂, hqt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hq
  have hq0 : (0 : ℝ) ≤ q := q.2
  set V : ℝ → ℝ := frozenDrive w₁ t₂ with hV
  have hVc : Continuous V := continuous_frozenDrive_of_lt hw ht₂ζ
  have hV0 : V 0 = 0 := by rw [hV, frozenDrive_zero (hq0.trans hqt₂.le), hw0]
  have hEq : ∀ r ∈ Icc (0 : ℝ) t₂, Strip.extPath w₁ r = V r := fun r hr => (frozenDrive_eq hr).symm
  have hK : fwdHull (Strip.extPath w₁) q = fwdHull V q := fwdHull_eq_of_eqOn hq0 hqt₂ hEq
  have hM : ∀ z, fwdMap (Strip.extPath w₁) q z = fwdMap V q z := fun z =>
    fwdMap_eq_of_eqOn hq0 fun r hr => hEq r ⟨hr.1, hr.2.trans hqt₂.le⟩
  have hMi : fwdMapInv (Strip.extPath w₁) q = fwdMapInv V q := fwdMapInv_eq_of_eqOn hq0 hqt₂ hEq
  -- the centred preimages
  set B : Set ℂ := (fun z => z - x₁) '' A with hB
  have hBK : ∀ b ∈ B, b ∈ H \ fwdHull V q := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨mem_H_sub_ofReal (hAH ha) x₁, fun hK' => ?_⟩
    refine hA.ne_of_mem ha ⟨a - x₁, by rw [hK]; exact hK', by ring⟩ rfl
  set C : Set ℂ := fwdMap V q '' B with hC
  have hCH : C ⊆ H := by
    rintro _ ⟨b, hb, rfl⟩
    exact FwdHolo.mapsTo_fwdMap hVc hq0 (hBK b hb)
  -- `0` is in the closure of `C`
  have hC0 : (0 : ℂ) ∈ closure C := by
    have himg : (fun z => z - ((x₁ : ℂ) + (w₁ q : ℂ))) '' (physMap x₁ (Strip.extPath w₁) q '' A) = C := by
      ext c
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨a - x₁, ⟨a, ha, rfl⟩, ?_⟩
        simp only [physMap, Strip.extPath_coe, hM]
        ring
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
        simp only [physMap, Strip.extPath_coe, hM]
        ring
    have hcs : Continuous fun z : ℂ => z - ((x₁ : ℂ) + (w₁ q : ℂ)) := by fun_prop
    have h1 := hcs.continuousAt.continuousWithinAt.mem_closure_image hacc
    rw [himg, sub_self] at h1
    exact h1
  -- the inverse map tends to the tip
  have htip : Tendsto (fwdMapInv V q) (𝓝[H] 0) (𝓝 (η q)) := by
    have := hη.tendsto_fwdMapInv_tip hw hw0 hq
    rw [show (fun s : ℝ => w₁ s.toNNReal) = Strip.extPath w₁ from rfl, hMi] at this
    exact this
  have hne : (𝓝[C] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hC0
  have hlim : Tendsto (fwdMapInv V q) (𝓝[C] 0) (𝓝 (η q)) := htip.mono_left (nhdsWithin_mono _ hCH)
  have hev : ∀ᶠ c in 𝓝[C] (0 : ℂ), fwdMapInv V q c ∈ B := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    obtain ⟨b, hb, rfl⟩ := hc
    rw [RS.fwdMapInv_fwdMap hVc hV0 hq0 (hBK b hb)]
    exact hb
  have hηB : η q ∈ closure B := mem_closure_of_tendsto hlim hev
  have hca : Continuous fun z : ℂ => z + (x₁ : ℂ) := by fun_prop
  have h2 := hca.continuousAt.continuousWithinAt.mem_closure_image hηB
  have hBA : (fun z => z + (x₁ : ℂ)) '' B = A := by
    rw [hB, image_image]
    simp
  rw [hBA] at h2
  exact h2

/-! ### The large hulls before contact -/

/-- The hulls of the curve started at `0` with driver `w₂` at the times before `c`. -/
def preContactHulls (w₂ : ℝ → ℝ) (c : ℝ≥0∞) : Set ℂ :=
  ⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < c), physHull 0 w₂ s

theorem physHull_zero (w : ℝ → ℝ) (s : ℝ) : physHull 0 w s = fwdHull w s := by
  simp [physHull]

theorem preContactHulls_subset_H (w₂ : ℝ → ℝ) (c : ℝ≥0∞) : preContactHulls w₂ c ⊆ H := by
  intro z hz
  simp only [preContactHulls, mem_iUnion, physHull_zero] at hz
  obtain ⟨s, -, hs⟩ := hz
  exact hs.1

/-- Before the contact time the large hulls miss the small hull. -/
theorem disjoint_preContactHulls (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ) :
    Disjoint (preContactHulls wj (contactTime 0 wj ζj xk wk τ)) (physHull xk wk τ) := by
  rw [Set.disjoint_left]
  intro z hz hzk
  simp only [preContactHulls, mem_iUnion] at hz
  obtain ⟨s, hs, hzs⟩ := hz
  have hne : (closure (physHull 0 wj s) ∩ closure (physHull xk wk τ)).Nonempty :=
    ⟨z, subset_closure hzs, subset_closure hzk⟩
  have hle : contactTime 0 wj ζj xk wk τ ≤ (s : ℝ≥0∞) :=
    (min_le_right _ _).trans (iInf₂_le s hne)
  exact absurd hs (not_lt.2 hle)

/-- Before `lifeEnd` the large curve is in its strip life. -/
theorem isStripLife_of_lt_lifeEnd {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {s : ℝ≥0} (hs : (s : ℝ≥0∞) < lifeEnd w v ζ) :
    Strip.IsStripLife w v ζ s := by
  by_contra hns
  exact absurd hs (not_lt.2 (iInf₂_le s hns))

/-- The large hulls before contact lie in the large hulls over the strip life. -/
theorem preContactHulls_subset_lifeHull (w₂ v₂ : ℝ≥0 → ℝ) (ζ₂ : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ) :
    preContactHulls (Strip.extPath w₂) (contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂) xk wk τ) ⊆
      ⋃ (t : ℝ≥0) (_ : Strip.IsStripLife w₂ v₂ ζ₂ t), fwdHull (fun s : ℝ => w₂ s.toNNReal) t := by
  intro z hz
  simp only [preContactHulls, mem_iUnion, physHull_zero] at hz ⊢
  obtain ⟨s, hs, hzs⟩ := hz
  exact ⟨s, isStripLife_of_lt_lifeEnd (hs.trans_le (min_le_left _ _)), hzs⟩

/-- **The tip lies in `S`** (pathwise, L593–L596): if the `g_q`-images of the large hulls before contact accumulate
at the tip image, the tip `η(q) + x₁` lies in the closure of the large hulls over the strip life. -/
theorem tip_mem_lifeHullClosure {x₁ : ℝ} {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ₁)
    (hw : ContinuousOn w₁ {s | (s : ℝ≥0∞) < ζ₁}) (hw0 : w₁ 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w₁ ζ₁ η) {w₂ v₂ : ℝ≥0 → ℝ} {ζ₂ : ℝ≥0∞}
    (hacc : (x₁ : ℂ) + (w₁ q : ℂ) ∈ closure (physMap x₁ (Strip.extPath w₁) q ''
      preContactHulls (Strip.extPath w₂)
        (contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂) x₁ (Strip.extPath w₁) q))) :
    η q + x₁ ∈ lifeHullClosure w₂ v₂ ζ₂ :=
  closure_mono (preContactHulls_subset_lifeHull w₂ v₂ ζ₂ _ _ _)
    (mem_closure_of_mem_closure_physMap hq hw hw0 hη (preContactHulls_subset_H _ _)
      (disjoint_preContactHulls _ _ _ _ _) hacc)

/-- **The image chain carries the image accumulation to the large hulls**: before the image contact time the image
hulls are the `g_τ`-images of the hulls of curve `j` before contact. -/
theorem mem_closure_physMap_of_imageChain {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ}
    {x' : ℝ} {w' : ℝ → ℝ} {clk : ℝ → ℝ} {ζ' : ℝ≥0∞} {p : ℂ}
    (hch : IsImageChainUpTo xj wj ζj xk wk τ x' w' clk ζ')
    (hp : p ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ'), physHull x' w' t)) :
    p ∈ closure (physMap xk wk τ ''
      ⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ), physHull xj wj s) := by
  refine closure_mono ?_ hp
  intro z hz
  simp only [mem_iUnion] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  obtain ⟨s, hs, hts⟩ := (hch.2.2.2.1 t).1 ht
  have hmono : physHull x' w' t ⊆ physHull x' w' (clk s) :=
    image_mono ((fwdHull_mono (W := w')).1 hts.le)
  rw [← hch.2.2.2.2 s hs] at hmono
  exact image_mono (subset_biUnion_of_mem (u := fun s : ℝ≥0 => physHull xj wj s) hs) (hmono hzt)

/-- **The image hulls before `ζ'` are exactly the `g_τ`-images of the hulls of curve `j` before contact** (the clock
is continuous, strictly increasing and cofinal in `[0, ζ')`). -/
theorem iUnion_physHull_eq_of_imageChain {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ}
    {x' : ℝ} {w' : ℝ → ℝ} {clk : ℝ → ℝ} {ζ' : ℝ≥0∞}
    (hch : IsImageChainUpTo xj wj ζj xk wk τ x' w' clk ζ') :
    (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ'), physHull x' w' t) =
      physMap xk wk τ '' ⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ), physHull xj wj s := by
  refine Subset.antisymm (fun z hz => ?_) ?_
  · simp only [mem_iUnion] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨s, hs, hts⟩ := (hch.2.2.2.1 t).1 ht
    have hmono : physHull x' w' t ⊆ physHull x' w' (clk s) :=
      image_mono ((fwdHull_mono (W := w')).1 hts.le)
    rw [← hch.2.2.2.2 s hs] at hmono
    exact image_mono (subset_biUnion_of_mem (u := fun s : ℝ≥0 => physHull xj wj s) hs) (hmono hzt)
  · rw [image_iUnion₂]
    refine iUnion₂_subset fun s hs => ?_
    set c := contactTime xj wj ζj xk wk τ
    have hmem : ∀ r : ℝ≥0, (r : ℝ≥0∞) < c → (r : ℝ) ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < c} :=
      fun r hr => ⟨r.2, by rwa [ENNReal.ofReal_coe_nnreal]⟩
    have h0 : (0 : ℝ) ≤ clk s := by
      have := hch.2.2.1.monotoneOn (hmem 0 (lt_of_le_of_lt (by simp) hs)) (hmem s hs) s.2
      simpa [hch.1] using this
    obtain ⟨s', hss', hs'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    have hlt : clk s < clk s' :=
      hch.2.2.1 (hmem s hs) (hmem s' hs'c) (by exact_mod_cast ENNReal.coe_lt_coe.1 hss')
    have ht : (((clk s).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ' :=
      (hch.2.2.2.1 _).2 ⟨s', hs'c, by rwa [Real.coe_toNNReal _ h0]⟩
    rw [hch.2.2.2.2 s hs]
    intro z hz
    simp only [mem_iUnion]
    exact ⟨(clk s).toNNReal, ht, by rwa [Real.coe_toNNReal _ h0]⟩

/-! ### The per-time statements and their reductions -/

/-- **The large hulls before contact accumulate at the small tip image, (G3)** (L563–L594): for every (G3) dual pair
and every deterministic time `q`, almost surely on `{q < ζ₁}`, the `g_q`-images of the large hulls before their
contact with the small hull at `q` (capped by the end of the large strip life) accumulate at the tip image
`y + W₁(q)`. -/
def LargeAccumG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
          (y : ℂ) + (W₁ q ω : ℂ) ∈ closure (physMap y (Strip.extPath (W₁ · ω)) q ''
            preContactHulls (Strip.extPath (W₂ · ω))
              (contactTime 0 (Strip.extPath (W₂ · ω)) (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
                (Strip.extPath (W₁ · ω)) q))

/-- **The large hulls before contact accumulate at the small tip image, (Eight)** (L563–L594). -/
def LargeAccumEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
          (x : ℂ) + (W₁ q ω : ℂ) ∈ closure (physMap x (Strip.extPath (W₁ · ω)) q ''
            preContactHulls (Strip.extPath (W₂ · ω))
              (contactTime 0 (Strip.extPath (W₂ · ω)) (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
                (Strip.extPath (W₁ · ω)) q))

/-- The per-time statement (G3) of `A2Part3Exhaust` from the large-hull accumulation (pull-back through the inverse
map of the small prefix; the small path is regular almost surely). -/
theorem tipInHullG3Statement_of_largeAccum {κ : ℝ} (h : LargeAccumG3Statement.{u} κ) :
    TipInHullG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  filter_upwards [h hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0,
    hpair.2.1.2.2.2.2] with ω hω hpath hq η hη
  exact tip_mem_lifeHullClosure hq hpath.2.2.2.1 hpath.1 hη (hω hq)

/-- The per-time statement (Eight) of `A2Part3Exhaust` from the large-hull accumulation. -/
theorem tipInHullEightStatement_of_largeAccum {κ : ℝ} (h : LargeAccumEightStatement.{u} κ) :
    TipInHullEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  filter_upwards [h hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0,
    hpair.2.1.2.2.2.2] with ω hω hpath hq η hη
  exact tip_mem_lifeHullClosure hq hpath.2.2.2.1 hpath.1 hη (hω hq)

/-- **The image hulls accumulate at the image of the small tip, (G3)** (L563–L594). For every (G3) dual pair, every
deterministic time `q` and every image process of the conditional image law at the constant stopping time `q` (the
fourth clause of `IsA2DualPair`: the large curve mapped by `g_q`, a local evolution of the image word up to the image
`ζ'` of the contact time, tied to the large hulls by `IsImageChainUpTo`), almost surely on `{q < ζ₁}` the image hulls
before `ζ'` accumulate at the image `y + W₁(q)` of the small tip (the mark `w` of the image word, weight `−κ/2`). -/
def ImageTipG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin 4 → ℝ≥0 → Ω → ℝ)
          (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (clk : Ω → ℝ → ℝ),
          Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P (isStoppingTime_const 𝓕₁ q).measurableSpace
            {ω | (q : ℝ≥0∞) < ζ₁ ω}
            (fun ω => ![VR₁ 1 q ω - VR₁ 2 q ω, VR₁ 0 q ω - VR₁ 2 q ω, W₁ q ω - VR₁ 2 q ω, VL₁ 0 q ω - VR₁ 2 q ω])
            (fun _ => ![]) (largeG3ImgRhoL κ) ![] 𝓖 W' VL' VR' B' ζ' →
          (∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
            IsImageChainUpTo 0 (Strip.extPath (W₂ · ω)) (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
              (Strip.extPath (W₁ · ω)) q (y + VR₁ 2 q ω) (Strip.extPath (W' · ω)) (clk ω) (ζ' ω)) →
          ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
            (y : ℂ) + (W₁ q ω : ℂ) ∈
              closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ' ω), physHull (y + VR₁ 2 q ω) (Strip.extPath (W' · ω)) t)

/-- **The image hulls accumulate at the image of the small tip, (Eight)** (L563–L594); image word: source
`x + VR₁ 1`, left marks `x⁺`, the small tip, `x⁻`. -/
def ImageTipEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin 3 → ℝ≥0 → Ω → ℝ)
          (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (clk : Ω → ℝ → ℝ),
          Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P (isStoppingTime_const 𝓕₁ q).measurableSpace
            {ω | (q : ℝ≥0∞) < ζ₁ ω}
            (fun ω => ![VR₁ 0 q ω - VR₁ 1 q ω, W₁ q ω - VR₁ 1 q ω, VL₁ 0 q ω - VR₁ 1 q ω])
            (fun _ => ![]) (largeEightImgRhoL κ) ![] 𝓖 W' VL' VR' B' ζ' →
          (∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
            IsImageChainUpTo 0 (Strip.extPath (W₂ · ω)) (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
              (Strip.extPath (W₁ · ω)) q (x + VR₁ 1 q ω) (Strip.extPath (W' · ω)) (clk ω) (ζ' ω)) →
          ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
            (x : ℂ) + (W₁ q ω : ℂ) ∈
              closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ' ω), physHull (x + VR₁ 1 q ω) (Strip.extPath (W' · ω)) t)

/-- The large-hull form (G3) from the image-chart form, through the conditional image law at the constant stopping
time `q`. -/
theorem largeAccumG3Statement_of_imageTip {κ : ℝ} (h : ImageTipG3Statement.{u} κ) :
    LargeAccumG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hE, hch⟩ := hpair.2.2.2 (fun _ => q) (isStoppingTime_const 𝓕₁ q)
  filter_upwards [h hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0 𝓖 W' VL' VR'
    B' ζ' clk hE hch, hch] with ω h1 h2 hq
  exact mem_closure_physMap_of_imageChain (h2 hq) (h1 hq)

/-- The large-hull form (Eight) from the image-chart form. -/
theorem largeAccumEightStatement_of_imageTip {κ : ℝ} (h : ImageTipEightStatement.{u} κ) :
    LargeAccumEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hE, hch⟩ := hpair.2.2.2 (fun _ => q) (isStoppingTime_const 𝓕₁ q)
  filter_upwards [h hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0 𝓖 W' VL' VR'
    B' ζ' clk hE hch, hch] with ω h1 h2 hq
  exact mem_closure_physMap_of_imageChain (h2 hq) (h1 hq)

/-- **A.2, part 3, (G3)** from the image-chart accumulation. -/
theorem smallInHullG3Statement_of_imageTip {κ : ℝ} (h : ImageTipG3Statement.{u} κ) :
    A2SmallInHullG3Statement.{u} κ :=
  smallInHullG3Statement_of_tip (tipInHullG3Statement_of_largeAccum (largeAccumG3Statement_of_imageTip h))

/-- **A.2, part 3, (Eight)** from the image-chart accumulation. -/
theorem smallInHullEightStatement_of_imageTip {κ : ℝ} (h : ImageTipEightStatement.{u} κ) :
    A2SmallInHullEightStatement.{u} κ :=
  smallInHullEightStatement_of_tip (tipInHullEightStatement_of_largeAccum (largeAccumEightStatement_of_imageTip h))

end InteractingSLE.ZhanGT4.A2X.P3
