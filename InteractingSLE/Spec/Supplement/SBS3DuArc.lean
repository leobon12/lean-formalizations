/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DvTime
import InteractingSLE.Spec.Supplement.WalkContinuum
import InteractingSLE.Spec.Supplement.SBLwPath
import InteractingSLE.Spec.Supplement.SB2LkFF
import InteractingSLE.Spec.Supplement.SBLuPath

/-!
# D5's F2a: the stage theorems along a proper parametrization of the lower walk

Worker PROVE-R6-CORNER (round 9). Deterministic geometry turning `exists_canon_package`, Lemma S2's lift and the
time-change lemma into drivenness of the canonical stage curve of an actual piece:

* `exists_arc_of_cut`: a compact preconnected set through `β 0`, cut by a preconnected set at one point, is an
  initial arc `β([0, σ])` of the proper curve `β`, and the cutting set lies on `β([σ, ∞))`;
* `exists_timeChange_fin`, `exists_timeChange_top`: a piece on `β([σ, ∞))` is `β (σ + φ₀ ·)` for a continuous
  increasing time change `φ₀` (through `β`'s closed embedding);
* `canonCurve_congr`: the canonical curve only reads the piece up to its lifetime;
* `stagePath_facts`: a finite-fibre path from `0` for `A ∪ β([0, σ])`;
* `mem_diff_fill_union`: beyond the cut, the tail's points in `ℍ ∖ fill A` are in `ℍ ∖ fill (A ∪ β([0, σ]))` (the lift
  puts the tail in the closure of `ℍ ∖ fill (A ∪ β([0, σ]))`, and a frontier point of it in `ℍ` lies on `A` or on the
  initial arc);
* **`isDrivenCurve_stage_fin`**, **`isDrivenCurve_stage_top`**: for a cut `σ` at the largest real point of
  `A ∪ β([0, σ])` and a finite (resp. infinite last) piece from `β σ` whose times in `ℍ ∖ fill A` are dense, the
  canonical stage curve for `A ∪ β([0, σ])` is driven.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.SB.Dv

open Sec7.PocketTraversal Sec7.Lemma71C

/-! ### Arcs of a proper curve cut at a point -/

/-- **A compact preconnected set through `β 0` cut by a preconnected set at one point is an initial arc**: if `P` is
compact and preconnected with `β 0 ∈ P`, `T` is preconnected with a point other than `x`, both lie on the proper curve
`β`, and `P ∩ T = {x}`, then `x = β σ`, `P = β([0, σ])` and `T ⊆ β([σ, ∞))`. -/
theorem exists_arc_of_cut {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) {P T : Set ℂ} {x : ℂ}
    (hP : IsCompact P) (hPc : IsPreconnected P) (h0 : β 0 ∈ P) (hPr : P ⊆ range β) (hTr : T ⊆ range β)
    (hTc : IsPreconnected T) (hPT : P ∩ T = {x}) (hT2 : ∃ y ∈ T, y ≠ x) :
    ∃ σ : ℝ≥0, β σ = x ∧ P = β '' Icc 0 σ ∧ T ⊆ β '' Ici σ := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hβ
  have hinj : Function.Injective β := hβ.2.1
  set I := β ⁻¹' P with hIdef
  set J := β ⁻¹' T with hJdef
  have hIc : IsCompact I := he.isCompact_preimage hP
  have hIp : IsPreconnected I := by
    rw [hIdef, ← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hPr]
    exact hPc
  have hJp : IsPreconnected J := by
    rw [hJdef, ← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hTr]
    exact hTc
  have hI0 : (0 : ℝ≥0) ∈ I := h0
  have hIne : I.Nonempty := ⟨0, hI0⟩
  set σ := sSup I with hσdef
  have hσI : σ ∈ I := hIc.sSup_mem hIne
  have hIeq : I = Icc 0 σ := by
    refine Subset.antisymm (fun t ht => ⟨(zero_le : (0 : ℝ≥0) ≤ t), le_csSup hIc.bddAbove ht⟩) ?_
    exact hIp.ordConnected.out hI0 hσI
  have hPeq : P = β '' Icc 0 σ := by
    rw [← hIeq, hIdef, image_preimage_eq_of_subset hPr]
  -- the cut point
  have hxT : x ∈ T := (hPT.symm ▸ mem_singleton x : x ∈ P ∩ T).2
  have hxP : x ∈ P := (hPT.symm ▸ mem_singleton x : x ∈ P ∩ T).1
  obtain ⟨τ, hτ⟩ := hTr hxT
  have hτI : τ ∈ I := by show β τ ∈ P; rw [hτ]; exact hxP
  have hτJ : τ ∈ J := by show β τ ∈ T; rw [hτ]; exact hxT
  have hIJ : ∀ t ∈ I, t ∈ J → t = τ := fun t htI htJ => by
    have : β t ∈ P ∩ T := ⟨htI, htJ⟩
    rw [hPT, mem_singleton_iff, ← hτ] at this
    exact hinj this
  obtain ⟨y, hyT, hyx⟩ := hT2
  obtain ⟨ty, hty⟩ := hTr hyT
  have htyJ : ty ∈ J := by show β ty ∈ T; rw [hty]; exact hyT
  have htyI : ty ∉ I := fun h => hyx (by rw [← hty, hIJ ty h htyJ, hτ])
  have hσty : σ < ty := by
    by_contra hle
    exact htyI (hIeq ▸ ⟨(zero_le : (0 : ℝ≥0) ≤ ty), not_lt.1 hle⟩)
  have hτσ : τ = σ := by
    have hτle : τ ≤ σ := le_csSup hIc.bddAbove hτI
    have hσJ : σ ∈ J := hJp.ordConnected.out hτJ htyJ ⟨hτle, hσty.le⟩
    exact (hIJ σ hσI hσJ).symm
  refine ⟨σ, by rw [← hτσ, hτ], hPeq, ?_⟩
  intro z hz
  obtain ⟨t, ht⟩ := hTr hz
  refine ⟨t, ?_, ht⟩
  by_contra hlt
  have htI : t ∈ I := hIeq ▸ ⟨(zero_le : (0 : ℝ≥0) ≤ t), (not_le.1 hlt).le⟩
  have htJ : t ∈ J := by show β t ∈ T; rw [ht]; exact hz
  have := hIJ t htI htJ
  rw [this, hτσ] at hlt
  exact hlt (le_refl σ)

/-! ### The time change of a piece along a proper curve -/

/-- A continuous map of `ℝ≥0` from `0`, injective on `[0, L)`, is strictly increasing there. -/
theorem strictMonoOn_Iio_of_injOn {φ : ℝ≥0 → ℝ≥0} (hc : Continuous φ) (h0 : φ 0 = 0) {L : ℝ≥0}
    (hi : InjOn φ (Iio L)) : StrictMonoOn φ (Iio L) := by
  intro a ha b hb hab
  have hsub : Icc 0 b ⊆ Iio L := fun x hx => lt_of_le_of_lt hx.2 hb
  have hm := hc.continuousOn.strictMonoOn_of_injOn_Icc (zero_le : (0 : ℝ≥0) ≤ b)
    (by rw [h0]; exact bot_le) (hi.mono hsub)
  exact hm ⟨bot_le, hab.le⟩ ⟨bot_le, le_rfl⟩ hab

/-- **The time change of a finite piece along a proper curve**: a piece `q`, continuous on `[0, L]`, injective on
`[0, L)`, from `β σ`, with values on `β([σ, ∞))`, is `β (σ + φ₀ ·)` on `[0, L]` for a continuous `φ₀` from `0`,
strictly increasing on `[0, L)`. -/
theorem exists_timeChange_fin {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) {q : ℝ≥0 → ℂ} {L σ : ℝ≥0}
    (hqc : ContinuousOn q (Icc 0 L)) (hqi : InjOn q (Iio L)) (hq0 : q 0 = β σ)
    (hqβ : ∀ t, t ≤ L → q t ∈ β '' Ici σ) :
    ∃ φ₀ : ℝ≥0 → ℝ≥0, Continuous φ₀ ∧ φ₀ 0 = 0 ∧ StrictMonoOn φ₀ (Iio L) ∧ ∀ t, t ≤ L → q t = β (σ + φ₀ t) := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hβ
  have hinj : Function.Injective β := hβ.2.1
  set q' : ℝ≥0 → ℂ := fun t => q (min t L) with hq'def
  have hq'c : Continuous q' :=
    hqc.comp_continuous (continuous_id.min continuous_const) fun t => ⟨bot_le, min_le_right _ _⟩
  have hex : ∀ t, ∃ τ, σ ≤ τ ∧ β τ = q' t := fun t => by
    obtain ⟨τ, hτ, he'⟩ := hqβ (min t L) (min_le_right _ _)
    exact ⟨τ, hτ, he'⟩
  choose φ₁ hφ₁σ hφ₁ using hex
  have hφ₁c : Continuous φ₁ := by
    rw [he.isInducing.continuous_iff]
    exact hq'c.congr fun t => (hφ₁ t).symm
  set φ₀ : ℝ≥0 → ℝ≥0 := fun t => φ₁ t - σ with hφ₀def
  have hφ₀c : Continuous φ₀ := hφ₁c.sub continuous_const
  have hval : ∀ t, β (σ + φ₀ t) = q' t := fun t => by
    rw [hφ₀def]; dsimp only; rw [add_tsub_cancel_of_le (hφ₁σ t)]; exact hφ₁ t
  have hφ₀0 : φ₀ 0 = 0 := by
    have h1 : β (φ₁ 0) = β σ := by rw [hφ₁ 0, ← hq0]; simp [hq'def]
    rw [hφ₀def]; dsimp only; rw [hinj h1, tsub_self]
  have hφ₀i : InjOn φ₀ (Iio L) := fun a ha b hb hab => by
    have h1 : q' a = q' b := by rw [← hval a, ← hval b, hab]
    have ha' : min a L = a := min_eq_left (le_of_lt ha)
    have hb' : min b L = b := min_eq_left (le_of_lt hb)
    simp only [hq'def, ha', hb'] at h1
    exact hqi ha hb h1
  refine ⟨φ₀, hφ₀c, hφ₀0, strictMonoOn_Iio_of_injOn hφ₀c hφ₀0 hφ₀i, fun t ht => ?_⟩
  rw [hval t]; simp [hq'def, min_eq_left ht]

/-! ### The canonical curve only reads the piece up to its lifetime -/

theorem canonGood_congr {X : Set ℂ} {q q' : ℝ≥0 → ℂ} {L : ℝ≥0∞} (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → q t = q' t) :
    canonGood X q L = canonGood X q' L := by
  ext t
  exact ⟨fun ht => ⟨ht.1, h t ht.1 ▸ ht.2⟩, fun ht => ⟨ht.1, (h t ht.1).symm ▸ ht.2⟩⟩

theorem canonCurve_congr {X : Set ℂ} {x₀ : ℝ} {q q' : ℝ≥0 → ℂ} {L : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → q t = q' t) : canonCurve X x₀ q L = canonCurve X x₀ q' L := by
  classical
  have hG := canonGood_congr (X := X) h
  have hv : ∀ t, canonVal X x₀ q L t = canonVal X x₀ q' L t := by
    intro t
    unfold canonVal
    rw [hG]
    split_ifs with hg
    · rw [h t hg.1]
    · have hm : Filter.map (fun t' => (Mo.hullChart (fillH X) x₀).1 (q t')) (𝓝[canonGood X q' L] t) =
          Filter.map (fun t' => (Mo.hullChart (fillH X) x₀).1 (q' t')) (𝓝[canonGood X q' L] t) :=
        Filter.map_congr (by
          filter_upwards [self_mem_nhdsWithin] with t' ht'
          rw [h t' ht'.1])
      simp only [limUnder, hm]
  funext u
  exact hv _

/-! ### A path for the upper prefix followed by an initial arc of the walk -/

/-- The initial arc `β([0, σ])` as a path on `[0, 1]`. -/
def arcPath (β : ℝ≥0 → ℂ) (σ : ℝ≥0) (s : ℝ) : ℂ := β ((σ : ℝ) * s).toNNReal

theorem continuousOn_arcPath {β : ℝ≥0 → ℂ} (hβ : Continuous β) (σ : ℝ≥0) :
    ContinuousOn (arcPath β σ) (Icc 0 1) :=
  (hβ.comp (continuous_real_toNNReal.comp (continuous_const.mul continuous_id))).continuousOn

theorem image_arcPath (β : ℝ≥0 → ℂ) (σ : ℝ≥0) : arcPath β σ '' Icc 0 1 = β '' Icc 0 σ := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨((σ : ℝ) * s).toNNReal, ⟨bot_le, ?_⟩, rfl⟩
    rw [Real.toNNReal_le_iff_le_coe]
    exact mul_le_of_le_one_right σ.2 hs.2
  · rintro ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ σ) with h0 | hpos
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have : t = 0 := le_antisymm (by rw [h0]; exact ht.2) bot_le
      simp [arcPath, this]
    · refine ⟨(t : ℝ) / σ, ⟨div_nonneg t.2 σ.2, (div_le_one (by exact_mod_cast hpos)).2 (by exact_mod_cast ht.2)⟩, ?_⟩
      simp only [arcPath]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hpos.ne'), Real.toNNReal_coe]

theorem arcPath_zero (β : ℝ≥0 → ℂ) (σ : ℝ≥0) : arcPath β σ 0 = β 0 := by simp [arcPath]

theorem arcPath_one (β : ℝ≥0 → ℂ) (σ : ℝ≥0) : arcPath β σ 1 = β σ := by simp [arcPath]

/-- The reverse of a path on `[0, 1]`. -/
def revPath (p : ℝ → ℂ) (s : ℝ) : ℂ := p (1 - s)

theorem image_revPath (p : ℝ → ℂ) : revPath p '' Icc 0 1 = p '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp [revPath]⟩

/-- **The path of the upper prefix followed by an initial arc of the walk**: `p`, back along `p`, then `β([0, σ])`. -/
def stagePath (p : ℝ → ℂ) (β : ℝ≥0 → ℂ) (σ : ℝ≥0) : ℝ → ℂ :=
  Lw.concatPath (Lw.concatPath p (revPath p)) (arcPath β σ)

theorem stagePath_facts {p : ℝ → ℂ} (hpc : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0) (σ : ℝ≥0) :
    ∃ p' : ℝ → ℂ, ContinuousOn p' (Icc 0 1) ∧ p' 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im) ∧
      (∀ z, (p' ⁻¹' {z} ∩ Icc 0 1).Finite) ∧ p' '' Icc 0 1 = p '' Icc 0 1 ∪ β '' Icc 0 σ := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ σ) with h0 | hpos
  · refine ⟨p, hpc, hp0, hpH, hpf, ?_⟩
    rw [← h0, Icc_self, image_singleton, hβ0, eq_comm, union_eq_left, singleton_subset_iff]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hj1 : p 1 = revPath p 0 := by simp [revPath]
  have hj2 : Lw.concatPath p (revPath p) 1 = arcPath β σ 0 := by
    rw [Lw.concatPath_one, arcPath_zero, hβ0]; simp [revPath, hp0]
  have hrc : ContinuousOn (revPath p) (Icc 0 1) :=
    hpc.comp (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1c := Lw.continuousOn_concatPath hpc hrc hj1
  have hac := continuousOn_arcPath hβ.1 σ
  have himg1 : Lw.concatPath p (revPath p) '' Icc 0 1 = p '' Icc 0 1 := by
    rw [Lw.image_concatPath hj1, image_revPath, union_self]
  have himg : stagePath p β σ '' Icc 0 1 = p '' Icc 0 1 ∪ β '' Icc 0 σ := by
    rw [stagePath, Lw.image_concatPath hj2, himg1, image_arcPath]
  refine ⟨stagePath p β σ, Lw.continuousOn_concatPath h1c hac hj2,
    by simp [stagePath, Lw.concatPath_zero, hp0], ?_, ?_, himg⟩
  · intro s hs
    have hz : stagePath p β σ s ∈ p '' Icc 0 1 ∪ β '' Icc 0 σ := himg ▸ ⟨s, hs, rfl⟩
    rcases hz with ⟨r, hr, he⟩ | ⟨t, _, he⟩
    · rw [← he]; exact hpH r hr
    · rw [← he]; exact hβ.2.2.1 t
  · have hrf : ∀ z, (revPath p ⁻¹' {z} ∩ Icc 0 1).Finite := fun z => by
      refine ((hpf z).image fun r => 1 - r).subset ?_
      rintro s ⟨hsz, hs⟩
      exact ⟨1 - s, ⟨hsz, ⟨by linarith [hs.2], by linarith [hs.1]⟩⟩, by ring⟩
    have haf : ∀ z, (arcPath β σ ⁻¹' {z} ∩ Icc 0 1).Finite := by
      intro z
      refine Lw.finite_fibre_of_injOn (fun a ha b hb hab => ?_) z
      have := hβ.2.1 hab
      have h2 := (Real.toNNReal_eq_toNNReal_iff (mul_nonneg σ.2 ha.1) (mul_nonneg σ.2 hb.1)).1 this
      exact mul_left_cancel₀ (show (σ : ℝ) ≠ 0 from NNReal.coe_ne_zero.2 hpos.ne') h2
    exact Lw.finite_fibre_concatPath hj2 (Lw.finite_fibre_concatPath hj1 hpf hrf) haf

/-! ### The canonical package from a pinch-invariant path image -/

/-- **`exists_canon_package` with the finite fibres from `PInv`** (the image may be the single point `{0}`): for a
path `p` from `0` in `ℍ̄` whose image `X` is a point or the image of a finite-fibre path from `0` (`LuM.PInv 0 X`). -/
theorem exists_canon_package_pinv {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hpv : LuM.PInv 0 (p '' Icc 0 1)) :
    ∃ (e : ℝ) (g : ℂ → ℂ),
      IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
        ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter e) ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (Mo.hullChart (fillH (p '' Icc 0 1)) 0).2.1 H ∧
      (∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH (p '' Icc 0 1)) 0).2.1 (𝓝[H] q) (𝓝 (g q))) ∧
      (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧
      MapsTo g (Hbar \ H) (frontier (H \ fillH (p '' Icc 0 1))) := by
  set X := p '' Icc 0 1 with hXdef
  have hXc : IsCompact X := isCompact_Icc.image_of_continuousOn hp
  have hXH : X ⊆ Hbar := by
    rintro _ ⟨s, hs, rfl⟩
    exact hpH s hs
  have hA := isHPHull_fillH_path hp hp0
  set c := Mo.hullChart (fillH X) 0 with hcdef
  have hD : IsDomainChart (H \ fillH X) c := Mo.isDomainChart_hullChart hA 0
  have hcc : c.IsConformal := Mo.isConformal_hullChart hA 0
  have hbij : IsConformalBijection c.2.1 H (H \ fillH X) := by
    have h := hcc.isConformalBijection
    rw [Mo.coe_dom_hullChart hA 0] at h
    exact h
  obtain ⟨B, hB⟩ := Mo.hullChart_inv_bounded hA 0
  have hInf : Tendsto c.2.1 (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-B)
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self H)] with z hz
    have h1 := hB z hz
    have h2 := norm_le_norm_add_norm_sub' z (c.2.1 z)
    rw [norm_sub_rev] at h2
    linarith
  obtain ⟨g, hgi, hgc, hgfr, -⟩ := exists_continuousOn_extension_of_ulc_fillH hXc hXH (ulc_image_Icc hp)
    (isPreconnected_real_union_path hp hp0) hbij hInf
  have hgt : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (g q)) := fun q hq =>
    (((hgc q hq).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hz => hgi hz)
  have hgB : ∀ w : ℂ, 0 ≤ w.im → ‖g w - w‖ ≤ B := fun w hw => by
    have hwH : w ∈ Hbar := hw
    have := GW1P.neBot_nhdsWithin_H hwH
    exact le_of_tendsto (((hgt w hwH).sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm)
      (eventually_nhdsWithin_of_forall fun z hz => hB z hz)
  have hgb : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂ := by
    refine ⟨1, B, zero_le_one, fun w hw => ?_⟩
    have h1 := hgB w hw
    have h2 := norm_le_norm_add_norm_sub' w (g w)
    rw [norm_sub_rev] at h2
    linarith
  have hpv' : LuM.PInv 0 (X ∪ ((↑) : ℝ → ℂ) '' (∅ : Set ℝ)) := by
    rw [image_empty, union_empty]; exact hpv
  have hgf := Lk.finite_fibre_of_pinv hpv' hD hgc hgi hgb
  have hmo : IsMapOut (fillH X) (fun z => c.1 z + ((0 : ℝ) : ℂ)) :=
    Mt.isMapOut_congr (ConformalImage.isMapOut_mapOut hA) fun z _ => by simp [hcdef]
  let M : WalkIntCanon.HullModel c := ⟨fillH X, 0, hA, Mo.coe_dom_hullChart hA 0, hmo⟩
  have hfree : ∀ x : ℝ, realMax X < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull := fun x hx =>
    Lx.exists_ball_disjoint_fillH_right hXc fun y hy => lt_of_le_of_lt (Lx.le_realMax_of_mem hXc hy) hx
  obtain ⟨e, he⟩ := Lx.exists_isRightEntryValue_of_hullModel hcc M hgc hgi hfree
  have hcob : Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH X)) (Bornology.cobounded ℂ) := by
    obtain ⟨B', hB'⟩ := (ConformalImage.isMapOut_mapOut hA).exists_norm_sub_le hA
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-B')
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self (H \ fillH X))] with z hz
    have h1 : ‖ConformalImage.mapOut (fillH X) z - z‖ ≤ B' := hB' z hz
    have h3 : c.1 z = ConformalImage.mapOut (fillH X) z := by simp [hcdef]
    have h2 := norm_le_norm_add_norm_sub' z (ConformalImage.mapOut (fillH X) z)
    rw [norm_sub_rev] at h2
    rw [h3]
    linarith
  have hlift : ∀ x > realMax X, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    exact (Restart.isCanonicalDerivLog_canonDerivLog hA).tendsto_im_nhdsWithin_zero hA
      (ConformalImage.isMapOut_mapOut hA) hρ hd
  exact ⟨e, g, Lf.isRightEntryChart_recenter hD he hcob hlift, hgc, hgi, hgt, hgf, hgfr⟩

/-- The stage path without finite fibres, with `PInv` of its image. -/
theorem stagePath_pinv {p : ℝ → ℂ} (hpc : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hpv : LuM.PInv 0 (p '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0) (σ : ℝ≥0) :
    ∃ p' : ℝ → ℂ, ContinuousOn p' (Icc 0 1) ∧ p' 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im) ∧
      LuM.PInv 0 (p' '' Icc 0 1) ∧ p' '' Icc 0 1 = p '' Icc 0 1 ∪ β '' Icc 0 σ := by
  have hj1 : p 1 = revPath p 0 := by simp [revPath]
  have hj2 : Lw.concatPath p (revPath p) 1 = arcPath β σ 0 := by
    rw [Lw.concatPath_one, arcPath_zero, hβ0]; simp [revPath, hp0]
  have hrc : ContinuousOn (revPath p) (Icc 0 1) :=
    hpc.comp (continuous_const.sub continuous_id).continuousOn fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1c := Lw.continuousOn_concatPath hpc hrc hj1
  have hac := continuousOn_arcPath hβ.1 σ
  have himg1 : Lw.concatPath p (revPath p) '' Icc 0 1 = p '' Icc 0 1 := by
    rw [Lw.image_concatPath hj1, image_revPath, union_self]
  have himg : stagePath p β σ '' Icc 0 1 = p '' Icc 0 1 ∪ β '' Icc 0 σ := by
    rw [stagePath, Lw.image_concatPath hj2, himg1, image_arcPath]
  have h0A : (0 : ℂ) ∈ p '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hpinv : LuM.PInv 0 (p '' Icc 0 1 ∪ β '' Icc 0 σ) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ σ) with h0 | hpos
    · refine hpv.union_of_subset ?_
      rw [← h0, Icc_self, image_singleton, hβ0, singleton_subset_iff]
      exact h0A
    · have hff : LuM.IsFFPath (arcPath β σ) := by
        refine ⟨hac, fun z => Lw.finite_fibre_of_injOn (fun a ha b hb hab => ?_) z, fun s _ => hβ.2.2.1 _⟩
        have := hβ.2.1 hab
        have h2 := (Real.toNNReal_eq_toNNReal_iff (mul_nonneg σ.2 ha.1) (mul_nonneg σ.2 hb.1)).1 this
        exact mul_left_cancel₀ (show (σ : ℝ) ≠ 0 from NNReal.coe_ne_zero.2 hpos.ne') h2
      have := hpv.join hff (by rw [arcPath_zero, hβ0]; exact h0A)
      rwa [image_arcPath] at this
  refine ⟨stagePath p β σ, Lw.continuousOn_concatPath h1c hac hj2,
    by simp [stagePath, Lw.concatPath_zero, hp0], ?_, himg ▸ hpinv, himg⟩
  intro s hs
  have hz : stagePath p β σ s ∈ p '' Icc 0 1 ∪ β '' Icc 0 σ := himg ▸ ⟨s, hs, rfl⟩
  rcases hz with ⟨r, hr, he⟩ | ⟨t, _, he⟩
  · rw [← he]; exact hpH r hr
  · rw [← he]; exact hβ.2.2.1 t

/-! ### The stage theorem for a finite piece -/

theorem realMax_eq_of_le {X : Set ℂ} (hX : IsCompact X) {x : ℝ} (hx : (x : ℂ) ∈ X)
    (hle : ∀ y : ℝ, (y : ℂ) ∈ X → y ≤ x) : realMax X = x :=
  le_antisymm (csSup_le ⟨x, hx⟩ hle) (Lx.le_realMax_of_mem hX hx)

theorem range_subset_closedLeftSide (β : ℝ≥0 → ℂ) : range β ⊆ InteractingSLE.closedLeftSide β :=
  fun _ hz => Or.inr (Or.inl hz)

/-- **The tail beyond the cut stays off the fill of the retained union** (item 5): with a lift `γ` of the tail of
`β` after `σ` through the hull chart of `X = A ∪ β([0, σ])`, every tail point `β (σ + s)`, `s > 0`, in `ℍ ∖ fill A` is
in `ℍ ∖ fill X`. -/
theorem mem_diff_fill_union {A : Set ℂ} (hAc : IsCompact A) {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β)
    {σ : ℝ≥0} (hX : IsHPHull (fillH (A ∪ β '' Icc 0 σ))) {R e : ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : Lk.IsTailLiftCurve (Mo.hullChart (fillH (A ∪ β '' Icc 0 σ)) 0) R (-e) β σ γ) {g : ℂ → ℂ}
    (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH (A ∪ β '' Icc 0 σ)) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH (A ∪ β '' Icc 0 σ)) 0).2.1 H)
    (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH (A ∪ β '' Icc 0 σ))))
    {s : ℝ≥0} (hs : 0 < s) (hz : β (σ + s) ∈ H \ fillH A) : β (σ + s) ∈ H \ fillH (A ∪ β '' Icc 0 σ) := by
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  have hD : IsDomainChart (H \ fillH X) (Mo.hullChart (fillH X) 0) := Mo.isDomainChart_hullChart hX 0
  set w : ℂ := γ s - ((-e : ℝ) : ℂ) with hwdef
  have hwH : w ∈ Hbar := by
    show 0 ≤ w.im
    simpa [hwdef] using hγ.2.1.2.2.1 s
  have := GW1P.neBot_nhdsWithin_H hwH
  have hgw : g w = β (σ + s) := tendsto_nhds_unique (hgt w hwH) (hγ.2.2.2 s)
  have hcl : β (σ + s) ∈ closure (H \ fillH X) := by
    rw [← hgw]
    by_cases hw : w ∈ H
    · rw [hgi hw]
      exact subset_closure (hD.image_eq ▸ mem_image_of_mem _ hw)
    · exact frontier_subset_closure (hgfr ⟨hwH, hw⟩)
  refine ⟨hz.1, fun hfill => ?_⟩
  have hfr : β (σ + s) ∈ frontier (H \ fillH X) := by
    rw [(show IsOpen (H \ fillH X) from hX.2.2.1).frontier_eq]
    exact ⟨hcl, fun h => h.2 hfill⟩
  rcases frontier_H_diff_fillH_subset hXc.isBounded hfr with hre | hXm
  · exact (ne_of_gt (show 0 < (β (σ + s)).im from hz.1)) hre
  rw [hXc.isClosed.closure_eq] at hXm
  rcases hXm with hA | ⟨τ, hτ, he⟩
  · exact hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure hA))
  · have := hβ.2.1 he
    have hle : σ + s ≤ σ := this ▸ hτ.2
    exact absurd hle (not_le.2 (lt_add_of_pos_right σ hs))

/-- A continuous `φ₀`, strictly increasing on `[0, L)`, stays below `φ₀ L` there. -/
theorem lt_of_strictMonoOn_Iio {φ₀ : ℝ≥0 → ℝ≥0} (hc : Continuous φ₀) {L : ℝ≥0} (hm : StrictMonoOn φ₀ (Iio L))
    {t : ℝ≥0} (ht : t < L) : φ₀ t < φ₀ L := by
  obtain ⟨t', htt', ht'L⟩ := exists_between ht
  refine lt_of_lt_of_le (hm ht ht'L htt') ?_
  have hsub : closure (Ioo t' L) ⊆ {s | φ₀ t' ≤ φ₀ s} :=
    (isClosed_le continuous_const hc).closure_subset_iff.2 fun s hs => (hm ht'L hs.2 hs.1).le
  exact hsub (by rw [closure_Ioo ht'L.ne]; exact ⟨ht'L.le, le_rfl⟩)

/-- **F2a at a finite stage, deterministic**: the upper prefix `A = p_A([0, 1])` (from `0`, finite fibres) on the
closed left of a proper curve `β` from `0`; a cut `σ` with `β σ = x` the largest real point of `A ∪ β([0, σ])`; a
finite piece `q` (continuous on `[0, L]`, injective on `[0, L)`, from `β σ`, on `β([σ, ∞))`) whose times in
`ℍ ∖ fill A` are dense in `[0, L)`. Then the canonical stage curve of `q` for `A ∪ β([0, σ])` is driven. -/
theorem isDrivenCurve_stage_fin {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β) {σ : ℝ≥0} {x : ℝ} (hx : β σ = x)
    (hle : ∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ β '' Icc 0 σ → y ≤ x)
    {q : ℝ≥0 → ℂ} {L : ℝ≥0} (hL : 0 < L) (hqc : ContinuousOn q (Icc 0 L)) (hqi : InjOn q (Iio L))
    (hq0 : q 0 = β σ) (hqβ : ∀ t, t ≤ L → q t ∈ β '' Ici σ)
    (hden : ∀ t : ℝ≥0, t < L →
      t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ q t' ∈ H \ fillH (pA '' Icc 0 1)}) :
    ∃ x₀ : ℝ, IsDrivenCurve (canonCurve (pA '' Icc 0 1 ∪ β '' Icc 0 σ) x₀ q L) := by
  set A := pA '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := stagePath_pinv hpc hp0 hpH hpv hβ hβ0 σ
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hxX : (x : ℂ) ∈ X := Or.inr ⟨σ, ⟨bot_le, le_rfl⟩, hx⟩
  have hRx : realMax X = x := realMax_eq_of_le hXc hxX hle
  have htL : tL = σ := hβ.2.1 (by rw [hγ.1, hRx, hx])
  rw [htL] at hγ
  obtain ⟨φ₀, hφc, hφ0, hφm, hqφ⟩ := exists_timeChange_fin hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (σ + φ₀ t) with hq'def
  have hcongr : canonCurve X e q L = canonCurve X e q' L :=
    canonCurve_congr fun t ht => hqφ t (by exact_mod_cast ht)
  have hφS : ∀ t : ℝ≥0, t < L → φ₀ t < φ₀ L := fun t ht => lt_of_strictMonoOn_Iio hφc hφm ht
  have hS : 0 < φ₀ L := by rw [← hφ0]; exact hφS 0 hL
  have hpos : ∀ t : ℝ≥0, 0 < t → t ≤ L → 0 < φ₀ t := fun t ht htL' => by
    rcases htL'.lt_or_eq with h | h
    · rw [← hφ0]; exact hφm hL h ht
    · rw [h]; exact hS
  -- the good times for the canonical chart contain the good times for `A`
  have hgood : {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} ⊆ canonGood X q' (L : ℝ≥0∞) := by
    rintro t' ⟨ht'L, ht'⟩
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      rw [← h, hq0, hx] at ht'
      have him : (0 : ℝ) < ((x : ℝ) : ℂ).im := ht'.1
      simp at him
    have ht'L' : t' ≤ L := by exact_mod_cast ht'L
    refine ⟨ht'L, ?_⟩
    have hq := hqφ t' ht'L'
    rw [hq] at ht'
    exact mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (hpos t' ht'0 ht'L') ht'
  have hdq : ∀ t : ℝ≥0, t < L → t ∈ closure (canonGood X q' (L : ℝ≥0∞)) := fun t ht =>
    closure_mono hgood (hden t ht)
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hmaps : MapsTo φ₀ (canonGood X q' (L : ℝ≥0∞)) {s' : ℝ≥0 | γ s' ∈ H} := fun t' ht' =>
    (canon_eq_of_lift_good (ζ := γ ∘ φ₀) hA (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr ht'.2).2
  have hdγ : ∀ s : ℝ≥0, (s : ℝ) < (φ₀ L : ℝ) → s ∈ closure {s' : ℝ≥0 | γ s' ∈ H} := by
    intro s hs
    have hs' : s < φ₀ L := by exact_mod_cast hs
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ L) hφc.continuousOn
      (show s ∈ Icc (φ₀ 0) (φ₀ L) from ⟨by rw [hφ0]; exact bot_le, hs'.le⟩)
    have htL' : t < L := lt_of_le_of_ne ht.2 fun h => (ne_of_lt hs') (by rw [← hts, h])
    rw [← hts]
    exact map_mem_closure hφc (hdq t htL') hmaps
  refine ⟨e, ?_⟩
  rw [hcongr]
  exact isDrivenCurve_canonCurve_of_timeChange hA hgt hgi hgfr hγ.2.1 hγ.2.2.1 hS hL hφc hφm hφ0 hφS hdγ hζl hdq

/-! ### The infinite last piece -/

/-- **The time change of an infinite piece along a proper curve**: a continuous injective piece from `β σ` onto the
tail `β([σ, ∞))` is `β (σ + φ₀ ·)` for a continuous strictly increasing surjection `φ₀` from `0`. -/
theorem exists_timeChange_top {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) {q : ℝ≥0 → ℂ} {σ : ℝ≥0}
    (hqc : Continuous q) (hqi : Function.Injective q) (hq0 : q 0 = β σ)
    (hqβ : range q = β '' Ici σ) :
    ∃ φ₀ : ℝ≥0 → ℝ≥0, Continuous φ₀ ∧ φ₀ 0 = 0 ∧ StrictMono φ₀ ∧ Function.Surjective φ₀ ∧
      ∀ t, q t = β (σ + φ₀ t) := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hβ
  have hinj : Function.Injective β := hβ.2.1
  have hex : ∀ t, ∃ τ, σ ≤ τ ∧ β τ = q t := fun t => by
    obtain ⟨τ, hτ, he'⟩ := hqβ ▸ (mem_range_self t : q t ∈ range q)
    exact ⟨τ, hτ, he'⟩
  choose φ₁ hφ₁σ hφ₁ using hex
  have hφ₁c : Continuous φ₁ := by
    rw [he.isInducing.continuous_iff]
    exact hqc.congr fun t => (hφ₁ t).symm
  set φ₀ : ℝ≥0 → ℝ≥0 := fun t => φ₁ t - σ with hφ₀def
  have hφ₀c : Continuous φ₀ := hφ₁c.sub continuous_const
  have hval : ∀ t, β (σ + φ₀ t) = q t := fun t => by
    rw [hφ₀def]; dsimp only; rw [add_tsub_cancel_of_le (hφ₁σ t)]; exact hφ₁ t
  have hφ₀0 : φ₀ 0 = 0 := by
    have h1 : β (φ₁ 0) = β σ := by rw [hφ₁ 0, hq0]
    rw [hφ₀def]; dsimp only; rw [hinj h1, tsub_self]
  have hφ₀i : Function.Injective φ₀ := fun a b hab => hqi (by rw [← hval a, ← hval b, hab])
  have hmono : StrictMono φ₀ := fun a b hab =>
    strictMonoOn_Iio_of_injOn hφ₀c hφ₀0 (L := b + 1) (hφ₀i.injOn) (lt_of_lt_of_le hab (le_add_right le_rfl))
      (lt_add_one b) hab
  have hsurj : Function.Surjective φ₀ := fun s => by
    obtain ⟨t, ht⟩ : β (σ + s) ∈ range q := hqβ ▸ ⟨σ + s, show σ ≤ σ + s from le_add_right le_rfl, rfl⟩
    refine ⟨t, ?_⟩
    have := hinj (show β (σ + φ₀ t) = β (σ + s) by rw [hval t, ht])
    exact add_left_cancel this
  exact ⟨φ₀, hφ₀c, hφ₀0, hmono, hsurj, fun t => (hval t).symm⟩

/-- **F2a at an infinite last stage, deterministic**: as `isDrivenCurve_stage_fin` with an infinite piece `q`
(continuous and injective on `[0, ∞)`, from `β σ`, onto `β([σ, ∞))`) whose times in `ℍ ∖ fill A` are dense. -/
theorem isDrivenCurve_stage_top {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β) {σ : ℝ≥0} {x : ℝ} (hx : β σ = x)
    (hle : ∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ β '' Icc 0 σ → y ≤ x)
    {q : ℝ≥0 → ℂ} (hqc : Continuous q) (hqi : Function.Injective q) (hq0 : q 0 = β σ)
    (hqβ : range q = β '' Ici σ)
    (hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | q t' ∈ H \ fillH (pA '' Icc 0 1)}) :
    ∃ x₀ : ℝ, IsDrivenCurve (canonCurve (pA '' Icc 0 1 ∪ β '' Icc 0 σ) x₀ q ⊤) := by
  set A := pA '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := stagePath_pinv hpc hp0 hpH hpv hβ hβ0 σ
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hxX : (x : ℂ) ∈ X := Or.inr ⟨σ, ⟨bot_le, le_rfl⟩, hx⟩
  have hRx : realMax X = x := realMax_eq_of_le hXc hxX hle
  have htL : tL = σ := hβ.2.1 (by rw [hγ.1, hRx, hx])
  rw [htL] at hγ
  obtain ⟨φ₀, hφc, hφ0, hφm, hφs, hqφ⟩ := exists_timeChange_top hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (σ + φ₀ t) with hq'def
  have hcongr : canonCurve X e q ⊤ = canonCurve X e q' ⊤ := canonCurve_congr fun t _ => hqφ t
  have hgood : {t' : ℝ≥0 | q t' ∈ H \ fillH A} ⊆ canonGood X q' ⊤ := by
    rintro t' ht'
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      have ht0 : q 0 ∈ H \ fillH A := h ▸ ht'
      rw [hq0, hx] at ht0
      have him : (0 : ℝ) < ((x : ℝ) : ℂ).im := ht0.1
      simp at him
    refine ⟨le_top, ?_⟩
    have ht'' : q t' ∈ H \ fillH A := ht'
    rw [hqφ t'] at ht''
    exact mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (by rw [← hφ0]; exact hφm ht'0) ht''
  have hdq : ∀ t : ℝ≥0, t ∈ closure (canonGood X q' ⊤) := fun t => closure_mono hgood (hden t)
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hmaps : MapsTo φ₀ (canonGood X q' ⊤) {s' : ℝ≥0 | γ s' ∈ H} := fun t' ht' =>
    (canon_eq_of_lift_good (ζ := γ ∘ φ₀) hA (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr ht'.2).2
  have hdγ : ∀ s : ℝ≥0, s ∈ closure {s' : ℝ≥0 | γ s' ∈ H} := fun s => by
    obtain ⟨t, rfl⟩ := hφs s
    exact map_mem_closure hφc (hdq t) hmaps
  -- the lift is driven
  set γ' : ℝ → ℂ := fun r => γ r.toNNReal with hγ'def
  have hc' : ContinuousOn γ' (Ici 0) := (hγ.2.1.1.comp continuous_real_toNNReal).continuousOn
  have hinj' : InjOn γ' (Ici 0) := fun a ha b hb hab => by
    have := hγ.2.1.2.1 hab
    rw [← Real.coe_toNNReal a ha, ← Real.coe_toNNReal b hb, this]
  have hH' : MapsTo γ' (Ici 0) Hbar := fun r _ => hγ.2.1.2.2.1 r.toNNReal
  have h0' : γ' 0 = 0 := by simp [hγ'def, hγ.2.2.1]
  have hinf' : Tendsto (fun r => ‖γ' r‖) atTop atTop := hγ.2.1.2.2.2.comp tendsto_real_toNNReal_atTop
  have hR : ∀ S : ℝ, interior {r ∈ Ioo (0 : ℝ) S | (γ' r).im = 0} = ∅ := fun S =>
    interior_real_eq_empty_of_dense fun s _ => hdγ s
  have hdr : IsDrivenCurve γ' :=
    ⟨hc', h0', fun S hS => FinRel.exists_localDriver_of_lt hc' hinj' hH' h0' hinf' (hR S) hS le_rfl⟩
  -- the time change on `[0, ∞)`
  set Φ : ℝ → ℝ := fun u => (φ₀ u.toNNReal : ℝ) with hΦdef
  have hΦc : Continuous Φ := NNReal.continuous_coe.comp (hφc.comp continuous_real_toNNReal)
  have hΦm : StrictMonoOn Φ (Ici 0) := fun a ha b hb hab => by
    show (φ₀ a.toNNReal : ℝ) < φ₀ b.toNNReal
    exact_mod_cast hφm ((Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt ha hab)).2 hab)
  have hΦ0 : Φ 0 = 0 := by simp [hΦdef, hφ0]
  have hΦs : ∀ t, 0 ≤ t → Φ '' Icc 0 t = Icc 0 (Φ t) := by
    intro t ht
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨?_, hΦm.monotoneOn hr.1 ht hr.2⟩
      rw [← hΦ0]; exact hΦm.monotoneOn (le_refl (0 : ℝ)) hr.1 hr.1
    · have := intermediate_value_Icc ht hΦc.continuousOn
      rwa [hΦ0] at this
  have hcomp := isDrivenCurve_comp hdr hΦc.continuousOn hΦm hΦ0 hΦs
  refine ⟨e, ?_⟩
  rw [hcongr]
  refine Vk.IsDrivenCurve.congr hcomp fun u hu => ?_
  show γ' (Φ u) = canonVal X e q' ⊤ (if (⊤ : ℝ≥0∞) = ⊤ then u else clockOf (⊤ : ℝ≥0∞).toReal u).toNNReal
  simp only [↓reduceIte]
  rw [canonVal_eq_of_lift (ζ := γ ∘ φ₀) hA (hγ.2.1.1.comp hφc) (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr
    (hdq _)]
  simp [hγ'def, hΦdef]

end InteractingSLE.Theorem14.SB.Dv






