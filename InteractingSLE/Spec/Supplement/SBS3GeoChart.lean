/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3GeoAccess
import InteractingSLE.Spec.Supplement.SB4RFrame
import InteractingSLE.Spec.Supplement.SB2LkS2

/-!
# Lemma S3's geometry for an arbitrary second chart, and its reflection (the lower pieces of SB2(2))

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580, and its use with the roles of the two
histories exchanged, supplement p. 631: "On every ordinary piece the strict angle comparison excludes a common open
arc with the other history, by the two exposed-height identities in S3"). Deterministic.

* **`exists_s3_geometry_of_chart`**: the assembled S3 geometry on S2's lift where the second history is the witness
  prefix `β'([0, q])` itself and its chart is **any** core chart (`IsChartCore`: holomorphic, finite fibres) of its
  filling — not necessarily a Loewner chart. This is the form needed when the second history is a walk prefix whose
  chart is a composed stage chart;
* the reflection `ρ(z) = −z̄`: `mem_refl_image`, `dist_refl`, `refl_image_fillH`, `refl_image_diff_inter_ball`,
  `map_refl_nhdsWithin_le`, `nhdsWithin_H_refl`, `refl_image_freeNear_subset`, **`IsChartCore.reflect`**;
* **`exists_s3_geometry_of_chart_right`**: the mirror image — the old history on the closed **left** of the
  proper witness, a **right** entry chart at `R = max (A ∩ ℝ)` (S2 reflected, as `Lk.s2LiftRight`): the approach is on
  the witness's **right**, in the joint domain, with both component accesses, and every core chart of the witness
  prefix tends along it to a **positive** real (the exposed right side `λ − ψχ`), with its transition gap.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.S3.Geo

open Supp9B (IsProperCurve leftSide rightSide closedRightSide refl reflectCurve refl_refl refl_im refl_re
  continuous_refl refl_injective reflectCurve_reflectCurve isProperCurve_reflectCurve)
open Sec7.ReverseArc

/-- **The S3 geometry on S2's lift for an arbitrary second chart.** As `exists_s3_geometry_of_s2`, but the second
history is the witness prefix `β'([0, q])`, `q = t_L + b`, with any core chart `(f, Φ)` of its filling (holomorphic,
finite fibres): the old-side facts and both accesses hold for every common arc, and for every such chart `f` tends
along the approach to a negative real `y` from `ℍ`, `Φ(y) = β'(t_L + t)`, and a ball about `y` misses
`f(fill(A ∪ β'[0, q]) ∖ fill(β'[0, q]))`. -/
theorem exists_s3_geometry_of_chart {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    {c : Chart} {g : ℂ → ℂ} (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      β' tL = realMin (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' (tL + s)) ∧
      ∀ a b t : ℝ≥0, t ∈ Ioo a b → β' '' Icc (tL + a) (tL + b) ⊆ p '' Icc 0 1 → β' (tL + b) ∈ H →
        0 < (γ t).re ∧ (𝓝[H] (γ t)).NeBot ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (leftSide β' ∩ (H \ fillH (p '' Icc 0 1 ∪ β' '' Icc 0 (tL + b)))) ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[H \ fillH (p '' Icc 0 1 ∪ β' '' Icc 0 (tL + b))] (β' (tL + t)) ∧
        (∀ S T : Set ℂ, β' '' Icc (tL + a) (tL + b) ⊆ S →
          S ⊆ fillH (p '' Icc 0 1 ∪ β' '' Icc 0 (tL + b)) → T ⊆ fillH (p '' Icc 0 1 ∪ β' '' Icc 0 (tL + b)) →
          ∃ r > 0, Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[FinRel.freeNear T S (β' (tL + t)) r] (β' (tL + t))) ∧
        ∀ {f Φ : ℂ → ℂ}, IsChartCore β' (tL + b) f Φ →
          DifferentiableOn ℂ f (H \ fillH (β' '' Icc 0 (tL + b))) →
          (∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) → IsOpen (H \ fillH (β' '' Icc 0 (tL + b))) →
          ∃ y : ℝ, y < 0 ∧ Φ y = β' (tL + t) ∧ Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝[H] (y : ℂ)) ∧
            ∃ r > 0, Disjoint (ball (y : ℂ) r)
              (f '' (fillH (p '' Icc 0 1 ∪ β' '' Icc 0 (tL + b)) \ fillH (β' '' Icc 0 (tL + b)))) := by
  obtain ⟨tL, γ, htL, hγp, hγ0, hlift, hcol⟩ :=
    exists_positive_left_joint_collar_of_s2 hp hp0 hpH hβ' hβ'0 hA hc hgc hgi hgf
  refine ⟨tL, γ, htL, hγp, hγ0, hlift, fun a b t ht harc hqH => ?_⟩
  set q : ℝ≥0 := tL + b with hqdef
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hab : a < b := ht.1.trans ht.2
  have hηc : IsCompact (β' '' Icc 0 q) := isCompact_Icc.image_of_continuousOn hβ'.1.continuousOn
  have hinjq : InjOn β' (Icc 0 q) := hβ'.2.1.injOn
  have hD := hc.1
  have hgd : DifferentiableOn ℂ g H := hD.isConformal.1.congr fun u hu => hgi hu
  have hgI : InjOn g H := (hgi.symm.injOn_iff.1 hD.isConformal.injOn)
  have hγc : Continuous γ := hγp.1
  have harc' : ∀ s ∈ Icc a b, g (γ s) ∈ A := fun s hs => by
    rw [hlift s]; exact harc ⟨tL + s, ⟨add_le_add le_rfl hs.1, add_le_add le_rfl hs.2⟩, rfl⟩
  have hreal : ∀ s ∈ Icc a b, (γ s).im = 0 := fun s hs =>
    im_eq_zero_of_landing_mem hD hgi (hγp.2.2.1 s) (harc' s hs)
  have hmono : StrictMonoOn (fun s => (γ s).re) (Ioo a b) :=
    strictMonoOn_re_of_lifted_common_arc hp hp0 hc hgc hgi hγp hγ0
      (by rintro _ ⟨s, hs, rfl⟩; exact harc' s ⟨hs.1.le, hs.2.le⟩)
  have hlift' : ∀ s ∈ Icc a b, g (γ s) = β' (tL + s) := fun s _ => hlift s
  have hfillsub : H \ fillH (A ∪ β' '' Icc 0 q) ⊆ H \ fillH (β' '' Icc 0 q) := fun z hz =>
    ⟨hz.1, fun hK' => hz.2 (fillH_mono subset_union_right hK')⟩
  have hcol' : ∀ s ∈ Ioo a b, ∃ ρ > 0, g '' (ball (γ s) ρ ∩ H) ⊆ H \ fillH (β' '' Icc 0 q) := by
    intro s hs
    obtain ⟨-, ρ, hρ, hρc, -, -, -⟩ := hcol a b s hs harc
    exact ⟨ρ, hρ, hρc.trans hfillsub⟩
  obtain ⟨hpos, ρ, hρ, hρc, hρL, hne, hgT⟩ := hcol a b t ht harc
  have hFL : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (leftSide β' ∩ (H \ fillH (A ∪ β' '' Icc 0 q))) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (γ t) hρ)] with u hu hub
    have hgu := hρc ⟨u, ⟨hub, hu⟩, rfl⟩
    refine ⟨?_, hgu⟩
    have h1 := image_leftSide_inter_H_subset hp hp0 hc hgc hgi hβ' htL hγp hγ0 hlift ⟨u, ⟨hρL ⟨hub, hu⟩, hu⟩, rfl⟩
    exact postCurve_leftSide_subset hβ' hβ'0 htL (realBase_facts hp hp0).2.2.2.1 h1
  have hFJ : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (H \ fillH (A ∪ β' '' Icc 0 q)) :=
    hFL.trans (principal_mono.2 inter_subset_right)
  have hFL' : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (leftSide β') := hFL.trans (principal_mono.2 inter_subset_left)
  have hgt : Tendsto g (𝓝[H] (γ t)) (𝓝 (β' (tL + t))) := hgT.mono_right nhdsWithin_le_nhds
  refine ⟨hpos, hne, hFL, le_inf hgt hFJ, fun S T hS hSJ hTJ => ?_, fun {f Φ} hch hfd hfin hDo => ?_⟩
  · exact exists_access_of_lifted_arc hD hgc hgi hβ'.2.1 hγc ht hreal hmono hlift
      (fun s hs => hS ⟨tL + s, ⟨add_le_add le_rfl hs.1, add_le_add le_rfl hs.2⟩, rfl⟩) hSJ hTJ hρ hρc
  · obtain ⟨y, hy0, hyT, hΦy⟩ := neg_tendsto_comp_of_lifted_arc hch hfd hfin hqH hinjq hDo hgc hgd hgI hγc hab
      rfl hreal hmono hlift' hcol' t ht
    have hFne : (Filter.map g (𝓝[H] (γ t))).NeBot := hne.map g
    have hfF : Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝 (y : ℂ)) := hyT
    have hfFH : Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝[H] (y : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hfF, ?_⟩
      filter_upwards [hFJ (mem_principal_self _)] with z hz
      exact hch.maps (hfillsub hz)
    obtain ⟨r, hr, hgap⟩ := exists_ball_disjoint_second_transition hch hηc hβ' (by rw [hβ'0]; simp)
      (fun s _ => rfl) hAc hA hFL' hFJ (show tL + t < q from add_lt_add_of_le_of_lt le_rfl ht.2) hfF hΦy
    exact ⟨y, hy0, hΦy, hfFH, r, hr, hgap⟩

/-! ### The reflection `z ↦ −z̄` -/

theorem mem_refl_image {S : Set ℂ} {z : ℂ} : z ∈ refl '' S ↔ refl z ∈ S :=
  ⟨fun ⟨w, hw, he⟩ => by rw [← he, refl_refl]; exact hw, fun hz => ⟨refl z, hz, refl_refl z⟩⟩

theorem refl_zero : refl 0 = 0 := by simp [Supp9B.refl]

theorem refl_sub (z w : ℂ) : refl (z - w) = refl z - refl w := by simp [Supp9B.refl]; ring

theorem dist_refl (z w : ℂ) : dist (refl z) (refl w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm, ← refl_sub, Lf.norm_refl]

theorem refl_mem_H_iff {z : ℂ} : refl z ∈ H ↔ z ∈ H := by
  show (0 : ℝ) < (refl z).im ↔ (0 : ℝ) < z.im
  rw [refl_im]

theorem refl_mem_Hbar_iff {z : ℂ} : refl z ∈ Hbar ↔ z ∈ Hbar := by
  show (0 : ℝ) ≤ (refl z).im ↔ (0 : ℝ) ≤ z.im
  rw [refl_im]

theorem refl_image_fillH (X : Set ℂ) : refl '' fillH X = fillH (refl '' X) := by
  have h1 := Lk.refl_image_H_diff_fillH X
  ext z
  rw [mem_refl_image]
  constructor
  · intro hz
    have hzH : z ∈ H := refl_mem_H_iff.1 (fillH_subset_H X hz)
    by_contra hn
    have h2 : z ∈ refl '' (H \ fillH X) := by rw [h1]; exact ⟨hzH, hn⟩
    exact (mem_refl_image.1 h2).2 hz
  · intro hz
    have hzH : z ∈ H := fillH_subset_H _ hz
    by_contra hn
    have h2 : refl (refl z) ∈ refl '' (H \ fillH X) := mem_image_of_mem _ ⟨refl_mem_H_iff.2 hzH, hn⟩
    rw [refl_refl, h1] at h2
    exact h2.2 hz

theorem refl_image_diff_inter_ball (S : Set ℂ) (p : ℂ) (r : ℝ) :
    refl '' ((H \ S) ∩ ball p r) = (H \ refl '' S) ∩ ball (refl p) r := by
  ext w
  rw [mem_refl_image]
  simp only [mem_inter_iff, Set.mem_sdiff, mem_ball, mem_refl_image, refl_mem_H_iff]
  rw [← dist_refl (refl w) p, refl_refl]

theorem map_refl_nhdsWithin_le (X : Set ℂ) (z : ℂ) : Filter.map refl (𝓝[X] z) ≤ 𝓝[refl '' X] (refl z) :=
  tendsto_nhdsWithin_iff.2 ⟨continuous_refl.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun _ hw => mem_image_of_mem _ hw⟩

theorem nhdsWithin_H_refl (z : ℂ) : 𝓝[H] (refl z) = Filter.map refl (𝓝[H] z) := by
  refine le_antisymm ?_ (by simpa only [Lf.refl_image_H] using map_refl_nhdsWithin_le H z)
  have h := map_refl_nhdsWithin_le H (refl z)
  rw [Lf.refl_image_H, refl_refl] at h
  calc 𝓝[H] (refl z) = Filter.map refl (Filter.map refl (𝓝[H] (refl z))) := by
        rw [Filter.map_map]
        have : refl ∘ refl = id := funext refl_refl
        rw [this, Filter.map_id]
    _ ≤ Filter.map refl (𝓝[H] z) := Filter.map_mono h

theorem refl_image_freeNear_subset (T S : Set ℂ) (p : ℂ) (r : ℝ) :
    refl '' FinRel.freeNear T S p r ⊆ FinRel.freeNear (refl '' T) (refl '' S) (refl p) r := by
  rintro _ ⟨z, ⟨hzD, hdisj⟩, rfl⟩
  have hzD' : refl z ∈ (H \ refl '' S) ∩ ball (refl p) r := by
    rw [← refl_image_diff_inter_ball]; exact mem_image_of_mem _ hzD
  refine ⟨hzD', ?_⟩
  have hset : refl '' ((H \ refl '' S) ∩ ball (refl p) r) = (H \ S) ∩ ball p r := by
    rw [refl_image_diff_inter_ball, Lf.refl_image_refl_image, refl_refl]
  have hcc := continuous_refl.continuousOn.image_connectedComponentIn_subset hzD'
  rw [hset, refl_refl] at hcc
  rw [Set.disjoint_left]
  intro w hw hwT
  exact Set.disjoint_left.1 hdisj (hcc (mem_image_of_mem _ hw)) (mem_refl_image.1 hwT)

/-- **A core chart reflected**: `(ρ ∘ f ∘ ρ, ρ ∘ Φ ∘ ρ)` is a core chart of the reflected filling. -/
theorem IsChartCore.reflect {η : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ} (h : IsChartCore η q f Φ) :
    IsChartCore (reflectCurve η) q (fun z => refl (f (refl z))) (fun w => refl (Φ (refl w))) := by
  have hK : reflectCurve η '' Icc 0 q = refl '' (η '' Icc 0 q) := (image_image refl η (Icc 0 q)).symm
  have hD : H \ fillH (reflectCurve η '' Icc 0 q) = refl '' (H \ fillH (η '' Icc 0 q)) := by
    rw [hK, Lk.refl_image_H_diff_fillH]
  have hmem : ∀ {z}, z ∈ H \ fillH (reflectCurve η '' Icc 0 q) → refl z ∈ H \ fillH (η '' Icc 0 q) :=
    fun {z} hz => by rw [hD] at hz; exact mem_refl_image.1 hz
  have hmem' : ∀ {z}, z ∈ H \ fillH (η '' Icc 0 q) → refl z ∈ H \ fillH (reflectCurve η '' Icc 0 q) :=
    fun {z} hz => by rw [hD, mem_refl_image, refl_refl]; exact hz
  refine ⟨fun z hz => Lf.refl_mem_H (h.maps (hmem hz)), fun z hz w hw he => ?_, ?_, ?_, ?_,
    fun w hw => hmem' (h.inv_mem (Lf.refl_mem_H hw)), fun w hw => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_⟩
  · exact refl_injective (h.injOn (hmem hz) (hmem hw) (refl_injective he))
  · exact continuous_refl.comp_continuousOn (h.cont.comp continuous_refl.continuousOn fun z hz => hmem hz)
  · obtain ⟨C, hC⟩ := h.bdd
    refine ⟨C, fun z hz => ?_⟩
    have h1 := hC (refl z) (hmem hz)
    have h2 : refl (f (refl z)) - z = refl (f (refl z) - refl z) := by rw [refl_sub, refl_refl]
    rw [h2, Lf.norm_refl]; exact h1
  · exact continuous_refl.comp_continuousOn
      (h.inv_cont.comp continuous_refl.continuousOn fun w hw => refl_mem_Hbar_iff.2 hw)
  · show refl (f (refl (refl (Φ (refl w))))) = w
    rw [refl_refl, h.f_inv _ (Lf.refl_mem_H hw), refl_refl]
  · show refl (Φ (refl (refl (f (refl z))))) = z
    rw [refl_refl, h.inv_f _ (hmem hz), refl_refl]
  · intro U p hU
    have hU' : ((U.map refl : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓝[H \ fillH (η '' Icc 0 q)] (refl p) := by
      rw [Ultrafilter.coe_map]
      refine (Filter.map_mono hU).trans ?_
      have h1 := map_refl_nhdsWithin_le (H \ fillH (reflectCurve η '' Icc 0 q)) p
      rw [hD, Lf.refl_image_refl_image] at h1
      rw [hD]; exact h1
    obtain ⟨y, hyH, hfy, hΦy⟩ := h.cluster (U.map refl) (refl p) hU'
    refine ⟨refl y, refl_mem_Hbar_iff.2 hyH, ?_, ?_⟩
    · rw [Ultrafilter.coe_map] at hfy
      exact (continuous_refl.tendsto y).comp (tendsto_map'_iff.1 hfy)
    · show refl (Φ (refl (refl y))) = p
      rw [refl_refl, hΦy, refl_refl]
  · show refl (Φ (refl 0)) = refl (η q)
    rw [refl_zero, h.tip]
  · intro hq y hy
    have hq' : η q ∈ H := refl_mem_H_iff.1 hq
    have h1 : Φ (refl (y : ℂ)) = η q := refl_injective hy
    rw [Lf.refl_ofReal] at h1
    have := h.tip_fibre hq' (-y) h1
    linarith
  · intro y hy
    have hy' : Φ ((-y : ℝ) : ℂ) ∈ H := by
      have h1 := refl_mem_H_iff.1 hy
      rwa [Lf.refl_ofReal] at h1
    obtain ⟨s, hs, hse⟩ := h.bdry (-y) hy'
    refine ⟨s, hs, ?_⟩
    show Supp9B.refl (η s) = Supp9B.refl (Φ (Supp9B.refl (y : ℂ)))
    rw [Lf.refl_ofReal, hse]

/-- **The S3 geometry, reflected** (Lemma S3 with the roles of left and right exchanged: SB2(2)'s lower pieces,
supplement p. 631). For a path image `A` from `0` on the closed **left** of a proper curve `β₀` from `0` and a right
entry chart of `A` at `R = max (A ∩ ℝ)` with a continuous finite-fibre inverse extension `g`, the tail of `β₀` after its
visit `t_R` to `R` has a proper lift `γ` (`g ∘ γ = β₀(t_R + ·)`), and for every common arc `β₀(t_R + [a, b]) ⊆ A`
with interior end and every `t ∈ (a, b)`: `γ(t)` is real and **negative**, the approach `g_*(𝓝[ℍ] γ(t))` is on the
**right** of `β₀`, in the joint domain, with both component accesses, and every core chart `(f, Φ)` of
`fill β₀([0, t_R + b])` tends along it to a **positive** real `y` (the exposed right side), `Φ(y) = β₀(t_R + t)`,
with a ball about `y` missing `f(fill(A ∪ β₀[0, t_R + b]) ∖ fill β₀[0, t_R + b])`.

Proof: reflect through `z ↦ −z̄` and apply `exists_s3_geometry_of_chart`. -/
theorem exists_s3_geometry_of_chart_right {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0) (hA : p '' Icc 0 1 ⊆ closedLeftSide β₀)
    {c : Chart} {g : ℂ → ℂ} (hc : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) :
    ∃ (tR : ℝ≥0) (γ : ℝ≥0 → ℂ),
      β₀ tR = realMax (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β₀ (tR + s)) ∧
      ∀ a b t : ℝ≥0, t ∈ Ioo a b → β₀ '' Icc (tR + a) (tR + b) ⊆ p '' Icc 0 1 → β₀ (tR + b) ∈ H →
        (γ t).re < 0 ∧ (𝓝[H] (γ t)).NeBot ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (rightSide β₀ ∩ (H \ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)))) ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[H \ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b))] (β₀ (tR + t)) ∧
        (∀ S T : Set ℂ, β₀ '' Icc (tR + a) (tR + b) ⊆ S →
          S ⊆ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) → T ⊆ fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) →
          ∃ r > 0, Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[FinRel.freeNear T S (β₀ (tR + t)) r] (β₀ (tR + t))) ∧
        ∀ {f Φ : ℂ → ℂ}, IsChartCore β₀ (tR + b) f Φ →
          DifferentiableOn ℂ f (H \ fillH (β₀ '' Icc 0 (tR + b))) →
          (∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) → IsOpen (H \ fillH (β₀ '' Icc 0 (tR + b))) →
          ∃ y : ℝ, 0 < y ∧ Φ y = β₀ (tR + t) ∧ Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝[H] (y : ℂ)) ∧
            ∃ r > 0, Disjoint (ball (y : ℂ) r)
              (f '' (fillH (p '' Icc 0 1 ∪ β₀ '' Icc 0 (tR + b)) \ fillH (β₀ '' Icc 0 (tR + b)))) := by
  set A := p '' Icc 0 1 with hAdef
  set p' : ℝ → ℂ := fun s => refl (p s) with hp'
  have hA' : p' '' Icc 0 1 = refl '' A := (Lk.refl_image_path p).symm
  have hp'c : ContinuousOn p' (Icc 0 1) := continuous_refl.comp_continuousOn hp
  have hp'0 : p' 0 = 0 := by show refl (p 0) = 0; rw [hp0, refl_zero]
  have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im := fun s hs => by
    show 0 ≤ (Supp9B.refl (p s)).im; rw [refl_im]; exact hpH s hs
  have hβ' := isProperCurve_reflectCurve hβ
  have hβ'0 : reflectCurve β₀ 0 = 0 := by show refl (β₀ 0) = 0; rw [hβ0, refl_zero]
  have h0im : (β₀ 0).im = 0 := by rw [hβ0]; rfl
  have hsub : p' '' Icc 0 1 ⊆ closedRightSide (reflectCurve β₀) := by
    rw [hA']
    exact (image_mono hA).trans (Lf.refl_image_closedLeftSide_subset hβ.2.2.1 h0im)
  have hc' : IsLeftEntryChart (p' '' Icc 0 1) (realMin (p' '' Icc 0 1)) (Lf.reflChart c) := by
    rw [hA', Lf.realMin_refl_image]
    exact Lf.isLeftEntryChart_reflChart hc
  set g' : ℂ → ℂ := fun w => refl (g (refl w)) with hg'
  have hg'c : ContinuousOn g' {z | 0 ≤ z.im} := by
    refine continuous_refl.comp_continuousOn (hgc.comp continuous_refl.continuousOn fun w (hw : 0 ≤ w.im) => ?_)
    show 0 ≤ (refl w).im
    rw [refl_im]; exact hw
  have hg'i : EqOn g' (Lf.reflChart c).2.1 H := fun w hw => by
    show Supp9B.refl (g (refl w)) = Supp9B.refl (c.2.1 (refl w))
    rw [hgi (Lf.refl_mem_H hw)]
  have hg'f : ∀ z, (g' ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite := fun z => by
    refine ((hgf (refl z)).image refl).subset fun w hw => ?_
    obtain ⟨hwz, hwi⟩ := hw
    refine ⟨refl w, ⟨?_, ?_⟩, refl_refl w⟩
    · show g (refl w) = refl z
      have h1 : refl (g (refl w)) = z := hwz
      rw [← h1, refl_refl]
    · show 0 ≤ (refl w).im
      rw [refl_im]; exact hwi
  obtain ⟨tR, γ', htR', hγ', hγ'0, hγ'g, hall⟩ :=
    exists_s3_geometry_of_chart hp'c hp'0 hp'H hβ' hβ'0 hsub hc' hg'c hg'i hg'f
  have hgg : ∀ z, g z = refl (g' (refl z)) := fun z => by
    show g z = Supp9B.refl (Supp9B.refl (g (Supp9B.refl (refl z)))); rw [refl_refl, refl_refl]
  have hR : β₀ tR = (realMax A : ℂ) := by
    have h1 : refl (β₀ tR) = ((-realMax A : ℝ) : ℂ) := by
      have := htR'; rw [hA', Lf.realMin_refl_image] at this; exact this
    have h2 := congrArg refl h1
    rw [refl_refl, Lf.refl_ofReal, neg_neg] at h2
    exact h2
  refine ⟨tR, reflectCurve γ', hR, isProperCurve_reflectCurve hγ', ?_, fun s => ?_, ?_⟩
  · show Supp9B.refl (γ' 0) = 0; rw [hγ'0, refl_zero]
  · have h1 : Supp9B.refl (g (Supp9B.refl (γ' s))) = Supp9B.refl (β₀ (tR + s)) := hγ'g s
    exact refl_injective h1
  intro a b t ht harc hqH
  have himg : ∀ (X : Set ℝ≥0), reflectCurve β₀ '' X = Supp9B.refl '' (β₀ '' X) := fun X =>
    (image_image Supp9B.refl β₀ X).symm
  have harc' : reflectCurve β₀ '' Icc (tR + a) (tR + b) ⊆ p' '' Icc 0 1 := by
    rw [himg, hA']; exact image_mono harc
  have hqH' : reflectCurve β₀ (tR + b) ∈ H := Lf.refl_mem_H hqH
  obtain ⟨hpos, hne, hFL, hFJ, hacc, hsec⟩ := hall a b t ht harc' hqH'
  have hJ : fillH (p' '' Icc 0 1 ∪ reflectCurve β₀ '' Icc 0 (tR + b)) =
      Supp9B.refl '' fillH (A ∪ β₀ '' Icc 0 (tR + b)) := by
    rw [hA', himg, ← image_union, refl_image_fillH]
  have hK : fillH (reflectCurve β₀ '' Icc 0 (tR + b)) = Supp9B.refl '' fillH (β₀ '' Icc 0 (tR + b)) := by
    rw [himg, refl_image_fillH]
  have hDJ : H \ fillH (p' '' Icc 0 1 ∪ reflectCurve β₀ '' Icc 0 (tR + b)) =
      Supp9B.refl '' (H \ fillH (A ∪ β₀ '' Icc 0 (tR + b))) := by
    rw [hA', himg, ← image_union, Lk.refl_image_H_diff_fillH]
  have hγt : reflectCurve γ' t = Supp9B.refl (γ' t) := rfl
  have hF : Filter.map g (𝓝[H] (reflectCurve γ' t)) =
      Filter.map Supp9B.refl (Filter.map g' (𝓝[H] (γ' t))) := by
    rw [hγt, nhdsWithin_H_refl, Filter.map_map, Filter.map_map]
    congr 1
    funext z
    show g (Supp9B.refl z) = Supp9B.refl (g' z)
    simp only [hg', refl_refl]
  have hpt : Supp9B.refl (reflectCurve β₀ (tR + t)) = β₀ (tR + t) := refl_refl _
  refine ⟨?_, ?_, ?_, ?_, fun S T hS hSJ hTJ => ?_, fun {f Φ} hch hfd hfin hDo => ?_⟩
  · show (Supp9B.refl (γ' t)).re < 0
    rw [refl_re]; linarith
  · rw [hγt, nhdsWithin_H_refl]; exact hne.map _
  · rw [hF]
    refine (Filter.map_mono hFL).trans ?_
    rw [Filter.map_principal, principal_mono]
    rintro _ ⟨z, ⟨hzL, hzJ⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 := Lf.refl_image_leftSide_subset hβ'.2.2.1 (by rw [hβ'0, Complex.zero_im])
        (mem_image_of_mem Supp9B.refl hzL)
      rwa [reflectCurve_reflectCurve] at h1
    · rw [hDJ] at hzJ
      exact mem_refl_image.1 hzJ
  · rw [hF]
    have h1 := (Filter.map_mono hFJ).trans (map_refl_nhdsWithin_le _ _)
    rw [hpt, hDJ, Lf.refl_image_refl_image] at h1
    exact h1
  · obtain ⟨r, hr, hle⟩ := hacc (Supp9B.refl '' S) (Supp9B.refl '' T) (by rw [himg]; exact image_mono hS)
      (by rw [hJ]; exact image_mono hSJ) (by rw [hJ]; exact image_mono hTJ)
    refine ⟨r, hr, ?_⟩
    rw [hF]
    have h1 := (Filter.map_mono hle).trans (map_refl_nhdsWithin_le _ _)
    have h2 := nhdsWithin_mono (Supp9B.refl (reflectCurve β₀ (tR + t)))
      (refl_image_freeNear_subset (Supp9B.refl '' T) (Supp9B.refl '' S) (reflectCurve β₀ (tR + t)) r)
    rw [Lf.refl_image_refl_image, Lf.refl_image_refl_image, hpt] at h2
    rw [hpt] at h1
    exact h1.trans h2
  · have hK' : H \ fillH (reflectCurve β₀ '' Icc 0 (tR + b)) =
        Supp9B.refl '' (H \ fillH (β₀ '' Icc 0 (tR + b))) := by
      rw [himg, Lk.refl_image_H_diff_fillH]
    have hch' := hch.reflect
    have hfd' : DifferentiableOn ℂ (fun z => Supp9B.refl (f (Supp9B.refl z)))
        (H \ fillH (reflectCurve β₀ '' Icc 0 (tR + b))) := by
      intro z hz
      rw [hK'] at hz
      have hz' := mem_refl_image.1 hz
      exact (Lf.differentiableAt_refl_comp ((hfd _ hz').differentiableAt (hDo.mem_nhds hz'))).differentiableWithinAt
    have hfin' : ∀ z, ((fun w => Supp9B.refl (Φ (Supp9B.refl w))) ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := fun z => by
      refine ((hfin (Supp9B.refl z)).image Supp9B.refl).subset fun w hw => ?_
      obtain ⟨hwz, hwi⟩ := hw
      refine ⟨Supp9B.refl w, ⟨?_, ?_⟩, refl_refl w⟩
      · show Φ (Supp9B.refl w) = Supp9B.refl z
        have h1 : Supp9B.refl (Φ (Supp9B.refl w)) = z := hwz
        rw [← h1, refl_refl]
      · show 0 ≤ (Supp9B.refl w).im
        rw [refl_im]; exact hwi
    have hDo' : IsOpen (H \ fillH (reflectCurve β₀ '' Icc 0 (tR + b))) := by
      rw [hK']
      have he : Supp9B.refl '' (H \ fillH (β₀ '' Icc 0 (tR + b))) =
          Supp9B.refl ⁻¹' (H \ fillH (β₀ '' Icc 0 (tR + b))) := by
        ext z; exact mem_refl_image
      rw [he]; exact hDo.preimage continuous_refl
    obtain ⟨y', hy'0, hΦy', hfy', r, hr, hgap'⟩ := hsec hch' hfd' hfin' hDo'
    refine ⟨-y', by linarith, ?_, ?_, r, hr, ?_⟩
    · have h1 : Supp9B.refl (Φ (Supp9B.refl (y' : ℂ))) = Supp9B.refl (β₀ (tR + t)) := hΦy'
      have h2 := refl_injective h1
      rwa [Lf.refl_ofReal] at h2
    · rw [hF, tendsto_map'_iff]
      have h1 := (Lf.tendsto_refl_nhdsWithin_H (y' : ℂ)).comp hfy'
      rw [Lf.refl_ofReal] at h1
      refine Tendsto.congr (fun w => ?_) h1
      show Supp9B.refl (Supp9B.refl (f (Supp9B.refl w))) = f (Supp9B.refl w)
      rw [refl_refl]
    · rw [Set.disjoint_left]
      rintro u hu ⟨z, hz, rfl⟩
      refine Set.disjoint_left.1 hgap' (show Supp9B.refl (f z) ∈ ball (y' : ℂ) r from ?_)
        ⟨Supp9B.refl z, ?_, ?_⟩
      · rw [mem_ball] at hu ⊢
        rw [← refl_refl (y' : ℂ), dist_refl, Lf.refl_ofReal]
        exact hu
      · rw [hJ, hK]
        refine ⟨mem_image_of_mem _ hz.1, fun h => hz.2 ?_⟩
        have h1 := mem_refl_image.1 h
        rwa [refl_refl] at h1
      · show Supp9B.refl (f (Supp9B.refl (Supp9B.refl z))) = Supp9B.refl (f z)
        rw [refl_refl]

end InteractingSLE.Theorem14.SB.S3.Geo
