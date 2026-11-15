/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightShift
import InteractingSLE.GFF.LocalSets.GermApprox
import InteractingSLE.Spec.Sec7.Lemma78MeanReal
import InteractingSLE.Spec.Sec5.Aux61OldBTriv
import InteractingSLE.Spec.Supplement.SBLwShift

/-!
# Germ σ-algebras and local-set means under a real translation

Packet PROVE-T14-SB2DRV (round 6), infrastructure for the late regime of SB2(1)'s (S) line mean: FIN's union mean is
stated in coordinates where the upper flow starts at `0`, so the line set, the field and the local-set means are moved
by the real translation `z ↦ z + c` (with the field `F(· − c) = Exist.flowField (−c) 0 F`).

* `tsupport_shiftTest_subset`, `sub_mem_germNbhd` (the germ neighbourhoods move with the set, the far region `‖z‖ >
  1/δ` up to `|c|`);
* **`germSigmaAt_translate_le`**, **`germSigma_translate`**: the germ σ-algebra of the translated set and field is that
  of the original pair;
* **`IsLocalSetMean.translate`**: a local-set mean, translated, is a local-set mean of the translated pair.

Deterministic transport lemmas; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.Lv.Shift

open LocalSets Sec7.SideHeight

/-- The support of a translated test function is the translated support. -/
theorem tsupport_shiftTest_subset (c : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (WholeField.shiftTest c φ) ⊆ (fun z : ℂ => z - c) '' tsupport φ := by
  have e : (⇑(WholeField.shiftTest c φ) : ℂ → ℝ) = (⇑φ) ∘ (Homeomorph.addRight (c : ℂ)) := by
    funext z
    simp only [Function.comp_apply, Homeomorph.coe_addRight, WholeField.shiftTest_apply]
  rw [e, tsupport_comp_eq_preimage]
  intro z hz
  exact ⟨z + c, hz, by ring⟩

/-- **Germ neighbourhoods move with the set**, the far region up to `|c|`. -/
theorem sub_mem_germNbhd {δ δ' : ℝ} (c : ℝ) (hδ' : δ' ≤ δ) (hfar : 1 / δ + |c| ≤ 1 / δ') {S : Set ℂ} {z : ℂ}
    (hz : z ∈ germNbhd δ' ((fun w : ℂ => w + c) '' S)) : z - c ∈ germNbhd δ S := by
  obtain ⟨hzH, hz⟩ := hz
  refine ⟨?_, ?_⟩
  · show 0 < (z - (c : ℂ)).im
    have : 0 < z.im := hzH
    simpa using this
  rcases hz with hz | hz
  · obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
    refine Or.inl (mem_thickening_iff.2 ⟨y - c, ?_, ?_⟩)
    · rcases hy with ⟨⟨s, hs, rfl⟩, hyH⟩ | hy
      · refine Or.inl ⟨by simpa using hs, ?_⟩
        show 0 < (s + (c : ℂ) - c).im
        have : 0 < (s + (c : ℂ)).im := hyH
        simpa using this
      · refine Or.inr ?_
        show (y - (c : ℂ)).im = 0
        have : y.im = 0 := hy
        simpa using this
    · rw [dist_sub_right]
      exact lt_of_lt_of_le hzy hδ'
  · refine Or.inr ?_
    show 1 / δ < ‖z - (c : ℂ)‖
    have h1 : ‖z‖ - ‖(c : ℂ)‖ ≤ ‖z - (c : ℂ)‖ := norm_sub_norm_le _ _
    have h2 : ‖(c : ℂ)‖ = |c| := Complex.norm_real c
    have h3 : 1 / δ' < ‖z‖ := hz
    linarith

/-- **The germ σ-algebra at scale `δ'` of the translated pair lies in that at scale `δ` of the original pair.** -/
theorem germSigmaAt_translate_le {Ω : Type*} (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (c : ℝ)
    {δ δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ δ) (hfar : 1 / δ + |c| ≤ 1 / δ') :
    germSigmaAt (fun ω => (fun z : ℂ => z + c) '' A ω) (fun ω => Exist.flowField (-c) 0 (h ω)) δ' ≤
      germSigmaAt A h δ := by
  have hcomap : MeasurableSpace.comap (fun ω => (fun z : ℂ => z + c) '' A ω) hittingSigma ≤
      MeasurableSpace.comap A hittingSigma := by
    rw [show (fun ω => (fun z : ℂ => z + c) '' A ω) = (fun S : Set ℂ => (fun z : ℂ => z + c) '' S) ∘ A from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_image_add c).comap_le
  unfold germSigmaAt
  refine sup_le (hcomap.trans le_sup_left) (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨φ, B, hB, rfl⟩
  set ψ := WholeField.shiftTest c φ with hψ
  have e : {ω | tsupport φ ⊆ germNbhd δ' ((fun z : ℂ => z + c) '' A ω)} ∩
      (fun ω => Exist.flowField (-c) 0 (h ω) φ) ⁻¹' B =
      {ω | tsupport φ ⊆ germNbhd δ' ((fun z : ℂ => z + c) '' A ω)} ∩
        ({ω | tsupport ψ ⊆ germNbhd δ (A ω)} ∩ (fun ω => h ω ψ) ⁻¹' B) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, flowField_neg_apply, hψ]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, (tsupport_shiftTest_subset c φ).trans ?_, h2⟩
      rintro _ ⟨z, hz, rfl⟩
      exact sub_mem_germNbhd c hδ' hfar (h1 hz)
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  rw [e]
  refine MeasurableSet.inter ?_ ?_
  · refine le_sup_left (b := MeasurableSpace.generateFrom _) _ (hcomap _ ?_)
    exact ⟨_, LocalSets.measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset hδ'0, rfl⟩
  · exact le_sup_right (a := MeasurableSpace.comap _ hittingSigma) _
      (MeasurableSpace.measurableSet_generateFrom ⟨ψ, B, hB, rfl⟩)

theorem germSigma_translate_le {Ω : Type*} (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (c : ℝ) :
    germSigma (fun ω => (fun z : ℂ => z + c) '' A ω) (fun ω => Exist.flowField (-c) 0 (h ω)) ≤ germSigma A h := by
  refine le_iInf fun n => ?_
  set N : ℕ := n + ⌈|c|⌉₊ with hN
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hceil : |c| ≤ (⌈|c|⌉₊ : ℝ) := Nat.le_ceil _
  have hNn : (n : ℝ) + 1 + |c| ≤ (N : ℝ) + 1 := by
    rw [hN]
    push_cast
    linarith
  refine (iInf_le _ N).trans (germSigmaAt_translate_le A h c (by positivity) ?_ ?_)
  · exact one_div_le_one_div_of_le hn0 (by linarith [abs_nonneg c])
  · rw [one_div_one_div, one_div_one_div]
    exact hNn

/-- **The germ σ-algebra of a translated pair is that of the original pair.** -/
theorem germSigma_translate {Ω : Type*} (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (c : ℝ) :
    germSigma (fun ω => (fun z : ℂ => z + c) '' A ω) (fun ω => Exist.flowField (-c) 0 (h ω)) = germSigma A h := by
  refine le_antisymm (germSigma_translate_le A h c) ?_
  have := germSigma_translate_le (fun ω => (fun z : ℂ => z + c) '' A ω)
    (fun ω => Exist.flowField (-c) 0 (h ω)) (-c)
  simp only [image_add_neg_image_add, flowField_neg_neg] at this
  exact this

/-- **A translated local-set mean is a local-set mean of the translated pair.** -/
theorem IsLocalSetMean.translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Ω → Set ℂ}
    {h g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g) (c : ℝ) :
    IsLocalSetMean (fun ω => (fun z : ℂ => z + c) '' A ω) (fun ω => Exist.flowField (-c) 0 (h ω)) P
      (fun ω => Exist.flowField (-c) 0 (g ω)) := by
  obtain ⟨hgm, hhar, hcz⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · rw [germSigma_translate]
    exact (Exist.measurable_flowField (-c) 0).comp hgm
  · filter_upwards [hhar] with ω hω
    exact isHarmonicDistOn_flowField_neg c hω
  · rw [germSigma_translate]
    have := isCondZeroBoundaryGFF_flowField_neg hcz c
    have e : (fun ω => Exist.flowField (-c) 0 (h ω - g ω)) =
        fun ω => Exist.flowField (-c) 0 (h ω) - Exist.flowField (-c) 0 (g ω) := by
      funext ω
      ext φ
      simp only [flowField_neg_apply, sub_apply]
    rwa [e] at this

/-- **The zero-boundary GFF is translation invariant.** -/
theorem isZeroBoundaryGFF_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P) (c : ℝ) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => Exist.flowField (-c) 0 (X ω)) P := by
  have h0 := Sec7.isCondZeroBoundaryGFF_bot hX
  have h1 : IsCondZeroBoundaryGFF P ⊥ (fun _ => H \ (∅ : Set ℂ)) (fun ω => X ω) := by
    simpa only [sdiff_empty, sub_zero] using h0
  have h2 := isCondZeroBoundaryGFF_flowField_neg (A := fun _ => (∅ : Set ℂ)) h1 c
  have h3 : IsCondZeroBoundaryGFF P ⊥ (fun _ => H) (fun ω => Exist.flowField (-c) 0 (X ω)) := by
    simpa only [image_empty, sdiff_empty] using h2
  exact Sec5.Aux61OldB.isZeroBoundaryGFF_of_isCondZeroBoundaryGFF_H bot_le
    ((Exist.measurable_flowField (-c) 0).comp hX.measurable) h3

/-! ### The chart read in seed-shifted coordinates -/

theorem image_add_real_H (m : ℝ) : (fun w : ℂ => w + m) '' H = H := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact add_real_mem_H' hy m
  · intro hw
    refine ⟨w - m, ?_, by ring⟩
    show 0 < (w - (m : ℂ)).im
    have : 0 < w.im := hw
    simpa using this

/-- **The domain of the seed-shifted chart is the shifted domain.** -/
theorem dom_shiftChart (c : Chart) (u m : ℝ) :
    ((Lw.shiftChart c u m).dom : Set ℂ) = (fun z : ℂ => z - u) '' (c.dom : Set ℂ) := by
  have e : (Lw.shiftChart c u m).2.1 '' H = (fun z : ℂ => z - u) '' (c.2.1 '' H) := by
    rw [image_image]
    conv_rhs => rw [← image_add_real_H m, image_image]
    rfl
  show interior ((Lw.shiftChart c u m).2.1 '' H) = _
  rw [e]
  have h2 := (Homeomorph.subRight (u : ℂ)).image_interior (c.2.1 '' H)
  have hf : (⇑(Homeomorph.subRight (u : ℂ)) : ℂ → ℂ) = fun z => z - (u : ℂ) := rfl
  rw [hf] at h2
  exact h2.symm

/-- **Transport in the seed-shifted chart**: the chart `z ↦ c(z + u) − m` transports the field `T(· + u)` exactly as
the recentred chart `z ↦ c(z) − m` transports `T`. -/
theorem chartTransport_shiftChart_flowField {c : Chart} {u m : ℝ} (hcs : (Lw.shiftChart c u m).IsConformal)
    (hcr : (c.recenter m).IsConformal) (σ a k : ℝ) (T : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport hcs σ a k (Exist.flowField u 0 T) φ = Chart.chartTransport hcr σ a k T φ := by
  have hlift : Chart.liftDist (Lw.shiftChart c u m) = Chart.liftDist (c.recenter m) := by
    unfold Chart.liftDist
    congr 1
    funext w
    show c.2.2 (c.2.1 (w + m) - u + u) = c.2.2 (c.2.1 (w + m))
    rw [sub_add_cancel]
  have hpush : Chart.pushTest (Exist.isConformal_shiftChart u) (Chart.pushTest hcs φ) = Chart.pushTest hcr φ := by
    ext z
    rw [Exist.pushTest_shiftChart_apply, Chart.coe_pushTest, Chart.coe_pushTest, dom_shiftChart, Chart.dom_recenter]
    have hmem : z - u ∈ (fun y : ℂ => y - u) '' (c.dom : Set ℂ) ↔ z ∈ (c.dom : Set ℂ) :=
      sub_left_injective.mem_set_image
    by_cases hz : z ∈ (c.dom : Set ℂ)
    · rw [indicator_of_mem (hmem.2 hz), indicator_of_mem hz]
      have hd : deriv (Lw.shiftChart c u m).1 (z - u) = deriv (c.recenter m).1 z := by
        show deriv (fun y => c.1 (y + u) - m) (z - u) = deriv (fun y => c.1 y - m) z
        rw [deriv_sub_const, deriv_sub_const, deriv_comp_add_const, sub_add_cancel]
      rw [hd]
      show ‖deriv (c.recenter m).1 z‖ ^ 2 * φ (c.1 (z - u + u) - m) = ‖deriv (c.recenter m).1 z‖ ^ 2 * φ (c.1 z - m)
      rw [sub_add_cancel]
    · rw [indicator_of_notMem (fun h' => hz (hmem.1 h')), indicator_of_notMem hz]
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply', Exist.flowField_apply, hpush, hlift]
  ring

end InteractingSLE.Theorem14.SB.Lv.Shift
