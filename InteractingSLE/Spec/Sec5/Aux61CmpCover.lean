/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpSeedCollar
import InteractingSLE.Spec.Sec5.Aux61GChoice16Field
import InteractingSLE.Spec.Sec5.Aux61GChoice16Seed

/-! # The physical germ cover from collar accesses

`PastGermCover` (GLUEINST phase 16) asks, at every window point `b ∈ O₀`, for
a smaller reference, a landing point `z₀`, full-ball containment of the actual
zero-time marked set near `z₀` in that reference, and the charted reference
germ. This file proves its **own side** completely from a deterministic
access condition on the actual sample:

* `SeedAccess W r c t b`: the chart point `b` is `(c ∘ F_r)(t)` for a point `t`
  of a free current collar `F_r(ℍ ∩ B(0, δ)) ⊆ dom c` whose real points never
  see the target `1`, and every physical preimage of `F̄_r(t)` lies in the collar;
* `OwnCollarPoint`: such an access, and off the seed the reference height at
  `b` is the own height at `t` (the own force word at the restart).

At such `b` the own reference at the restart time supplies all four clauses
(`ownGerm_of_collarPoint`): the hull identification of the actual coupling,
`exists_ball_inter_subset_dom`, `tendsto_inv_collar`, and either the landed
seed germ (`b = 0`) or `tendsto_charted_couplingMean_sub_refMean0_collar`.
The counterflow side is kept as the exact counterflow clause `CounterGerm`.

`pastGermCover_of_access` assembles `PastGermCover` when every window point of
every selected record is an own collar point or a counterflow germ point.
Deterministic in the access data; no source statement is replaced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cmp
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61GChoice16 Aux61Restart Aux61FibData
open Aux61ChLoc LawUnique GlueCond Aux61R1C Aux61Asm2 Aux61GInst Aux61GR1F
universe u

/-- **A free-collar access**: the chart real point `b` is the boundary value
of `c ∘ F_r` at a real point `t` of a free current collar of radius `δ`, whose
real points never reach the target `1`, and every physical preimage of
`F̄_r(t)` lies in the collar. -/
def SeedAccess (W : ℝ → ℝ) (r : ℝ) (c : Chart) (t b : ℝ) : Prop :=
  ∃ δ > 0, |t| < δ ∧ MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom ∧
    (∀ x : ℝ, |x| < δ → extendFrom H (fwdMapInv W r) x ≠ 1) ∧
    (∀ y : ℝ, extendFrom H (fwdMapInv W r) y = extendFrom H (fwdMapInv W r) t → |y| < δ) ∧
    Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] (t : ℂ)) (𝓝 (b : ℂ))

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- The effective left force positions of the own word at the restart. -/
abbrev ownVL (i : F.ι) (p : S.Ω × HistorySpace 0 0) : Fin S.nL → ℝ :=
  fun j => S.own.VL j (F.start i) p.1 - S.own.W (F.start i) p.1

/-- The effective right force positions of the own word at the restart. -/
abbrev ownVR (i : F.ι) (p : S.Ω × HistorySpace 0 0) : Fin S.nR → ℝ :=
  fun j => S.own.VR j (F.start i) p.1 - S.own.W (F.start i) p.1

/-- **The own side of the cover** at a sample: the chart point `b` has a free
collar access, and off the seed the reference height is the own height. -/
def OwnCollarPoint (i : F.ι) (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ t : ℝ, SeedAccess (fun s : ℝ => S.own.W s.toNNReal p.1) (F.start i) ((S.marksData F).chart i p) t b ∧
    (b = 0 ∨ (b ∉ (F.data i).JR ∧
      t ∉ Impl.forceJumpSet (Ito.weightWord S.ρL S.ρR) (ownVL S F i p) (ownVR S F i p) ∧
      (F.data i).bR b = Impl.forceBoundaryData (F.data i).κ (Ito.weightWord S.ρL S.ρR)
        (ownVL S F i p) (ownVR S F i p) t))

/-- **The counterflow side of the cover**: the exact clause of
`PastGermCover` for the retained counterflow reference. -/
def CounterGerm (i : F.ι) (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ z₀ : ℂ, z₀ ∈ sourceReferenceSet S (.inr ()) p ∪ {z : ℂ | z.im = 0} ∧
    (∃ r > 0, (S.marksData F).baseSets i 0 p ∩ ball z₀ r ⊆ sourceReferenceSet S (.inr ()) p) ∧
    Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
    Tendsto (fun z => sourceReferenceMean S (.inr ()) p (((S.marksData F).chart i p).2.1 z) +
      (S.marksData F).scale + (S.marksData F).constant * ((S.marksData F).chart i p).2.2
        (((S.marksData F).chart i p).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
      (𝓝[H] (b : ℂ)) (𝓝 0)

/-- On the live zero-time event the actual marked set is the complement of
the retained chart domain. -/
theorem baseSets_zero_eq {i : F.ι} {p : S.Ω × HistorySpace 0 0}
    (hc : ((S.marksData F).chart i p).IsConformal)
    (hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0) :
    (S.marksData F).baseSets i 0 p = H \ ((S.marksData F).chart i p).dom := by
  have h1 : (S.marksData F).baseSets i 0 p = liveSet (liveEv ((S.marksData F).Z i)
      ((S.marksData F).B i) ((S.marksData F).code i) 0) (fun p => Aux61Marks.chartSet
        ((S.marksData F).chart i p) (Aux61UnionK.chartHull ((S.marksData F).code i) 0 p)) p := rfl
  rw [h1, liveSet_of_mem hlive]
  show Aux61Marks.chartSet _ (Aux61UnionK.chartHull _ 0 p) = _
  rw [Aux61OldB.chartHull_zero, Aux61Marks.chartSet, sdiff_empty, ← hc.coe_dom]

variable {S F}

/-- **The own reference supplies every clause of the cover at an own collar
point**: the own hull at the restart time (actual hull identification), the
landing point `F̄_r(t)`, full-ball containment of the actual zero-time marked
set, and the charted own germ (the landed seed theorem at `b = 0`, the collar
theorem elsewhere). -/
theorem ownGerm_of_collarPoint
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hleft : PiecewiseConstantBoundaryData.leftLim (F.data i).bR 0 = -sleLambda (F.data i).κ)
    (hright : PiecewiseConstantBoundaryData.rightLim (F.data i).bR 0 = sleLambda (F.data i).κ)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i → ∀ b : ℝ, OwnCollarPoint S F i p b →
      ∃ z₀ : ℂ, z₀ ∈ sourceReferenceSet S (pastReferenceIndex q (.inl q)) p ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, (S.marksData F).baseSets i 0 p ∩ ball z₀ r ⊆
          sourceReferenceSet S (pastReferenceIndex q (.inl q)) p) ∧
        Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q (.inl q)) p
          (((S.marksData F).chart i p).2.1 z) + (S.marksData F).scale +
          (S.marksData F).constant * ((S.marksData F).chart i p).2.2
            (((S.marksData F).chart i p).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0) := by
  filter_upwards [hgeometry, S.physical_path, source_own_seed_germ S F hR i q hq hleft hright hgeometry,
    hR.physical_stop i, source_zero_alive_iff S F hR i] with p hg hp hseed hstop halive hB b hb
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0 :=
    ⟨hB, by rw [ENNReal.coe_zero]; exact halive.2 hsel⟩
  have hpi : pastReferenceIndex q (.inl q) = .inl q := by simp only [pastReferenceIndex, min_self]
  rw [hpi]
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  have hc := (hR.spec i).conf p he
  have hgeo := hg he
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) := by
    rw [WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 (F.start i).coe_nonneg]
    intro z hz
    exact ⟨(hgeo.retained hz).1, fun hP => (hgeo.retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hP))⟩
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hr0 : (0 : ℝ) < F.start i := NNReal.coe_pos.2 hgeo.start_pos
  have hh : sourceReferenceSet S (.inl q) p =
      fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) := by
    have h := Aux50Hit.regHull_stopHistory_cstop hp.1 (rationalTime q)
    change hullAt (rationalTime q) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime q) at h
    rw [hq]
    exact h
  obtain ⟨t, ⟨δ, hδ, ht, hcol, hone, hpre, htb⟩, hreg⟩ := hb
  refine ⟨extendFrom H (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i)) t, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    exact extendFrom_mem_hull_or_real hW hW0 hp.2.1 hr0 t
  · obtain ⟨ρ, hρ, hball⟩ := exists_ball_inter_subset_dom hW hW0 hp.2.1 hr0 hcol t hpre
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    rw [baseSets_zero_eq S F hc hlive] at hw
    rw [hh]
    by_contra hwK
    exact hw.1.2 (hball ⟨hw.2, hw.1.1, hwK⟩)
  · exact tendsto_inv_collar hW hW0 hp.2.1 hr0 hc hsub hBh hscale hδ hcol hone ht htb
  · by_cases hb0 : b = 0
    · subst hb0
      rw [Complex.ofReal_zero]
      exact hseed he
    · obtain ⟨hbJ, htJ, hheight⟩ := hreg.resolve_left hb0
      have hm := tendsto_charted_couplingMean_sub_refMean0_collar hW hW0 hp.2.1 hr0 hc hsub hBh
        hscale hδ hcol hone ha (hp.2.2.inj.mono Icc_subset_Ici_self)
        (fun u hu => hp.2.2.mem_H u hu.1) hgeo.lift (F.data i) (Ito.weightWord S.ρL S.ρR)
        (ownVL S F i p) (ownVR S F i p) ht htb htJ hb0 hbJ hheight
      rw [hR.kappa i] at hm
      change Tendsto (fun z =>
        couplingMean S.κ (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime q)
          (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR q p.1)
          (((S.marksData F).chart i p).2.1 z) + 0 + chiC S.κ *
          ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
          Aux61GlueK.refMean0 (F.data i) z) (𝓝[H] (b : ℂ)) (𝓝 0)
      have heq : Ito.rpath (fun t => S.own.W t p.1) = (fun t : ℝ => S.own.W t.toNNReal p.1) := rfl
      rw [heq] at hm
      simp only [sourcePatchExtension, ← hq, add_zero]
      exact hm

/-- **`PastGermCover` from collar accesses.** If, almost surely on the selected
records, every window point is an own collar point or a counterflow germ
point, the full-ball physical germ cover holds. -/
theorem pastGermCover_of_access
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hleft : PiecewiseConstantBoundaryData.leftLim (F.data i).bR 0 = -sleLambda (F.data i).κ)
    (hright : PiecewiseConstantBoundaryData.rightLim (F.data i).bR 0 = sleLambda (F.data i).κ)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (haccess : ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i →
      ∀ b ∈ ((S.marksData F).data i).O₀, OwnCollarPoint S F i p b ∨ CounterGerm S F i p b) :
    PastGermCover S F i q := by
  filter_upwards [haccess, ownGerm_of_collarPoint hR i q hq hleft hright hgeometry]
    with p hacc hown hB b hb
  rcases hacc hB b hb with h | ⟨z₀, h₁, h₂, h₃, h₄⟩
  · obtain ⟨z₀, h₁, h₂, h₃, h₄⟩ := hown hB b h
    exact ⟨.inl q, z₀, h₁, h₂, h₃, h₄⟩
  · exact ⟨.inr (), z₀, h₁, h₂, h₃, h₄⟩

/-- **The exact `ChoiceInputs.comparisons` field from collar accesses.** For
any restart choices with the restart/window prerequisites of
`choice_comparisons_of_past_germs`, the reference word of each index having the
canonical seed heights `∓λ`, and every window point of every selected record an
own collar point or a counterflow germ point of the actual cut family, the
full-ball comparison records exist. -/
theorem choice_comparisons_of_access {S : SourceSetting.{u}} (C : Aux61R1C.RestartChoices S)
    (hsel : ∀ i, MeasurableSet (C.selected i)) (w : Aux61GR1F.WindowFields C.toR1Restart)
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (V : Aux61SlitWZ.SeedWindows C)
    (hfinite : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      ∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
        boundedInverse (sourceChart C.fam (rationalTime S.s)
          S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (C.toR1Restart.data i).bR 0 =
      -sleLambda (C.toR1Restart.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (C.toR1Restart.data i).bR 0 =
      sleLambda (C.toR1Restart.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (cutSource S (withRecordPath S C.fam))).Z i p ∈
        (S.marksData (cutSource S (withRecordPath S C.fam))).B i →
      ∀ b ∈ ((S.marksData (cutSource S (withRecordPath S C.fam))).data i).O₀,
        OwnCollarPoint S (cutSource S (withRecordPath S C.fam)) i p b ∨
          CounterGerm S (cutSource S (withRecordPath S C.fam)) i p b) :
    ∀ i, Nonempty (Aux61GAlign.ZeroComparisons
      (S.marksData (cutSource S (withRecordPath S C.fam))) i) := by
  have hR := choice_cut_restart C hsel w hg V hfinite
  refine choice_comparisons_of_past_germs C hsel w hg V hfinite fun i => ?_
  refine pastGermCover_of_access hR i (C.q i.1) rfl (hleft i) (hright i) ?_ (haccess i)
  filter_upwards [hg i] with p hp he
  exact hp he.1

end InteractingSLE.Sec5.Aux61Cmp
