/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzLaw
import InteractingSLE.Spec.Supplement.RelSafeS7


/-!
# GW2 at a root `x`: the physical union in the re-centred chart (decision D8, layer 5, continued)

Packet PROVE-GW2-ROOTX, round 3. GB6's `RelSafeS.ae_compl_union_eq_relChart` at a root `x₀`: the explored physical
set is `x₀ + fwdHull W t` (D8), and before the stop the complement of the physical union `A ∪ (x₀ + K_t)` (`A` the
retained hull in the counterflow frame) is the inverse image, under D8's re-centred chart `relChartX`, of the
complement of the relative hull:

* `image_add_real_compl` (a real translation of a complement in `ℍ`);
* **`compl_union_eq_relChartX`** (deterministic, one sample: ROOT2's translated disjointness
  `RootI30.disjoint_closure_translated_hull`, the forward hull reader `RootH29.forwardHull` as the relative image of
  the translated hull, `baseRead = relBase` on the protected arc, the record chart as the joint chart);
* **`ae_compl_union_eq_relChartX`**, **`shape_of_unionX`** (the `LinesLocalX.shape` target for the root-`x`
  physical union).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.ReadD GW2TipSystem
open Supp8.RelSafe (supBelow)

/-- A real translation and its inverse move a complement in `ℍ` to the complement of the translated set. -/
theorem image_add_real_compl (a : ℝ) (F : Set ℂ) :
    (fun z : ℂ => z + a) '' (H \ (fun z : ℂ => z + ((-a : ℝ) : ℂ)) '' F) = H \ F := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyH, hyF⟩, rfl⟩
    refine ⟨?_, fun hF => hyF ⟨y + a, hF, ?_⟩⟩
    · have h : 0 < y.im := hyH
      change 0 < (y + (a : ℂ)).im
      rw [add_im, ofReal_im, add_zero]
      exact h
    · push_cast; ring
  · rintro ⟨hzH, hzF⟩
    refine ⟨z + ((-a : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · have h : 0 < z.im := hzH
      change 0 < (z + ((-a : ℝ) : ℂ)).im
      rw [add_im, ofReal_im, add_zero]
      exact h
    · rintro ⟨f, hf, hfz⟩
      have : f = z := by
        have h := congrArg (fun u : ℂ => u + (a : ℂ)) hfz
        simp only at h
        push_cast at h
        linear_combination h
      exact hzF (this ▸ hf)
    · push_cast; ring

/-! ### The physical union in the re-centred chart, on one sample -/

section ShapeSample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)

include hα hW hW0 hζ hx harc hwc hw0 hγ in
/-- **The complement of the root-`x` physical union is the inverse re-centred chart image of the complement of the
relative hull** (deterministic): before the root-`x` contact, if a relative driver's hull at the root-`x` clock is the
re-centred relative hull, then `ℍ ∖ (A ∪ (x + K_t))` (`A` the retained hull in the counterflow frame) is the image of
`ℍ ∖ K̃` under the inverse of D8's re-centred chart. -/
theorem compl_union_eq_relChartX {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) {R : ℝ≥0 → ℝ}
    (hR : fwdHull (fun r : ℝ => R r.toNNReal)
        (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) :
    H \ (Supp8.Q3Rel.invHull (rdrv (cfRec s W ζ ω)) s ∪ (fun z : ℂ => z + x) '' fwdHull (Ito.rpath w) t) =
      (relChartX x s (cfRec s W ζ ω)).2.1 '' (H \ fwdHull (fun r : ℝ => R r.toNNReal)
        (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)))) := by
  set U := rdrv (cfRec s W ζ ω) with hUdef
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have he := Gm.isRegularDriver_top hwc hw0
  -- a later good horizon
  obtain ⟨v, htv, hvT⟩ : ∃ v : ℝ≥0, t < v ∧ (v : ℝ≥0∞) < firstContactTime
      (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
    obtain ⟨v, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact ⟨v, ENNReal.coe_lt_coe.1 h1, h2⟩
  have hv0 : 0 < v := zero_le.trans_lt htv
  have hv' : (v : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (w, (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hvT
  -- the explored prefix up to `v` misses the retained prefix in the inversion
  have hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => γ t + x) '' Icc 0 v \ {0})) := by
    apply disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨_, ⟨⟨t', ht', rfl⟩, hn⟩, heq⟩
    change γ t' + (x : ℂ) ≠ 0 at hn
    change -(γ t' + (x : ℂ))⁻¹ = α u at heq
    have htn := (ENNReal.coe_le_coe.mpr ht'.2).trans_lt hvT
    apply notMem_of_lt_firstContactTime htn
    refine ⟨u, hu, ?_⟩
    have hn' : (x : ℂ) + γ t' ≠ 0 := by simpa only [add_comm] using hn
    rw [sphereInv_coe_of_ne hn']
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (by simpa only [add_comm] using heq.symm)
  have hd := RootI30.disjoint_closure_translated_hull hα hW hW0 hγ hwc hw0 hv0 hx harc hsep
  have hKU : fwdHull U s = fwdHull (Ito.rpath (W · ω)) s := GaugeE.record_hull_eq s hW0 hW.continuousOn hsζ
  have hd' : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun t => Ito.rpath w t + x) v)) := by
    rw [hKU]; exact hd
  have hdA := Supp8.Q3Rel.disjoint_closure_invHull hU s.coe_nonneg hd'
  rw [ConformalImageFull.fwdHull_add_const (Ito.rpath w) x v] at hdA
  -- the translated explored hull at `t`
  set K : Set ℂ := (fun z : ℂ => z + x) '' fwdHull (Ito.rpath w) t with hKdef
  have hwr : Continuous (Ito.rpath w) := hwc.comp continuous_real_toNNReal
  have hKv : K ⊆ (fun z : ℂ => z + x) '' fwdHull (Ito.rpath w) v :=
    image_mono (WangWu.fwdHull_mono (NNReal.coe_le_coe.2 htv.le))
  have hKH : K ⊆ H := by
    rintro _ ⟨y, hy, rfl⟩
    have hyH : 0 < y.im := (isHPHull_fwdHull hwr t.coe_nonneg).1 hy
    change 0 < (y + (x : ℂ)).im
    rw [add_im, ofReal_im, add_zero]
    exact hyH
  have hKA : ∀ z ∈ K, z ∉ Supp8.Q3Rel.invHull U s := fun z hz hzA =>
    disjoint_left.1 hdA (subset_closure (hKv hz)) (subset_closure hzA)
  have hKD : K ⊆ H \ Supp8.Q3Rel.invHull U s := fun z hz => ⟨hKH hz, hKA z hz⟩
  have hKrel : K ⊆ CoordB.relDomain U s := by
    intro z hz
    refine (CoordB.mem_relDomain_iff U s z).2 ⟨hKH hz, fun hzU => hKA z hz ⟨-z⁻¹, hzU, neg_inv_neg_inv z⟩⟩
  -- the forward hull reader is the relative image of the translated hull
  have hfwdH : RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) = relMap U s '' K := by
    unfold RootH29.forwardHull RootH29.translatedHull
    have h1 : fwdHull (rdrv (recOf (t : ℝ≥0∞) (w, ⊤))) t = fwdHull (Ito.rpath w) t :=
      RootZ21.fwdHull_record_of_live he ENNReal.coe_lt_top
    have h2 : (fun z : ℂ => (x : ℂ) + z) '' fwdHull (Ito.rpath w) t = K := by
      rw [hKdef]
      refine image_congr fun z _ => add_comm _ _
    simp only
    rw [h1, h2, inter_eq_left.2 hKrel]
  -- the root's chart image
  have hsafe0 : (x : ℂ) ∈ CoordB.relSafe U s := by
    have h := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv' (zero_le : (0 : ℝ≥0) ≤ v)
    rwa [hγ.1, add_zero] at h
  have hbase : baseRead x s (cfRec s W ζ ω) = GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) := by
    unfold baseRead GW2Bf.relBase
    rw [RootA22.boundaryRead_eq_relBdry s _ hsafe0]
  -- the record chart is the joint chart
  have hrt : rtime (cfRec s W ζ ω) = s := by
    unfold cfRec
    rw [rtime_recOf_coe, GW2JointKernel.cfE_snd, hζ, min_top_right, ENNReal.toNNReal_coe]
  have hdc := Supp8.Q3Rel.isDomainChart_rel hU hU0 s.coe_nonneg
  rw [hR, hfwdH]
  have hrc : ∀ S : Set ℂ, (relChartX x s (cfRec s W ζ ω)).2.1 '' S =
      (Supp8.RelSafeS.relChart (cfRec s W ζ ω)).2.1 ''
        ((fun z : ℂ => z + (baseRead x s (cfRec s W ζ ω) : ℂ)) '' S) := fun S => by
    rw [image_image]; rfl
  rw [hrc, hbase, image_add_real_compl, Supp8.RelSafeS.relChart_eq_jointChart hrt,
    show relMap U s = (GW2JointKernel.jointChart U s).1 from rfl,
    Supp8.RelSafeS.image_inv_compl_image_fwd hdc.1 hdc.2.1 hKD, sdiff_sdiff]

end ShapeSample

/-! ### The shape of the root-`x` physical union -/

section Shape

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {x₀ : ℝ} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)

include hGT hs₀ hx₀ in
/-- **The complement of the root-`x` physical union is the inverse re-centred chart image of the complement of the
relative hull** (GB6's `RelSafeS.ae_compl_union_eq_relChart` at a root `x₀`), almost surely on the good event
before the stop. -/
theorem ae_compl_union_eq_relChartX (hver : IsRelVersionX x₀ s P Wα ζα W γ α R V) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ GT → min (physClockX x₀ s Wα ζα W GT t ω) (V ω) < V ω →
      H \ (Supp8.Q3Rel.invHull (rdrv (cfRec s Wα ζα ω)) s ∪
          (fun z : ℂ => z + x₀) '' fwdHull (fun r : ℝ => W r.toNNReal ω) t) =
        (relChartX x₀ s (cfRec s Wα ζα ω)).2.1 ''
          (H \ fwdHull (Ito.rpath fun u => R u ω) (min (physClockX x₀ s Wα ζα W GT t ω) (V ω)).toNNReal) := by
  filter_upwards [hver.2.2.2.2.2.2] with ω hω hωG hlt
  have hg := hGT ω hωG
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hWc, hW0, hζ⟩, harc, -, hgx⟩ := hg
  obtain ⟨-, hreachV, hhull⟩ := hω hgx
  obtain ⟨hfc, hfm, hf0⟩ := clockX_props hGT hs₀ hx₀ hωG
  -- `t` is before the root-`x` contact
  have htc : (t : ℝ≥0∞) < contactX x₀ s γ α ω := by
    by_contra hcon
    have hle : contactX x₀ s γ α ω ≤ t := le_of_not_gt hcon
    have hV : V ω ≤ physClockX x₀ s Wα ζα W GT t ω := by
      rw [physClockX_eq_iSup hGT hs₀ hx₀ hωG]
      refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
      obtain ⟨t', ht', hut'⟩ := hreachV u hu
      have ht't : t' < t := by
        have := lt_of_lt_of_le ht' hle
        exact_mod_cast this
      refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < contactX x₀ s γ α ω) =>
        ENNReal.ofReal (clockX x₀ s Wα ζα W t' ω)) t' ⟨ht't, ht'⟩)
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hut'.le
    rw [min_eq_right hV] at hlt
    exact lt_irrefl _ hlt
  have hphys := physClockX_eq_clockX hGT hs₀ hx₀ hωG htc
  have h0 := (clock_props Wα ζα ω hα hWc hW0 hζ hs₀ hx₀ harc hwc hw0 hγ).1
  have hm := (clock_props Wα ζα ω hα hWc hW0 hζ hs₀ hx₀ harc hwc hw0 hγ).2.1
  have hnn : 0 ≤ clockX x₀ s Wα ζα W t ω := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact h0.ge
    · have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < contactX x₀ s γ α ω := lt_of_le_of_lt bot_le htc
      exact le_of_lt (lt_of_eq_of_lt h0.symm (hm h0T htc h))
  have hlt' : ENNReal.ofReal (clockX x₀ s Wα ζα W t ω) < V ω := by
    rw [hphys] at hlt
    exact lt_of_not_ge fun h => lt_irrefl _ (by rwa [min_eq_right h] at hlt)
  have hmin : min (physClockX x₀ s Wα ζα W GT t ω) (V ω) = ENNReal.ofReal (clockX x₀ s Wα ζα W t ω) := by
    rw [hphys]
    exact min_eq_left hlt'.le
  have hreal : (((ENNReal.ofReal (clockX x₀ s Wα ζα W t ω)).toNNReal : ℝ≥0) : ℝ) = clockX x₀ s Wα ζα W t ω := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnn]
  have hH' : fwdHull (fun r : ℝ => R r.toNNReal ω)
        (RootH29.forwardCapacity x₀ s t (cfRec s Wα ζα ω, recOf (t : ℝ≥0∞) ((fun t => W t ω), ⊤))) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x₀ s (cfRec s Wα ζα ω, recOf (t : ℝ≥0∞) ((fun t => W t ω), ⊤)) : ℝ) :
        ℂ)) '' RootH29.forwardHull x₀ s t (cfRec s Wα ζα ω, recOf (t : ℝ≥0∞) ((fun t => W t ω), ⊤)) :=
    hhull t htc hlt'.le
  have key := compl_union_eq_relChartX Wα ζα ω (α := α ω) (s := s) (x := x₀) (w := fun t => W t ω)
    (γ := γ ω) hα hWc hW0 hζ hx₀ harc hwc hw0 hγ (t := t) htc (R := fun u => R u ω) hH'
  rw [hmin, hreal]
  exact key

include hGT hs₀ hx₀ in
/-- **The stage shape of the root-`x` physical union** (GW2Sde's `shape_of_union` at a root `x₀`): when the union is
the counterflow's retained set together with the explored hull at `T + t` translated to the root, the shape target
holds on every event inside the good records. -/
theorem shape_of_unionX (hver : IsRelVersionX x₀ s P Wα ζα W γ α R V)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s) {F : Set Ω}
    (hF : ∀ᵐ ω ∂P, ω ∈ F → cfRec s Wα ζα ω ∈ goodX x₀ s) (T : ℝ≥0) {B : ℝ≥0 → Ω → Set ℂ}
    (hB : ∀ t ω, B t ω = Supp8.Q3Rel.invHull (rdrv (cfRec s Wα ζα ω)) s ∪
      (fun z : ℂ => z + x₀) '' fwdHull (fun r : ℝ => W r.toNNReal ω) ((T + t : ℝ≥0) : ℝ)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) < V ω →
      H \ B t ω = (relChartX x₀ s (cfRec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => R u ω) (min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω)).toNNReal) := by
  filter_upwards [ae_compl_union_eq_relChartX hGT hs₀ hx₀ hver (T + t), hGTae, hF] with ω h1 h2 h3 hωF hlt
  rw [hB]
  exact h1 (h2.2 (h3 hωF)) hlt

end Shape

end InteractingSLE.Theorem14.GW2Rz
