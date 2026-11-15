/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Chain
import InteractingSLE.Spec.Supplement.GW2RootI30Disjoint
import InteractingSLE.Spec.Supplement.GW2RootH29Actual
import InteractingSLE.Spec.Supplement.GW2RootF14Extension

/-!
# The Borel low-arc reader is the actual relative capacity clock

Packet PROVE-T14-GW2ROOT2. Extend only a protected physical prefix using
the landed complete-model theorem. The untouched real connector proves
the required hull separation. The translated chain theorem then identifies
the concrete reader and proves its strict increase and continuity.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB ConformalImageFull

/-- The low-arc capacity reader is an intrinsic relative Loewner clock.
The original source traces supply every geometric and clock conclusion. -/
theorem exists_reader_chain {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    let a := fun t => RootH29.forwardCapacity x s t p
    ∃ V : ℝ → ℝ, Continuous V ∧ a 0 = 0 ∧
      StrictMonoOn a (Icc 0 v) ∧ ContinuousOn a (Icc 0 v) ∧
      ∀ t ∈ Icc 0 v,
        a t = relClock (Ito.rpath (W · ω)) s (fun q => Ito.rpath e.1 q + x) t ∧
        fwdHull V (a t) = RootH29.forwardHull x s t p ∧
        IsFilling (RootH29.forwardHull x s t p)
          (relMap (Ito.rpath (W · ω)) s '' ((fun q => γ q + x) '' Icc 0 t ∩ H)) := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let a := fun t => RootH29.forwardCapacity x s t p
  let U := Ito.rpath (W · ω)
  obtain ⟨D, hvD, hDS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hv
  have hvD' : v < D := ENNReal.coe_lt_coe.mp hvD
  have hD : 0 < D := lt_of_le_of_lt zero_le hvD'
  obtain ⟨wc, γc, b, hDb, hwc, hwc0, hγc, hew, heγ⟩ :=
    RootF14.exists_complete_prefix_model hγ he.1 he.2.1 (lt_min_iff.mp hDS).2
  let WC : ℝ → ℝ := fun q => Ito.rpath wc q + x
  have hWC : Continuous WC := (hwc.comp continuous_real_toNNReal).add continuous_const
  have hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => γc t + x) '' Icc 0 D \ {0})) := by
    apply disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨_, ⟨⟨t, ht, rfl⟩, hn⟩, heq⟩
    change γc t + (x : ℂ) ≠ 0 at hn
    change -(γc t + (x : ℂ))⁻¹ = α u at heq
    rw [heγ ⟨zero_le, ht.2.trans hDb.le⟩] at hn heq
    have htn := (ENNReal.coe_le_coe.mpr ht.2).trans_lt (lt_min_iff.mp hDS).1
    apply notMem_of_lt_firstContactTime htn
    refine ⟨u, hu, ?_⟩
    have hn' : (x : ℂ) + γ t ≠ 0 := by simpa only [add_comm] using hn
    rw [sphereInv_coe_of_ne hn']
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (by simpa only [add_comm] using heq.symm)
  have hd := disjoint_closure_translated_hull hα hW hW0 hγc hwc hwc0 hD hx harc hsep
  have hU : Continuous U := hW.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simpa only [U, Ito.rpath, Real.toNNReal_zero] using hW0
  have htip := hα.tendsto_fwdMapInv_tip hW.continuousOn hW0
    (show (s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  obtain ⟨V, hV, h0, hm, hc, hK⟩ := exists_relative_chain hWC hU hU0
    (by exact_mod_cast hs) (by exact_mod_cast hD) htip hd
  have hrec := GaugeE.record_prefix_eq s hW0 hW.continuousOn
    (show (s : ℝ≥0∞) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap (rdrv p.1) s = relMap U s := relMap_eq_of_eqOn s.coe_nonneg hrec
  have hphys : ∀ t ∈ Icc 0 v, fwdHull WC t =
      fwdHull (fun q => Ito.rpath e.1 q + x) t := by
    intro t ht
    simp only [WC, fwdHull_add_const]
    have heq := RootF14.fwdHull_eq_of_prefix_eq hew ((ht.2.trans hvD'.le).trans_lt hDb)
    change fwdHull (Ito.rpath wc) t = fwdHull (Ito.rpath e.1) t at heq
    rw [heq]
  have hrecord : ∀ t ∈ Icc 0 v, RootH29.translatedHull x t p.2 = fwdHull WC t := by
    intro t ht
    unfold RootH29.translatedHull
    rw [RootZ21.fwdHull_record_of_le_of_live he (lt_min_iff.mp hv).2 ht.2,
      hphys t ht, fwdHull_add_const]
    exact image_congr fun z _ => add_comm _ _
  have hforward : ∀ t ∈ Icc 0 v, RootH29.forwardHull x s t p =
      relMap U s '' fwdHull WC t := by
    intro t ht
    have hsub : fwdHull WC t ⊆ relDomain (rdrv p.1) s := by
      intro z hz
      apply (mem_relDomain_iff _ _ _).mpr
      refine ⟨(isHPHull_fwdHull hWC t.coe_nonneg).1 hz, ?_⟩
      have hUK : fwdHull (rdrv p.1) s = fwdHull U s :=
        GaugeE.record_hull_eq s hW0 hW.continuousOn
          (by rw [hζ]; exact ENNReal.coe_lt_top)
      rw [hUK]
      exact fun hbad => disjoint_left.mp hd (subset_closure hbad)
        (subset_closure ⟨z, (QuantumZipper.fwdHull_mono (W := WC)).1
          (show (t : ℝ) ≤ D by exact_mod_cast ht.2.trans hvD'.le) hz, rfl⟩)
    unfold RootH29.forwardHull
    rw [hrecord t ht, inter_eq_left.mpr hsub, hmap]
  have heclock : EqOn a (fun t : ℝ≥0 => relClock U s WC t) (Icc 0 v) := by
    intro t ht
    have htD : (t : ℝ) ∈ Icc (0 : ℝ) (D : ℝ) :=
      ⟨t.coe_nonneg, by exact_mod_cast ht.2.trans hvD'.le⟩
    have hHull : IsHPHull (relMap U s '' fwdHull WC t) := by
      rw [← (hK t htD).2]
      exact isHPHull_fwdHull hV (hK t htD).1
    change (WholeField.hcapHit (RootH29.forwardHull x s t p)).toReal / 2 = _
    rw [hforward t ht, WholeField.IsHPHull.hcapHit_eq hHull]
    rw [ENNReal.toReal_ofReal (HPHull.hcap_nonneg ⟨_, hHull⟩)]
    exact congrArg (· / 2) (ConformalImage.hcapSet_eq hHull).symm
  have hmaps : MapsTo ((↑) : ℝ≥0 → ℝ) (Icc 0 v) (Icc 0 D) :=
    fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht.2.trans hvD'.le⟩
  change ∃ V : ℝ → ℝ, Continuous V ∧ a 0 = 0 ∧
    StrictMonoOn a (Icc 0 v) ∧ ContinuousOn a (Icc 0 v) ∧
    ∀ t ∈ Icc 0 v, a t = relClock U s (fun q => Ito.rpath e.1 q + x) t ∧
      fwdHull V (a t) = RootH29.forwardHull x s t p ∧
      IsFilling (RootH29.forwardHull x s t p)
        (relMap U s '' ((fun q => γ q + x) '' Icc 0 t ∩ H))
  refine ⟨V, hV, (heclock ⟨zero_le, zero_le⟩).trans h0, ?_, ?_, ?_⟩
  · intro t ht u hu htu
    rw [heclock ht, heclock hu]
    exact hm (hmaps ht) (hmaps hu) (NNReal.coe_lt_coe.mpr htu)
  · exact (hc.comp NNReal.continuous_coe.continuousOn hmaps).congr heclock
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [heclock ht]
      change ConformalImage.hcapSet (relMap U s '' fwdHull WC t) / 2 = _
      rw [hphys t ht]
      rfl
    · rw [heclock ht, (hK t (hmaps ht)).2, hforward t ht]
    · have hfill := isFilling_image_add_full
        (isHPHull_fwdHull (hwc.comp continuous_real_toNNReal) t.coe_nonneg) x
        (hγc.2.2 t ENNReal.coe_lt_top)
      rw [← fwdHull_add_const, image_image] at hfill
      have htrace : (fun q => γc q + (x : ℂ)) '' Icc 0 t =
          (fun q => γ q + (x : ℂ)) '' Icc 0 t := image_congr fun q hq =>
        congrArg (· + (x : ℂ)) (heγ ⟨zero_le,
          ((hq.2.trans ht.2).trans hvD'.le).trans hDb.le⟩)
      rw [htrace] at hfill
      rw [hforward t ht]
      exact isFilling_relMap_image hWC hU hU0 (by exact_mod_cast hs)
        (by exact_mod_cast hD.le) htip hd (hmaps ht) hfill

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
