/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocRat
import InteractingSLE.Spec.Supplement.GW4SafeRClipSet
import InteractingSLE.Spec.Sec5.GlueCondHit
import InteractingSLE.Spec.Sec7.Lemma71Capacity

/-!
# GW4: the chart set of the union lies in the relative hull, and the relative hull in the safe hull

Packet PROVE-GW4-CLOC, step 4 (deterministic geometry).

* `chartSet_subset_relHullFam`: for a component `C` disjoint from the walks `S`, the chart set of
  `relClosureH (S ∪ K_t)` (`K_t` the counterflow hull read from a good history) is contained in the relative hull
  `relHullFam c C w t` (a point of `C` in the relative closure of the union is in `K_t`, which is relatively closed;
  the inverted chart maps it into the relative hull);
* `lt_exit_of_lineClock_lt`, **`hullAt_subset_fwdHull_of_lineClock_lt`**: on the safe event `{lineClock t < V}` the
  physical time `t` is before the exit, and the relative hull at `t` is the hull of the version at `lineClock t`
  (`Frame.physClockG_eq_rcap`, `Frame.fwdHull_eq_hullAt_of_version`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets GW4Traverse GW4Rel Sec5.GlueCond

/-- **The chart set of the union lies in the relative hull.** -/
theorem chartSet_subset_relHullFam {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) {S : Set ℂ} (hSC : Disjoint S C) {y : LawUnique.HistorySpace 0 0}
    (hy : y ∈ Sec5.CfRegQ.goodCfSet) {w : ℝ≥0 → ℝ} (hw : Sec5.Prop411Q.cfDrv y = fun s : ℝ => w s.toNNReal) (t : ℝ≥0) :
    chartSet c (relClosureH (S ∪ cfHullQ t y)) ⊆ relHullFam c C w t := by
  intro v hv
  have hconf := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  have hvH : v ∈ H := chartSet_subset_H _ _ hv
  rw [mem_chartSet_iff hconf hvH] at hv
  have hzC : c.2.1 (-v⁻¹) ∈ C := hch.2.2.1 (negInv_mem_H hvH)
  have hzK : c.2.1 (-v⁻¹) ∈ cfHullQ t y := by
    obtain ⟨hzH, hzcl⟩ := hv
    have hcl : closure ((S ∪ cfHullQ t y) ∩ H) ⊆ closure S ∪ closure (cfHullQ t y) := by
      rw [← closure_union]
      exact closure_mono inter_subset_left
    rcases hcl hzcl with h1 | h1
    · exact absurd hzC (Set.disjoint_left.1 (hSC.closure_left hCo) h1)
    · by_contra hzn
      obtain ⟨a, ha1, ha2⟩ := mem_closure_iff.1 h1 (H \ cfHullQ t y) (cfHullQ_relClosed t y).2 ⟨hzH, hzn⟩
      exact ha1.2 ha2
  rw [cfHullQ_eq_of_mem_goodCfSet hy t, hw] at hzK
  obtain ⟨w₀, hw₀, hzw₀⟩ := hzK
  have hzw₀' : -w₀⁻¹ = c.2.1 (-v⁻¹) := hzw₀
  refine ⟨w₀, ⟨hw₀, ?_⟩, ?_⟩
  · show -w₀⁻¹ ∈ C
    rw [hzw₀']
    exact hzC
  · show -(c.1 (-w₀⁻¹))⁻¹ = v
    rw [hzw₀', hch.2.2.2.1.2 (negInv_mem_H hvH), inv_neg, inv_inv, neg_neg]

section Clock

variable {F : Frame} (hF : F.IsOk) {Ω : Type*} {Wd : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
include hF hGT

/-- On the safe event the physical time is before the exit. -/
theorem lt_exit_of_lineClock_lt {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous fun t => R t ω) (hR0 : R 0 ω = 0)
    (hver : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ω →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal ω) s = F.hullAt (fun u => Wd u ω) t)
    {t : ℝ≥0} (hlt : lineClock F Wd GT V t ω < V ω) : (t : ℝ≥0∞) < F.exit (fun u => Wd u ω) := by
  have hw := hGT ω hω
  set w : ℝ≥0 → ℝ := fun u => Wd u ω with hw_def
  have hP : F.physClockG Wd GT t ω < V ω := by
    by_contra hge
    exact (lt_irrefl _) (hlt.trans_le (le_min (not_lt.1 hge) le_rfl))
  have hℓ : lineClock F Wd GT V t ω = F.physClockG Wd GT t ω := min_eq_left hP.le
  have hfin : F.physClockG Wd GT t ω ≠ ⊤ := (hP.trans_le le_top).ne
  by_contra hex
  rw [not_lt] at hex
  set s : ℝ≥0 := (F.physClockG Wd GT t ω).toNNReal with hs_def
  have hsP : (s : ℝ≥0∞) = F.physClockG Wd GT t ω := ENNReal.coe_toNNReal hfin
  obtain ⟨t₃, ht₃⟩ := hver s (hsP.symm ▸ hP)
  have hRc' : Continuous fun r : ℝ => R r.toNNReal ω := hRc.comp continuous_real_toNNReal
  have hR0' : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp [hR0]
  have hb : Bornology.IsBounded (F.hullAt w t₃) :=
    ht₃ ▸ (isHPHull_fwdHull hRc' s.coe_nonneg).2.1
  have ht₃e := Frame.lt_exit_of_isBounded hF hw hb
  have hcap := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hRc' hR0' s.coe_nonneg ht₃
  have hr₃ : F.rcap w t₃ = s := by
    rw [Frame.rcap, hcap]; ring
  set t₄ : ℝ≥0 := max t₃ (F.ent w) with ht₄
  have hr₄ : F.rcap w t₄ = s := by
    rcases le_total t₃ (F.ent w) with h' | h'
    · rw [ht₄, max_eq_right h', Frame.rcap_eq_zero_of_le hF hw le_rfl, ← hr₃, Frame.rcap_eq_zero_of_le hF hw h']
    · rw [ht₄, max_eq_left h', hr₃]
  have ht₄e : (t₄ : ℝ≥0∞) < F.exit w := by
    rw [ht₄, ENNReal.coe_max]
    exact max_lt ht₃e (Frame.ent_lt_exit hF hw)
  obtain ⟨T, hT, hloc⟩ := Frame.exists_isLoc_gt hF hw ht₄e
  set t₅ : ℝ≥0 := (t₄ + T) / 2 with ht₅
  have h45 : t₄ < t₅ := by rw [ht₅]; exact left_lt_add_div_two.2 hT
  have h5T : t₅ < T := by rw [ht₅]; exact add_div_two_lt_right.2 hT
  have ht₅e : (t₅ : ℝ≥0∞) < F.exit w := (ENNReal.coe_lt_coe.2 h5T).trans hloc.2.2
  have hstrict : F.rcap w t₄ < F.rcap w t₅ :=
    Frame.rcap_strictMono hF hloc (le_max_right _ _) h45 h5T
  have hge : ENNReal.ofReal (F.rcap w t₅) ≤ F.physClockG Wd GT t ω := by
    rw [Frame.physClockG_eq_supBelow hF hGT hω]
    refine le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < F.exit w) =>
      ENNReal.ofReal (F.rcap w t')) t₅ ⟨?_, ht₅e⟩
    exact ENNReal.coe_lt_coe.1 (ht₅e.trans_le hex)
  have hlt' : ENNReal.ofReal (F.rcap w t₄) < ENNReal.ofReal (F.rcap w t₅) :=
    (ENNReal.ofReal_lt_ofReal_iff ((hr₄ ▸ s.coe_nonneg).trans_lt hstrict)).2 hstrict
  rw [hr₄, ENNReal.ofReal_coe_nnreal, hsP] at hlt'
  exact (lt_irrefl _) (hlt'.trans_le hge)

/-- **On the safe event the relative hull at `t` is contained in the hull of the version at `lineClock t`.** -/
theorem hullAt_subset_fwdHull_of_lineClock_lt {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous fun t => R t ω) (hR0 : R 0 ω = 0)
    (hver : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ω →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal ω) s = F.hullAt (fun u => Wd u ω) t)
    {t : ℝ≥0} (hlt : lineClock F Wd GT V t ω < V ω) :
    F.hullAt (fun u => Wd u ω) t ⊆
      fwdHull (fun r : ℝ => R r.toNNReal ω) (lineClock F Wd GT V t ω).toNNReal := by
  have hw := hGT ω hω
  rcases le_total t (F.ent fun u => Wd u ω) with hte | hte
  · rw [Frame.hullAt_eq_empty_of_le hF hw hte]
    exact empty_subset _
  have hex := lt_exit_of_lineClock_lt hF hGT hω hRc hR0 hver hlt
  have hP : F.physClockG Wd GT t ω < V ω := by
    by_contra hge
    exact (lt_irrefl _) (hlt.trans_le (le_min (not_lt.1 hge) le_rfl))
  have hℓ : lineClock F Wd GT V t ω = F.physClockG Wd GT t ω := min_eq_left hP.le
  have hrc := Frame.physClockG_eq_rcap hF hGT hω hex
  set s : ℝ≥0 := (lineClock F Wd GT V t ω).toNNReal with hs_def
  have hsr : (s : ℝ) = F.rcap (fun u => Wd u ω) t := by
    rw [hs_def, ENNReal.coe_toNNReal_eq_toReal, hℓ, hrc, ENNReal.toReal_ofReal (Frame.rcap_nonneg hF hw hex)]
  have hsV : (s : ℝ≥0∞) < V ω := by
    rw [hs_def, ENNReal.coe_toNNReal (hlt.trans_le le_top).ne]
    exact hlt
  obtain ⟨t₃, ht₃⟩ := hver s hsV
  have hRc' : Continuous fun r : ℝ => R r.toNNReal ω := hRc.comp continuous_real_toNNReal
  have hR0' : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp [hR0]
  rw [Frame.fwdHull_eq_hullAt_of_version hF hw hRc' hR0' ht₃ hte hex hsr]

end Clock

end InteractingSLE.Theorem14.GW4Fix.CLoc
