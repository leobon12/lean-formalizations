/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeGB6Drv

/-!
# GB6's relative driver read in the physical history, part 3: the physical clock

Packet PROVE-GB6-RELSAFE. The physical clock of part 2 is GB6's relative clock stopped at the first contact:

* `continuous_supBelow` (generic): `t ↦ sup_{t' < t, t' < L} f t'` is continuous for `f` continuous, monotone on
  `[0, L)` with `f 0 = 0` (it is `f` before `L` and constant after);
* **`physClock_eq_iSup`**: on the good event, `physClock t = sup_{t' < t, t' < T_c} a(t')` (`a` = `gb6Clock`);
* **`physClock_eq_gb6Clock`**: before the first contact, `physClock t = a(t)`;
* `physClock_zero`, `monotone_physClock`, **`continuous_physClock`** (every sample).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Supp8.RelSafe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Sec7.Lemma71C Sec7.PocketTraversal

/-! ### Suprema below a time -/

section Sup

/-- `sup_{t' < t, t' < L} f t'`. -/
def supBelow (f : ℝ≥0 → ℝ≥0∞) (L : ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < L), f t'

variable {f : ℝ≥0 → ℝ≥0∞} {L : ℝ≥0∞}

theorem monotone_supBelow : Monotone (supBelow f L) := fun _ _ hst =>
  iSup₂_mono' fun t' ht' => ⟨t', ⟨ht'.1.trans_le hst, ht'.2⟩, le_rfl⟩

theorem supBelow_zero : supBelow f L 0 = 0 :=
  ENNReal.iSup_eq_zero.2 fun t' => ENNReal.iSup_eq_zero.2 fun h => absurd h.1 (not_lt_zero (a := t'))

theorem supBelow_eq_of_lt (hf : ContinuousOn f {t | (t : ℝ≥0∞) < L}) (hm : MonotoneOn f {t | (t : ℝ≥0∞) < L})
    (h0 : f 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < L) : supBelow f L t = f t := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
  · subst h; rw [supBelow_zero, h0]
  refine le_antisymm (iSup₂_le fun t' ht' => hm ht'.2 ht ht'.1.le) ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ContinuousAt f t := hf.continuousAt (hopen.mem_nhds ht)
  have hne : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h⟩
  have hlim : Tendsto f (𝓝[<] t) (𝓝 (f t)) := hca.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t' ht'
  exact le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < L) => f t') t'
    ⟨ht', (ENNReal.coe_lt_coe.2 ht').trans ht⟩

theorem supBelow_eq_of_le {t t₂ : ℝ≥0} (ht : L ≤ t) (ht₂ : L ≤ t₂) : supBelow f L t₂ = supBelow f L t := by
  unfold supBelow
  refine iSup_congr fun t' => ?_
  have h : ∀ u : ℝ≥0, L ≤ u → (t' < u ∧ (t' : ℝ≥0∞) < L ↔ (t' : ℝ≥0∞) < L) := fun u hu =>
    ⟨fun h => h.2, fun h => ⟨ENNReal.coe_lt_coe.1 (h.trans_le hu), h⟩⟩
  simp only [h t ht, h t₂ ht₂]

/-- **Continuity of the stopped clock.** -/
theorem continuous_supBelow (hf : ContinuousOn f {t | (t : ℝ≥0∞) < L})
    (hm : MonotoneOn f {t | (t : ℝ≥0∞) < L}) (h0 : f 0 = 0) : Continuous (supBelow f L) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  rcases lt_trichotomy (t : ℝ≥0∞) L with ht | ht | ht
  · have hev : supBelow f L =ᶠ[𝓝 t] f := by
      filter_upwards [hopen.mem_nhds ht] with t' ht'
      exact supBelow_eq_of_lt hf hm h0 ht'
    exact (hf.continuousAt (hopen.mem_nhds ht)).congr hev.symm
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · rw [← continuousWithinAt_Iio_iff_Iic]
      have hlim := (monotone_supBelow (f := f) (L := L)).tendsto_nhdsLT t
      have hsup : sSup (supBelow f L '' Iio t) = supBelow f L t := by
        refine le_antisymm (sSup_le ?_) ?_
        · rintro _ ⟨t', ht', rfl⟩
          exact monotone_supBelow ht'.le
        · refine iSup₂_le fun t' ht' => ?_
          rw [← supBelow_eq_of_lt hf hm h0 ht'.2]
          exact le_sSup ⟨t', ht'.1, rfl⟩
      rw [hsup] at hlim
      exact hlim
    · refine (continuousWithinAt_const (b := supBelow f L t)).congr (fun t' ht' => ?_) rfl
      exact supBelow_eq_of_le ht.ge (ht.ge.trans (ENNReal.coe_le_coe.2 ht'))
  · have hopen' : IsOpen {t' : ℝ≥0 | L < (t' : ℝ≥0∞)} := isOpen_lt continuous_const ENNReal.continuous_coe
    have hev : supBelow f L =ᶠ[𝓝 t] fun _ => supBelow f L t := by
      filter_upwards [hopen'.mem_nhds ht] with t' ht'
      exact supBelow_eq_of_le ht.le ht'.le
    exact continuousAt_const.congr hev.symm

end Sup

/-! ### The physical clock on the good event -/

section Clock

variable {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω)

include hGT in
/-- **The local event on the good event**: a positive horizon before the first contact. -/
theorem mem_locEv_iff {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    ω ∈ locEv s W Wα ζα GT T ↔ 0 < T ∧ (T : ℝ≥0∞) < gb6Tc s γ α ω := by
  refine ⟨fun h => ⟨h.1.1, lt_gb6Tc_of_mem_locEv hGT h⟩, fun h => ⟨⟨h.1, hω⟩, ?_⟩⟩
  have hg := hGT ω hω
  have hγc := continuous_γ hg
  have hA := continuous_sepRec hGT (s := s) (Wα := Wα) (ζα := ζα) ω
  have e : SourceC.prefixGap (sepTr W GT T ω) (sepRec s Wα ζα GT ω) T s =
      SourceC.prefixGap (γ ω) (sepRec s Wα ζα GT ω) T s := by
    unfold SourceC.prefixGap
    refine iInf_congr fun p => ?_
    rw [sepTr_of_mem hGT hω]
    simp only [min_eq_left p.1.2.2]
  show 0 < SourceC.prefixGap (sepTr W GT T ω) (sepRec s Wα ζα GT ω) T s
  rw [e]
  refine (SourceC.lt_firstContactTime_iff hγc hA T s).1 ?_
  rw [SourceC.firstContactTime_eq_of_prefix_eq (α := α ω) (fun v hv => by
    rw [sepRec_of_mem hGT hω]; exact congrArg (α ω) (min_eq_left hv))]
  exact h.2

include hGT in
/-- **The local lifetime is the supremum of the relative clock before the horizon.** -/
theorem capLife_gb6Curve_eq {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv s W Wα ζα GT T) :
    capLife (gb6Curve s W Wα ζα T ω) =
      ⨆ (t' : ℝ≥0) (_ : t' < T), ENNReal.ofReal (gb6Clock s W Wα ω t') := by
  have hωG := hω.1.2
  have hT : 0 < T := hω.1.1
  have hs0 := pos_of_physGood (hGT ω hωG)
  obtain ⟨⟨hWc, hW0, hγt⟩, ⟨h0, hc, hα⟩, hs, -, -, htip⟩ := hGT ω hωG
  have hTc := lt_gb6Tc_of_mem_locEv hGT hω
  have hγ : IsGeneratingTrace (fun t => W t ω) ⊤ (phTr W ω) := by
    rw [phTr_eq (hGT ω hωG)]; exact hγt
  have hd : Disjoint (closure (fwdHull (rdrv (gb6Rec s Wα ζα ω)) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath (fun t => W t ω)) T)) := by
    rw [GaugeE.record_hull_eq s h0 hc hs]
    exact GB6.disjoint_closure_fwdHull_of_lt_firstContactTime hα hc h0 hγt hWc.continuousOn hW0 hs
      ENNReal.coe_lt_top hTc
  have hclk : ∀ t' : ℝ≥0, gb6Clock s W Wα ω t' =
      relClock (rdrv (gb6Rec s Wα ζα ω)) s (Ito.rpath (fun t => W t ω)) t' := fun t' => by
    rw [gb6Clock, GaugeE.record_relClock_eq s h0 hc hs]
    rfl
  have hiff := CoordB.lt_localLife_iff (continuous_rdrv _) (rdrv_zero _) hs0 htip hWc hW0 hγ hT hd
  refine le_antisymm (ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
    (iSup₂_le fun t' ht' => ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
  · obtain ⟨t', ht', hrt⟩ := (hiff r).1 hr
    refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < T) =>
      ENNReal.ofReal (gb6Clock s W Wα ω t')) t' ht')
    rw [hclk, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hrt.le
  · refine ((hiff r).2 ⟨t', ht', ?_⟩).le
    rw [← hclk]
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).1 hr

include hGT in
/-- **The physical clock on the good event** is GB6's relative clock stopped at the first contact. -/
theorem physClock_eq_iSup {t : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    physClock s W Wα ζα GT t ω =
      supBelow (fun t' => ENNReal.ofReal (gb6Clock s W Wα ω t')) (gb6Tc s γ α ω) t := by
  refine le_antisymm (iSup_le fun k => ?_) (iSup₂_le fun t' ht' => ?_)
  · unfold locLife
    by_cases hk : ω ∈ locEv s W Wα ζα GT (hz t k)
    · rw [indicator_of_mem hk, capLife_gb6Curve_eq hGT hk]
      have hTc := lt_gb6Tc_of_mem_locEv hGT hk
      refine iSup₂_le fun t' ht' => ?_
      exact le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < gb6Tc s γ α ω) =>
        ENNReal.ofReal (gb6Clock s W Wα ω t')) t'
        ⟨ht'.trans_le (hz_le t k), (ENNReal.coe_lt_coe.2 ht').trans hTc⟩
    · rw [indicator_of_notMem hk]
      exact zero_le
  · have hlt : (t' : ℝ≥0∞) < min (t : ℝ≥0∞) (gb6Tc s γ α ω) :=
      lt_min (ENNReal.coe_lt_coe.2 ht'.1) ht'.2
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hqt : (q : ℝ) < t := by
      have h := hq2.trans_le (min_le_left _ _)
      rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe (by exact_mod_cast hq0)] at h
      exact h
    obtain ⟨k, hk⟩ := exists_hz_eq hqt
    have hmem : ω ∈ locEv s W Wα ζα GT (hz t k) := by
      rw [mem_locEv_iff hGT hω, hk]
      refine ⟨lt_of_le_of_lt zero_le (ENNReal.coe_lt_coe.1 hq1), hq2.trans_le (min_le_right _ _)⟩
    refine le_trans ?_ (le_iSup _ k)
    rw [locLife, indicator_of_mem hmem, capLife_gb6Curve_eq hGT hmem]
    exact le_iSup₂ (f := fun (t'' : ℝ≥0) (_ : t'' < hz t k) =>
      ENNReal.ofReal (gb6Clock s W Wα ω t'')) t' (by rw [hk]; exact ENNReal.coe_lt_coe.1 hq1)

end Clock

end InteractingSLE.Supp8.RelSafe
