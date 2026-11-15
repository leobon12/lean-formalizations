/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeLocal

/-!
# BW1's relative driver read in the physical history, part 2: the physical clock and the readable driver

Packet PROVE-BW1-SAFELAW. GB6's `RelSafeGB6Drv` and `RelSafeGB6Clock` with the retained time read from the record.
From the local curves of part 1 with the horizons `T_k(t) = min(q_k, t)` (`RelSafe.hz`):

* `bClock t = sup_k 1_{E_k} capLife(Γ_{T_k})` — BW1's relative clock at physical time `t` stopped at the first
  contact — and `bDrv t u`, the local driver of the first horizon whose curve lives past `u`; both read only the
  record and the physical driver before `t` (**`measurable_bClock`**, **`measurable_bDrv`**);
* **`eq_bDrv_of_version`**: a process whose hulls at the relative clock values are the mapped physical hulls
  (`VersionAtB`, the pathwise content of `IsBW1VersionHulls`) is the readable driver below the clock and the stop;
* **`bClock_eq_iSup`**: on the good event `bClock t = sup_{t' < t, t' < T_c} a(t')` (`a = BW1Ver.rclk`), hence
  `bClock` is continuous, nondecreasing, `0` at `0` for every sample, and equals `a` before the first contact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.ReadD Supp8.RelSafe Sec7.Lemma71C Sec7.PocketTraversal
  BW1Ver

section Defs

variable {Ω : Type*}

/-- The local lifetime with horizon `T` on its event (`0` off it). -/
def locLife (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (locEv rec W GT T).indicator (fun ω => capLife (bCurve rec W T ω)) ω

/-- The local relative driver with horizon `T` on its event (`0` off it). -/
def locDrv (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T u : ℝ≥0) (ω : Ω) : ℝ :=
  (locEv rec W GT T).indicator (CoordB.drivenDriver (bCurve rec W T) u) ω

/-- **BW1's relative clock read in the physical history**: the supremum of the local lifetimes of the horizons
before `t`. -/
def bClock (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k, locLife rec W GT (hz t k) ω

/-- The horizons whose local curve lives past `u`. -/
def validEv (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t u : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | (u : ℝ≥0∞) < locLife rec W GT (hz t k) ω}

/-- **BW1's relative driver read in the physical history**: the local driver of the first horizon before `t` whose
curve lives past `u`. -/
def bDrv (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t u : ℝ≥0) (ω : Ω) : ℝ :=
  locDrv rec W GT (hz t (selIdx (validEv rec W GT t u) ω)) u ω

/-- **The pathwise content of a version with hull identities at one sample**: a continuous relative driver from
`0` whose hulls, at every relative clock value before the first contact and not after the stop, are the mapped
physical hulls. -/
def VersionAtB (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  Continuous (fun t => R t ω) ∧ R 0 ω = 0 ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < bTc rec W ω → ENNReal.ofReal (rclk (rec ω) (W · ω) t) ≤ V ω →
      fwdHull (Ito.rpath (R · ω)) (rclk (rec ω) (W · ω) t) =
        relMap (rdrv (rec ω)) (recS (rec ω)) '' fwdHull (Ito.rpath (W · ω)) t

end Defs

section Meas

variable {Ω : Type*} {m : MeasurableSpace Ω} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {t : ℝ≥0}
  (hGT : ∀ ω ∈ GT, BGood rec W ω) (hrec : Measurable[m] rec)
  (hW : ∀ r ≤ t, Measurable[m] (W r)) (hGTm : MeasurableSet[m] GT)

include hGT hrec hW hGTm

/-- **The physical clock at `t` reads only the record and the physical driver before `t`.** -/
theorem measurable_bClock : Measurable[m] (bClock rec W GT t) := by
  let _ : MeasurableSpace Ω := m
  exact Measurable.iSup fun k => measurable_indicator_localLife hGT hrec hW hGTm (hz_le t k)

/-- **The physical relative driver at `t` reads only the record and the physical driver before `t`.** -/
theorem measurable_bDrv (u : ℝ≥0) : Measurable[m] (bDrv rec W GT t u) := by
  have hidx : Measurable[m] (selIdx (validEv rec W GT t u)) :=
    measurable_selIdx fun k => measurableSet_lt measurable_const
      (measurable_indicator_localLife hGT hrec hW hGTm (hz_le t k))
  exact @Ito.measurable_comp_index Ω ℝ m _ (fun ω k => locDrv rec W GT (hz t k) u ω)
    (fun k => measurable_indicator_localDrv hGT hrec hW hGTm (hz_le t k) u) _ hidx

end Meas

section Ident

variable {Ω : Type*} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, BGood rec W ω)

include hGT in
/-- **A version is the local driver** at every relative time below the local lifetime and the stop (uniqueness of
the Loewner driver of the filled local curve, `IsDrivenCurve.segDrv_eq`). -/
theorem eq_localDrv_of_version {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω}
    (hω : ω ∈ locEv rec W GT T) (hR : VersionAtB rec W R V ω) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < capLife (bCurve rec W T ω)) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = CoordB.drivenDriver (bCurve rec W T) u ω := by
  have hωG := hω.1.2
  have hT : 0 < T := hω.1.1
  have hg := hGT ω hωG
  have hs0 := pos_recS_of_bGood hg
  have hTc := lt_bTc_of_mem_locEv hGT hω
  have hd := hg.disjoint hTc
  have hcv := isDrivenCurve_of_mem_locEv hGT hω
  have hdd : CoordB.drivenDriver (bCurve rec W T) u ω = segDrv (bCurve rec W T ω) u := by
    simp only [CoordB.drivenDriver, hu, ↓reduceIte, segDriver]
  rw [hdd]
  obtain ⟨hRc, hR0, hhull⟩ := hR
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0u | hu0
  · subst h0u
    rw [hR0]
    have h := hcv.segDriver_spec.1
    simp only [segDriver] at h
    exact_mod_cast h.symm
  have hu' : ENNReal.ofReal (u : ℝ) < capLife (bCurve rec W T ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hS0, hSu⟩ := hcv.capInv_spec u.coe_nonneg hu'
  have hSpos : 0 < capInv (bCurve rec W T ω) u := by
    rcases eq_or_lt_of_le hS0 with h | h
    · exfalso
      rw [← h, hcv.capClock_zero] at hSu
      exact (ne_of_lt hu0) (by exact_mod_cast hSu)
    · exact h
  have hK : ∀ τ ∈ Icc 0 (capInv (bCurve rec W T ω) u),
      fwdHull (fun r : ℝ => R r.toNNReal ω) (capClock (bCurve rec W T ω) τ) =
        fillH (bCurve rec W T ω '' Icc 0 τ) := by
    intro τ hτ
    have hτT : clockOf T τ < T := clockOf_lt (by exact_mod_cast hT) hτ.1
    have hτ0 : 0 ≤ clockOf T τ := clockOf_nonneg (by exact_mod_cast hT) hτ.1
    have hcap := CoordB.capClock_localCurve (continuous_rdrv _) (rdrv_zero _) hs0 hg.tip hg.cont hg.zero
      hg.ctrace hd hT hτ.1
    have ht''c : (((clockOf T τ).toNNReal : ℝ≥0) : ℝ) = clockOf T τ := Real.coe_toNNReal _ hτ0
    have hclk : rclk (rec ω) (W · ω) (clockOf T τ).toNNReal = capClock (bCurve rec W T ω) τ := by
      rw [bCurve, hcap, rclk, ht''c]
    have hle : capClock (bCurve rec W T ω) τ ≤ u := by
      rw [← hSu]
      exact hcv.strictMonoOn_capClock.monotoneOn hτ.1 hS0 hτ.2
    have hlt : (((clockOf T τ).toNNReal : ℝ≥0) : ℝ≥0∞) < bTc rec W ω := by
      refine lt_trans (ENNReal.coe_lt_coe.2 ?_) hTc
      exact (Real.toNNReal_lt_iff_lt_coe hτ0).2 hτT
    have hV : ENNReal.ofReal (rclk (rec ω) (W · ω) (clockOf T τ).toNNReal) ≤ V ω := by
      rw [hclk]
      exact (ENNReal.ofReal_le_ofReal hle).trans (by rwa [ENNReal.ofReal_coe_nnreal])
    have h1 := hhull _ hlt hV
    rw [hclk] at h1
    change fwdHull (Ito.rpath (R · ω)) (capClock (bCurve rec W T ω) τ) = _
    rw [h1, ht''c]
    obtain ⟨V', -, -, hK'⟩ := CoordB.exists_relBdry_prefix_driver (continuous_rdrv _) (rdrv_zero _) hs0 hg.tip
      hg.cont hg.zero hg.ctrace hd
    have hq : clockOf T τ ∈ Icc (0 : ℝ) T := ⟨hτ0, hτT.le⟩
    have himg : bCurve rec W T ω '' Icc 0 τ =
        (fun r : ℝ => CoordB.relBdry (rdrv (rec ω)) (recS (rec ω)) (phTr W ω r.toNNReal)) ''
          Icc 0 (clockOf T τ) :=
      image_relCurve_Icc (L := (T : ℝ)) (fun r : ℝ => CoordB.relBdry (rdrv (rec ω)) (recS (rec ω))
        (phTr W ω r.toNNReal)) (by exact_mod_cast hT) hτ.1
    rw [himg]
    exact ((hK' _ hq).2.1.symm.trans (hK' _ hq).2.2).symm
  have hRc' : Continuous (fun r : ℝ => R r.toNNReal ω) := hRc.comp continuous_real_toNNReal
  have hR0' : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hR0]
  have h := hcv.segDrv_eq hSpos hRc' hR0' hK u.coe_nonneg hSu.ge
  rw [h]
  simp only [Real.toNNReal_coe]

omit hGT in
/-- Off the good event the physical clock vanishes. -/
theorem bClock_eq_zero_of_notMem {t : ℝ≥0} {ω : Ω} (hω : ω ∉ GT) : bClock rec W GT t ω = 0 := by
  unfold bClock locLife
  refine ENNReal.iSup_eq_zero.2 fun k => indicator_of_notMem (fun h => hω h.1.2) _

include hGT in
/-- **A version is the physical relative driver** at every relative time below the physical clock and the stop
(pathwise, on the good event). -/
theorem eq_bDrv_of_version {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hR : ω ∈ GT → VersionAtB rec W R V ω) (t u : ℝ≥0)
    (hu : (u : ℝ≥0∞) < bClock rec W GT t ω) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = bDrv rec W GT t u ω := by
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hu
  have hv := selIdx_mem (valid := validEv rec W GT t u) (show ω ∈ validEv rec W GT t u k from hk)
  set k' := selIdx (validEv rec W GT t u) ω
  have hmem : ω ∈ locEv rec W GT (hz t k') := by
    by_contra hn
    have h0 : locLife rec W GT (hz t k') ω = 0 := indicator_of_notMem hn _
    have hv' : (u : ℝ≥0∞) < locLife rec W GT (hz t k') ω := hv
    rw [h0] at hv'
    exact not_lt_zero hv'
  have hlife : (u : ℝ≥0∞) < capLife (bCurve rec W (hz t k') ω) := by
    have hv' : (u : ℝ≥0∞) < locLife rec W GT (hz t k') ω := hv
    rwa [locLife, indicator_of_mem hmem] at hv'
  show R u ω = locDrv rec W GT (hz t k') u ω
  rw [locDrv, indicator_of_mem hmem]
  exact eq_localDrv_of_version hGT hmem (hR hmem.1.2) hlife huV

end Ident

/-! ### The physical clock on the good event -/

section Clock

variable {Ω : Type*} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  (hGT : ∀ ω ∈ GT, BGood rec W ω)

include hGT in
/-- **The local lifetime is the supremum of the relative clock before the horizon.** -/
theorem capLife_bCurve_eq {T : ℝ≥0} {ω : Ω} (hω : ω ∈ locEv rec W GT T) :
    capLife (bCurve rec W T ω) = ⨆ (t' : ℝ≥0) (_ : t' < T), ENNReal.ofReal (rclk (rec ω) (W · ω) t') := by
  have hωG := hω.1.2
  have hT : 0 < T := hω.1.1
  have hg := hGT ω hωG
  have hs0 := pos_recS_of_bGood hg
  have hd := hg.disjoint (lt_bTc_of_mem_locEv hGT hω)
  have hiff := CoordB.lt_localLife_iff (continuous_rdrv _) (rdrv_zero _) hs0 hg.tip hg.cont hg.zero hg.ctrace hT hd
  refine le_antisymm (ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
    (iSup₂_le fun t' ht' => ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
  · obtain ⟨t', ht', hrt⟩ := (hiff r).1 hr
    refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < T) =>
      ENNReal.ofReal (rclk (rec ω) (W · ω) t')) t' ht')
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hrt.le
  · refine ((hiff r).2 ⟨t', ht', ?_⟩).le
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).1 hr

include hGT in
/-- **The physical clock on the good event** is BW1's relative clock stopped at the first contact. -/
theorem bClock_eq_iSup {t : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) :
    bClock rec W GT t ω = supBelow (fun t' => ENNReal.ofReal (rclk (rec ω) (W · ω) t')) (bTc rec W ω) t := by
  refine le_antisymm (iSup_le fun k => ?_) (iSup₂_le fun t' ht' => ?_)
  · unfold locLife
    by_cases hk : ω ∈ locEv rec W GT (hz t k)
    · rw [indicator_of_mem hk, capLife_bCurve_eq hGT hk]
      have hTc := lt_bTc_of_mem_locEv hGT hk
      refine iSup₂_le fun t' ht' => ?_
      exact le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < bTc rec W ω) =>
        ENNReal.ofReal (rclk (rec ω) (W · ω) t')) t'
        ⟨ht'.trans_le (hz_le t k), (ENNReal.coe_lt_coe.2 ht').trans hTc⟩
    · rw [indicator_of_notMem hk]
      exact zero_le
  · have hlt : (t' : ℝ≥0∞) < min (t : ℝ≥0∞) (bTc rec W ω) :=
      lt_min (ENNReal.coe_lt_coe.2 ht'.1) ht'.2
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hqt : (q : ℝ) < t := by
      have h := hq2.trans_le (min_le_left _ _)
      rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe (by exact_mod_cast hq0)] at h
      exact h
    obtain ⟨k, hk⟩ := exists_hz_eq hqt
    have hmem : ω ∈ locEv rec W GT (hz t k) := by
      rw [mem_locEv_iff hGT hω, hk]
      refine ⟨lt_of_le_of_lt zero_le (ENNReal.coe_lt_coe.1 hq1), hq2.trans_le (min_le_right _ _)⟩
    refine le_trans ?_ (le_iSup _ k)
    rw [locLife, indicator_of_mem hmem, capLife_bCurve_eq hGT hmem]
    exact le_iSup₂ (f := fun (t'' : ℝ≥0) (_ : t'' < hz t k) =>
      ENNReal.ofReal (rclk (rec ω) (W · ω) t'')) t' (by rw [hk]; exact ENNReal.coe_lt_coe.1 hq1)

include hGT in
theorem bClock_props {ω : Ω} (hω : ω ∈ GT) :
    ContinuousOn (fun t => ENNReal.ofReal (rclk (rec ω) (W · ω) t)) {t | (t : ℝ≥0∞) < bTc rec W ω} ∧
      MonotoneOn (fun t => ENNReal.ofReal (rclk (rec ω) (W · ω) t)) {t | (t : ℝ≥0∞) < bTc rec W ω} ∧
      ENNReal.ofReal (rclk (rec ω) (W · ω) 0) = 0 := by
  obtain ⟨ha0, hsm, hac⟩ := (hGT ω hω).clock_regular
  refine ⟨ENNReal.continuous_ofReal.comp_continuousOn hac, fun x hx y hy hxy =>
    ENNReal.ofReal_le_ofReal (hsm.monotoneOn hx hy hxy), ?_⟩
  rw [ha0, ENNReal.ofReal_zero]

include hGT in
theorem bClock_zero (ω : Ω) : bClock rec W GT 0 ω = 0 := by
  by_cases hω : ω ∈ GT
  · rw [bClock_eq_iSup hGT hω, supBelow_zero]
  · exact bClock_eq_zero_of_notMem hω

include hGT in
theorem monotone_bClock (ω : Ω) : Monotone fun t => bClock rec W GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [bClock_eq_iSup hGT hω]
    exact monotone_supBelow
  · simp only [bClock_eq_zero_of_notMem hω]
    exact monotone_const

include hGT in
theorem continuous_bClock (ω : Ω) : Continuous fun t => bClock rec W GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [bClock_eq_iSup hGT hω]
    obtain ⟨h1, h2, h3⟩ := bClock_props hGT hω
    exact continuous_supBelow h1 h2 h3
  · simp only [bClock_eq_zero_of_notMem hω]
    exact continuous_const

include hGT in
/-- Before the first contact the physical clock is BW1's relative clock. -/
theorem bClock_eq_rclk {ω : Ω} (hω : ω ∈ GT) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < bTc rec W ω) :
    bClock rec W GT t ω = ENNReal.ofReal (rclk (rec ω) (W · ω) t) := by
  obtain ⟨h1, h2, h3⟩ := bClock_props hGT hω
  rw [bClock_eq_iSup hGT hω]
  exact supBelow_eq_of_lt h1 h2 h3 ht

end Clock

end InteractingSLE.Theorem14.BW1Safe
