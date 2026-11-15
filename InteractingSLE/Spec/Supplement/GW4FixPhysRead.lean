/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixSafeR
import InteractingSLE.Spec.Supplement.RelSafeGB6Read

/-!
# GW4's relative driver read in the physical history (PROVE-GB6-RELSAFE's core for GW4)

Packet PROVE-T14-GW4FIX (continuation). The instance of `Supp8.RelSafe` (`RelSafeCore`) for GW4's relative traversal:

* deterministic: `rcap_strictMono`; **`fwdHull_eq_hullAt_of_version`** (a Loewner hull of a continuous driver that is
  some relative hull is the relative hull of the same capacity); **`eq_segDrv_of_version`** (a version's driver is the
  local driver below the local lifetime and up to the stop, the stop included by continuity);
* `physClockG`, `physDrvG`: GW4's relative clock and driver at physical time `t`, from the horizons `hz t k ≤ t`
  (`RelSafe.hz`) — readable in any σ-algebra reading the driver on `[0, t]`;
* **`ae_eq_physDrvG_of_version`**: every version of the relative traversal agrees with `physDrvG t` below the
  physical clock and up to its stop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Conn GB11Chart GW4Rel Sec7.PocketTraversal Sec7.Lemma71C

namespace Frame

variable {F : Frame}

/-! ### Identification of a version with the local driver -/

section Ident

variable (hF : F.IsOk) {w : ℝ≥0 → ℝ}
include hF

theorem rcap_strictMono {T : ℝ≥0} (h : F.IsLoc w T) {t t' : ℝ≥0} (h1 : F.ent w ≤ t) (htt' : t < t')
    (h2 : t' < T) : F.rcap w t < F.rcap w t' := by
  obtain ⟨-, hL0⟩ := horizon_of_isLoc h
  obtain ⟨v, hv, hvt⟩ := exists_ent_add_clockOf_eq h1 (htt'.trans h2)
  obtain ⟨v', hv', hvt'⟩ := exists_ent_add_clockOf_eq (h1.trans htt'.le) h2
  rw [← hvt, ← hvt', ← capClock_curve hF h hv, ← capClock_curve hF h hv']
  have hcc : clockOf ((T : ℝ) - F.ent w) v < clockOf ((T : ℝ) - F.ent w) v' := by
    have h3 := NNReal.coe_lt_coe.2 htt'
    rw [← hvt, ← hvt', NNReal.coe_add, NNReal.coe_add, Real.coe_toNNReal _ (clockOf_nonneg hL0 hv),
      Real.coe_toNNReal _ (clockOf_nonneg hL0 hv')] at h3
    linarith
  have hvv : v < v' := (strictMonoOn_clockOf hL0).lt_iff_lt hv hv' |>.1 hcc
  exact (isDrivenCurve_curve hF h).strictMonoOn_capClock hv hv' hvv

/-- **A Loewner hull that is a relative hull is the relative hull of its capacity.** -/
theorem fwdHull_eq_hullAt_of_version (hw : F.IsPathOk w) {R : ℝ → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0)
    {s t₃ : ℝ≥0} (hs : fwdHull R s = F.hullAt w t₃) {t : ℝ≥0} (ht : F.ent w ≤ t)
    (htσ : (t : ℝ≥0∞) < F.exit w) (hst : (s : ℝ) = F.rcap w t) : fwdHull R s = F.hullAt w t := by
  have hcap := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hRc hR0 s.coe_nonneg hs
  have hb : Bornology.IsBounded (F.hullAt w t₃) := hs ▸ (isHPHull_fwdHull hRc s.coe_nonneg).2.1
  have hlt := lt_exit_of_isBounded hF hw hb
  set t₄ := max t₃ (F.ent w) with ht₄
  have hA : F.hullAt w t₃ = F.hullAt w t₄ := by
    rcases le_total t₃ (F.ent w) with h' | h'
    · rw [hullAt_eq_empty_of_le hF hw h', hullAt_eq_empty_of_le hF hw (max_le h' le_rfl)]
    · rw [ht₄, max_eq_left h']
  have ht₄σ : (t₄ : ℝ≥0∞) < F.exit w := by
    rw [ht₄, ENNReal.coe_max]
    exact max_lt hlt (ent_lt_exit hF hw)
  have hr₄ : F.rcap w t₄ = F.rcap w t := by
    rw [rcap, ← hA, hcap, ← hst]
    ring
  obtain ⟨T, hT1, hT2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (max t₄ t : ℝ≥0∞) < F.exit w by
    rw [← ENNReal.coe_max]; exact (ENNReal.coe_max t₄ t).symm ▸ max_lt ht₄σ htσ)
  have hT : max t₄ t < T := ENNReal.coe_lt_coe.1 hT1
  have hloc : F.IsLoc w T := ⟨hw, lt_of_le_of_lt ht ((le_max_right _ _).trans_lt hT), hT2⟩
  have heq : t₄ = t := by
    rcases lt_trichotomy t₄ t with h' | h' | h'
    · exact absurd hr₄ (rcap_strictMono hF hloc (le_max_right _ _) h' ((le_max_right _ _).trans_lt hT)).ne
    · exact h'
    · exact absurd hr₄ (rcap_strictMono hF hloc ht h' ((le_max_left _ _).trans_lt hT)).ne'
  rw [hs, hA, heq]

/-- **A version's driver is the local driver** below the local lifetime and up to the stop. -/
theorem eq_segDrv_of_version {T : ℝ≥0} (h : F.IsLoc w T) {R : ℝ≥0 → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hver : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V → ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) s = F.hullAt w t)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < capLife (F.curve w T)) (huV : (u : ℝ≥0∞) ≤ V) :
    R u = segDrv (F.curve w T) u := by
  have hRc' : Continuous fun r : ℝ => R r.toNNReal := hRc.comp continuous_real_toNNReal
  have hR0' : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hR0]
  have hcv := isDrivenCurve_curve hF h
  have hstrict : ∀ v : ℝ≥0, (v : ℝ≥0∞) < capLife (F.curve w T) → (v : ℝ≥0∞) < V →
      R v = segDrv (F.curve w T) v := by
    intro v hv hvV
    have key := eq_segDrv_of_clockHull hF h hRc' hR0' hv fun t ht0 htT hle => by
      obtain ⟨v', hv', hvt'⟩ := exists_ent_add_clockOf_eq ht0 htT
      have hnn : 0 ≤ F.rcap w t := by
        rw [← hvt', ← capClock_curve hF h hv']
        exact hcv.capClock_nonneg hv'
      set s : ℝ≥0 := (F.rcap w t).toNNReal with hsdef
      have hst : (s : ℝ) = F.rcap w t := Real.coe_toNNReal _ hnn
      have hsV : (s : ℝ≥0∞) < V := by
        refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hvV
        rw [← NNReal.coe_le_coe, hst]
        exact hle
      obtain ⟨t₃, hs3⟩ := hver s hsV
      have htσ : (t : ℝ≥0∞) < F.exit w := (ENNReal.coe_lt_coe.2 htT).trans h.2.2
      rw [← hst]
      exact fwdHull_eq_hullAt_of_version hF h.1 hRc' hR0' hs3 ht0 htσ hst
    rw [key]
    simp only [Real.toNNReal_coe]
  by_cases huV' : (u : ℝ≥0∞) < V
  · exact hstrict u hu huV'
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0u | hu0
  · subst h0u
    have h0 := hcv.segDriver_spec.1
    simp only [segDriver] at h0
    rw [hR0, NNReal.coe_zero]
    exact_mod_cast h0.symm
  have hVu : V = u := le_antisymm (le_of_not_gt huV') huV
  have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
  have hc2 : ContinuousAt (segDriver (F.curve w T)) u :=
    (hcv.segDriver_spec.2.1 u hu).continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hu)
  have hev : (fun v => R v) =ᶠ[𝓝[<] u] segDriver (F.curve w T) := by
    filter_upwards [self_mem_nhdsWithin] with v (hv : v < u)
    have hvu : (v : ℝ≥0∞) < u := ENNReal.coe_lt_coe.2 hv
    exact hstrict v (hvu.trans hu) (hVu ▸ hvu)
  exact tendsto_nhds_unique ((hRc.tendsto u).mono_left nhdsWithin_le_nhds)
    (((hc2.tendsto).mono_left nhdsWithin_le_nhds).congr' hev.symm)

end Ident

/-! ### The physical clock and driver -/

section Phys

variable {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}

variable (F) in
/-- **GW4's relative clock read in the physical history**: the supremum of the local lifetimes of the horizons
before `t`. -/
def physClockG (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k, F.locLife W' GT (Supp8.RelSafe.hz t k) ω

variable (F) in
/-- The horizons before `t` whose local curve lives past `u`. -/
def validG (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t u : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | (u : ℝ≥0∞) < F.locLife W' GT (Supp8.RelSafe.hz t k) ω}

variable (F) in
/-- **GW4's relative driver read in the physical history**: the local driver of the first horizon before `t` whose
curve lives past `u`. -/
def physDrvG (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t u : ℝ≥0) (ω : Ω) : ℝ :=
  F.locDrv W' GT (Supp8.RelSafe.hz t (Supp8.RelSafe.selIdx (F.validG W' GT t u) ω)) u ω

variable (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω))
include hF hGT

/-- **A version is the physical relative driver** below the physical clock and up to its stop (pathwise). -/
theorem eq_physDrvG_of_version {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hver : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ω → ∃ t,
      fwdHull (fun r : ℝ => R r.toNNReal ω) s = F.hullAt (fun r => W' r ω) t)
    (t u : ℝ≥0) (hu : (u : ℝ≥0∞) < F.physClockG W' GT t ω) (huV : (u : ℝ≥0∞) ≤ V ω) :
    R u ω = F.physDrvG W' GT t u ω := by
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hu
  have hv := Supp8.RelSafe.selIdx_mem (valid := F.validG W' GT t u) (show ω ∈ F.validG W' GT t u k from hk)
  obtain ⟨hm, hl⟩ := mem_of_lt_locLife hv
  show R u ω = F.locDrv W' GT _ u ω
  rw [locDrv_eq hm hl]
  exact eq_segDrv_of_version hF (isLoc_of_mem_locEv hGT hm) hRc hR0 hver hl huV

variable {m : MeasurableSpace Ω} {t : ℝ≥0} (hW : ∀ r ≤ t, Measurable[m] (W' r)) (hGTm : MeasurableSet[m] GT)
include hW hGTm

/-- **The physical clock at `t` reads only the physical driver before `t`.** -/
theorem measurable_physClockG : Measurable[m] (F.physClockG W' GT t) :=
  Measurable.iSup fun k => measurable_locLife hF hGT hW hGTm (Supp8.RelSafe.hz_le t k)

/-- **The physical relative driver at `t` reads only the physical driver before `t`.** -/
theorem measurable_physDrvG (u : ℝ≥0) : Measurable[m] (F.physDrvG W' GT t u) := by
  have hidx : Measurable[m] (Supp8.RelSafe.selIdx (F.validG W' GT t u)) :=
    Supp8.RelSafe.measurable_selIdx fun k => measurableSet_lt measurable_const
      (measurable_locLife hF hGT hW hGTm (Supp8.RelSafe.hz_le t k))
  exact Ito.measurable_comp_index (F := fun ω k => F.locDrv W' GT (Supp8.RelSafe.hz t k) u ω)
    (fun k => measurable_locDrv hF hGT hW hGTm (Supp8.RelSafe.hz_le t k) u) hidx

end Phys

/-! ### The relative capacity clock in physical time -/

section RCap

variable (hF : F.IsOk) {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w)
include hF hw

theorem exists_isLoc_gt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < F.exit w) : ∃ T : ℝ≥0, t < T ∧ F.IsLoc w T := by
  have hm : ((max t (F.ent w) : ℝ≥0) : ℝ≥0∞) < F.exit w := by
    rw [ENNReal.coe_max]; exact max_lt ht (ent_lt_exit hF hw)
  obtain ⟨T, hT1, hT2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hm
  have hT : max t (F.ent w) < T := ENNReal.coe_lt_coe.1 hT1
  exact ⟨T, (le_max_left _ _).trans_lt hT, hw, (le_max_right _ _).trans_lt hT, hT2⟩

theorem rcap_eq_zero_of_le {t : ℝ≥0} (ht : t ≤ F.ent w) : F.rcap w t = 0 := by
  obtain ⟨T, -, hloc⟩ := exists_isLoc_gt hF hw (ent_lt_exit hF hw)
  have h1 : F.rcap w t = F.rcap w (F.ent w) := by
    simp only [rcap, hullAt_eq_empty_of_le hF hw ht, hullAt_eq_empty_of_le hF hw le_rfl]
  have h2 := capClock_curve hF hloc (le_refl (0 : ℝ))
  rw [clockOf_zero, Real.toNNReal_zero, add_zero, (isDrivenCurve_curve hF hloc).capClock_zero] at h2
  rw [h1, ← h2]

theorem rcap_nonneg {t : ℝ≥0} (ht : (t : ℝ≥0∞) < F.exit w) : 0 ≤ F.rcap w t := by
  rcases le_total t (F.ent w) with h | h
  · rw [rcap_eq_zero_of_le hF hw h]
  · obtain ⟨T, htT, hloc⟩ := exists_isLoc_gt hF hw ht
    obtain ⟨v, hv, hvt⟩ := exists_ent_add_clockOf_eq h htT
    rw [← hvt, ← capClock_curve hF hloc hv]
    exact (isDrivenCurve_curve hF hloc).capClock_nonneg hv

theorem monotoneOn_rcap : MonotoneOn (fun t => ENNReal.ofReal (F.rcap w t)) {t | (t : ℝ≥0∞) < F.exit w} := by
  intro t ht t' ht' htt'
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total t' (F.ent w) with h' | h'
  · rw [rcap_eq_zero_of_le hF hw (htt'.trans h'), rcap_eq_zero_of_le hF hw h']
  · obtain ⟨T, htT, hloc⟩ := exists_isLoc_gt hF hw ht'
    rcases le_total t (F.ent w) with h | h
    · rw [rcap_eq_zero_of_le hF hw h]
      exact rcap_nonneg hF hw ht'
    · exact rcap_mono hF hloc h htt' htT

theorem continuousOn_rcap : ContinuousOn (fun t => ENNReal.ofReal (F.rcap w t)) {t | (t : ℝ≥0∞) < F.exit w} := by
  intro t₀ ht₀
  obtain ⟨T, ht₀T, hloc⟩ := exists_isLoc_gt hF hw ht₀
  have hcv := isDrivenCurve_curve hF hloc
  obtain ⟨T', hT'1, hT'2⟩ := exists_between (max_lt ht₀T hloc.2.1)
  have hT'e : F.ent w < T' := (le_max_right _ _).trans_lt hT'1
  have ht₀T' : t₀ < T' := (le_max_left _ _).trans_lt hT'1
  set L : ℝ := (T : ℝ) - F.ent w with hL
  set M : ℝ := (T' : ℝ) - F.ent w with hM
  have hML : M < L := by simp only [hM, hL]; linarith [NNReal.coe_lt_coe.2 hT'2]
  have hM0 : 0 ≤ M := by simp only [hM]; linarith [NNReal.coe_lt_coe.2 hT'e]
  set x : ℝ≥0 → ℝ := fun t => min (max 0 ((t : ℝ) - F.ent w)) M with hx
  have hx0 : ∀ t, 0 ≤ x t := fun t => le_min (le_max_left _ _) hM0
  have hxM : ∀ t, x t ≤ M := fun t => min_le_right _ _
  have hden : ∀ t, 0 < L - x t := fun t => by linarith [hxM t]
  set φ : ℝ≥0 → ℝ := fun t => x t / (L - x t) with hφ
  have hxc : Continuous x :=
    (continuous_const.max (NNReal.continuous_coe.sub continuous_const)).min continuous_const
  have hφc : Continuous φ := hxc.div (continuous_const.sub hxc) fun t => (hden t).ne'
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => div_nonneg (hx0 t) (hden t).le
  have hcomp : Continuous fun t => capClock (F.curve w T) (φ t) :=
    hcv.continuousOn_capClock.comp_continuous hφc fun t => mem_Ici.2 (hφ0 t)
  have hL0 : 0 < L := (horizon_of_isLoc hloc).2
  have heq : ∀ t : ℝ≥0, t < T' → F.rcap w t = capClock (F.curve w T) (φ t) := by
    intro t htT'
    rcases le_total t (F.ent w) with h | h
    · have hxt : x t = 0 := by
        simp only [hx]
        rw [max_eq_left (by linarith [NNReal.coe_le_coe.2 h]), min_eq_left hM0]
      simp only [hφ, hxt, zero_div, hcv.capClock_zero]
      exact rcap_eq_zero_of_le hF hw h
    · have hxt : x t = (t : ℝ) - F.ent w := by
        simp only [hx]
        rw [max_eq_right (by linarith [NNReal.coe_le_coe.2 h]), min_eq_left (by
          simp only [hM]; linarith [NNReal.coe_lt_coe.2 htT'])]
      have hxL : x t < L := by linarith [hxM t]
      have hcl : clockOf L (φ t) = x t := by
        unfold clockOf
        have hne : L - x t ≠ 0 := (hden t).ne'
        have hL' : L ≠ 0 := hL0.ne'
        simp only [hφ]
        have h1' : 1 + x t / (L - x t) = L / (L - x t) := by field_simp; ring
        rw [h1', div_div_div_cancel_right₀ hne]
        field_simp
      rw [capClock_curve hF hloc (hφ0 t), hcl, hxt]
      congr 1
      apply NNReal.eq
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith [NNReal.coe_le_coe.2 h])]
      ring
  have hev : (fun t => ENNReal.ofReal (F.rcap w t)) =ᶠ[𝓝 t₀]
      fun t => ENNReal.ofReal (capClock (F.curve w T) (φ t)) := by
    filter_upwards [(isOpen_gt' T').mem_nhds ht₀T'] with t ht
    rw [heq t ht]
  exact ((ENNReal.continuous_ofReal.comp hcomp).continuousAt.congr hev.symm).continuousWithinAt

theorem rcap_zero : ENNReal.ofReal (F.rcap w 0) = 0 := by
  rw [rcap_eq_zero_of_le hF hw zero_le, ENNReal.ofReal_zero]

end RCap

/-! ### The physical clock is the relative clock stopped at the exit -/

section ClockG

variable {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}

theorem physClockG_eq_zero_of_notMem {t : ℝ≥0} {ω : Ω} (hω : ω ∉ GT) : F.physClockG W' GT t ω = 0 :=
  ENNReal.iSup_eq_zero.2 fun _ => indicator_of_notMem (fun h => hω h.1) _

variable (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω))
include hF hGT

theorem physClockG_eq_supBelow {ω : Ω} (hω : ω ∈ GT) (t : ℝ≥0) :
    F.physClockG W' GT t ω = Supp8.RelSafe.supBelow (fun t' => ENNReal.ofReal (F.rcap (fun r => W' r ω) t'))
      (F.exit (fun r => W' r ω)) t := by
  have hw := hGT ω hω
  refine le_antisymm (iSup_le fun k => ?_) (iSup₂_le fun t' ht' => ?_)
  · by_cases hm : ω ∈ F.locEv W' GT (Supp8.RelSafe.hz t k)
    · rw [locLife, indicator_of_mem hm]
      have hloc := isLoc_of_mem_locEv hGT hm
      refine le_of_forall_lt fun x hx => ?_
      obtain ⟨t', -, h1, h2⟩ := exists_lt_rcap_of_lt_capLife hF hloc hx
      exact h2.trans_le (le_iSup₂_of_le (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < F.exit _) =>
        ENNReal.ofReal (F.rcap (fun r => W' r ω) t')) t'
        ⟨h1.trans_le (Supp8.RelSafe.hz_le t k), (ENNReal.coe_lt_coe.2 h1).trans hm.2.2⟩ le_rfl)
    · rw [locLife, indicator_of_notMem hm]
      exact zero_le
  · dsimp only
    rcases le_total t' (F.ent (fun r => W' r ω)) with h | h
    · rw [rcap_eq_zero_of_le hF hw h, ENNReal.ofReal_zero]
      exact zero_le
    · have hlt : (t' : ℝ≥0∞) < min (t : ℝ≥0∞) (F.exit (fun r => W' r ω)) :=
        lt_min (ENNReal.coe_lt_coe.2 ht'.1) ht'.2
      obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
      have hqt : (q : ℝ) < t := by
        have h' : ENNReal.ofReal (q : ℝ) < ENNReal.ofReal (t : ℝ) := by
          rw [ENNReal.ofReal_coe_nnreal]
          exact hq2.trans_le (min_le_left _ _)
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq0').1 h'
      obtain ⟨k, hk⟩ := Supp8.RelSafe.exists_hz_eq hqt
      have hT1 : t' < Supp8.RelSafe.hz t k := by
        rw [hk, ← ENNReal.coe_lt_coe]
        exact hq1
      have hm : ω ∈ F.locEv W' GT (Supp8.RelSafe.hz t k) :=
        ⟨hω, lt_of_le_of_lt h hT1, by rw [hk]; exact hq2.trans_le (min_le_right _ _)⟩
      have hloc := isLoc_of_mem_locEv hGT hm
      refine (ofReal_rcap_lt_capLife hF hloc h hT1).le.trans ?_
      refine le_trans (le_of_eq ?_) (le_iSup (fun k => F.locLife W' GT (Supp8.RelSafe.hz t k) ω) k)
      rw [locLife, indicator_of_mem hm]

theorem physClockG_zero (ω : Ω) : F.physClockG W' GT 0 ω = 0 := by
  by_cases hω : ω ∈ GT
  · rw [physClockG_eq_supBelow hF hGT hω, Supp8.RelSafe.supBelow_zero]
  · exact physClockG_eq_zero_of_notMem hω

theorem monotone_physClockG (ω : Ω) : Monotone fun t => F.physClockG W' GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [physClockG_eq_supBelow hF hGT hω]
    exact Supp8.RelSafe.monotone_supBelow
  · simp only [physClockG_eq_zero_of_notMem hω]
    exact monotone_const

theorem continuous_physClockG (ω : Ω) : Continuous fun t => F.physClockG W' GT t ω := by
  by_cases hω : ω ∈ GT
  · simp only [physClockG_eq_supBelow hF hGT hω]
    exact Supp8.RelSafe.continuous_supBelow (continuousOn_rcap hF (hGT ω hω)) (monotoneOn_rcap hF (hGT ω hω))
      (rcap_zero hF (hGT ω hω))
  · simp only [physClockG_eq_zero_of_notMem hω]
    exact continuous_const

/-- Before the exit the physical clock is the relative capacity clock. -/
theorem physClockG_eq_rcap {ω : Ω} (hω : ω ∈ GT) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < F.exit (fun r => W' r ω)) :
    F.physClockG W' GT t ω = ENNReal.ofReal (F.rcap (fun r => W' r ω) t) := by
  rw [physClockG_eq_supBelow hF hGT hω]
  exact Supp8.RelSafe.supBelow_eq_of_lt (continuousOn_rcap hF (hGT ω hω)) (monotoneOn_rcap hF (hGT ω hω))
    (rcap_zero hF (hGT ω hω)) ht

end ClockG

end Frame

end InteractingSLE.Theorem14.GW4Fix
