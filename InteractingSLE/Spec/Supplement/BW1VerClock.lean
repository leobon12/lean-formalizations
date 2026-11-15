/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerCoord

/-!
# The measurable inverse relative clock

Packet PROVE-BW1-INPUTS2. On a good sample the relative clock `a(t)` before the contact is the lifetime of GB6's local
relative curve with horizon `t` (`IsGoodSample.capLife_localCurve`), which is measurable in the sample; so the clock
(`clkM`) and its inverse (`invClk`, a countable supremum over rational physical times) are measurable. On a good sample
with relative coordinates the inverse clock is continuous, strictly increasing, maps the relative interval `[0, L)`
onto the physical interval `[0, T_c)`, and inverts the clock (`sample_invClk`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.CoordB Supp8.GB6.GaugeE Sec7.PocketTraversal
  Sec7.Lemma71C

section Good

variable {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

theorem IsGoodSample.clock_regular (hg : IsGoodSample r A w γ) :
    rclk r w 0 = 0 ∧ StrictMonoOn (rclk r w) {t | (t : ℝ≥0∞) < contactT γ A (recS r)} ∧
      ContinuousOn (rclk r w) {t | (t : ℝ≥0∞) < contactT γ A (recS r)} :=
  relative_clock_regular (continuous_rdrv r) (rdrv_zero r) (by exact_mod_cast hg.pos) hg.tip hg.cont hg.zero
    hg.ctrace hg.contactT_pos fun _ hT => hg.disjoint hT

/-- **Before the contact, the relative clock is the lifetime of the local relative curve.** -/
theorem IsGoodSample.capLife_localCurve (hg : IsGoodSample r A w γ) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < contactT γ A (recS r)) :
    capLife (localCurve (rdrv r) (recS r) γ t) = ENNReal.ofReal (rclk r w t) := by
  obtain ⟨-, ham, hac⟩ := hg.clock_regular
  have hiff := fun ρ : ℝ≥0 => lt_localLife_iff (continuous_rdrv r) (rdrv_zero r) (by exact_mod_cast hg.pos)
    hg.tip hg.cont hg.zero hg.ctrace ht0 (hg.disjoint ht) ρ
  have hlt : ∀ t' : ℝ≥0, t' < t → rclk r w t' < rclk r w t := fun t' h =>
    ham ((ENNReal.coe_lt_coe.2 h).trans ht) ht h
  apply le_antisymm
  · by_contra hcon
    obtain ⟨ρ, hρ1, hρ2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_of_not_ge hcon)
    obtain ⟨t', ht', hρt'⟩ := (hiff ρ).1 hρ2
    rw [← ENNReal.ofReal_coe_nnreal] at hρ1
    have h1 := ((ENNReal.ofReal_lt_ofReal_iff'.1 hρ1).1)
    linarith [hlt t' ht']
  · refine ENNReal.le_of_forall_pos_nnreal_lt fun ρ _ hρ => ?_
    rw [← ENNReal.ofReal_coe_nnreal] at hρ
    have hρ' : (ρ : ℝ) < rclk r w t := (ENNReal.ofReal_lt_ofReal_iff'.1 hρ).1
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < contactT γ A (recS r)} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    have hca : ContinuousAt (rclk r w) t := hac.continuousAt (hopen.mem_nhds ht)
    have hne : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
    have hev : ∀ᶠ t' in 𝓝[<] t, (ρ : ℝ) < rclk r w t' :=
      (hca.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hρ')
    obtain ⟨t', hρt', ht'⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ((hiff ρ).2 ⟨t', ht', hρt'⟩).le

end Good

section Meas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {rec : Ω → RecData} {Wd : ℝ≥0 → Ω → ℝ} {Γ A : Ω → ℝ≥0 → ℂ}
  {M : Set Ω}

/-- The contact event of a positive physical time. -/
def clkEv (rec : Ω → RecData) (Γ A : Ω → ℝ≥0 → ℂ) (M : Set Ω) (t : ℝ≥0) : Set Ω :=
  M ∩ {ω | (t : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω))}

open Classical in
/-- **The relative clock read through the local lifetimes**: `0` at `t = 0`, the lifetime of the local relative
curve with horizon `t` on the contact event, `0` elsewhere. -/
def clkM (rec : Ω → RecData) (Γ A : Ω → ℝ≥0 → ℂ) (M : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t = 0 then 0 else ((clkEv rec Γ A M t).indicator
    (fun ω => capLife (localCurve (rdrv (rec ω)) (recS (rec ω)) (Γ ω) t)) ω).toReal

theorem measurable_clkM (hrec : Measurable rec) (hΓc : ∀ ω, Continuous (Γ ω)) (hAc : ∀ ω, Continuous (A ω))
    (hΓm : ∀ t, Measurable fun ω => Γ ω t) (hAm : ∀ t, Measurable fun ω => A ω t) (hM : MeasurableSet M)
    (hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω)) (t : ℝ≥0) :
    Measurable (clkM rec Γ A M t) := by
  classical
  unfold clkM
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    exact measurable_const
  · simp only [ht, ↓reduceIte]
    have ht0 : 0 < t := lt_of_le_of_ne zero_le (Ne.symm ht)
    let V : ℝ≥0 → Ω → ℝ := fun t ω => rdrv (rec ω) t
    have hVm : ∀ t, Measurable (V t) := fun t => (measurable_rdrv_apply t).comp hrec
    have hVc : ∀ ω, Continuous (V · ω) := fun ω => continuous_rdrv_nn (rec ω)
    have hV0 : ∀ ω, V 0 ω = 0 := fun ω => rdrv_zero (rec ω)
    have hVr : ∀ ω, Ito.rpath (V · ω) = rdrv (rec ω) := fun ω => rpath_rdrv (rec ω)
    have hE : MeasurableSet (clkEv rec Γ A M t) :=
      hM.inter (measurableSet_lt_contactT hΓc hAc hΓm hAm (measurable_recS.comp hrec) t)
    have hgeom : ∀ ω ∈ clkEv rec Γ A M t, ∃ (w : ℝ≥0 → ℝ) (p : ℂ), Continuous w ∧ w 0 = 0 ∧
        IsGeneratingTrace w ⊤ (Γ ω) ∧
        Tendsto (QuantumZipper.fwdMapInv (Ito.rpath (V · ω)) (recS (rec ω))) (𝓝[H] 0) (𝓝 p) ∧
        Disjoint (closure (fwdHull (Ito.rpath (V · ω)) (recS (rec ω))))
          (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) t)) := by
      intro ω hω
      have hg := hgood ω hω.1
      refine ⟨(Wd · ω), A ω (recS (rec ω)), hg.cont, hg.zero, hg.ctrace, ?_, ?_⟩
      · rw [hVr]; exact hg.tip
      · rw [hVr]; exact hg.disjoint hω.2
    have hcurve : ∀ ω ∈ clkEv rec Γ A M t, IsDrivenCurve (localCurve (rdrv (rec ω)) (recS (rec ω)) (Γ ω) t) := by
      intro ω hω
      have hg := hgood ω hω.1
      exact isDrivenCurve_localCurve (continuous_rdrv _) (rdrv_zero _) (by exact_mod_cast hg.pos) hg.tip hg.cont
        hg.zero hg.ctrace ht0 (hg.disjoint hω.2)
    have hm := measurable_indicator_localCurve_rand hVm hVc hV0 (measurable_recS.comp hrec) hΓm hE ht0 hgeom
    simp only [hVr] at hm
    exact ENNReal.measurable_toReal.comp (measurable_indicator_capLife hE hcurve hm)

omit mΩ in
theorem clkM_eq (hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω)) {ω : Ω} (hω : ω ∈ M) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω))) : clkM rec Γ A M t ω = rclk (rec ω) (Wd · ω) t := by
  classical
  unfold clkM
  by_cases ht0 : t = 0
  · simp only [ht0, ↓reduceIte]
    exact ((hgood ω hω).clock_regular.1).symm
  · simp only [ht0, ↓reduceIte]
    have hg := hgood ω hω
    rw [indicator_of_mem (show ω ∈ clkEv rec Γ A M t from ⟨hω, ht⟩),
      hg.capLife_localCurve (lt_of_le_of_ne zero_le (Ne.symm ht0)) ht,
      ENNReal.toReal_ofReal]
    obtain ⟨ha0, ham, -⟩ := hg.clock_regular
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω)) := by
      rw [ENNReal.coe_zero]; exact hg.contactT_pos
    have := ham.monotoneOn h0 ht zero_le
    rwa [ha0] at this

open Classical in
/-- **The inverse relative clock**: the supremum of the rational physical times before the contact whose clock is
below `u`. -/
def invClk (rec : Ω → RecData) (Γ A : Ω → ℝ≥0 → ℂ) (M : Set Ω) (ω : Ω) (u : ℝ≥0) : ℝ≥0 :=
  (⨆ q : ℚ≥0, if ω ∈ M ∧ ((q : ℝ≥0) : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω)) ∧
    clkM rec Γ A M q ω < u then ((q : ℝ≥0) : ℝ≥0∞) else 0).toNNReal

theorem measurable_invClk (hrec : Measurable rec) (hΓc : ∀ ω, Continuous (Γ ω)) (hAc : ∀ ω, Continuous (A ω))
    (hΓm : ∀ t, Measurable fun ω => Γ ω t) (hAm : ∀ t, Measurable fun ω => A ω t) (hM : MeasurableSet M)
    (hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω)) (u : ℝ≥0) :
    Measurable fun ω => invClk rec Γ A M ω u := by
  classical
  unfold invClk
  refine ENNReal.measurable_toNNReal.comp (Measurable.iSup fun q => Measurable.ite ?_ measurable_const
    measurable_const)
  exact hM.inter ((measurableSet_lt_contactT hΓc hAc hΓm hAm (measurable_recS.comp hrec) q).inter
    (measurableSet_lt (measurable_clkM hrec hΓc hAc hΓm hAm hM hgood q) measurable_const))

end Meas

/-- **An inverse of a continuous strictly increasing clock is a continuous strictly increasing bijection of the
relative interval onto the physical interval** (deterministic). -/
theorem inverse_clock_props {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (hab : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L) {ℓ : ℝ≥0 → ℝ≥0}
    (hℓ : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → (ℓ u : ℝ≥0∞) < Tc ∧ a (ℓ u) = u) :
    StrictMonoOn ℓ {u | (u : ℝ≥0∞) < L} ∧ ContinuousOn ℓ {u | (u : ℝ≥0∞) < L} ∧
      ℓ '' {u | (u : ℝ≥0∞) < L} = {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := by
  have hsm : StrictMonoOn ℓ {u | (u : ℝ≥0∞) < L} := by
    intro u hu u' hu' huu'
    by_contra hcon
    have hle := ham.monotoneOn (hℓ u' hu').1 (hℓ u hu).1 (le_of_not_gt hcon)
    rw [(hℓ u hu).2, (hℓ u' hu').2] at hle
    exact absurd (NNReal.coe_le_coe.1 hle) (not_le.2 huu')
  have himg : ℓ '' {u | (u : ℝ≥0∞) < L} = {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hℓ u hu).1
    · intro ht
      obtain ⟨h0, hL⟩ := hab t ht
      have huL : (((a t).toNNReal : ℝ≥0) : ℝ≥0∞) < L := by rwa [ENNReal.ofReal.eq_1] at hL
      refine ⟨(a t).toNNReal, huL, ?_⟩
      obtain ⟨hT, ha⟩ := hℓ _ huL
      rw [Real.coe_toNNReal _ h0] at ha
      exact ham.injOn hT ht ha
  refine ⟨hsm, fun u hu => ?_, himg⟩
  have hopenL : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hopenT : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
  refine (continuousAt_of_monotoneOn_of_image_mem_nhds hsm.monotoneOn (hopenL.mem_nhds hu) ?_).continuousWithinAt
  rw [himg]
  exact hopenT.mem_nhds (hℓ u hu).1

section Spec

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {rec : Ω → RecData} {Wd : ℝ≥0 → Ω → ℝ} {Γ A : Ω → ℝ≥0 → ℂ}
  {M : Set Ω}

omit mΩ in
/-- **On a good sample with coordinates, the inverse clock inverts the clock.** -/
theorem invClk_spec (hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω)) {ω : Ω} (hω : ω ∈ M)
    {D : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hC : IsSampleCoord (rec ω) (A ω) (Wd · ω) (Γ ω) D L) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) < L) :
    (invClk rec Γ A M ω u : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω)) ∧
      rclk (rec ω) (Wd · ω) (invClk rec Γ A M ω u) = u := by
  classical
  have hg := hgood ω hω
  obtain ⟨-, ham, -⟩ := hg.clock_regular
  obtain ⟨t, ht, hat, -⟩ := (sample_readout hg hC).2.2.2.2.1 u hu
  have hS : (⨆ q : ℚ≥0, if ω ∈ M ∧ ((q : ℝ≥0) : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω)) ∧
      clkM rec Γ A M q ω < u then ((q : ℝ≥0) : ℝ≥0∞) else 0) = (t : ℝ≥0∞) := by
    apply le_antisymm
    · refine iSup_le fun q => ?_
      split_ifs with hq
      · obtain ⟨-, hqT, hqa⟩ := hq
        rw [clkM_eq hgood hω hqT, ← hat] at hqa
        have hqt : (q : ℝ≥0) < t := by
          by_contra h
          exact absurd (ham.monotoneOn ht hqT (le_of_not_gt h)) (not_le.2 hqa)
        exact ENNReal.coe_le_coe.2 hqt.le
      · exact zero_le
    · refine le_of_forall_lt fun c hc => ?_
      have hcne : c ≠ ⊤ := (hc.trans ENNReal.coe_lt_top).ne
      have hct : c.toNNReal < t := by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hcne]; exact hc
      obtain ⟨q, hcq, hqt⟩ := Supp8.GB6.HullId.exists_nnrat_btwn hct
      have hqT : ((q : ℝ≥0) : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω)) :=
        (ENNReal.coe_lt_coe.2 hqt).trans ht
      have hcond : ω ∈ M ∧ ((q : ℝ≥0) : ℝ≥0∞) < contactT (Γ ω) (A ω) (recS (rec ω)) ∧
          clkM rec Γ A M q ω < u := by
        refine ⟨hω, hqT, ?_⟩
        rw [clkM_eq hgood hω hqT, ← hat]
        exact ham hqT ht hqt
      calc c = ((c.toNNReal : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_toNNReal hcne).symm
        _ < ((q : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hcq
        _ ≤ _ := le_iSup_of_le q (by simp only [hcond, and_self, ↓reduceIte, le_refl])
  have hinv : invClk rec Γ A M ω u = t := by
    unfold invClk
    rw [hS, ENNReal.toNNReal_coe]
  rw [hinv]
  exact ⟨ht, hat⟩

end Spec

end InteractingSLE.Theorem14.BW1Ver
