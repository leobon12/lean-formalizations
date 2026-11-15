/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50HitHist

/-!
# Aux. lemma 50 for every `κ < 8`: the history functionals along a coupling

Packet PROVE-AUX50B. Along a coupling whose lifetime is infinite, the history stopped at a rule `s` is a continuous
history, its regularized driver is `W_{· ∧ S}`, and the Borel functionals of `Aux50HitHist` read the coupling's own
Loewner objects at the stop:

* `regPath_stopHistory`, `fwdHull_regPath_stopHistory`, `regHull_stopHistory_cstop`: the driver and the hulls;
* **`histLab_iff`**: the label event of the history at `N` is `WholeField.IsLabel` of the coupling's driver;
* **`histQ_eq`**: the retained Green energy of the history at `N` is the coupling's `Q_{U_N}`
  (`VTe_congr_of_eqOn`: `V_T` depends only on the driver on `[0, T]`);
* `safeRule_eq`: the safe exit rule of the history is the safe exit time of the coupling's driver.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Aux50Hit

open LawUnique Sec4 QuantumZipper LQGMetric WholeField

variable {nL nR : ℕ}

/-! ### Deterministic congruences -/

section Congr

/-- The hull is relatively closed in `ℍ`. -/
theorem closure_fwdHull_inter_H {V : ℝ → ℝ} (hV : Continuous V) {t : ℝ} (ht : 0 ≤ t) :
    closure (fwdHull V t) ∩ (upperHalfPlaneOpens : Set ℂ) = fwdHull V t := by
  ext z
  constructor
  · rintro ⟨hzc, hzH⟩
    by_contra hzK
    have hz : z ∈ H \ fwdHull V t := ⟨hzH, hzK⟩
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzc _ (FwdHolo.isOpen_compl_fwdHull hV ht) hz
    exact hy1.2 hy2
  · intro hz
    exact ⟨subset_closure hz, hz.1⟩

/-- **`V_T(a, b)` depends only on the driver on `[0, T]`** (for `a, b ∈ ℍ`). -/
theorem VTe_congr_of_eqOn {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V') {T : ℝ}
    (h : EqOn V V' (Icc 0 T)) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) :
    K3.VTe V T a b = K3.VTe V' T a b := by
  have hhull : ∀ t, 0 ≤ t → t ≤ T → fwdHull V t = fwdHull V' t := fun t ht htT =>
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hV hV' ht fun r hr => h ⟨hr.1, hr.2.trans htT⟩
  have hlt : ∀ (W : ℝ → ℝ) (z : ℂ), z ∈ H → ∀ t : ℝ, (ENNReal.ofReal t < swallowTime W z ↔ z ∉ fwdHull W t) :=
    fun W z hz t => ⟨fun h' hK => not_le.2 h' hK.2, fun h' => not_le.1 fun hle => h' ⟨hz, hle⟩⟩
  have hidx : K3.vtIdx V T a b = K3.vtIdx V' T a b := by
    ext t
    simp only [K3.vtIdx, mem_ofPred_eq]
    constructor
    · rintro ⟨ht, htT, h1, h2⟩
      rw [hlt V a ha, hhull t ht htT] at h1
      rw [hlt V b hb, hhull t ht htT] at h2
      exact ⟨ht, htT, (hlt V' a ha t).2 h1, (hlt V' b hb t).2 h2⟩
    · rintro ⟨ht, htT, h1, h2⟩
      rw [hlt V' a ha, ← hhull t ht htT] at h1
      rw [hlt V' b hb, ← hhull t ht htT] at h2
      exact ⟨ht, htT, (hlt V a ha t).2 h1, (hlt V b hb t).2 h2⟩
  unfold K3.VTe
  rw [hidx]
  refine iInf_congr fun t => iInf_congr fun ht => ?_
  have hEq : EqOn V V' (Icc 0 t) := fun r hr => h ⟨hr.1, hr.2.trans ht.2.1⟩
  simp only [K3.vtKer, Ito.fwdMap_congr_of_eqOn hEq]

/-- **The retained Green energy depends only on the driver on `[0, T]`.** -/
theorem retainedGreenEnergy_congr {w w' : ℝ≥0 → ℝ} (hw : Continuous (Ito.rpath w))
    (hw' : Continuous (Ito.rpath w')) {T : ℝ≥0} (h : EqOn (Ito.rpath w) (Ito.rpath w') (Icc 0 (T : ℝ)))
    (φ : TestOn upperHalfPlaneOpens) :
    WangWu.retainedGreenEnergy w T φ = WangWu.retainedGreenEnergy w' T φ := by
  unfold WangWu.retainedGreenEnergy
  refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae
    (Eventually.of_forall fun b => ?_))
  show φ a * WangWu.retainedGreen w T a b * φ b = φ a * WangWu.retainedGreen w' T a b * φ b
  by_cases hab : a ∈ H ∧ b ∈ H
  · simp only [WangWu.retainedGreen, K3.VT, VTe_congr_of_eqOn hw hw' h hab.1 hab.2]
  · rcases not_and_or.1 hab with ha | hb
    · simp [testOn_eq_zero_of_notMem_H φ ha]
    · simp [testOn_eq_zero_of_notMem_H φ hb]

/-- **The safe condition at `t` depends only on the driver on `[0, t]`.** -/
theorem isSafeAt_congr {w w' : ℝ≥0 → ℝ} {t : ℝ≥0} (h : EqOn (Ito.rpath w) (Ito.rpath w') (Icc 0 (t : ℝ)))
    {K : Set ℂ} {δ Nb : ℝ} {σ₀ : ℝ≥0} {ζ : ℝ≥0∞} :
    Coupling.IsSafeAt K δ Nb σ₀ ζ w t ↔ Coupling.IsSafeAt K δ Nb σ₀ ζ w' t := by
  unfold Coupling.IsSafeAt
  have hsol : ∀ z : ℂ, (∃ u, IsForwardSol (Ito.rpath w) z t u) ↔ ∃ u, IsForwardSol (Ito.rpath w') z t u :=
    fun z => ⟨fun ⟨u, hu⟩ => ⟨u, (Ito.isForwardSol_iff_of_eqOn h u).1 hu⟩,
      fun ⟨u, hu⟩ => ⟨u, (Ito.isForwardSol_iff_of_eqOn h u).2 hu⟩⟩
  simp only [hsol, Ito.fwdMap_congr_of_eqOn h]

/-- **The safe exit time depends only on the driver up to the horizon `σ₀`.** -/
theorem safeExitTime_congr {w w' : ℝ≥0 → ℝ} {σ₀ : ℝ≥0}
    (h : EqOn (Ito.rpath w) (Ito.rpath w') (Icc 0 (σ₀ : ℝ))) {K : Set ℂ} {δ Nb : ℝ} {ζ : ℝ≥0∞} :
    Coupling.safeExitTime K δ Nb σ₀ ζ w = Coupling.safeExitTime K δ Nb σ₀ ζ w' := by
  unfold Coupling.safeExitTime
  congr 1
  ext t
  simp only [mem_ofPred_eq]
  by_cases ht : t ≤ σ₀
  · have h' : EqOn (Ito.rpath w) (Ito.rpath w') (Icc 0 (t : ℝ)) := fun r hr =>
      h ⟨hr.1, hr.2.trans (by exact_mod_cast ht)⟩
    rw [isSafeAt_congr h']
  · exact ⟨fun _ hs => ht hs.2.1, fun _ hs => ht hs.2.1⟩

end Congr

/-! ### Along a coupling path with infinite lifetime -/

section Path

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- **A good path**: infinite lifetime, `W₀ = 0`, and continuous driving coordinates. -/
def IsGoodPath (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
    (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}

theorem ae_isGoodPath {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, IsGoodPath W VL VR ζ ω := by
  filter_upwards [hζ, hE.2.2.2.2] with ω h1 hp
  exact ⟨h1, hp.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩

theorem IsGoodPath.isGoodStop (hg : IsGoodPath W VL VR ζ ω) (s : HistorySpace nL nR → ℝ≥0) :
    IsGoodStop s W VL VR ζ ω :=
  ⟨by rw [hg.1]; exact ENNReal.coe_lt_top, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

theorem IsGoodPath.continuous (hg : IsGoodPath W VL VR ζ ω) : Continuous fun t => W t ω := by
  have h := hg.2.2.1
  rw [hg.1] at h
  simpa [continuousOn_univ] using h

theorem IsGoodPath.continuous_rpath (hg : IsGoodPath W VL VR ζ ω) :
    Continuous (Ito.rpath fun t => W t ω) :=
  hg.continuous.comp continuous_real_toNNReal

/-- **The regularized driver of a stopped history is the stopped driver.** -/
theorem regPath_stopHistory (hg : IsGoodPath W VL VR ζ ω) (s : HistorySpace nL nR → ℝ≥0) :
    regPath (stopHistory s (killedHistory W VL VR ζ ω)) =
      fun t => W (min t (s (killedHistory W VL VR ζ ω))) ω := by
  rw [(isContHist_stopHistory (hg.isGoodStop s)).regPath_eq]
  funext t
  exact histPath_stopHistory (hg.isGoodStop s).1 hg.2.2.1 t

theorem eqOn_rpath_regPath_stopHistory (hg : IsGoodPath W VL VR ζ ω) (s : HistorySpace nL nR → ℝ≥0) :
    EqOn (Ito.rpath (regPath (stopHistory s (killedHistory W VL VR ζ ω)))) (Ito.rpath fun t => W t ω)
      (Icc 0 (s (killedHistory W VL VR ζ ω) : ℝ)) := by
  intro r hr
  rw [regPath_stopHistory hg s]
  simp only [Ito.rpath]
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]

/-- On a good path, the hulls of the stopped history before the stop are those of the driver. -/
theorem fwdHull_regPath_stopHistory (hg : IsGoodPath W VL VR ζ ω) (s : HistorySpace nL nR → ℝ≥0)
    {t : ℝ≥0} (ht : t ≤ s (killedHistory W VL VR ζ ω)) :
    fwdHull (Ito.rpath (regPath (stopHistory s (killedHistory W VL VR ζ ω)))) t =
      fwdHull (Ito.rpath fun t => W t ω) t :=
  YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_rpath_regPath _) hg.continuous_rpath t.coe_nonneg
    fun r hr => eqOn_rpath_regPath_stopHistory hg s ⟨hr.1, hr.2.trans (by exact_mod_cast ht)⟩

/-- On a good path, the hull of the history stopped at a rule is the driver's hull at the stop. -/
theorem regHull_stopHistory (hg : IsGoodPath W VL VR ζ ω) (s : HistorySpace nL nR → ℝ≥0) :
    regHull (stopHistory s (killedHistory W VL VR ζ ω)) =
      fwdHull (Ito.rpath fun t => W t ω) (s (killedHistory W VL VR ζ ω)) := by
  unfold regHull
  rw [histStop, stopHistory_fst_toNNReal, fwdHull_regPath_stopHistory hg s le_rfl]
  exact closure_fwdHull_inter_H hg.continuous_rpath (NNReal.coe_nonneg _)

/-- On a good path, the hull of the history stopped at a constant time `t` is the driver's hull at `t`. -/
theorem regHull_stopHistory_cstop (hg : IsGoodPath W VL VR ζ ω) (t : ℝ≥0) :
    regHull (stopHistory (cstop t) (killedHistory W VL VR ζ ω)) = fwdHull (Ito.rpath fun t => W t ω) t := by
  unfold regHull
  rw [histStop, stopHistory_fst_toNNReal]
  show closure (fwdHull (Ito.rpath (regPath (stopHistory (cstop t) (killedHistory W VL VR ζ ω)))) (t : ℝ)) ∩
    (upperHalfPlaneOpens : Set ℂ) = _
  rw [fwdHull_regPath_stopHistory hg (cstop t) (le_refl t)]
  exact closure_fwdHull_inter_H hg.continuous_rpath t.coe_nonneg

/-- **The label event of the history at `N` is the label property of the driver.** -/
theorem histLab_iff (hg : IsGoodPath W VL VR ζ ω) (N : ℕ) {C : Set ℂ} (hCH : C ⊆ H) :
    histLab N C (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) ↔ IsLabel (fun t => W t ω) C N := by
  have hst : ∀ s : ℝ≥0, s ≤ N → regHull (stopHistory (cstop s) (stopHistory (natStop N)
      (killedHistory W VL VR ζ ω))) = fwdHull (Ito.rpath fun t => W t ω) s := fun s hs => by
    rw [stopHistory_cstop_natStop hs, regHull_stopHistory_cstop hg]
  rw [histLab, IsLabel, IsActiveLabel, isPocketLabel_iff hCH, hst _ le_rfl]
  simp only [hst _ (ratTime_le N _)]
  rfl

/-- **The retained Green energy of the history at `N` is the coupling's.** -/
theorem histQ_eq (hg : IsGoodPath W VL VR ζ ω) (N : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    histQ N φ (stopHistory (cstop N) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))) =
      WangWu.retainedGreenEnergy (fun t => W t ω) N φ := by
  rw [stopHistory_cstop_natStop le_rfl]
  exact retainedGreenEnergy_congr (continuous_rpath_regPath _) hg.continuous_rpath
    (eqOn_rpath_regPath_stopHistory hg (cstop N)) φ

/-- **The safe exit rule of the history is the safe exit time of the driver.** -/
theorem safeRule_eq (hg : IsGoodPath W VL VR ζ ω) (K : Set ℂ) (m : ℝ) (N k : ℕ) :
    safeRule K m N k (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) =
      Coupling.safeExitTime K (m / ((k : ℝ) + 1)) k N ⊤ (fun t => W t ω) :=
  safeExitTime_congr (eqOn_rpath_regPath_stopHistory hg (natStop N))

end Path

end Aux50Hit

end InteractingSLE
