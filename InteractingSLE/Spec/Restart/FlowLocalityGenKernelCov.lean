/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenKernelProb
import InteractingSLE.WangWu.BridgeTrace
import InteractingSLE.Spec.Restart.FlowStopIdentCMContactTilt

/-!
# Flow locality with a general agreement set: the retained covariance against a test off the hull

Packet PROVE-G7A-LOC (PROVE-G3RESTART §5.2, step 4). With every born pocket retained, the conditional covariance at a
stop is that of the zero-boundary GFF on `ℍ \ η[0,t]` (pockets included). Against a test `φ` off the filled hull it
only sees the **alive part** of the other function: QuantumZipper's node C5 writes the covariance with the kernel
`V_t` (`K3.zeroGFFTestCov_compl_image_eq`), which is `G_ℍ(f_t a, f_t b)` between alive points
(`K3.VTe_eq_vtKer_of_lt`) and `0` between an alive point and a swallowed one (`K3.VTe_eq_zero_of_swallowTime_ne`).

* **`zeroGFFTestCov_eq_greenCross_of_alive`**: `Cov_{ℍ∖η[0,t]}(φ, ψ) = greenCross_t(φ, 1_{ℍ∖K_t} ψ)`;
* `zeroGFFTestCov_self_eq_of_alive`: `Cov_{ℍ∖η[0,t]}(φ, φ) = E_t(φ)` (the frozen Loewner Green energy);
* **`tendsto_zeroGFFTestCov_of_alive`**: for tests `s_n` dominated by and converging to a bounded compactly
  supported `v`, `Cov_{ℍ∖η[0,t]}(φ, s_n) → greenCross_t(φ, 1_{ℍ∖K_t} v)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Metric QuantumZipper
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.FlowLocalityGen

/-- **The retained covariance against a test off the hull** sees only the alive part of the other test. -/
theorem zeroGFFTestCov_eq_greenCross_of_alive {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) (harea : volume (η '' Icc 0 t ∩ H) = 0) {W : ℝ → ℝ} (hW : Continuous W) {t₂ : ℝ}
    (htt₂ : (t : ℝ) < t₂) (hWeq : ∀ r ∈ Icc (0 : ℝ) t₂, W r = Ito.rpath w r)
    (φ ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull W t)) :
    zeroGFFTestCov (H \ η '' Icc 0 t) φ ψ = LocalExt.greenCross W t φ ((H \ fwdHull W t).indicator ψ) := by
  obtain ⟨W', η', T', htT', hg, heq, himg⟩ := hη.exists_genTrace hw hw0 ht
  let ρ : TestFun H := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  let σ : TestFun H := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩
  have harea' : volume (η' '' Icc 0 (t : ℝ) ∩ H) = 0 := by rwa [himg]
  have hC5 := K3.zeroGFFTestCov_compl_image_eq hg (NNReal.coe_nonneg t) harea' ρ σ
  rw [himg] at hC5
  rw [hC5, LocalExt.greenCross]
  have hT₃ : (t : ℝ) < min T' t₂ := lt_min htT' htt₂
  have heq' : EqOn W' W (Icc 0 (min T' t₂)) := fun r hr => by
    rw [hWeq r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩]
    exact (heq ⟨hr.1, hr.2.trans (min_le_left _ _)⟩).symm
  have hφH : ∀ z, φ z ≠ 0 → z ∈ H \ fwdHull W t := fun z hz => by
    have hzt : z ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 hz)
    exact ⟨φ.tsupport_subset hzt, Set.disjoint_left.1 hφ hzt⟩
  have hψH : ∀ z, ψ z ≠ 0 → z ∈ H := fun z hz =>
    ψ.tsupport_subset (subset_tsupport ψ (Function.mem_support.2 hz))
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  refine integral_congr_ae ?_
  have hne : ∀ᵐ b ∂(volume : Measure ℂ), b ≠ a := by
    have h0 : (volume : Measure ℂ) {a} = 0 := measure_singleton a
    exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun b hb => hb
  filter_upwards [hne] with b hba
  show φ a * ψ b * K3.VT W' t a b = _
  by_cases hφa : φ a = 0
  · simp [hφa]
  have ha := hφH a hφa
  by_cases hψb : ψ b = 0
  · simp [hψb]
  have hb : b ∈ H := hψH b hψb
  have hV : K3.VTe W' t a b = K3.VTe W t a b :=
    WangWu.VTe_eq_of_eqOn hT₃ hg.contW.continuousOn hW.continuousOn heq' ha.1 hb
  have haT : ¬ swallowTime W a ≤ ENNReal.ofReal (t : ℝ) := fun h => ha.2 ⟨ha.1, h⟩
  by_cases hbK : b ∈ fwdHull W t
  · have h0 : K3.VTe W t a b = 0 := by
      refine K3.VTe_eq_zero_of_swallowTime_ne hW ha.1 hb (fun he => haT (he ▸ hbK.2)) ?_
      exact min_le_of_right_le hbK.2
    rw [indicator_of_notMem (fun h => h.2 hbK), K3.VT, hV, h0]
    simp
  · have hbA : b ∈ H \ fwdHull W t := ⟨hb, hbK⟩
    have hbT : ¬ swallowTime W b ≤ ENNReal.ofReal (t : ℝ) := fun h => hbK ⟨hb, h⟩
    have hk : K3.VTe W t a b = K3.vtKer W t a b :=
      K3.VTe_eq_vtKer_of_lt hW ha.1 hb (NNReal.coe_nonneg t) (lt_of_not_ge haT) (lt_of_not_ge hbT)
    have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
    have hfa : fwdMap W t a ∈ Hbar :=
      (Ito.im_fwdMap_pos hW ht0 ha (s := (t : ℝ)) ⟨ht0, le_rfl⟩).le
    have hfb : fwdMap W t b ∈ Hbar :=
      (Ito.im_fwdMap_pos hW ht0 hbA (s := (t : ℝ)) ⟨ht0, le_rfl⟩).le
    have hfab : fwdMap W t a ≠ fwdMap W t b := fun h =>
      hba (FwdHolo.injOn_fwdMap hW ht0 ha hbA h).symm
    have hG := greenH_nonneg hfa hfb hfab
    rw [indicator_of_mem hbA, K3.VT, hV, hk, K3.vtKer, ENNReal.toReal_ofReal hG]
    ring

/-- The retained variance of a test off the hull is the frozen Loewner Green energy. -/
theorem zeroGFFTestCov_self_eq_of_alive {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) (harea : volume (η '' Icc 0 t ∩ H) = 0) {W : ℝ → ℝ} (hW : Continuous W) {t₂ : ℝ}
    (htt₂ : (t : ℝ) < t₂) (hWeq : ∀ r ∈ Icc (0 : ℝ) t₂, W r = Ito.rpath w r)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull W t)) :
    zeroGFFTestCov (H \ η '' Icc 0 t) φ φ = loewnerGreenEnergy W t φ := by
  rw [zeroGFFTestCov_eq_greenCross_of_alive hη hw hw0 ht harea hW htt₂ hWeq φ φ hφ,
    LocalExt.loewnerGreenEnergy_eq_greenCross]
  congr 1
  funext z
  by_cases hz : z ∈ H \ fwdHull W t
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz]
    by_contra hne
    have hzt : z ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 (Ne.symm hne))
    exact hz ⟨φ.tsupport_subset hzt, Set.disjoint_left.1 hφ hzt⟩

/-- **The retained cross covariance along dominated approximations** of a bounded compactly supported `v`. -/
theorem tendsto_zeroGFFTestCov_of_alive {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) (harea : volume (η '' Icc 0 t ∩ H) = 0) {W : ℝ → ℝ} (hW : Continuous W) {t₂ : ℝ}
    (htt₂ : (t : ℝ) < t₂) (hWeq : ∀ r ∈ Icc (0 : ℝ) t₂, W r = Ito.rpath w r)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull W t)) {v : ℂ → ℝ}
    (hvm : Measurable v) {C : ℝ} (hvC : ∀ z, |v z| ≤ C) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hvK : ∀ z, v z ≠ 0 → z ∈ K) {s : ℕ → LQGMetric.TestOn upperHalfPlaneOpens} (hsle : ∀ n z, |s n z| ≤ |v z|)
    (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (v z))) :
    Tendsto (fun n => zeroGFFTestCov (H \ η '' Icc 0 t) φ (s n)) atTop
      (𝓝 (LocalExt.greenCross W t φ ((H \ fwdHull W t).indicator v))) := by
  have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  simp_rw [zeroGFFTestCov_eq_greenCross_of_alive hη hw hw0 ht harea hW htt₂ hWeq φ _ hφ]
  have hAm : MeasurableSet (H \ fwdHull W t) := (FwdHolo.isOpen_compl_fwdHull hW ht0).measurableSet
  have hgt : ∀ f : ℂ → ℝ, Measurable f → (∃ C', ∀ z, |f z| ≤ C') → (∀ z, f z ≠ 0 → z ∈ K) →
      LocalExt.IsGreenTest W t ((H \ fwdHull W t).indicator f) := by
    intro f hfm ⟨C', hC'⟩ hfK
    refine ⟨hfm.indicator hAm, ⟨C', fun z => ?_⟩, ⟨K, hK, hKH, fun z hz => hfK z ?_⟩, fun z hz => ?_⟩
    · by_cases hz : z ∈ H \ fwdHull W t
      · rw [indicator_of_mem hz]; exact hC' z
      · rw [indicator_of_notMem hz, abs_zero]; exact (abs_nonneg _).trans (hC' z)
    · by_contra h0
      exact hz (by
        by_cases hz' : z ∈ H \ fwdHull W t
        · rw [indicator_of_mem hz']; exact h0
        · rw [indicator_of_notMem hz'])
    · by_contra hz'
      exact hz (indicator_of_notMem hz' _)
  have hsK : ∀ n z, s n z ≠ 0 → z ∈ K := fun n z hz => hvK z fun h0 => hz (by
    have := hsle n z
    rw [h0, abs_zero] at this
    exact abs_nonpos_iff.1 this)
  have hgv := hgt v hvm ⟨C, hvC⟩ hvK
  have hgs : ∀ n, LocalExt.IsGreenTest W t ((H \ fwdHull W t).indicator (s n)) := fun n =>
    hgt (s n) (s n).continuous.measurable ⟨C, fun z => (hsle n z).trans (hvC z)⟩ (hsK n)
  have hle : ∀ n z, |(H \ fwdHull W t).indicator (s n) z| ≤ |(H \ fwdHull W t).indicator v z| := fun n z => by
    by_cases hz : z ∈ H \ fwdHull W t
    · rw [indicator_of_mem hz, indicator_of_mem hz]; exact hsle n z
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]
  have hlim : ∀ z, Tendsto (fun n => (H \ fwdHull W t).indicator (s n) z) atTop
      (𝓝 ((H \ fwdHull W t).indicator v z)) := fun z => by
    by_cases hz : z ∈ H \ fwdHull W t
    · simp only [indicator_of_mem hz]; exact hslim z
    · simp only [indicator_of_notMem hz]; exact tendsto_const_nhds
  exact (FlowStopIdentCM.tendsto_greenCross_of_dominated ht0 htt₂ hW.continuousOn
    (LocalExt.isGreenTest_of_testOn φ hφ) hgv hgs hgv hle hlim).1

end InteractingSLE.Restart.FlowLocalityGen
