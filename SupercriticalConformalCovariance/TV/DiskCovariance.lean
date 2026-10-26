import SupercriticalConformalCovariance.TV.DiskKernel
import LQGMetric.Field.GreenFn
import LQGMetric.Field.ZeroBoundaryAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Metric Function
open QuantumZipper QuantumZipper.K3
open LQGMetric
open scoped ComplexConjugate

namespace SupercriticalConformalCovariance.TV

theorem isConformalOnto_comp
    {D E F : Set ℂ} {φ ψ : ℂ → ℂ}
    (hφ : IsConformalOnto φ D E) (hψ : IsConformalOnto ψ E F) :
    IsConformalOnto (ψ ∘ φ) D F := by
  refine ⟨hφ.isOpen, hψ.diffOn.comp hφ.diffOn ?_, ?_, ?_, ?_⟩
  · rw [← hφ.image_eq]
    exact fun _ h => mem_image_of_mem φ h
  · intro x hx y hy hxy
    exact hφ.injOn hx hy (hψ.injOn
      (hφ.image_eq ▸ mem_image_of_mem φ hx)
      (hφ.image_eq ▸ mem_image_of_mem φ hy) hxy)
  · rw [image_comp, hφ.image_eq, hψ.image_eq]
  · intro z hz
    have hφz : DifferentiableAt ℂ φ z :=
      hφ.diffOn.differentiableAt (hφ.isOpen.mem_nhds hz)
    have hψz : DifferentiableAt ℂ ψ (φ z) :=
      hψ.diffOn.differentiableAt (hψ.isOpen.mem_nhds
        (hφ.image_eq ▸ mem_image_of_mem φ hz))
    rw [deriv_comp z hψz hφz]
    exact mul_ne_zero (hψ.deriv_ne _ (hφ.image_eq ▸ mem_image_of_mem φ hz))
      (hφ.deriv_ne _ hz)

theorem affOpens_one_neg_cancel (U : TopologicalSpace.Opens ℂ) (w : ℂ) :
    affOpens 1 (-w) (affOpens 1 w U) = U := by
  ext z
  simp [affOpens, LQGMetric.affMap]

theorem isConformalOnto_shifted_discMap {L : ℝ} (hL : 0 < L) (w : ℂ) :
    IsConformalOnto
      (discMap 0 L ∘ affFwd 1 (-w))
      (affOpens 1 w ⟨ball (0 : ℂ) L, isOpen_ball⟩) H := by
  have hs := LQGMetric.isConformalOnto_affFwd
    (r := (1 : ℝ)) (z := -w) one_ne_zero
    (affOpens 1 w ⟨ball (0 : ℂ) L, isOpen_ball⟩)
  rw [affOpens_one_neg_cancel] at hs
  exact isConformalOnto_comp hs (isConformalOnto_discMap_m7d hL)

theorem exists_zeroGFFTestCov_disk_translated_green
    {L : ℝ} (hL : 0 < L)
    (φ ψ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩) :
    ∃ w : ℂ,
      let U : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) L, isOpen_ball⟩
      let V := affOpens 1 w U
      (V : Set ℂ) ⊆ H ∧
      zeroGFFTestCov U φ ψ =
        ∫ p : ℂ × ℂ,
          (zbPull 1 w one_ne_zero φ) p.1 *
          (zbPull 1 w one_ne_zero ψ) p.2 *
          greenH ((discMap 0 L ∘ affFwd 1 (-w)) p.1)
            ((discMap 0 L ∘ affFwd 1 (-w)) p.2)
        ∂((volume : Measure ℂ).prod volume) := by
  obtain ⟨w, hw⟩ :=
    LQGMetric.exists_affOpens_one_subset_H
      (U := ⟨ball (0 : ℂ) L, isOpen_ball⟩) isBounded_ball
  refine ⟨w, hw, ?_⟩
  have hg := LQGMetric.zeroGFFTestCov_eq_green hw
    (isConformalOnto_shifted_discMap hL w)
    (zbPull 1 w one_ne_zero φ) (zbPull 1 w one_ne_zero ψ)
  rw [LQGMetric.zeroGFFTestCov_affine (r := (1 : ℝ))
    (z := w) one_ne_zero φ ψ] at hg
  simpa using hg

theorem integral_prod_add_right_eq_self (f : ℂ × ℂ → ℝ)
    (hf : Measurable f) (w : ℂ) :
    (∫ p : ℂ × ℂ, f (p.1 + w, p.2 + w)
      ∂((volume : Measure ℂ).prod volume)) =
      ∫ p : ℂ × ℂ, f p ∂((volume : Measure ℂ).prod volume) := by
  let shift : ℂ × ℂ → ℂ × ℂ :=
    Prod.map (fun z => z + w) (fun z => z + w)
  have hm : Measurable shift := by fun_prop
  have heq : Measure.map shift ((volume : Measure ℂ).prod volume) =
      (volume : Measure ℂ).prod volume := by
    rw [← Measure.map_prod_map (volume : Measure ℂ) volume
      (by fun_prop : Measurable fun z : ℂ => z + w)
      (by fun_prop : Measurable fun z : ℂ => z + w)]
    simp [MeasureTheory.map_add_right_eq_self]
  calc
    _ = ∫ p, f (shift p) ∂((volume : Measure ℂ).prod volume) := rfl
    _ = ∫ p, f p ∂(Measure.map shift ((volume : Measure ℂ).prod volume)) :=
      (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [heq]

theorem integrable_prod_add_right_iff (f : ℂ × ℂ → ℝ)
    (hf : Measurable f) (w : ℂ) :
    Integrable (fun p : ℂ × ℂ => f (p.1 + w, p.2 + w))
      ((volume : Measure ℂ).prod volume) ↔
    Integrable f ((volume : Measure ℂ).prod volume) := by
  let shift : ℂ × ℂ → ℂ × ℂ :=
    Prod.map (fun z => z + w) (fun z => z + w)
  have hm : Measurable shift := by fun_prop
  have heq : Measure.map shift ((volume : Measure ℂ).prod volume) =
      (volume : Measure ℂ).prod volume := by
    rw [← Measure.map_prod_map (volume : Measure ℂ) volume
      (by fun_prop : Measurable fun z : ℂ => z + w)
      (by fun_prop : Measurable fun z : ℂ => z + w)]
    simp [MeasureTheory.map_add_right_eq_self]
  have h := (integrable_map_measure (μ := ((volume : Measure ℂ).prod volume))
    hf.aestronglyMeasurable hm.aemeasurable).symm
  rw [heq] at h
  simpa only [shift, Prod.map, Function.comp_def] using h

/-- Covariance of a zero-boundary GFF on a disk as a signed Green-kernel integral. -/
theorem zeroGFFTestCov_disk_eq_discG {L : ℝ} (hL : 0 < L)
    (φ ψ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩) :
    zeroGFFTestCov (ball (0 : ℂ) L) φ ψ =
      ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 * discG 0 L p.1 p.2
        ∂((volume : Measure ℂ).prod volume) := by
  obtain ⟨w, _, hg⟩ := exists_zeroGFFTestCov_disk_translated_green hL φ ψ
  let f : ℂ × ℂ → ℝ := fun p =>
    (zbPull 1 w one_ne_zero φ) p.1 *
    (zbPull 1 w one_ne_zero ψ) p.2 *
    greenH ((discMap 0 L ∘ affFwd 1 (-w)) p.1)
      ((discMap 0 L ∘ affFwd 1 (-w)) p.2)
  have hfm : Measurable f := by
    have hm : Measurable (discMap 0 L ∘ affFwd 1 (-w)) :=
      (measurable_discMap_m7d 0 L).comp (continuous_affFwd 1 (-w)).measurable
    exact (((zbPull 1 w one_ne_zero φ).continuous.measurable.comp measurable_fst).mul
      ((zbPull 1 w one_ne_zero ψ).continuous.measurable.comp measurable_snd)).mul
      (measurable_greenH.comp
        ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))
  have hchange := integral_prod_add_right_eq_self f hfm w
  rw [← hchange] at hg
  have hshift (p : ℂ × ℂ) :
      f (p.1 + w, p.2 + w) =
      φ p.1 * ψ p.2 * greenH (discMap 0 L p.1) (discMap 0 L p.2) := by
    simp [f, zbPull_apply, LQGMetric.affMap, affFwd]
  simp_rw [hshift] at hg
  apply hg.trans
  apply integral_congr_ae
  filter_upwards [LQGMetric.ae_ne_diag] with p hp
  by_cases h1 : p.1 ∈ ball (0 : ℂ) L
  · by_cases h2 : p.2 ∈ ball (0 : ℂ) L
    · rw [greenH_discMap_m7d hL h1 h2 hp]
    · rw [ψ.zero_on_compl h2]
      simp
  · rw [φ.zero_on_compl h1]
    simp

theorem integrable_diskHarmonicKernel_test_mul {L : ℝ} (hL : 0 < L)
    (φ ψ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩) :
    Integrable (fun p : ℂ × ℂ =>
      φ p.1 * ψ p.2 * diskHarmonicKernel L p.1 p.2)
      ((volume : Measure ℂ).prod volume) := by
  let K : Set (ℂ × ℂ) := tsupport (φ : ℂ → ℝ) ×ˢ tsupport (ψ : ℂ → ℝ)
  have hK : IsCompact K := φ.hasCompactSupport.isCompact.prod ψ.hasCompactSupport.isCompact
  have hnum : ∀ p ∈ K, (L : ℂ) ^ 2 - p.1 * conj p.2 ≠ 0 := by
    intro p hp
    have h1 : ‖p.1‖ < L := by
      have := φ.tsupport_subset hp.1
      simpa [mem_ball, dist_zero_right] using this
    have h2 : ‖p.2‖ < L := by
      have := ψ.tsupport_subset hp.2
      simpa [mem_ball, dist_zero_right] using this
    have hprod : ‖p.1‖ * ‖p.2‖ < L ^ 2 := by
      calc
        ‖p.1‖ * ‖p.2‖ ≤ L * ‖p.2‖ :=
          mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
        _ < L * L := mul_lt_mul_of_pos_left h2 hL
        _ = L ^ 2 := by ring
    simpa only [Complex.ofReal_zero, sub_zero] using
      (numer_ne_zero_m7d (t := 0) (r := L) (x := p.1) (y := p.2)
        (by simpa only [Complex.ofReal_zero, sub_zero] using hprod))
  have hnumc : ContinuousOn (fun p : ℂ × ℂ =>
      ‖(L : ℂ) ^ 2 - p.1 * conj p.2‖) K :=
    (continuous_const.sub (continuous_fst.mul
      (Complex.continuous_conj.comp continuous_snd))).norm.continuousOn
  have hkc : ContinuousOn (fun p : ℂ × ℂ =>
      diskHarmonicKernel L p.1 p.2) K := by
    exact continuousOn_const.sub (hnumc.log fun p hp =>
      norm_ne_zero_iff.mpr (hnum p hp))
  have hfc : ContinuousOn (fun p : ℂ × ℂ =>
      φ p.1 * ψ p.2 * diskHarmonicKernel L p.1 p.2) K :=
    ((φ.continuous.comp continuous_fst).continuousOn.mul
      ((ψ.continuous.comp continuous_snd).continuousOn)).mul hkc
  have hsup : support (fun p : ℂ × ℂ =>
      φ p.1 * ψ p.2 * diskHarmonicKernel L p.1 p.2) ⊆ K := by
    intro p hp
    constructor
    · by_contra hnot
      have hz : φ p.1 = 0 := image_eq_zero_of_notMem_tsupport hnot
      exact hp (by simp [hz])
    · by_contra hnot
      have hz : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
      exact hp (by simp [hz])
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp
    (hfc.integrableOn_compact hK)

theorem integrable_green_test_prod
    {V : TopologicalSpace.Opens ℂ} {m : ℂ → ℂ}
    (hVH : (V : Set ℂ) ⊆ H) (hm : IsConformalOnto m V H)
    (φ ψ : TestOn V) :
    Integrable (fun p : ℂ × ℂ => φ p.1 * ψ p.2 *
      greenH (m p.1) (m p.2))
      ((volume : Measure ℂ).prod volume) := by
  have hφ0 : ∀ x ∉ (V : Set ℂ), φ x = 0 := fun x hx => φ.zero_on_compl hx
  have hψ0 : ∀ x ∉ (V : Set ℂ), ψ x = 0 := fun x hx => ψ.zero_on_compl hx
  have hφn : ∀ x ∉ (V : Set ℂ), -φ x = 0 := fun x hx => by rw [hφ0 x hx, neg_zero]
  have hψn : ∀ x ∉ (V : Set ℂ), -ψ x = 0 := fun x hx => by rw [hψ0 x hx, neg_zero]
  obtain ⟨M1, R1, b1⟩ := bddDens_test φ.continuous φ.hasCompactSupport
  obtain ⟨M2, R2, b2⟩ := bddDens_test (φ := fun z => -φ z)
    φ.continuous.neg φ.hasCompactSupport.neg
  obtain ⟨M3, R3, b3⟩ := bddDens_test ψ.continuous ψ.hasCompactSupport
  obtain ⟨M4, R4, b4⟩ := bddDens_test (φ := fun z => -ψ z)
    ψ.continuous.neg ψ.hasCompactSupport.neg
  have i1 := integrable_greenDensProd hm φ.continuous ψ.continuous hφ0 hψ0
    (kerInt_ne_top hm hVH b1 b3)
  have i2 := integrable_greenDensProd (f := fun z => φ z) (g := fun z => -ψ z)
    hm φ.continuous ψ.continuous.neg hφ0 hψn
      (kerInt_ne_top hm hVH b1 b4)
  have i3 := integrable_greenDensProd (f := fun z => -φ z) (g := fun z => ψ z)
    hm φ.continuous.neg ψ.continuous hφn hψ0
      (kerInt_ne_top hm hVH b2 b3)
  have i4 := integrable_greenDensProd (f := fun z => -φ z) (g := fun z => -ψ z)
    hm φ.continuous.neg ψ.continuous.neg hφn hψn
      (kerInt_ne_top hm hVH b2 b4)
  have he : (fun p : ℂ × ℂ => φ p.1 * ψ p.2 *
      greenH (m p.1) (m p.2)) =
      fun p => greenDensProd m V φ ψ p -
        greenDensProd m V φ (fun z => -ψ z) p -
        greenDensProd m V (fun z => -φ z) ψ p +
        greenDensProd m V (fun z => -φ z) (fun z => -ψ z) p := by
    funext p
    by_cases h1 : p.1 ∈ (V : Set ℂ)
    · by_cases h2 : p.2 ∈ (V : Set ℂ)
      · simp only [greenDensProd, confMod_eqOn h1, confMod_eqOn h2]
        calc
          φ p.1 * ψ p.2 * greenH (m p.1) (m p.2) =
              (max (φ p.1) 0 - max (-φ p.1) 0) *
              (max (ψ p.2) 0 - max (-ψ p.2) 0) *
              greenH (m p.1) (m p.2) := by
                rw [max_sub_max_neg_K3, max_sub_max_neg_K3]
          _ = _ := by ring
      · simp [greenDensProd, hψ0 _ h2, hψn _ h2]
    · simp [greenDensProd, hφ0 _ h1, hφn _ h1]
  rw [he]
  exact ((i1.sub i2).sub i3).add i4

theorem integrable_discG_test_mul {L : ℝ} (hL : 0 < L)
    (φ ψ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩) :
    Integrable (fun p : ℂ × ℂ => φ p.1 * ψ p.2 * discG 0 L p.1 p.2)
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨w, hw, _⟩ := exists_zeroGFFTestCov_disk_translated_green hL φ ψ
  let f : ℂ × ℂ → ℝ := fun p =>
    (zbPull 1 w one_ne_zero φ) p.1 *
    (zbPull 1 w one_ne_zero ψ) p.2 *
    greenH ((discMap 0 L ∘ affFwd 1 (-w)) p.1)
      ((discMap 0 L ∘ affFwd 1 (-w)) p.2)
  have hfm : Measurable f := by
    have hm : Measurable (discMap 0 L ∘ affFwd 1 (-w)) :=
      (measurable_discMap_m7d 0 L).comp (continuous_affFwd 1 (-w)).measurable
    exact (((zbPull 1 w one_ne_zero φ).continuous.measurable.comp measurable_fst).mul
      ((zbPull 1 w one_ne_zero ψ).continuous.measurable.comp measurable_snd)).mul
      (measurable_greenH.comp
        ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))
  have hfi : Integrable f ((volume : Measure ℂ).prod volume) :=
    integrable_green_test_prod hw (isConformalOnto_shifted_discMap hL w)
      (zbPull 1 w one_ne_zero φ) (zbPull 1 w one_ne_zero ψ)
  have hshift : (fun p : ℂ × ℂ => f (p.1 + w, p.2 + w)) =
      fun p => φ p.1 * ψ p.2 * greenH (discMap 0 L p.1) (discMap 0 L p.2) := by
    funext p
    simp [f, zbPull_apply, LQGMetric.affMap, affFwd]
  have hi := (integrable_prod_add_right_iff f hfm w).mpr hfi
  rw [hshift] at hi
  apply hi.congr
  filter_upwards [LQGMetric.ae_ne_diag] with p hp
  by_cases h1 : p.1 ∈ ball (0 : ℂ) L
  · by_cases h2 : p.2 ∈ ball (0 : ℂ) L
    · rw [greenH_discMap_m7d hL h1 h2 hp]
    · rw [ψ.zero_on_compl h2]
      simp
  · rw [φ.zero_on_compl h1]
    simp

theorem integrable_log_test_mul {L : ℝ} (hL : 0 < L)
    (φ ψ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩) :
    Integrable (fun p : ℂ × ℂ =>
      φ p.1 * (-Real.log ‖p.1 - p.2‖) * ψ p.2)
      ((volume : Measure ℂ).prod volume) := by
  have hi := (integrable_discG_test_mul hL φ ψ).add
    (integrable_diskHarmonicKernel_test_mul hL φ ψ)
  have he : (fun p : ℂ × ℂ =>
      φ p.1 * ψ p.2 * discG 0 L p.1 p.2 +
      φ p.1 * ψ p.2 * diskHarmonicKernel L p.1 p.2) =
      fun p => φ p.1 * (-Real.log ‖p.1 - p.2‖) * ψ p.2 := by
    funext p
    simp only [discG, diskHarmonicKernel, Complex.ofReal_zero, sub_zero]
    ring
  rw [← he]
  exact hi

theorem logCov_sub_zeroGFFTestCov_disk_eq_harmonicKernel
    {L : ℝ} (hL : 0 < L)
    (φ ψ : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩) :
    LQGMetric.logCov φ ψ -
      zeroGFFTestCov (ball (0 : ℂ) L) φ ψ =
      ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 *
        diskHarmonicKernel L p.1 p.2
        ∂((volume : Measure ℂ).prod volume) := by
  have hiLog := integrable_log_test_mul hL φ ψ
  have hiG := integrable_discG_test_mul hL φ ψ
  have hlog : LQGMetric.logCov φ ψ =
      ∫ p : ℂ × ℂ, φ p.1 * (-Real.log ‖p.1 - p.2‖) * ψ p.2
        ∂((volume : Measure ℂ).prod volume) := by
    rw [LQGMetric.logCov]
    exact (integral_prod _ hiLog).symm
  rw [hlog, zeroGFFTestCov_disk_eq_discG hL, ← integral_sub hiLog hiG]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [discG, diskHarmonicKernel, Complex.ofReal_zero, sub_zero]
  ring

end SupercriticalConformalCovariance.TV
