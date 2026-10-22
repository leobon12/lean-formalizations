import HigherDimLQGMetric.Locality.StageFinite
import HigherDimLQGMetric.Limits.JointInternalMeas

/-! Median-normalized truncated LFPP metrics and their internal coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l7a_truncScaledMetric {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (g : DistRd d) : ContMetric d :=
  (fieldLfppMetric ξ ⟨truncMollify κ ε g,
    l2c_continuous_truncMollify hd hκ hε g⟩).smul
      (aEps κ ξ ε)⁻¹ (inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε))

theorem l7a_truncScaledMetric_isLength {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (g : DistRd d) :
    (l7a_truncScaledMetric hd κ hκ ξ hε g).IsLength := by
  exact ContMetric.isLength_smul
    (inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε))
    (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε g,
      l2c_continuous_truncMollify hd hκ hε g⟩)

theorem l7a_truncScaledMetric_apply {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (g : DistRd d)
    (p : Rd d × Rd d) :
    (l7a_truncScaledMetric hd κ hκ ξ hε g).1 p =
      (aEps κ ξ ε)⁻¹ * fieldLfpp ξ (truncMollify κ ε g) p := by
  rfl

theorem l7a_truncScaledInternal_eq_smul {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (g : DistRd d)
    (U : TopologicalSpace.Opens (Rd d))
    (hUc : IsPreconnected (U : Set (Rd d))) :
    internalC (l7a_truncScaledMetric hd κ hκ ξ hε g)
      (l7a_truncScaledMetric_isLength hd κ hκ ξ hε g) U.isOpen hUc =
      (aEps κ ξ ε)⁻¹ • l7a_truncInternal hd hκ hε ξ g U hUc := by
  exact l6c_internalC_smul
    (fieldLfppMetric ξ ⟨truncMollify κ ε g,
      l2c_continuous_truncMollify hd hκ hε g⟩)
    (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε g,
      l2c_continuous_truncMollify hd hκ hε g⟩)
    (inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε)) U.isOpen hUc

theorem l7a_measurable_truncScaledMetric {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Measurable (l7a_truncScaledMetric hd κ hκ ξ hε) := by
  let φ : DistRd d → C(Rd d, ℝ) := fun g =>
    ⟨truncMollify κ ε g, l2c_continuous_truncMollify hd hκ hε g⟩
  have hφ : Measurable φ := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro z
    exact measurable_distOn_apply (truncTest κ ε z)
  have hD : Measurable (fun g => fieldLfppMetric ξ (φ g)) :=
    (l6c_measurable_fieldLfppMetric ξ).comp hφ
  let s : ℝ := (aEps κ ξ ε)⁻¹
  have hs : 0 < s := inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε)
  have hsmul : Continuous (fun D : ContMetric d => D.smul s hs) := by
    apply Continuous.subtype_mk
    change Continuous (fun D : ContMetric d => s • D.1)
    exact (continuous_const_smul s).comp continuous_subtype_val
  exact hsmul.measurable.comp hD

theorem l7a_measurable_truncScaledInternal {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (U : TopologicalSpace.Opens (Rd d))
    (hUc : IsPreconnected (U : Set (Rd d))) :
    Measurable (fun g =>
      internalC (l7a_truncScaledMetric hd κ hκ ξ hε g)
        (l7a_truncScaledMetric_isLength hd κ hκ ξ hε g)
        U.isOpen hUc) := by
  letI := U.isOpen.locallyCompactSpace
  exact measurable_internalC_of_measurable
    (l7a_truncScaledMetric hd κ hκ ξ hε)
    (l7a_measurable_truncScaledMetric hd κ hκ ξ hε)
    (l7a_truncScaledMetric_isLength hd κ hκ ξ hε) U.isOpen hUc

/-- Deterministic median normalization preserves the finite-stage independence
of all internal coordinates. -/
theorem l7a_indep_scaled_of_unscaled {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G R : MeasurableSpace Ω)
    {ι κ' : Type*} (S : Finset ι) (T : Finset κ')
    (g g' : Ω → DistRd d)
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (hind : Indep
      (G ⊔ ⨆ i ∈ S, MeasurableSpace.comap
        (fun ω => l7a_truncInternal hd hκ hε ξ (g ω) (W i) (hWc i ‹i ∈ S›))
        inferInstance)
      (R ⊔ ⨆ j ∈ T, MeasurableSpace.comap
        (fun ω => l7a_truncInternal hd hκ hε ξ (g' ω) (W' j) (hW'c j ‹j ∈ T›))
        inferInstance) P) :
    Indep
      (G ⊔ ⨆ i ∈ S, MeasurableSpace.comap
        (fun ω => internalC (l7a_truncScaledMetric hd κ hκ ξ hε (g ω))
          (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g ω))
          (W i).isOpen (hWc i ‹i ∈ S›)) inferInstance)
      (R ⊔ ⨆ j ∈ T, MeasurableSpace.comap
        (fun ω => internalC (l7a_truncScaledMetric hd κ hκ ξ hε (g' ω))
          (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g' ω))
          (W' j).isOpen (hW'c j ‹j ∈ T›)) inferInstance) P := by
  have hs (U : Set (Rd d)) :
      Continuous (fun E : C(U × U, ℝ) => (aEps κ ξ ε)⁻¹ • E) := by
    fun_prop
  have hA : G ⊔ ⨆ i ∈ S, MeasurableSpace.comap
      (fun ω => internalC (l7a_truncScaledMetric hd κ hκ ξ hε (g ω))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g ω))
        (W i).isOpen (hWc i ‹i ∈ S›)) inferInstance ≤
      G ⊔ ⨆ i ∈ S, MeasurableSpace.comap
        (fun ω => l7a_truncInternal hd hκ hε ξ (g ω) (W i)
          (hWc i ‹i ∈ S›)) inferInstance := by
    refine sup_le le_sup_left (iSup₂_le fun i hi => ?_)
    rw [show (fun ω => internalC
      (l7a_truncScaledMetric hd κ hκ ξ hε (g ω))
      (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g ω))
      (W i).isOpen (hWc i hi)) =
      (fun E : C((↑(W i) : Set (Rd d)) × (↑(W i) : Set (Rd d)), ℝ) =>
        (aEps κ ξ ε)⁻¹ • E) ∘
      (fun ω => l7a_truncInternal hd hκ hε ξ (g ω) (W i) (hWc i hi)) from
        funext fun ω => l7a_truncScaledInternal_eq_smul hd κ hκ ξ hε
          (g ω) (W i) (hWc i hi), ← MeasurableSpace.comap_comp]
    have hcoord : MeasurableSpace.comap
        (fun ω => l7a_truncInternal hd hκ hε ξ (g ω) (W i) (hWc i hi))
        inferInstance ≤
        (⨆ i ∈ S, MeasurableSpace.comap
          (fun ω => l7a_truncInternal hd hκ hε ξ (g ω) (W i)
            (hWc i ‹i ∈ S›)) inferInstance) :=
      le_iSup₂_of_le i hi le_rfl
    exact (MeasurableSpace.comap_mono (hs (W i)).measurable.comap_le).trans
      (hcoord.trans le_sup_right)
  have hB : R ⊔ ⨆ j ∈ T, MeasurableSpace.comap
      (fun ω => internalC (l7a_truncScaledMetric hd κ hκ ξ hε (g' ω))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g' ω))
        (W' j).isOpen (hW'c j ‹j ∈ T›)) inferInstance ≤
      R ⊔ ⨆ j ∈ T, MeasurableSpace.comap
        (fun ω => l7a_truncInternal hd hκ hε ξ (g' ω) (W' j)
          (hW'c j ‹j ∈ T›)) inferInstance := by
    refine sup_le le_sup_left (iSup₂_le fun j hj => ?_)
    rw [show (fun ω => internalC
      (l7a_truncScaledMetric hd κ hκ ξ hε (g' ω))
      (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g' ω))
      (W' j).isOpen (hW'c j hj)) =
      (fun E : C((↑(W' j) : Set (Rd d)) × (↑(W' j) : Set (Rd d)), ℝ) =>
        (aEps κ ξ ε)⁻¹ • E) ∘
      (fun ω => l7a_truncInternal hd hκ hε ξ (g' ω) (W' j) (hW'c j hj)) from
        funext fun ω => l7a_truncScaledInternal_eq_smul hd κ hκ ξ hε
          (g' ω) (W' j) (hW'c j hj), ← MeasurableSpace.comap_comp]
    have hcoord : MeasurableSpace.comap
        (fun ω => l7a_truncInternal hd hκ hε ξ (g' ω) (W' j) (hW'c j hj))
        inferInstance ≤
        (⨆ j ∈ T, MeasurableSpace.comap
          (fun ω => l7a_truncInternal hd hκ hε ξ (g' ω) (W' j)
            (hW'c j ‹j ∈ T›)) inferInstance) :=
      le_iSup₂_of_le j hj le_rfl
    exact (MeasurableSpace.comap_mono (hs (W' j)).measurable.comap_le).trans
      (hcoord.trans le_sup_right)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hA) hB

end HigherDimLQGMetric
