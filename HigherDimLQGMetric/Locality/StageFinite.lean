import HigherDimLQGMetric.Locality.StageAll

/-! Finite-family truncated LFPP independence with a single exterior cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The continuous internal metric of the truncated LFPP field. -/
def l7a_truncInternal {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) (g : DistRd d)
    (W : TopologicalSpace.Opens (Rd d))
    (hWc : IsPreconnected (W : Set (Rd d))) : C(W × W, ℝ) :=
  internalC (fieldLfppMetric ξ ⟨truncMollify κ ε g,
      l2c_continuous_truncMollify hd hκ hε g⟩)
    (fieldLfppMetric_isLength ξ ⟨truncMollify κ ε g,
      l2c_continuous_truncMollify hd hκ hε g⟩) W.isOpen hWc

theorem l7a_indep_stage_finite {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → DistRd d) (V : TopologicalSpace.Opens (Rd d))
    {ι κ' : Type*} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (hWcomp : ∀ i ∈ S, IsCompact (closure (W i : Set (Rd d))))
    (hW'comp : ∀ j ∈ T, IsCompact (closure (W' j : Set (Rd d))))
    (hWV : ∀ i ∈ S, closure (W i : Set (Rd d)) ⊆ V)
    (hW'U : ∀ j ∈ T, closure (W' j : Set (Rd d)) ⊆ extOpen V)
    (H : Ω → Rd d → ℝ)
    (hHcont : ∀ ω, ContinuousOn (H ω) (extOpen V))
    (hind : Indep
      (MeasurableSpace.comap (fun ω => restrictTo (extOpen V) (g ω) -
        ofFunOn (extOpen V) (H ω)) inferInstance)
      (fieldSigmaRd g V) P) :
    ∃ (φ : C(Rd d, ℝ)) (hφsup : tsupport φ ⊆ extOpen V),
      HasCompactSupport φ ∧ ∃ m : ℕ, ∀ k : ℕ,
      let g' : Ω → DistRd d := fun ω => g ω - ofCont
        ⟨fun z => φ z * H ω z,
          l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω)
            (hHcont ω) hφsup⟩
      let R : Ω → DistOn (extOpen V) := fun ω =>
        restrictTo (extOpen V) (g ω) - ofFunOn (extOpen V) (H ω)
      Indep
        (fieldSigmaRd g V ⊔ ⨆ i ∈ S,
          MeasurableSpace.comap (fun ω => l7a_truncInternal hd hκ
            (hεs (k + m)) ξ (g ω) (W i) (hWc i ‹i ∈ S›)) inferInstance)
        (MeasurableSpace.comap R inferInstance ⊔ ⨆ j ∈ T,
          MeasurableSpace.comap (fun ω => l7a_truncInternal hd hκ
            (hεs (k + m)) ξ (g' ω) (W' j) (hW'c j ‹j ∈ T›)) inferInstance) P := by
  classical
  let K : Set (Rd d) := ⋃ i ∈ S, closure (W i : Set (Rd d))
  let K' : Set (Rd d) := ⋃ j ∈ T, closure (W' j : Set (Rd d))
  have hK : IsCompact K := S.isCompact_biUnion hWcomp
  have hK' : IsCompact K' := T.isCompact_biUnion hW'comp
  have hKV : K ⊆ V := iUnion₂_subset hWV
  have hK'U : K' ⊆ extOpen V := iUnion₂_subset hW'U
  obtain ⟨φ, U₁, _, hφcomp, hφsup, hU₁open, hK'U₁, hφ1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hK' (extOpen V).isOpen hK'U
  have hU₁ext : U₁ ⊆ extOpen V := by
    intro z hz
    apply hφsup
    apply subset_tsupport
    change φ z ≠ 0
    rw [hφ1 z hz]
    norm_num
  let U₁o : TopologicalSpace.Opens (Rd d) := ⟨U₁, hU₁open⟩
  have hU₁exto : U₁o ≤ extOpen V := hU₁ext
  obtain ⟨f, _, _, hfcomp, hfsup, _, hKf, hf1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hK V.isOpen hKV
  obtain ⟨f', _, _, hf'comp, hf'sup, _, hK'f', hf'1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hK' hU₁open hK'U₁
  obtain ⟨m₁, hm₁⟩ := l7a_eventually_sqrt_margin
    hfcomp.isCompact V.isOpen hfsup hεt
  obtain ⟨m₂, hm₂⟩ := l7a_eventually_sqrt_margin
    hf'comp.isCompact hU₁open hf'sup hεt
  refine ⟨φ, hφsup, hφcomp, m₁ + m₂, fun k => ?_⟩
  have hleft : ∀ z ∈ Function.support f,
      Metric.closedBall z (Real.sqrt (εs (k + (m₁ + m₂)))) ⊆ V := by
    intro z hz
    have hz' : z ∈ tsupport f := subset_tsupport _ hz
    simpa only [show k + (m₁ + m₂) = (k + m₂) + m₁ by omega] using
      hm₁ (k + m₂) z hz'
  have hright : ∀ z ∈ Function.support f',
      Metric.closedBall z (Real.sqrt (εs (k + (m₁ + m₂)))) ⊆ U₁o := by
    intro z hz
    have hz' : z ∈ tsupport f' := subset_tsupport _ hz
    change Metric.closedBall z (Real.sqrt (εs (k + (m₁ + m₂)))) ⊆ U₁
    simpa only [show k + (m₁ + m₂) = (k + m₁) + m₂ by omega] using
      hm₂ (k + m₁) z hz'
  let g' : Ω → DistRd d := fun ω => g ω - ofCont
    ⟨fun z => φ z * H ω z,
      l7a_continuous_cutoffH (extOpen V).isOpen φ (H ω) (hHcont ω) hφsup⟩
  let R : Ω → DistOn (extOpen V) := fun ω =>
    restrictTo (extOpen V) (g ω) - ofFunOn (extOpen V) (H ω)
  have hres : ∀ ω, restrictTo U₁o (g' ω) =
      restrictOn hU₁exto (R ω) := fun ω =>
    l7a_cutoff_residual_restrict V U₁o hU₁exto φ (H ω)
      (hHcont ω) hφsup hφ1 (g ω)
  have hfield : fieldSigmaRd g' U₁o ≤ MeasurableSpace.comap R inferInstance := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    change MeasurableSpace.comap (fun ω => restrictTo U₁o (g' ω)) inferInstance ≤
      MeasurableSpace.comap R inferInstance
    apply measurable_iff_comap_le.mp
    have hm : Measurable (fun ω => restrictOn hU₁exto (R ω)) :=
      (measurable_restrictOn hU₁exto).comp (comap_measurable R)
    convert hm using 1
    funext ω
    exact hres ω
  have hAi (i : ι) (hi : i ∈ S) :
      MeasurableSpace.comap (fun ω => l7a_truncInternal hd hκ
        (hεs (k + (m₁ + m₂))) ξ (g ω) (W i) (hWc i hi)) inferInstance ≤
        fieldSigmaRd g V := by
    have hfWi : ∀ z ∈ W i, f z = 1 := fun z hz =>
      hf1 z (hKf (mem_iUnion₂.mpr ⟨i, hi, subset_closure hz⟩))
    exact (l7a_measurable_truncInternalC hd hκ (hεs _)
      ξ V (W i) (hWc i hi) f hfWi hleft g).comap_le
  have hBj (j : κ') (hj : j ∈ T) :
      MeasurableSpace.comap (fun ω => l7a_truncInternal hd hκ
        (hεs (k + (m₁ + m₂))) ξ (g' ω) (W' j) (hW'c j hj)) inferInstance ≤
        MeasurableSpace.comap R inferInstance := by
    have hfWj : ∀ z ∈ W' j, f' z = 1 := fun z hz =>
      hf'1 z (hK'f' (mem_iUnion₂.mpr ⟨j, hj, subset_closure hz⟩))
    exact (l7a_measurable_truncInternalC hd hκ (hεs _)
      ξ U₁o (W' j) (hW'c j hj) f' hfWj hright g').comap_le.trans hfield
  have hL : fieldSigmaRd g V ⊔ ⨆ i ∈ S,
      MeasurableSpace.comap (fun ω => l7a_truncInternal hd hκ
        (hεs (k + (m₁ + m₂))) ξ (g ω) (W i) (hWc i ‹i ∈ S›)) inferInstance ≤
      fieldSigmaRd g V := sup_le le_rfl (iSup₂_le hAi)
  have hR : MeasurableSpace.comap R inferInstance ⊔ ⨆ j ∈ T,
      MeasurableSpace.comap (fun ω => l7a_truncInternal hd hκ
        (hεs (k + (m₁ + m₂))) ξ (g' ω) (W' j) (hW'c j ‹j ∈ T›)) inferInstance ≤
      MeasurableSpace.comap R inferInstance := sup_le le_rfl (iSup₂_le hBj)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm hL) hR

end HigherDimLQGMetric
