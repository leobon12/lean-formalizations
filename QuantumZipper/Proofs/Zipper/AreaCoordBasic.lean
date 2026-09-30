import QuantumZipper.Proofs.Zipper.PStarAreaCoord
import QuantumZipper.Proofs.LQG.VagueUniqueOn
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.RS.KoebeLoewnerTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AREA-COORD (1): the transported area measure and its test functions (deterministic)

Theorem 1.3 / 1.8, node E6, input `E6.WedgeAreaCoordStmt` (W-A-cc, `PStarAreaCoord.lean`). For a
continuous driver `W` with `W 0 = 0`, a time `t ≥ 0` and a measure `μ` on `ℂ` (the quantum area of
the field before unzipping), this file builds the **transported measure**

  `areaTransport μ W t = (μ|_{ℍ \ K_t}).map f_t`,

the image of `μ|_{ℍ \ K_t}` under the centered forward Loewner map `f_t`, and the **transported
test function** `transTest W t f = 1_{ℍ \ K_t} · (f ∘ f_t)`. Main facts:

* `areaTransport_apply`: for Borel `S ⊆ ℍ`, `areaTransport μ W t S = μ (f_t⁻¹ '' S)` — exactly the
  right-hand side of W-A-cc;
* `areaTransport_compl_H`, `areaTransport_lt_top`: the transported measure is concentrated on
  `ℍ` and finite on compact subsets of `ℍ` (if `μ` is);
* `integral_areaTransport`: `∫ f d(areaTransport μ W t) = ∫ transTest W t f dμ`;
* `continuous_transTest`, `hasCompactSupport_transTest`, `tsupport_transTest_subset`: for `f`
  continuous with compact support in `ℍ`, `transTest W t f` is again continuous with compact
  support in `ℍ` (its support lies in the compact set `f_t⁻¹(tsupport f) ⊆ ℍ \ K_t`);
* `isVagueLimitOn_areaTransport`: if `areaApprox`-type measures `μs₀ k → μ` vaguely on `ℍ` and
  `∫ f dμs k − ∫ transTest W t f dμs₀ k → 0` for every test function `f`, then
  `μs k → areaTransport μ W t` vaguely on `ℍ`.

This is the measure-theoretic bookkeeping of Sheffield–Wang, *Field-measure correspondence in
Liouville quantum gravity almost surely commutes with all conformal maps simultaneously*,
Trans. AMS 372 (2020), arXiv:1605.06171, proof of Thm 1.4, p. 11–12: the change of coordinates
turning (3.5) into (3.6)/(3.7) (there with `φ = f_t⁻¹`, `φ⁻¹(S) ↔ S`). The Loewner inputs are
cited in the lemmas used (`RS.fwdMapInv_fwdMap`, `RS.image_fwdMapInv_H`, `FwdHolo.*`). Own
elementary proofs otherwise.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

section Transport

variable {W : ℝ → ℝ} {t : ℝ}

/-- The quantum area `μ` of the field before unzipping, carried to the unzipped coordinates:
the image of `μ|_{ℍ \ K_t}` under the centered forward map `f_t`. -/
def areaTransport (μ : Measure ℂ) (W : ℝ → ℝ) (t : ℝ) : Measure ℂ :=
  (μ.restrict (H \ fwdHull W t)).map (fwdMap W t)

/-- A test function `f` of the unzipped coordinates, read in the original coordinates:
`1_{ℍ \ K_t} · (f ∘ f_t)`. -/
def transTest (W : ℝ → ℝ) (t : ℝ) (f : ℂ → ℝ) : ℂ → ℝ :=
  (H \ fwdHull W t).indicator fun w => f (fwdMap W t w)

theorem measurableSet_compl_fwdHull (hW : Continuous W) (ht : 0 ≤ t) :
    MeasurableSet (H \ fwdHull W t) :=
  (FwdHolo.isOpen_compl_fwdHull hW ht).measurableSet

theorem continuousOn_fwdMap_compl (hW : Continuous W) (ht : 0 ≤ t) :
    ContinuousOn (fwdMap W t) (H \ fwdHull W t) :=
  (FwdHolo.differentiableOn_fwdMap hW ht).continuousOn

theorem continuousOn_fwdMapInv_H (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    ContinuousOn (fwdMapInv W t) H :=
  (RS.differentiableOn_fwdMapInv hW hW0 ht).continuousOn

theorem aemeasurable_fwdMap_restrict (hW : Continuous W) (ht : 0 ≤ t) (μ : Measure ℂ) :
    AEMeasurable (fwdMap W t) (μ.restrict (H \ fwdHull W t)) :=
  (continuousOn_fwdMap_compl hW ht).aemeasurable (measurableSet_compl_fwdHull hW ht)

/-- For `S ⊆ ℍ`: `f_t⁻¹'(S) ∩ (ℍ \ K_t) = f̂_t(S)` (`f̂_t = fwdMapInv W t`). -/
theorem preimage_fwdMap_inter_eq (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {S : Set ℂ}
    (hS : S ⊆ H) : fwdMap W t ⁻¹' S ∩ (H \ fwdHull W t) = fwdMapInv W t '' S := by
  ext z
  constructor
  · rintro ⟨hzS, hz⟩
    exact ⟨fwdMap W t z, hzS, RS.fwdMapInv_fwdMap hW hW0 ht hz⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · show fwdMap W t (fwdMapInv W t w) ∈ S
      rw [RS.fwdMap_fwdMapInv hW hW0 ht (hS hw)]
      exact hw
    · rw [← RS.image_fwdMapInv_H hW hW0 ht]
      exact ⟨w, hS hw, rfl⟩

/-- **The transported measure is the right-hand side of W-A-cc.** -/
theorem areaTransport_apply (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) (μ : Measure ℂ)
    {S : Set ℂ} (hSm : MeasurableSet S) (hS : S ⊆ H) :
    areaTransport μ W t S = μ (fwdMapInv W t '' S) := by
  unfold areaTransport
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_fwdMap_restrict hW ht μ) hSm,
    Measure.restrict_apply' (measurableSet_compl_fwdHull hW ht),
    preimage_fwdMap_inter_eq hW hW0 ht hS]

/-- The transported measure does not charge `ℂ \ ℍ`. -/
theorem areaTransport_compl_H (hW : Continuous W) (ht : 0 ≤ t) (μ : Measure ℂ) :
    areaTransport μ W t Hᶜ = 0 := by
  unfold areaTransport
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_fwdMap_restrict hW ht μ)
      isOpen_H.measurableSet.compl,
    Measure.restrict_apply' (measurableSet_compl_fwdHull hW ht)]
  have : fwdMap W t ⁻¹' Hᶜ ∩ (H \ fwdHull W t) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    intro hz h'
    exact hz (FwdHolo.mapsTo_fwdMap hW ht h')
  rw [this, measure_empty]

/-- `f̂_t` maps compact subsets of `ℍ` to compact subsets of `ℍ \ K_t`. -/
theorem isCompact_image_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) : IsCompact (fwdMapInv W t '' K) :=
  hK.image_of_continuousOn ((continuousOn_fwdMapInv_H hW hW0 ht).mono hKH)

theorem image_fwdMapInv_subset (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {K : Set ℂ}
    (hKH : K ⊆ H) : fwdMapInv W t '' K ⊆ H \ fwdHull W t := by
  rw [← RS.image_fwdMapInv_H hW hW0 ht]
  exact image_mono hKH

/-- The transported measure is finite on compact subsets of `ℍ` if `μ` is. -/
theorem areaTransport_lt_top (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {μ : Measure ℂ}
    (hμ : ∀ K, IsCompact K → K ⊆ H → μ K < ⊤) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    areaTransport μ W t K < ⊤ := by
  rw [areaTransport_apply hW hW0 ht μ hK.measurableSet hKH]
  exact hμ _ (isCompact_image_fwdMapInv hW hW0 ht hK hKH)
    ((image_fwdMapInv_subset hW hW0 ht hKH).trans sdiff_subset)

/-- Integrals against the transported measure are integrals of the transported test function. -/
theorem integral_areaTransport (hW : Continuous W) (ht : 0 ≤ t) (μ : Measure ℂ) {f : ℂ → ℝ}
    (hf : Continuous f) :
    ∫ z, f z ∂(areaTransport μ W t) = ∫ w, transTest W t f w ∂μ := by
  unfold areaTransport transTest
  rw [integral_map (aemeasurable_fwdMap_restrict hW ht μ)
      hf.aestronglyMeasurable,
    integral_indicator (measurableSet_compl_fwdHull hW ht)]

/-! ### The transported test function -/

/-- The support of `transTest W t f` lies in `f̂_t(tsupport f)`. -/
theorem support_transTest_subset (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (f : ℂ → ℝ) : support (transTest W t f) ⊆ fwdMapInv W t '' tsupport f := by
  intro w hw
  unfold transTest at hw
  rw [support_indicator] at hw
  obtain ⟨hwU, hwf⟩ := hw
  exact ⟨fwdMap W t w, subset_tsupport f hwf, RS.fwdMapInv_fwdMap hW hW0 ht hwU⟩

theorem tsupport_transTest_subset_image (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {f : ℂ → ℝ} (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    tsupport (transTest W t f) ⊆ fwdMapInv W t '' tsupport f :=
  closure_minimal (support_transTest_subset hW hW0 ht f)
    (isCompact_image_fwdMapInv hW hW0 ht hfc hfH).isClosed

theorem hasCompactSupport_transTest (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {f : ℂ → ℝ} (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    HasCompactSupport (transTest W t f) :=
  IsCompact.of_isClosed_subset (isCompact_image_fwdMapInv hW hW0 ht hfc hfH)
    (isClosed_tsupport _) (tsupport_transTest_subset_image hW hW0 ht hfc hfH)

theorem tsupport_transTest_subset_compl (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {f : ℂ → ℝ} (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    tsupport (transTest W t f) ⊆ H \ fwdHull W t :=
  (tsupport_transTest_subset_image hW hW0 ht hfc hfH).trans
    (image_fwdMapInv_subset hW hW0 ht hfH)

theorem tsupport_transTest_subset (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {f : ℂ → ℝ} (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    tsupport (transTest W t f) ⊆ H :=
  (tsupport_transTest_subset_compl hW hW0 ht hfc hfH).trans sdiff_subset

/-- **The transported test function is continuous**: on the open set `ℍ \ K_t` it is `f ∘ f_t`,
and its topological support is a compact subset of `ℍ \ K_t`. -/
theorem continuous_transTest (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    Continuous (transTest W t f) := by
  refine continuous_of_tsupport fun w hw => ?_
  have hwU := tsupport_transTest_subset_compl hW hW0 ht hfc hfH hw
  have hU : IsOpen (H \ fwdHull W t) := FwdHolo.isOpen_compl_fwdHull hW ht
  have hcont : ContinuousAt (fun w => f (fwdMap W t w)) w :=
    hf.continuousAt.comp ((continuousOn_fwdMap_compl hW ht).continuousAt (hU.mem_nhds hwU))
  refine hcont.congr ?_
  filter_upwards [hU.mem_nhds hwU] with v hv
  unfold transTest
  rw [indicator_of_mem hv]

/-! ### Vague convergence to the transported measure -/

/-- **Vague convergence to the transported measure.** If `μs₀ k → μ` vaguely on `ℍ` and, for
every test function `f` with compact support in `ℍ`, the integrals of `f` against `μs k` and of
the transported test function against `μs₀ k` merge, then `μs k → areaTransport μ W t` vaguely on
`ℍ`. -/
theorem isVagueLimitOn_areaTransport (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {μs μs₀ : ℕ → Measure ℂ} {μ : Measure ℂ} (h₀ : IsVagueLimitOn H μs₀ μ)
    (hmerge : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ H →
      Tendsto (fun k => ∫ z, f z ∂(μs k) - ∫ w, transTest W t f w ∂(μs₀ k)) atTop (𝓝 0)) :
    IsVagueLimitOn H μs (areaTransport μ W t) := by
  refine ⟨areaTransport_compl_H hW ht μ, fun K hK hKH => areaTransport_lt_top hW hW0 ht h₀.2.1
    hK hKH, fun f hf hfc hfH => ?_⟩
  rw [integral_areaTransport hW ht μ hf]
  have h1 := h₀.2.2 (transTest W t f) (continuous_transTest hW hW0 ht hf hfc hfH)
    (hasCompactSupport_transTest hW hW0 ht hfc hfH) (tsupport_transTest_subset hW hW0 ht hfc hfH)
  have h2 := (hmerge f hf hfc hfH).add h1
  rw [zero_add] at h2
  refine h2.congr fun k => ?_
  ring

end Transport

/-! ### `qAreaMeasure` is a vague limit when it is not junk -/

/-- If `qAreaMeasure γ x ≠ 0`, it is not the junk value, hence a vague limit of `areaApprox`. -/
theorem isVagueLimitOn_qAreaMeasure_of_ne_zero {γ : ℝ} {x : FieldSample}
    (h : qAreaMeasure γ x ≠ 0) : IsVagueLimitOn H (areaApprox γ x) (qAreaMeasure γ x) := by
  by_cases hex : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ
  · rw [qAreaMeasure_eq hex.choose_spec]
    exact hex.choose_spec
  · exfalso
    apply h
    unfold qAreaMeasure
    simp only [hex, ↓reduceDIte]

/-- Under `AreaAll`, `qAreaMeasure` is a vague limit of `areaApprox`. -/
theorem isVagueLimitOn_qAreaMeasure_of_areaAll {γ : ℝ} {x : FieldSample} (h : AreaAll γ x) :
    IsVagueLimitOn H (areaApprox γ x) (qAreaMeasure γ x) := by
  refine isVagueLimitOn_qAreaMeasure_of_ne_zero fun h0 => ?_
  have := h.2
  rw [h0] at this
  simp at this

end QuantumZipper.E6
