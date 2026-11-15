import InteractingSLE.GFF.LocalSets.AbsContTwoDomains
import SupercriticalConformalCovariance.Reversal.Inverse
import SupercriticalConformalCovariance.ZBConformal.GFFLaw
import LQGMetric.Complex.HarmonicComp


/-!
# Absolute continuity after a conformal map (specification p. 46, remark after Proposition 3.4)

Source: `source/ig1-specification.pdf`, §3.1, the remark after Proposition 3.4 (p. 46; transcription
`source/spec/p001-048.md#prop-3.4`, L1140; graph node `SPEC.prop-3.4#conformal-transfer`):
"Although Proposition 3.4 is stated in the case that `U` is bounded, an analogous result holds when
`U` is not bounded. We will in particular use this result in the following setting without
reference: `D₁ = D₂ = D` and there exists a conformal transformation `φ : D → D̃` where `D̃` is
bounded and `Ũ = φ(U)` satisfies the hypotheses of Proposition 3.4 part (i) or part (ii)."

Route: `(h + F)|_U` is the pullback by `φ|_U` of `(h ∘ φ⁻¹ + F ∘ φ⁻¹)|_Ũ`
(`restrictAdd_eq_distPullback`); `h ∘ φ⁻¹` is a zero-boundary GFF on `D̃`
(SupercriticalConformalCovariance `isZeroBoundaryGFF_distPullback`), `F ∘ φ⁻¹` is harmonic
(LQGMetric `harmonicOnNhd_comp_holo`), and absolute continuity is preserved by the measurable
pullback map.

## Main results

* `restrictAdd_eq_distPullback`: the conformal transport identity;
* `map_restrictAdd_absolutelyContinuous_of_conformal`: transfer of `≪`;
* `map_restrictAdd_mutuallyAbsCont_boundary_of_conformal`: part (ii) after a conformal map;
* `map_restrictAdd_mutuallyAbsCont_interior_of_conformal`: part (i) after a conformal map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open LQGMetric
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)
open SupercriticalConformalCovariance.ZBConformal (distPullback distPullback_apply
  measurable_distPullback integral_mul_confPushTest isZeroBoundaryGFF_distPullback)
open SupercriticalConformalCovariance.Reversal (inverse_conformal confPushTest_inverse_left)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

namespace InteractingSLE
namespace GFF

/-- The restriction of a conformal bijection `φ : D → E` to `U ⊆ D` onto `W = φ(U)`. -/
lemma isConformalBijection_restrict {φ : ℂ → ℂ} {D E U W : Opens ℂ}
    (hφ : IsConformalBijection φ D E) (hUD : U ≤ D) (hW : (W : Set ℂ) = φ '' U) :
    IsConformalBijection φ U W :=
  ⟨hφ.1.mono hUD, by rw [hW]; exact (hφ.2.injOn.mono hUD).bijOn_image⟩

lemma image_le_of_isConformalBijection {φ : ℂ → ℂ} {D E U W : Opens ℂ}
    (hφ : IsConformalBijection φ D E) (hUD : U ≤ D) (hW : (W : Set ℂ) = φ '' U) : W ≤ E := by
  intro y hy
  have hy' : y ∈ (W : Set ℂ) := hy
  rw [hW] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  exact hφ.2.mapsTo (hUD hx)

/-- **Conformal transport of `(T + F)|_U`.** For a conformal bijection `φ : D → E`, `U ⊆ D` open,
`W = φ(U)` and `F` continuous on `D`:
`(T + F)|_U = ((T ∘ φ⁻¹) + F ∘ φ⁻¹)|_W ∘ φ` (pullback of distributions by `φ|_U`). -/
theorem restrictAdd_eq_distPullback {φ : ℂ → ℂ} {D E U W : Opens ℂ}
    (hφ : IsConformalBijection φ D E) (hUD : U ≤ D) (hW : (W : Set ℂ) = φ '' U)
    (T : DistOn D) {F : ℂ → ℝ} (hF : ContinuousOn F D) :
    restrictAdd U T F = distPullback (isConformalBijection_restrict hφ hUD hW)
      (restrictAdd W (distPullback (inverse_conformal hφ) T) (F ∘ Function.invFunOn φ D)) := by
  have hφU := isConformalBijection_restrict hφ hUD hW
  have hWE : W ≤ E := image_le_of_isConformalBijection hφ hUD hW
  have hψ := inverse_conformal hφ
  have hleft : ∀ x ∈ (D : Set ℂ), Function.invFunOn φ D (φ x) = x :=
    fun _ hx => hφ.2.injOn.leftInvOn_invFunOn hx
  have hcU : ContinuousOn F U := hF.mono hUD
  have hcW : ContinuousOn (F ∘ Function.invFunOn φ D) W := by
    refine hF.comp (hψ.1.continuousOn.mono hWE) fun y hy => ?_
    have hy' : y ∈ (W : Set ℂ) := hy
    rw [hW] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    rw [hleft x (hUD hx)]; exact hUD hx
  ext χ
  simp only [distPullback_apply, restrictAdd, add_apply, restrictDist_apply]
  have hA : testIncl W E (confPushTest hφU χ) = confPushTest hφ (testIncl U D χ) := by
    apply DFunLike.coe_injective
    rw [coe_testIncl hWE]
    exact coe_confPushTest_restrict hφ hφU hUD (testIncl U D χ) χ (coe_testIncl hUD χ).symm
  rw [hA, confPushTest_inverse_left hφ, smoothDist_apply hcU, smoothDist_apply hcW]
  congr 1
  have := integral_mul_confPushTest hφU χ (F ∘ Function.invFunOn φ D)
  rw [show (∫ x, (confPushTest hφU χ) x * (F ∘ Function.invFunOn φ D) x) =
    ∫ y, (F ∘ Function.invFunOn φ D) y * (confPushTest hφU χ) y from by
      congr 1; funext y; ring, this]
  congr 1; funext x
  by_cases hx : x ∈ (U : Set ℂ)
  · simp only [Function.comp_apply, hleft x (hUD hx)]; ring
  · have h0 : χ x = 0 := by simpa using χ.zero_on_compl hx
    rw [h0]; ring

/-- **Transfer of absolute continuity along a conformal map.** -/
theorem map_restrictAdd_absolutelyContinuous_of_conformal {φ : ℂ → ℂ} {D E U W : Opens ℂ}
    (hφ : IsConformalBijection φ D E) (hUD : U ≤ D) (hW : (W : Set ℂ) = φ '' U)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} {h₁ : Ω₁ → DistOn D} {h₂ : Ω₂ → DistOn D} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) {F₁ F₂ : ℂ → ℝ} (hF₁ : ContinuousOn F₁ D) (hF₂ : ContinuousOn F₂ D)
    (hac : P₁.map (fun ω => restrictAdd W (distPullback (inverse_conformal hφ) (h₁ ω))
        (F₁ ∘ Function.invFunOn φ D)) ≪
      P₂.map (fun ω => restrictAdd W (distPullback (inverse_conformal hφ) (h₂ ω))
        (F₂ ∘ Function.invFunOn φ D))) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) := by
  have hM := measurable_distPullback (isConformalBijection_restrict hφ hUD hW)
  have hRA : ∀ F : ℂ → ℝ, Measurable fun T : DistOn E => restrictAdd W T F := fun F =>
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp (measurable_restrictDist W)).add_const _
  have hg₁ : Measurable fun ω => restrictAdd W (distPullback (inverse_conformal hφ) (h₁ ω))
      (F₁ ∘ Function.invFunOn φ D) :=
    (hRA _).comp ((measurable_distPullback (inverse_conformal hφ)).comp hh₁)
  have hg₂ : Measurable fun ω => restrictAdd W (distPullback (inverse_conformal hφ) (h₂ ω))
      (F₂ ∘ Function.invFunOn φ D) :=
    (hRA _).comp ((measurable_distPullback (inverse_conformal hφ)).comp hh₂)
  have e₁ : (fun ω => restrictAdd U (h₁ ω) F₁) =
      distPullback (isConformalBijection_restrict hφ hUD hW) ∘
        fun ω => restrictAdd W (distPullback (inverse_conformal hφ) (h₁ ω))
          (F₁ ∘ Function.invFunOn φ D) :=
    funext fun ω => restrictAdd_eq_distPullback hφ hUD hW (h₁ ω) hF₁
  have e₂ : (fun ω => restrictAdd U (h₂ ω) F₂) =
      distPullback (isConformalBijection_restrict hφ hUD hW) ∘
        fun ω => restrictAdd W (distPullback (inverse_conformal hφ) (h₂ ω))
          (F₂ ∘ Function.invFunOn φ D) :=
    funext fun ω => restrictAdd_eq_distPullback hφ hUD hW (h₂ ω) hF₂
  rw [e₁, e₂, ← Measure.map_map hM hg₁, ← Measure.map_map hM hg₂]
  exact hac.map hM


/-- **Proposition 3.4 (ii) after a conformal map** (specification p. 46: "an analogous result
holds when `U` is not bounded … `D₁ = D₂ = D` and there exists a conformal transformation
`φ : D → D̃` … `Ũ = φ(U)` satisfies the hypotheses of … part (ii)"). Let `D ≠ ℂ` be a simply
connected domain, `h₁, h₂` zero-boundary GFFs on `D`, `F₁, F₂` harmonic on `D`, `φ : D → E` a
conformal bijection, `U ⊆ D` open (possibly unbounded) with `W = φ(U)` bounded, and `W'` a
neighbourhood of `cl W` such that `(F₁ − F₂) ∘ φ⁻¹ → 0` at the points of `∂E ∩ W'`. Then the laws
of `(h₁ + F₁)|_U` and `(h₂ + F₂)|_U` are mutually absolutely continuous. (Boundedness of `E`,
assumed in the source, is not needed beyond that of `W`.) -/
theorem map_restrictAdd_mutuallyAbsCont_boundary_of_conformal {φ : ℂ → ℂ} {D E U W : Opens ℂ}
    {W' : Set ℂ} (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) (hφ : IsConformalBijection φ D E) (hUD : U ≤ D)
    (hW : (W : Set ℂ) = φ '' U) (hWb : Bornology.IsBounded (W : Set ℂ))
    (hW' : W' ∈ 𝓝ˢ (closure (W : Set ℂ)))
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D} {h₂ : Ω₂ → DistOn D} (hh₁ : IsZeroBoundaryGFF D h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D)
    (hbd : ∀ z ∈ frontier (E : Set ℂ) ∩ W', Tendsto
      (fun y => F₁ (Function.invFunOn φ D y) - F₂ (Function.invFunOn φ D y)) (𝓝[(E : Set ℂ)] z)
      (𝓝 0)) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ∧
      P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ≪ P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) := by
  have hψ := inverse_conformal hφ
  have hE : ZBAdmissible E :=
    SupercriticalConformalCovariance.ZBConformal.zbAdmissible_of_conf hψ
      (zbAdmissible_of_isSimplyConnected hDc hDs hDne)
  have hWE : (W : Set ℂ) ⊆ E := image_le_of_isConformalBijection hφ hUD hW
  have hF₁' : InnerProductSpace.HarmonicOnNhd (F₁ ∘ Function.invFunOn φ D) E :=
    LQGMetric.harmonicOnNhd_comp_holo D.isOpen E.isOpen hF₁ hψ.1 hψ.2.mapsTo
  have hF₂' : InnerProductSpace.HarmonicOnNhd (F₂ ∘ Function.invFunOn φ D) E :=
    LQGMetric.harmonicOnNhd_comp_holo D.isOpen E.isOpen hF₂ hψ.1 hψ.2.mapsTo
  have hint : closure (W : Set ℂ) ⊆ interior W' := subset_interior_iff_mem_nhdsSet.2 hW'
  obtain ⟨ac12, ac21⟩ := map_restrictAdd_mutuallyAbsCont_of_tendsto_frontier hE hWb hWE
    isOpen_interior hint (isZeroBoundaryGFF_distPullback hψ hh₁)
    (isZeroBoundaryGFF_distPullback hψ hh₂) hF₁' hF₂'
    fun z hz => hbd z ⟨hz.1, interior_subset hz.2⟩
  have hc₁ : ContinuousOn F₁ D := (contDiffOn_of_harmonicOnNhd (n := 0) hF₁).continuousOn
  have hc₂ : ContinuousOn F₂ D := (contDiffOn_of_harmonicOnNhd (n := 0) hF₂).continuousOn
  exact ⟨map_restrictAdd_absolutelyContinuous_of_conformal hφ hUD hW hh₁.measurable
      hh₂.measurable hc₁ hc₂ ac12,
    map_restrictAdd_absolutelyContinuous_of_conformal hφ hUD hW hh₂.measurable
      hh₁.measurable hc₂ hc₁ ac21⟩

/-- **Proposition 3.4 (i) after a conformal map** (specification p. 46, the same remark with
part (i)): `D ≠ ℂ` simply connected, `φ : D → E` conformal, `U ⊆ D` open with `W = φ(U)` bounded
and `dist(W, ∂E) > 0`. Then for harmonic `F₁, F₂` on `D` the laws of `(h₁ + F₁)|_U` and
`(h₂ + F₂)|_U` are mutually absolutely continuous. -/
theorem map_restrictAdd_mutuallyAbsCont_interior_of_conformal {φ : ℂ → ℂ} {D E U W : Opens ℂ}
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) (hφ : IsConformalBijection φ D E) (hUD : U ≤ D)
    (hW : (W : Set ℂ) = φ '' U) (hWb : Bornology.IsBounded (W : Set ℂ))
    (hdist : ∃ δ > 0, ∀ z ∈ (W : Set ℂ), ∀ w ∈ frontier (E : Set ℂ), δ ≤ dist z w)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → DistOn D} {h₂ : Ω₂ → DistOn D} (hh₁ : IsZeroBoundaryGFF D h₁ P₁)
    (hh₂ : IsZeroBoundaryGFF D h₂ P₂) {F₁ F₂ : ℂ → ℝ}
    (hF₁ : InnerProductSpace.HarmonicOnNhd F₁ D) (hF₂ : InnerProductSpace.HarmonicOnNhd F₂ D) :
    P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) ≪ P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ∧
      P₂.map (fun ω => restrictAdd U (h₂ ω) F₂) ≪ P₁.map (fun ω => restrictAdd U (h₁ ω) F₁) := by
  have hψ := inverse_conformal hφ
  have hE : ZBAdmissible E :=
    SupercriticalConformalCovariance.ZBConformal.zbAdmissible_of_conf hψ
      (zbAdmissible_of_isSimplyConnected hDc hDs hDne)
  have hWE : (W : Set ℂ) ⊆ E := image_le_of_isConformalBijection hφ hUD hW
  have hcl : closure (W : Set ℂ) ⊆ E := closure_subset_of_dist_frontier E.isOpen hWE hdist
  have hF₁' : InnerProductSpace.HarmonicOnNhd (F₁ ∘ Function.invFunOn φ D) E :=
    LQGMetric.harmonicOnNhd_comp_holo D.isOpen E.isOpen hF₁ hψ.1 hψ.2.mapsTo
  have hF₂' : InnerProductSpace.HarmonicOnNhd (F₂ ∘ Function.invFunOn φ D) E :=
    LQGMetric.harmonicOnNhd_comp_holo D.isOpen E.isOpen hF₂ hψ.1 hψ.2.mapsTo
  have hg₁ := isZeroBoundaryGFF_distPullback hψ hh₁
  have hg₂ := isZeroBoundaryGFF_distPullback hψ hh₂
  have hc₁ : ContinuousOn F₁ D := (contDiffOn_of_harmonicOnNhd (n := 0) hF₁).continuousOn
  have hc₂ : ContinuousOn F₂ D := (contDiffOn_of_harmonicOnNhd (n := 0) hF₂).continuousOn
  exact ⟨map_restrictAdd_absolutelyContinuous_of_conformal hφ hUD hW hh₁.measurable
      hh₂.measurable hc₁ hc₂
      (map_restrictAdd_absolutelyContinuous hE hE hWb hcl hcl hg₁ hg₂ hF₁' hF₂'),
    map_restrictAdd_absolutelyContinuous_of_conformal hφ hUD hW hh₂.measurable
      hh₁.measurable hc₂ hc₁
      (map_restrictAdd_absolutelyContinuous hE hE hWb hcl hcl hg₂ hg₁ hF₂' hF₁')⟩


end GFF
end InteractingSLE
