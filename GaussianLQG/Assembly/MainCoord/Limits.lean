import LQGMetric.Prob.Median
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Limit and median tools for the proof of Theorem `thm:main`

General facts used in Steps 3, 4 and 6 of the proof of blueprint Theorem `thm:main`
(`blueprint/sections/s7-medians.tex`):

* `tendstoInMeasure_comp_of_tendsto_uncurry`: a continuous-mapping theorem for convergence in
  probability with deterministic, continuously convergent maps. If `X_i → Z` in probability along a
  countably generated filter `l`, and `G_i(y_i) → G₀(z)` whenever `i → l` and `y_i → z`, then
  `G_i(X_i) → G₀(Z)` in probability. (Proof: every sequence in `l` has a subsequence along which
  `X_i → Z` almost surely.)
* `tendstoInDistribution_Ioo_of_tendstoInMeasure`: convergence in probability as `γ ↓ 0` implies
  convergence in law, in the form of (1.8) (indexed by `γ ∈ (0,2)`, limit given by its law).
* `tendsto_exp_mul_sub_one_div`: the deterministic limit behind Steps 3 and 6. If `ξ_γ / γ → 1/2`
  and `c_γ → c₀` as `γ ↓ 0`, then `(exp(ξ_γ (y + c_γ)) - 1) / γ → (z + c₀) / 2` as `γ ↓ 0` and
  `y → z`. The blueprint writes `(e^x - 1)/γ = (ξ/γ)(x/ξ)ψ(x)` with `ψ(x) = (e^x - 1)/x`; here we
  use the equivalent bound `|e^x - 1 - x| ≤ x²` for `|x| ≤ 1`.
* `isMedian_gaussianReal`, `eq_of_isMedian_gaussianReal`: the mean of a Gaussian is a median
  (symmetry), and it is the only median when the variance is positive (the law charges every
  nonempty open interval).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

/-! ## Continuous mapping for convergence in probability -/

/-- **Continuous mapping with deterministic maps.** Let `X_i → Z` in `P`-probability along a
countably generated filter `l` (`P` finite). Let `G i : ℝ → ℝ` converge continuously to `G₀`:
`G_i(y) → G₀(z)` as `(i, y) → l × 𝓝 z`, for every `z`. If each `G_i ∘ X_i` is a.e.-strongly
measurable, then `G_i(X_i) → G₀(Z)` in `P`-probability. -/
theorem tendstoInMeasure_comp_of_tendsto_uncurry {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {l : Filter ι} [l.IsCountablyGenerated]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} (hXZ : TendstoInMeasure P X l Z)
    {G : ι → ℝ → ℝ} {G₀ : ℝ → ℝ}
    (hG : ∀ z, Tendsto (fun p : ι × ℝ => G p.1 p.2) (l ×ˢ 𝓝 z) (𝓝 (G₀ z)))
    (hmeas : ∀ i, AEStronglyMeasurable (fun ω => G i (X i ω)) P) :
    TendstoInMeasure P (fun i ω => G i (X i ω)) l (fun ω => G₀ (Z ω)) := by
  intro ε hε
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- along `ns`, extract a subsequence on which `X → Z` almost surely
  obtain ⟨ms, hms, hae⟩ := (hXZ.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G (ns (ms k)) (X (ns (ms k)) ω)) atTop (𝓝 (G₀ (Z ω))) := by
    filter_upwards [hae] with ω hω
    exact (hG (Z ω)).comp ((hns.comp hms.tendsto_atTop).prodMk hω)
  exact tendstoInMeasure_of_tendsto_ae (fun k => hmeas (ns (ms k))) hlim ε hε

/-- **Convergence in probability implies convergence in law** (Step 4), in the form of (1.8):
if `X_γ → Z` in `P`-probability as `γ ↓ 0` and `Z` has law `ν`, then `X_γ → ν` in law along
`γ ↓ 0`, `γ ∈ (0,2)`. -/
theorem tendstoInDistribution_Ioo_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ} {Z : Ω → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hXZ : TendstoInMeasure P X (𝓝[>] 0) Z)
    (hX : ∀ γ : Ioo (0 : ℝ) 2, AEMeasurable (X γ) P) (hZ : AEMeasurable Z P)
    (hlaw : P.map Z = ν) :
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) => X γ) ((𝓝[>] (0 : ℝ)).comap Subtype.val)
      (id : ℝ → ℝ) (fun _ => P) ν := by
  have hconv := (hXZ.comp tendsto_comap).tendstoInDistribution_of_aemeasurable hX hZ
  have e : (⟨P.map Z, inferInstance⟩ : ProbabilityMeasure ℝ) = ⟨ν.map id, inferInstance⟩ :=
    Subtype.ext (show P.map Z = ν.map id by rw [Measure.map_id, hlaw])
  have h := hconv.tendsto
  rw [e] at h
  exact ⟨hX, aemeasurable_id, h⟩

/-! ## The deterministic limit of Steps 3 and 6 -/

/-- If `ξ_γ / γ → 1/2` as `γ ↓ 0`, then `ξ_γ → 0`. -/
theorem tendsto_zero_of_tendsto_div_self {ξ : ℝ → ℝ}
    (hξ : Tendsto (fun γ => ξ γ / γ) (𝓝[>] 0) (𝓝 (1 / 2))) :
    Tendsto ξ (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have h := hξ.mul hid
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ (hγ : 0 < γ)
  exact div_mul_cancel₀ (ξ γ) hγ.ne'

/-- **The deterministic limit behind Steps 3 and 6.** If `ξ_γ / γ → 1/2` and `c_γ → c₀` as
`γ ↓ 0`, then `(exp(ξ_γ (y + c_γ)) - 1) / γ → (z + c₀) / 2` as `γ ↓ 0` and `y → z`. -/
theorem tendsto_exp_mul_sub_one_div {ξ c : ℝ → ℝ} {c₀ : ℝ}
    (hξ : Tendsto (fun γ => ξ γ / γ) (𝓝[>] 0) (𝓝 (1 / 2))) (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀))
    (z : ℝ) :
    Tendsto (fun p : ℝ × ℝ => (Real.exp (ξ p.1 * (p.2 + c p.1)) - 1) / p.1)
      (𝓝[>] 0 ×ˢ 𝓝 z) (𝓝 ((z + c₀) / 2)) := by
  set F : Filter (ℝ × ℝ) := 𝓝[>] 0 ×ˢ 𝓝 z with hF
  -- the pieces: `w = y + c_γ`, `r = ξ_γ / γ`, `s = ξ_γ`, `x = s w`
  have hw : Tendsto (fun p : ℝ × ℝ => p.2 + c p.1) F (𝓝 (z + c₀)) :=
    tendsto_snd.add (hc.comp tendsto_fst)
  have hr : Tendsto (fun p : ℝ × ℝ => ξ p.1 / p.1) F (𝓝 (1 / 2)) := hξ.comp tendsto_fst
  have hs : Tendsto (fun p : ℝ × ℝ => ξ p.1) F (𝓝 0) :=
    (tendsto_zero_of_tendsto_div_self hξ).comp tendsto_fst
  have hx : Tendsto (fun p : ℝ × ℝ => ξ p.1 * (p.2 + c p.1)) F (𝓝 0) := by
    have h := hs.mul hw
    rwa [zero_mul] at h
  -- main term `x / γ = r w → (z + c₀) / 2`
  have hmain : Tendsto (fun p : ℝ × ℝ => ξ p.1 / p.1 * (p.2 + c p.1)) F (𝓝 ((z + c₀) / 2)) := by
    have h := hr.mul hw
    rwa [one_div_mul_eq_div] at h
  -- error term `(e^x - 1 - x) / γ`, bounded by `x² / γ = r s w²`
  have hbound : Tendsto (fun p : ℝ × ℝ => ξ p.1 / p.1 * ξ p.1 * (p.2 + c p.1) ^ 2) F (𝓝 0) := by
    have h := (hr.mul hs).mul (hw.pow 2)
    rwa [mul_zero, zero_mul] at h
  have hpos : ∀ᶠ p : ℝ × ℝ in F, 0 < p.1 :=
    tendsto_fst.eventually (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0))
  have hsmall : ∀ᶠ p : ℝ × ℝ in F, |ξ p.1 * (p.2 + c p.1)| ≤ 1 := by
    have h := hx.abs
    rw [abs_zero] at h
    exact h.eventually (ge_mem_nhds zero_lt_one)
  have herr : Tendsto (fun p : ℝ × ℝ =>
      (Real.exp (ξ p.1 * (p.2 + c p.1)) - 1 - ξ p.1 * (p.2 + c p.1)) / p.1) F (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hpos, hsmall] with p hp1 hp2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp1, div_le_iff₀ hp1]
    have hkey := Real.abs_exp_sub_one_sub_id_le hp2
    have hid : ξ p.1 / p.1 * ξ p.1 * (p.2 + c p.1) ^ 2 * p.1 =
        (ξ p.1 * (p.2 + c p.1)) ^ 2 := by
      field_simp
    rw [hid]
    exact hkey
  have hsum := hmain.add herr
  rw [add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun p => ?_)
  ring

/-! ## Medians of Gaussian laws -/

/-- The mean of a Gaussian law is a median (by symmetry about the mean). -/
theorem isMedian_gaussianReal (μ : ℝ) (v : ℝ≥0) : LQGMetric.IsMedian (gaussianReal μ v) μ := by
  set G := gaussianReal μ v with hG
  have hsymm : G.map (fun x => 2 * μ - x) = G := by
    rw [hG, gaussianReal_map_const_sub]
    congr 1
    ring
  have hIci : G (Ici μ) = G (Iic μ) := by
    conv_lhs => rw [← hsymm]
    rw [Measure.map_apply (by fun_prop) measurableSet_Ici]
    congr 1
    ext x
    simp only [mem_preimage, mem_Ici, mem_Iic]
    constructor <;> intro h <;> linarith
  have hcover : 1 ≤ G (Iic μ) + G (Iic μ) := by
    calc (1 : ℝ≥0∞) = G univ := measure_univ.symm
      _ ≤ G (Iic μ ∪ Ici μ) := measure_mono fun x _ => by
          rcases le_total x μ with h | h
          · exact Or.inl h
          · exact Or.inr h
      _ ≤ G (Iic μ) + G (Ici μ) := measure_union_le _ _
      _ = G (Iic μ) + G (Iic μ) := by rw [hIci]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ G (Iic μ) := by
    rw [ENNReal.inv_le_iff_le_mul (fun _ => two_ne_zero) (fun h => absurd h ENNReal.ofNat_ne_top),
      two_mul]
    exact hcover
  rw [LQGMetric.isMedian_iff]
  exact ⟨hhalf, hIci ▸ hhalf⟩

/-- A Gaussian law with positive variance has a unique median, its mean. -/
theorem eq_of_isMedian_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {m : ℝ}
    (hm : LQGMetric.IsMedian (gaussianReal μ v) m) : m = μ := by
  have hU : LQGMetric.lowerMedianLaw (gaussianReal μ v) =
      LQGMetric.upperMedianLaw (gaussianReal μ v) := by
    refine LQGMetric.lowerMedianLaw_eq_upperMedianLaw_of_noGap fun a b hab _ => ?_
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h := gaussianReal_absolutelyContinuous' μ hv h0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h
    linarith
  exact LQGMetric.IsMedian.eq_of_unique hU hm (isMedian_gaussianReal μ v)

end GaussianLQG
