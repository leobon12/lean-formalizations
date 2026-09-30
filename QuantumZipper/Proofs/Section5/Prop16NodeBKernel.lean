import QuantumZipper.Proofs.GFF.K3.MixedM6
import QuantumZipper.Proofs.LQG.PalmArea
import QuantumZipper.Proofs.Section5.Prop16PalmZoom

/-!
# Proposition 1.6, Palm node B′: covariance inputs of the Palm formula for the mixed field

Items (3) and (4) of the D30 expert's list for node B′ (`Prop16PalmIdMaskStmt`): the
covariance asymptotics that the abstract Palm formula (`Palm.palm_formula`,
`PalmFree.palm_formula_weight`) needs, for the mixed GFF `X` of Proposition 1.6
(`IsMixedGFF D S X P`, `S = [c,d]`), near the free arc.

By K3 node M6 (`K3.mixedLocalKernel`, proved), on measures carried by a compact `K` with uniform
local half-discs the mixed covariance is `kernelCov (neumannH + k)` with `k` continuous on
`K × K`. With `k̂ = remK K k` (`k` on `K × K`, `0` elsewhere; jointly measurable and bounded):

* `tendsto_dualCov_mixed_fc`, `tendsto_cov_mixed_fc` (**hcov**): for `μ` admissible and carried
  by `K`, and `x ∈ ℝ ∩ K` whose small folded circles are carried by `K`,
  `Cov(X μ, X fc(x, 2^{-n})) → ∫ G(x, ·) dμ`, `G(x, z) = neumannH x z + k̂(z, x)`
  (`mixedGreenK`, jointly measurable);
* `mixedGreenSample_eq`: the Palm shift `mixedGreenSample D S x` of `Prop16PalmZoom.lean` is
  `∫ G(x, ·) dμ` on such `μ` (no junk value there);
* `var_mixed_fc_add_log` (**hvarbd**, exact form), `abs_kernelCov_remK_le` (the bound) and
  `tendsto_var_mixed_fc` (**hvar**): `Var X(fc(x, 2^{-n})) + 2 log 2^{-n} = kernelCov k̂ (fc, fc)`,
  bounded by `sup_{K×K} |k|`, and `→ k(x, x)`.

Source: the covariance structure of the GFF near a free boundary arc (Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, arXiv:0808.1560, §3.3 p. 22, and §6.1: `G = G_N + ` a
continuous correction), in the form of the project's node M6. The limits themselves
(uniform continuity of `k` on `K × K`, `-2 log` of concentric semicircles) are own elementary
arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-! ## 1. The truncated remainder kernel -/

open Classical in
/-- The remainder kernel `k` on `K × K`, extended by `0`. -/
def remK (K : Set ℂ) (k : ℂ → ℂ → ℝ) (y w : ℂ) : ℝ :=
  (K ×ˢ K).piecewise (Function.uncurry k) 0 (y, w)

/-- The mixed Green kernel at the boundary point `x`: `G(x, z) = neumannH x z + k̂(z, x)`. -/
def mixedGreenK (K : Set ℂ) (k : ℂ → ℂ → ℝ) (x : ℝ) (z : ℂ) : ℝ :=
  neumannH (x : ℂ) z + remK K k z (x : ℂ)

section Kernel

variable {K : Set ℂ} {k : ℂ → ℂ → ℝ}

theorem remK_of_mem {y w : ℂ} (hy : y ∈ K) (hw : w ∈ K) : remK K k y w = k y w := by
  classical
  simp [remK, Set.piecewise, hy, hw]

theorem remK_of_not_mem_left {y w : ℂ} (hy : y ∉ K) : remK K k y w = 0 := by
  classical
  simp [remK, Set.piecewise, hy]

theorem measurable_remK (hK : IsClosed K) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) :
    Measurable (Function.uncurry (remK K k)) := by
  classical
  have h := hk.measurable_piecewise (g := (0 : ℂ × ℂ → ℝ)) continuousOn_const
    (hK.prod hK).measurableSet
  convert h using 1
  funext p
  simp only [Function.uncurry, remK, Set.piecewise]

theorem exists_bound_remK (hK : IsCompact K) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y w, |remK K k y w| ≤ M := by
  classical
  obtain ⟨C, hC⟩ := (hK.prod hK).exists_bound_of_continuousOn hk
  refine ⟨max C 0, le_max_right _ _, fun y w => ?_⟩
  by_cases h : (y, w) ∈ K ×ˢ K
  · rw [remK_of_mem h.1 h.2]
    exact (hC (y, w) h).trans (le_max_left _ _)
  · have : remK K k y w = 0 := by simp [remK, Set.piecewise, h]
    rw [this, abs_zero]; exact le_max_right _ _

theorem measurable_mixedGreenK (hK : IsClosed K)
    (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) :
    Measurable (Function.uncurry (mixedGreenK K k)) := by
  have h1 : Measurable fun p : ℝ × ℂ => neumannH (p.1 : ℂ) p.2 :=
    measurable_neumannH.comp ((Complex.continuous_ofReal.measurable.comp measurable_fst).prodMk
      measurable_snd)
  have h2 : Measurable fun p : ℝ × ℂ => remK K k p.2 (p.1 : ℂ) :=
    (measurable_remK hK hk).comp
      (measurable_snd.prodMk (Complex.continuous_ofReal.measurable.comp measurable_fst))
  exact h1.add h2

/-- A bounded measurable function against a finite measure, uniformly close to a constant. -/
theorem abs_integral_sub_le_of_ae {ν : Measure ℂ} [IsProbabilityMeasure ν] {f : ℂ → ℝ}
    (hf : Integrable f ν) {v ε : ℝ} (h : ∀ᵐ w ∂ν, |f w - v| ≤ ε) :
    |∫ w, f w ∂ν - v| ≤ ε := by
  have e : ∫ w, f w ∂ν - v = ∫ w, (f w - v) ∂ν := by
    rw [integral_sub hf (integrable_const v), integral_const, probReal_univ, one_smul]
  rw [e, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := ν) (C := ε)
    (h.mono fun w hw => by rwa [Real.norm_eq_abs])
  rwa [probReal_univ, mul_one] at this

variable (hK : IsCompact K) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
include hK hk

theorem integrable_remK_right (ν : Measure ℂ) [IsFiniteMeasure ν] (y : ℂ) :
    Integrable (fun w => remK K k y w) ν := by
  obtain ⟨M, -, hM⟩ := exists_bound_remK hK hk
  exact Integrable.of_bound
    ((measurable_remK hK.isClosed hk).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    M (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hM y w)

theorem integrable_remK_left (μ : Measure ℂ) [IsFiniteMeasure μ] (w : ℂ) :
    Integrable (fun y => remK K k y w) μ := by
  obtain ⟨M, -, hM⟩ := exists_bound_remK hK hk
  exact Integrable.of_bound
    ((measurable_remK hK.isClosed hk).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    M (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y w)

theorem integrable_inner_remK (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun y => ∫ w, remK K k y w ∂ν) μ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_remK hK hk
  have hsm : StronglyMeasurable fun y => ∫ w, remK K k y w ∂ν :=
    StronglyMeasurable.integral_prod_right' (f := Function.uncurry (remK K k))
      (measurable_remK hK.isClosed hk).stronglyMeasurable
  refine Integrable.of_bound hsm.aestronglyMeasurable (M * ν.real univ)
    (ae_of_all _ fun y => ?_)
  have := norm_integral_le_of_norm_le_const (μ := ν) (C := M)
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hM y w)
  linarith

/-- `|kernelCov k̂ μ ν| ≤ M` for probability measures, whenever `|k̂| ≤ M`. -/
theorem abs_kernelCov_remK_le {M : ℝ} (hM : ∀ y w, |remK K k y w| ≤ M) (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : |kernelCov (remK K k) μ ν| ≤ M := by
  have hin : ∀ y, |∫ w, remK K k y w ∂ν| ≤ M := fun y => by
    have := abs_integral_sub_le_of_ae (v := 0) (ε := M) (integrable_remK_right hK hk ν y)
      (ae_of_all _ fun w => by rw [sub_zero]; exact hM y w)
    rwa [sub_zero] at this
  have h0 := abs_integral_sub_le_of_ae (v := 0) (ε := M) (integrable_inner_remK hK hk μ ν)
    (ae_of_all _ fun y => by rw [sub_zero]; exact hin y)
  rw [sub_zero] at h0
  exact h0

/-- Splitting `kernelCov (neumannH + k)` on admissible measures carried by `K`. -/
theorem kernelCov_add_eq_remK {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0)
    (hν : IsAdmissibleH ν) (hνK : ν Kᶜ = 0) :
    kernelCov (fun x y => neumannH x y + k x y) μ ν =
      kernelCov neumannH μ ν + kernelCov (remK K k) μ ν := by
  haveI := hμ.1
  haveI := hν.1
  unfold kernelCov
  have hin : ∀ᵐ y ∂μ, ∫ w, (neumannH y w + k y w) ∂ν =
      ∫ w, neumannH y w ∂ν + ∫ w, remK K k y w ∂ν := by
    have hyK : ∀ᵐ y ∂μ, y ∈ K := mem_ae_iff.2 hμK
    filter_upwards [hyK] with y hy
    have hwK : ∀ᵐ w ∂ν, w ∈ K := mem_ae_iff.2 hνK
    rw [← integral_add (PalmArea.integrable_neumannH_left hν y)
      (integrable_remK_right hK hk ν y)]
    refine integral_congr_ae ?_
    filter_upwards [hwK] with w hw
    rw [remK_of_mem hy hw]
  rw [integral_congr_ae hin, integral_add ?_ (integrable_inner_remK hK hk μ ν)]
  exact (integrable_neumannH_prod hμ hν).integral_prod_left

omit hK hk in
theorem tendsto_radius_zero_nodeB : Tendsto radius atTop (𝓝 0) :=
  RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds

/-- `kernelCov k̂ μ fc(x, 2^{-n}) → ∫ k̂(·, x) dμ` (uniform continuity of `k` on `K × K`). -/
theorem tendsto_kernelCov_remK_fc (μ : Measure ℂ) [IsFiniteMeasure μ] {x : ℝ} (hx : (x : ℂ) ∈ K)
    (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Tendsto (fun n => kernelCov (remK K k) μ (Palm.fcK x n)) atTop
      (𝓝 (∫ y, remK K k y (x : ℂ) ∂μ)) := by
  have huc := (hK.prod hK).uniformContinuousOn_of_continuous hk
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set m := μ.real univ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  obtain ⟨δ, hδ, hδk⟩ := huc (ε / (m + 1)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hev.and (tendsto_radius_zero_nodeB.eventually (gt_mem_nhds hδ)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hKn, hrn⟩ := hN n hn
  have hinner : ∀ y, |∫ w, remK K k y w ∂(Palm.fcK x n) - remK K k y x| ≤ ε / (m + 1) := by
    intro y
    refine abs_integral_sub_le_of_ae (integrable_remK_right hK hk _ y) ?_
    have hwK : ∀ᵐ w ∂(Palm.fcK x n), w ∈ K := mem_ae_iff.2 hKn
    filter_upwards [hwK, Palm.ae_fcK x n] with w hw hwx
    by_cases hy : y ∈ K
    · rw [remK_of_mem hy hw, remK_of_mem hy hx]
      have := hδk (y, w) ⟨hy, hw⟩ (y, x) ⟨hy, hx⟩ (by
        rw [Prod.dist_eq, dist_self]
        exact max_lt hδ (by rw [dist_eq_norm]; exact lt_of_le_of_lt hwx hrn))
      rw [Real.dist_eq] at this; exact this.le
    · rw [remK_of_not_mem_left hy, remK_of_not_mem_left hy, sub_zero, abs_zero]; positivity
  rw [Real.dist_eq]
  unfold kernelCov
  rw [← integral_sub (integrable_inner_remK hK hk _ _) (integrable_remK_left hK hk μ _)]
  calc |∫ y, (∫ w, remK K k y w ∂(Palm.fcK x n) - remK K k y x) ∂μ|
      ≤ ε / (m + 1) * m := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const
          (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hinner y)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- `kernelCov k̂ fc(x, 2^{-n}) fc(x, 2^{-n}) → k(x, x)`. -/
theorem tendsto_kernelCov_remK_fc_fc {x : ℝ} (hx : (x : ℂ) ∈ K)
    (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Tendsto (fun n => kernelCov (remK K k) (Palm.fcK x n) (Palm.fcK x n)) atTop
      (𝓝 (k x x)) := by
  have huc := (hK.prod hK).uniformContinuousOn_of_continuous hk
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδk⟩ := huc (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hev.and (tendsto_radius_zero_nodeB.eventually (gt_mem_nhds hδ)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hKn, hrn⟩ := hN n hn
  have hwK : ∀ᵐ w ∂(Palm.fcK x n), w ∈ K := mem_ae_iff.2 hKn
  have hinner : ∀ᵐ y ∂(Palm.fcK x n),
      |∫ w, remK K k y w ∂(Palm.fcK x n) - k x x| ≤ ε / 2 := by
    filter_upwards [hwK, Palm.ae_fcK x n] with y hy hyx
    refine abs_integral_sub_le_of_ae (integrable_remK_right hK hk _ y) ?_
    filter_upwards [hwK, Palm.ae_fcK x n] with w hw hwx
    rw [remK_of_mem hy hw]
    have := hδk (y, w) ⟨hy, hw⟩ (x, x) ⟨hx, hx⟩ (by
      rw [Prod.dist_eq]
      exact max_lt (by rw [dist_eq_norm]; exact lt_of_le_of_lt hyx hrn)
        (by rw [dist_eq_norm]; exact lt_of_le_of_lt hwx hrn))
    rw [Real.dist_eq] at this; exact this.le
  rw [Real.dist_eq]
  have := abs_integral_sub_le_of_ae (integrable_inner_remK hK hk _ _) hinner
  unfold kernelCov
  linarith

end Kernel

/-! ## 2. The mixed field: covariance and variance at shrinking boundary circles -/

section Mixed

variable {D S K : Set ℂ} {R : ℝ} {k : ℂ → ℂ → ℝ}

theorem isAdmissibleDual_of_localHyp (hL : K3.MixedLocalHyp D S K R) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) : IsAdmissibleDual D (mixedSpace D S) μ :=
  K3.isAdmissibleDual_mixed_of_local hL.isOpen hL.subset_H hL.bounded hL.free_real hL.compact
    hL.pos hL.local_ hμ hμK

theorem isAdmissibleH_fcK (x : ℝ) (n : ℕ) : IsAdmissibleH (Palm.fcK x n) :=
  isAdmissibleH_foldedCircle (show (0 : ℝ) ≤ ((x : ℂ)).im by simp) (radius_pos n)

variable (hL : K3.MixedLocalHyp D S K R) (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K))
  (hkc : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Kᶜ = 0 → IsAdmissibleH ν → ν Kᶜ = 0 →
    dualCov D (mixedSpace D S) μ ν = kernelCov (fun x y => neumannH x y + k x y) μ ν)
include hL hk hkc

/-- **hcov (dual form).** `dualCov(μ, fc(x, 2^{-n})) → ∫ G(x, ·) dμ`. -/
theorem tendsto_dualCov_mixed_fc {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0)
    {x : ℝ} (hx : (x : ℂ) ∈ K) (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Tendsto (fun n => dualCov D (mixedSpace D S) μ (Palm.fcK x n)) atTop
      (𝓝 (∫ z, mixedGreenK K k x z ∂μ)) := by
  have := hμ.1
  have hK := hL.compact
  have e : ∫ z, mixedGreenK K k x z ∂μ =
      ∫ y, neumannH (x : ℂ) y ∂μ + ∫ y, remK K k y (x : ℂ) ∂μ :=
    integral_add (PalmArea.integrable_neumannH_left hμ _) (integrable_remK_left hK hk μ _)
  rw [e]
  refine ((PalmFree.tendsto_integral_fcPot hμ x).add
    (tendsto_kernelCov_remK_fc hK hk μ hx hev)).congr' ?_
  filter_upwards [hev] with n hn
  rw [hkc μ _ hμ hμK (isAdmissibleH_fcK x n) hn,
    kernelCov_add_eq_remK hK hk hμ hμK (isAdmissibleH_fcK x n) hn,
    PalmFree.kernelCov_fc_right' μ (x : ℂ) (radius_pos n)]

/-- **The Palm shift on measures carried by `K`**: no junk value. -/
theorem mixedGreenSample_eq {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0)
    {x : ℝ} (hx : (x : ℂ) ∈ K) (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Prop16Asm.mixedGreenSample D S x μ = ∫ z, mixedGreenK K k x z ∂μ :=
  (tendsto_dualCov_mixed_fc hL hk hkc hμ hμK hx hev).limUnder_eq

/-- **hcov.** `Cov(X μ, X fc(x, 2^{-n})) → ∫ G(x, ·) dμ` for the mixed GFF. -/
theorem tendsto_cov_mixed_fc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsMixedGFF D S X P) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hμK : μ Kᶜ = 0) {x : ℝ} (hx : (x : ℂ) ∈ K) (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Tendsto (fun n => cov[fun ω => X ω μ, fun ω => X ω (Palm.fcK x n); P]) atTop
      (𝓝 (∫ z, mixedGreenK K k x z ∂μ)) := by
  refine (tendsto_dualCov_mixed_fc hL hk hkc hμ hμK hx hev).congr' ?_
  filter_upwards [hev] with n hn
  exact (hX.covariance_eq _ _ (isAdmissibleDual_of_localHyp hL hμ hμK)
    (isAdmissibleDual_of_localHyp hL (isAdmissibleH_fcK x n) hn)).symm

/-- **hvarbd (exact form).** On a circle carried by `K`,
`Var X(fc(x, 2^{-n})) + 2 log 2^{-n} = kernelCov k̂ (fc, fc)`. -/
theorem var_mixed_fc_add_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsMixedGFF D S X P) {x : ℝ} {n : ℕ}
    (hn : Palm.fcK x n Kᶜ = 0) :
    Var[fun ω => X ω (Palm.fcK x n); P] + 2 * Real.log (radius n) =
      kernelCov (remK K k) (Palm.fcK x n) (Palm.fcK x n) := by
  have ha := isAdmissibleDual_of_localHyp hL (isAdmissibleH_fcK x n) hn
  rw [← covariance_self (hX.measurable_coord _).aemeasurable, hX.covariance_eq _ _ ha ha,
    hkc _ _ (isAdmissibleH_fcK x n) hn (isAdmissibleH_fcK x n) hn,
    kernelCov_add_eq_remK hL.compact hk (isAdmissibleH_fcK x n) hn (isAdmissibleH_fcK x n) hn,
    kernelCov_fc_real_sameCenter (radius_pos n) (radius_pos n), max_self]
  ring

/-- **hvar.** `Var X(fc(x, 2^{-n})) + 2 log 2^{-n} → k(x, x)`. -/
theorem tendsto_var_mixed_fc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsMixedGFF D S X P) {x : ℝ} (hx : (x : ℂ) ∈ K)
    (hev : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0) :
    Tendsto (fun n => Var[fun ω => X ω (Palm.fcK x n); P] + 2 * Real.log (radius n)) atTop
      (𝓝 (k x x)) :=
  (tendsto_kernelCov_remK_fc_fc hL.compact hk hx hev).congr' (hev.mono fun _ hn =>
    (var_mixed_fc_add_log hL hk hkc hX hn).symm)

end Mixed

end Prop16Asm

end QuantumZipper
