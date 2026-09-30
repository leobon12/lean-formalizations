import QuantumZipper.Proofs.Zipper.E4L3

/-!
# E4-L3i, deterministic inputs I: the E4L3 limits along a general filter

`handoff/E4.md`, item hL3i (interior law continuity), for Sheffield, arXiv:1012.4797, proof of
Lemma 5.6 (pp. 66–68). The E4L3 lemmas (`E4L3Basic`, `E4L3Conv`) are proved along `𝓝[<] τ`;
here they are restated and reproved (copied and generalized) along an arbitrary filter `l`
with `l ≤ 𝓝[Icc 0 T₁] τ`, `τ ∈ [0, T₁]`. The only uses of the filter in the original proofs
are that eventually `s ∈ [0, T₁]` (uniform bounds, measurability) and continuity of the reverse
flow `s ↦ revMap V s z` on `Ici 0` (`ReverseFlow.continuousOn_revMap_time`), so the proofs go
through verbatim. Main application: `l = 𝓝[≥] s` at a live time `s` (right-continuity).

* `tendsto_integral_comp_revMap_gen`, `tendsto_log_norm_deriv_revMap_gen`, `tendsto_qt_gen`;
* `tendsto_neumannH_revMap_gen`, `tendsto_kk_gen`, `tendsto_kernelCov_left_gen`.

Own elementary arguments (dominated convergence), as in `E4L3Basic`/`E4L3Conv`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace E4Grid

open E1 TwoPoint PalmNorm

variable {V : ℝ → ℝ} {l : Filter ℝ} [l.IsCountablyGenerated] {τ T₁ : ℝ}

omit [l.IsCountablyGenerated] in
theorem eventually_mem_Icc_gen (hl : l ≤ 𝓝[Icc 0 T₁] τ) : ∀ᶠ s in l, s ∈ Icc (0 : ℝ) T₁ :=
  hl self_mem_nhdsWithin

omit [l.IsCountablyGenerated] in
theorem tendsto_revMap_gen (hV : Continuous V) {z : ℂ} (hz : z ∈ H) (hl : l ≤ 𝓝[Icc 0 T₁] τ)
    (hτ : τ ∈ Icc (0 : ℝ) T₁) : Tendsto (fun s => revMap V s z) l (𝓝 (revMap V τ z)) :=
  (ReverseFlow.continuousOn_revMap_time V hV z hz τ hτ.1).tendsto.mono_left
    (hl.trans (nhdsWithin_mono _ Icc_subset_Ici_self))

/-- **Dominated convergence along the reverse flow**, general filter. -/
theorem tendsto_integral_comp_revMap_gen (hV : Continuous V) {ϖ : Measure ℂ} [IsFiniteMeasure ϖ]
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0) (hl : l ≤ 𝓝[Icc 0 T₁] τ)
    (hτ : τ ∈ Icc (0 : ℝ) T₁)
    {G : ℝ → ℂ → ℝ} (hGm : Measurable (Function.uncurry G)) {a : ℝ → ℝ} {a₀ : ℝ}
    (ha : Tendsto a l (𝓝 a₀))
    (hGc : ContinuousOn (Function.uncurry G) (Icc (a₀ - 1) (a₀ + 1) ×ˢ H)) :
    Tendsto (fun s => ∫ z, G (a s) (revMap V s z) ∂ϖ) l
      (𝓝 (∫ z, G a₀ (revMap V τ z) ∂ϖ)) := by
  obtain ⟨δ, R, hδ, -, hb⟩ := revMap_bounds hV hK hKH T₁
  set S : Set (ℝ × ℂ) := Icc (a₀ - 1) (a₀ + 1) ×ˢ (Metric.closedBall 0 R ∩ {w | δ ≤ w.im})
  have hSc : IsCompact S := isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im))
  have hSH : S ⊆ Icc (a₀ - 1) (a₀ + 1) ×ˢ H :=
    prod_mono le_rfl fun w hw => show 0 < w.im from hδ.trans_le hw.2
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn (hGc.mono hSH)
  have hKae := ae_mem_of_compl_null hϖK
  have hev : ∀ᶠ s in l, s ∈ Icc 0 T₁ ∧ a s ∈ Icc (a₀ - 1) (a₀ + 1) :=
    (eventually_mem_Icc_gen hl).and (ha (Icc_mem_nhds (by linarith) (by linarith)))
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
    (integrable_const B) ?_
  · filter_upwards [hev] with s hs
    exact (hGm.comp (measurable_const.prodMk
      (measurable_revMap hV hs.1.1))).aestronglyMeasurable
  · filter_upwards [hev] with s hs
    filter_upwards [hKae] with z hz
    obtain ⟨-, -, h⟩ := hb z hz
    obtain ⟨h1, h2⟩ := h s hs.1
    exact hB (a s, revMap V s z) ⟨hs.2, by simpa using h1, h2⟩
  · filter_upwards [hKae] with z hz
    have hzH : z ∈ H := hKH hz
    have hc : ContinuousAt (Function.uncurry G) (a₀, revMap V τ z) :=
      hGc.continuousAt (prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
        (isOpen_H.mem_nhds (im_revMap_pos hV hzH hτ.1)))
    exact hc.tendsto.comp (ha.prodMk_nhds (tendsto_revMap_gen hV hzH hl hτ))

theorem tendsto_log_norm_deriv_revMap_gen (hV : Continuous V) {z : ℂ} (hz : z ∈ H)
    (hl : l ≤ 𝓝[Icc 0 T₁] τ) (hτ : τ ∈ Icc (0 : ℝ) T₁) :
    Tendsto (fun s => Real.log ‖deriv (revMap V s) z‖) l
      (𝓝 (Real.log ‖deriv (revMap V τ) z‖)) := by
  have hT₁ : 0 ≤ T₁ := hτ.1.trans hτ.2
  have hII : IntervalIntegrable (fun r => 2 / revMap V r z ^ 2) MeasureTheory.volume 0 T₁ :=
    RegCont.intervalIntegrable_two_div_sq_revMap hV hz hT₁
  have hc : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, 2 / revMap V r z ^ 2) (uIcc 0 T₁) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hT₁]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT₁).1 hII)
  rw [uIcc_of_le hT₁] at hc
  have hre := (Complex.continuous_re.tendsto _).comp ((hc τ hτ).tendsto.mono_left hl)
  rw [log_norm_deriv_revMap V hV hτ.1 hz]
  refine hre.congr' ?_
  filter_upwards [eventually_mem_Icc_gen hl] with s hs
  rw [log_norm_deriv_revMap V hV hs.1 hz]; rfl

theorem tendsto_qt_gen (κ : ℝ) (hV : Continuous V) {ϖ : Measure ℂ} [IsFiniteMeasure ϖ]
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0) (hl : l ≤ 𝓝[Icc 0 T₁] τ)
    (hτ : τ ∈ Icc (0 : ℝ) T₁) :
    Tendsto (fun s => B2.qt κ V s ϖ) l (𝓝 (B2.qt κ V τ ϖ)) := by
  have hT₁ : 0 ≤ T₁ := hτ.1.trans hτ.2
  obtain ⟨δ, R, hδ, -, hb⟩ := revMap_bounds hV hK hKH T₁
  have hKae := ae_mem_of_compl_null hϖK
  refine Tendsto.const_mul _ (tendsto_integral_filter_of_dominated_convergence
    (fun _ => 2 * T₁ / δ ^ 2) ?_ ?_ (integrable_const _) ?_)
  · exact Eventually.of_forall fun s =>
      (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable
  · filter_upwards [eventually_mem_Icc_gen hl] with s hs
    filter_upwards [hKae] with z hz
    have hzH : z ∈ H := hKH hz
    rw [Real.norm_eq_abs]
    refine (RegCont.abs_log_norm_deriv_revMap_le_small hV hs.1 hzH).trans ?_
    have hzδ := (hb z hz).1
    have : δ ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ hδ.le hzδ 2
    exact div_le_div₀ (by linarith) (by linarith [hs.2]) (by positivity) this
  · filter_upwards [hKae] with z hz
    exact tendsto_log_norm_deriv_revMap_gen hV (hKH hz) hl hτ

omit [l.IsCountablyGenerated] in
theorem tendsto_neumannH_revMap_gen (hV : Continuous V) {z w : ℂ} (hzH : z ∈ H) (hwH : w ∈ H)
    (hl : l ≤ 𝓝[Icc 0 T₁] τ) (hτ : τ ∈ Icc (0 : ℝ) T₁)
    (hinj : z ≠ w → revMap V τ z ≠ revMap V τ w) :
    Tendsto (fun s => neumannH (revMap V s z) (revMap V s w)) l
      (𝓝 (neumannH (revMap V τ z) (revMap V τ w))) := by
  have hpz := im_revMap_pos hV hzH hτ.1
  have hpw := im_revMap_pos hV hwH hτ.1
  by_cases hzw : z = w
  · subst hzw
    exact tendsto_neumannH_diag (g := fun s => revMap V s z)
      (tendsto_revMap_gen hV hzH hl hτ) hpz
  · exact tendsto_neumannH_comp (g₁ := fun s => revMap V s z) (g₂ := fun s => revMap V s w)
      (tendsto_revMap_gen hV hzH hl hτ) (tendsto_revMap_gen hV hwH hl hτ) (hinj hzw)
      (ne_conj_of_im_pos hpz hpw)

variable {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} {α C : ℝ}

/-- **`k(ϖ_s, ϖ_s) → k(ϖ_τ, ϖ_τ)`**, general filter. -/
theorem tendsto_kk_gen (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0)
    (hα : 0 < α) (hF : IsFrostman ϖ α C) (hl : l ≤ 𝓝[Icc 0 T₁] τ) (hτ : τ ∈ Icc (0 : ℝ) T₁) :
    Tendsto (fun s => kernelCov neumannH (varpiT V s ϖ) (varpiT V s ϖ)) l
      (𝓝 (kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ))) := by
  obtain ⟨δ, R, hδ, hR, hb⟩ := revMap_bounds hV hK hKH T₁
  have hKae := ae_mem_of_compl_null hϖK
  have hadm : IsAdmissibleH ϖ := by
    refine FrostmanReg.isAdmissibleH_of_frostman (R := R) (measure_mono_null ?_ hϖK) hF hα
    refine compl_subset_compl.2 fun z hz => ⟨mem_closedBall_zero_iff.2 (hb z hz).2.1, ?_⟩
    exact le_of_lt (show 0 < z.im from hKH hz)
  have heq : ∀ s, 0 ≤ s → kernelCov neumannH (varpiT V s ϖ) (varpiT V s ϖ) =
      ∫ p, neumannH (revMap V s p.1) (revMap V s p.2) ∂(ϖ.prod ϖ) := fun s hs =>
    kernelCov_map_eq_prod (measurable_revMap hV hs)
      (varpiT_good hV hK hKH hϖK hα hF hs).adm
  have hae : ∀ᵐ p ∂ϖ.prod ϖ, p.1 ∈ K ∧ p.2 ∈ K :=
    (Measure.quasiMeasurePreserving_fst.ae hKae).and
      (Measure.quasiMeasurePreserving_snd.ae hKae)
  have hbd : Integrable (fun p : ℂ × ℂ => |neumannH p.1 p.2| +
      (|Real.log (R / δ)| + 2 * (|Real.log (2 * δ)| + |Real.log (2 * R)|))) (ϖ.prod ϖ) :=
    (integrable_neumannH_prod hadm hadm).abs.add (integrable_const _)
  have hmeas : ∀ᶠ s in l, AEStronglyMeasurable
      (fun p : ℂ × ℂ => neumannH (revMap V s p.1) (revMap V s p.2)) (ϖ.prod ϖ) := by
    filter_upwards [eventually_mem_Icc_gen hl] with s hs
    have hm := measurable_revMap hV hs.1
    exact (measurable_neumannH.comp ((hm.comp measurable_fst).prodMk
      (hm.comp measurable_snd))).aestronglyMeasurable
  have hbound : ∀ᶠ s in l, ∀ᵐ p ∂(ϖ.prod ϖ),
      ‖neumannH (revMap V s p.1) (revMap V s p.2)‖ ≤ |neumannH p.1 p.2| +
        (|Real.log (R / δ)| + 2 * (|Real.log (2 * δ)| + |Real.log (2 * R)|)) := by
    filter_upwards [eventually_mem_Icc_gen hl] with s hs'
    filter_upwards [hae] with p hp
    obtain ⟨hz1, hz2, hz3⟩ := hb p.1 hp.1
    obtain ⟨hw1, hw2, hw3⟩ := hb p.2 hp.2
    obtain ⟨c1, c2⟩ := twoPoint_cmp hV hKH hδ hR hb hs' hp.1 hp.2
    rw [Real.norm_eq_abs]
    exact abs_neumannH_le hδ hz1 hw1 (hz3 s hs').2 (hw3 s hs').2 hz2 hw2 (hz3 s hs').1
      (hw3 s hs').1 c1 c2
  have hlim : ∀ᵐ p ∂(ϖ.prod ϖ), Tendsto
      (fun s => neumannH (revMap V s p.1) (revMap V s p.2)) l
      (𝓝 (neumannH (revMap V τ p.1) (revMap V τ p.2))) := by
    filter_upwards [hae] with p hp
    refine tendsto_neumannH_revMap_gen hV (hKH hp.1) (hKH hp.2) hl hτ fun hzw h => hzw ?_
    have c := (twoPoint_cmp hV hKH hδ hR hb hτ hp.1 hp.2).1
    rw [h, sub_self, norm_zero, zero_mul] at c
    have : ‖p.1 - p.2‖ = 0 := le_antisymm (nonpos_of_mul_nonpos_left c hδ) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hT := tendsto_integral_filter_of_dominated_convergence _ hmeas hbound hbd hlim
  rw [heq τ hτ.1]
  refine hT.congr' ?_
  filter_upwards [eventually_mem_Icc_gen hl] with s hs
  exact (heq s hs.1).symm

/-- **`k(ϖ_s, ν) → k(ϖ_τ, ν)`** for a good measure `ν`, general filter. -/
theorem tendsto_kernelCov_left_gen (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hl : l ≤ 𝓝[Icc 0 T₁] τ) (hτ : τ ∈ Icc (0 : ℝ) T₁) {ν : Measure ℂ}
    (hν : GoodMeas ν) :
    Tendsto (fun s => kernelCov neumannH (varpiT V s ϖ) ν) l
      (𝓝 (kernelCov neumannH (varpiT V τ ϖ) ν)) := by
  have := hν.prob
  have hc := hν.continuous_neuPot
  rw [varpiT, kernelCov_map_left (measurable_revMap hV hτ.1)]
  refine (tendsto_integral_comp_revMap_gen hV hK hKH hϖK hl hτ (G := fun _ w => neuPot ν w)
    ((measurable_neuPot ν).comp measurable_snd) (a := fun _ => 0) (a₀ := 0) tendsto_const_nhds
    (hc.comp continuous_snd).continuousOn).congr' ?_
  filter_upwards [eventually_mem_Icc_gen hl] with s hs
  rw [varpiT, kernelCov_map_left (measurable_revMap hV hs.1)]

end E4Grid
end QuantumZipper
