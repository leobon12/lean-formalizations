import QuantumZipper.Proofs.LQG.LogSingularity

/-!
# G3 fidelity F2 (part 2): vague limits cut along sets with atomless finite frontier

If `νₖ → ν` vaguely on `ℝ`, the `νₖ` are finite on compacts, `S` is a measurable set whose
frontier lies in a finite set `F` of non-atoms of `ν`, and the sets `Sₖ` agree with `S` away from
any fixed neighbourhood of `F` for large `k`, then `∫_{Sₖ} f dνₖ → ∫_S f dν` for every continuous
compactly supported `f` (`tendsto_integral_cut`).

This is the portmanteau theorem for sets with `ν`-null boundary (e.g. Billingsley, *Convergence
of Probability Measures*, 2nd ed., Thm 2.1 (v)), in the vague form with moving sets; the proof is
the standard one: split `f 1_{Sₖ}` with a continuous cutoff `τ_δ` equal to `1` near `F`,
`f 1_S (1 − τ_δ)` is continuous, and `∫ τ_δ dν → Σ_{p ∈ F} ν{p} = 0`. Written out here (own
elementary proof, AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3Fid

open LogSing

/-- The cutoff near a finite set: `1` on the `δ/2`-neighbourhood of `F`, `0` off its
`δ`-neighbourhood. -/
def cutF (F : Finset ℝ) (δ : ℝ) (t : ℝ) : ℝ := min 1 (∑ p ∈ F, trapS p δ t)

theorem continuous_cutF (F : Finset ℝ) (δ : ℝ) : Continuous (cutF F δ) :=
  continuous_const.min (continuous_finset_sum _ fun p _ => continuous_trapS p δ)

theorem cutF_nonneg (F : Finset ℝ) (δ t : ℝ) : 0 ≤ cutF F δ t :=
  le_min zero_le_one (Finset.sum_nonneg fun _ _ => trapS_nonneg)

theorem cutF_le_one (F : Finset ℝ) (δ t : ℝ) : cutF F δ t ≤ 1 := min_le_left _ _

theorem cutF_eq_one {F : Finset ℝ} {δ : ℝ} (hδ : 0 < δ) {t p : ℝ} (hp : p ∈ F)
    (h : |t - p| ≤ δ / 2) : cutF F δ t = 1 := by
  refine le_antisymm (cutF_le_one F δ t) (le_min le_rfl ?_)
  rw [← trapS_eq_one (s := p) (t := t) hδ h]
  exact Finset.single_le_sum (f := fun p => trapS p δ t) (fun _ _ => trapS_nonneg) hp

theorem hasCompactSupport_cutF (F : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (cutF F δ) := by
  have hs : HasCompactSupport (fun t => ∑ p ∈ F, trapS p δ t) := by
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | insert a F ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (hasCompactSupport_trapS hδ).add ih
  refine hs.mono fun t ht => ?_
  intro h0
  apply ht
  simp [cutF, h0]

theorem cutF_le_sum (F : Finset ℝ) (δ t : ℝ) : cutF F δ t ≤ ∑ p ∈ F, trapS p δ t :=
  min_le_right _ _

theorem trapS_le_indicator {p δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    trapS p δ t ≤ (Icc (p - δ) (p + δ)).indicator 1 t := by
  by_cases h : t ∈ Icc (p - δ) (p + δ)
  · rw [indicator_of_mem h]
    exact max_le zero_le_one (min_le_left _ _)
  · rw [indicator_of_notMem h, trapS_eq_zero hδ]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- The piece of `f 1_S` away from `F` is continuous. -/
theorem continuous_indicator_mul_cutF {S : Set ℝ} {F : Finset ℝ} (hfr : frontier S ⊆ ↑F)
    {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (S.indicator fun t => f t * (1 - cutF F δ t)) := by
  have hg : Continuous fun t => f t * (1 - cutF F δ t) :=
    hf.mul (continuous_const.sub (continuous_cutF F δ))
  refine continuous_iff_continuousAt.2 fun t => ?_
  by_cases hi : t ∈ interior S
  · refine hg.continuousAt.congr ?_
    filter_upwards [isOpen_interior.mem_nhds hi] with u hu
    rw [indicator_of_mem (interior_subset hu)]
  by_cases hc : t ∈ closure S
  · have hp : t ∈ (F : Set ℝ) := hfr ⟨hc, hi⟩
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have hb : Metric.ball t (δ / 2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by linarith)
    filter_upwards [hb] with u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    by_cases huS : u ∈ S
    · rw [indicator_of_mem huS, cutF_eq_one hδ hp hu.le]; ring
    · rw [indicator_of_notMem huS]
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have ho : (closure S)ᶜ ∈ 𝓝 t := isClosed_closure.isOpen_compl.mem_nhds hc
    filter_upwards [ho] with u hu
    rw [indicator_of_notMem fun h => hu (subset_closure h)]

/-- The mass of the cutoff under an atomless-at-`F` locally finite measure is small. -/
theorem exists_integral_cutF_lt {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {F : Finset ℝ}
    (hF : ∀ p ∈ F, ν {p} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∫ t, cutF F δ t ∂ν < ε := by
  set ε' := ε / ((F.card : ℝ) + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hev : ∀ p ∈ F, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ν (Icc (p - δ) (p + δ)) < ENNReal.ofReal ε' := by
    intro p hp
    have ht := tendsto_measure_biInter_gt (μ := ν) (s := fun r => Icc (p - r) (p + r)) (a := 0)
      (fun r _ => measurableSet_Icc.nullMeasurableSet)
      (fun i j _ hij => Icc_subset_Icc (by linarith) (by linarith))
      ⟨1, one_pos, (isCompact_Icc.measure_lt_top).ne⟩
    have hI : (⋂ r > (0 : ℝ), Icc (p - r) (p + r)) = {p} := by
      ext t
      simp only [mem_iInter, mem_Icc, mem_singleton_iff]
      constructor
      · intro h
        by_contra hne
        have hpos : 0 < |t - p| / 2 := by
          have := abs_pos.2 (sub_ne_zero.2 hne); linarith
        obtain ⟨h1, h2⟩ := h _ hpos
        rcases le_or_gt 0 (t - p) with h0 | h0
        · rw [abs_of_nonneg h0] at h1 h2; exact hne (by linarith)
        · rw [abs_of_neg h0] at h1 h2; exact hne (by linarith)
      · rintro rfl r hr; constructor <;> linarith
    rw [hI, hF p hp] at ht
    exact ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε'0))
  obtain ⟨δ, hδall, hδ⟩ := ((Filter.eventually_all_finset F).2 hev).and
    self_mem_nhdsWithin |>.exists
  refine ⟨δ, hδ, ?_⟩
  have hint : ∀ p ∈ F, Integrable (trapS p δ) ν := fun p _ =>
    (continuous_trapS p δ).integrable_of_hasCompactSupport (hasCompactSupport_trapS hδ)
  calc ∫ t, cutF F δ t ∂ν ≤ ∫ t, ∑ p ∈ F, trapS p δ t ∂ν :=
        integral_mono ((continuous_cutF F δ).integrable_of_hasCompactSupport
          (hasCompactSupport_cutF F hδ)) (integrable_finset_sum F hint) (cutF_le_sum F δ)
    _ = ∑ p ∈ F, ∫ t, trapS p δ t ∂ν := integral_finset_sum F hint
    _ ≤ ∑ p ∈ F, ε' := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hfin : ν (Icc (p - δ) (p + δ)) < ⊤ := isCompact_Icc.measure_lt_top
        calc ∫ t, trapS p δ t ∂ν ≤ ∫ t, (Icc (p - δ) (p + δ)).indicator 1 t ∂ν :=
              integral_mono (hint p hp) ((integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator
                measurableSet_Icc) (trapS_le_indicator hδ)
          _ = ν.real (Icc (p - δ) (p + δ)) := integral_indicator_one measurableSet_Icc
          _ ≤ ε' := by
              rw [measureReal_def]
              exact ENNReal.toReal_le_of_le_ofReal hε'0.le (hδall p hp).le
    _ = F.card * ε' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ < ε := by
        rw [hε', mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Cut vague limits.** -/
theorem tendsto_integral_cut {νs : ℕ → Measure ℝ} {ν : Measure ℝ} (hν : IsVagueLimitR νs ν)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k)) {F : Finset ℝ} (hF : ∀ p ∈ F, ν {p} = 0)
    {S : Set ℝ} (hSm : MeasurableSet S) (hfr : frontier S ⊆ ↑F) {Sk : ℕ → Set ℝ}
    (hSk : ∀ k, MeasurableSet (Sk k))
    (hcut : ∀ δ > 0, ∀ᶠ k in atTop, ∀ t, (∀ p ∈ F, δ < |t - p|) → (t ∈ Sk k ↔ t ∈ S))
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun k => ∫ t in Sk k, f t ∂νs k) atTop (𝓝 (∫ t in S, f t ∂ν)) := by
  have := hν.1
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (4 * (M + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδν⟩ := exists_integral_cutF_lt hF hε'0
  set τ := cutF F δ with hτ
  set g := S.indicator fun t => f t * (1 - τ t) with hg
  have hgc : Continuous g := continuous_indicator_mul_cutF hfr hδ hf
  have hgcs : HasCompactSupport g := by
    refine hfc.mono fun t ht h0 => ht ?_
    simp [hg, h0]
  have hτc := continuous_cutF F δ
  have hτcs := hasCompactSupport_cutF F hδ
  have h1 := hν.2 g hgc hgcs
  have h2 := hν.2 τ hτc hτcs
  rw [Metric.tendsto_atTop] at h1 h2
  obtain ⟨K1, hK1⟩ := h1 (ε / 4) (by positivity)
  obtain ⟨K2, hK2⟩ := h2 ε' hε'0
  obtain ⟨K3, hK3⟩ := eventually_atTop.1 (hcut (δ / 2) (by linarith))
  refine ⟨max K1 (max K2 K3), fun k hk => ?_⟩
  have hk1 : K1 ≤ k := le_of_max_le_left hk
  have hk2 : K2 ≤ k := le_of_max_le_left (le_of_max_le_right hk)
  have hk3 : K3 ≤ k := le_of_max_le_right (le_of_max_le_right hk)
  -- decomposition
  have hdec : ∀ (A : Set ℝ), (∀ t, τ t < 1 → (t ∈ A ↔ t ∈ S)) →
      A.indicator f = g + A.indicator fun t => f t * τ t := by
    intro A hA
    funext t
    simp only [Pi.add_apply, hg]
    rcases (cutF_le_one F δ t).lt_or_eq with hlt | heq
    · by_cases hS : t ∈ S
      · rw [indicator_of_mem hS, indicator_of_mem ((hA t hlt).2 hS), indicator_of_mem
          ((hA t hlt).2 hS)]; ring
      · have hA' : t ∉ A := fun h => hS ((hA t hlt).1 h)
        rw [indicator_of_notMem hS, indicator_of_notMem hA', indicator_of_notMem hA']; ring
    · have : τ t = 1 := heq
      by_cases hA' : t ∈ A
      · by_cases hS : t ∈ S
        · rw [indicator_of_mem hS, indicator_of_mem hA', indicator_of_mem hA', this]; ring
        · rw [indicator_of_notMem hS, indicator_of_mem hA', indicator_of_mem hA', this]; ring
      · by_cases hS : t ∈ S
        · rw [indicator_of_mem hS, indicator_of_notMem hA', indicator_of_notMem hA', this]; ring
        · rw [indicator_of_notMem hS, indicator_of_notMem hA', indicator_of_notMem hA']; ring
  have hfar : ∀ t, τ t < 1 → ∀ p ∈ F, δ / 2 < |t - p| := by
    intro t ht p hp
    by_contra h
    exact (cutF_eq_one hδ hp (not_lt.1 h)).not_lt ht
  have hdk := hdec (Sk k) fun t ht => hK3 k hk3 t (hfar t ht)
  have hd := hdec S fun t _ => Iff.rfl
  have hfk := hfin k
  have hig : ∀ μ : Measure ℝ, [IsFiniteMeasureOnCompacts μ] → Integrable g μ :=
    fun μ _ => hgc.integrable_of_hasCompactSupport hgcs
  have hiτ : ∀ μ : Measure ℝ, [IsFiniteMeasureOnCompacts μ] → Integrable τ μ :=
    fun μ _ => hτc.integrable_of_hasCompactSupport hτcs
  have hifτ : ∀ μ : Measure ℝ, [IsFiniteMeasureOnCompacts μ] → ∀ A, MeasurableSet A →
      Integrable (A.indicator fun t => f t * τ t) μ := fun μ _ A hA =>
    ((hf.mul hτc).integrable_of_hasCompactSupport (hτcs.mul_left)).indicator hA
  have hbound : ∀ μ : Measure ℝ, [IsFiniteMeasureOnCompacts μ] → ∀ A, MeasurableSet A →
      ‖∫ t, A.indicator (fun t => f t * τ t) t ∂μ‖ ≤ M * ∫ t, τ t ∂μ := by
    intro μ _ A hA
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hiτ μ).const_mul M) (ae_of_all _ fun t => ?_)
    by_cases htA : t ∈ A
    · rw [indicator_of_mem htA, norm_mul, Real.norm_eq_abs (τ t), abs_of_nonneg
        (cutF_nonneg F δ t)]
      exact mul_le_mul_of_nonneg_right (hM t) (cutF_nonneg F δ t)
    · rw [indicator_of_notMem htA, norm_zero]
      exact mul_nonneg hM0 (cutF_nonneg F δ t)
  rw [← integral_indicator (hSk k), ← integral_indicator hSm, hdk, hd]
  simp only [Pi.add_apply]
  rw [integral_add (hig _) (hifτ _ _ (hSk k)), integral_add (hig _) (hifτ _ _ hSm), Real.dist_eq]
  have e1 := hK1 k hk1
  have e2 := hK2 k hk2
  rw [Real.dist_eq] at e1 e2
  have b1 := hbound (νs k) (Sk k) (hSk k)
  have b2 := hbound ν S hSm
  have hτν0 : 0 ≤ ∫ t, τ t ∂ν := integral_nonneg (cutF_nonneg F δ)
  have hτk : ∫ t, τ t ∂νs k < 2 * ε' := by
    have := (abs_lt.1 e2).2; linarith
  have hMε : M * (3 * ε') < 3 * ε / 4 := by
    rw [hε']
    rw [show M * (3 * (ε / (4 * (M + 1)))) = (3 / 4) * ε * (M / (M + 1)) by field_simp]
    have : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  have hb1 : ‖∫ t, (Sk k).indicator (fun t => f t * τ t) t ∂νs k‖ ≤ M * (2 * ε') :=
    b1.trans (mul_le_mul_of_nonneg_left hτk.le hM0)
  have hb2 : ‖∫ t, S.indicator (fun t => f t * τ t) t ∂ν‖ ≤ M * ε' :=
    b2.trans (mul_le_mul_of_nonneg_left hδν.le hM0)
  rw [Real.norm_eq_abs] at hb1 hb2
  have := abs_le.1 hb1
  have := abs_le.1 hb2
  have := abs_lt.1 e1
  rw [abs_lt]
  constructor <;> nlinarith

end G3Fid
end Thm18Asm
end QuantumZipper
