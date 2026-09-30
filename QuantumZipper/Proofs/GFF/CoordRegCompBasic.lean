import QuantumZipper.Proofs.GFF.CoordRegEnergy

/-!
# RC3 composition law, deterministic inputs: strip bounds and `|log Im|` integrability

The RC3-general theorem `CoordReg.ae_evalReg_coordChange_revMap_gen` needs, for the measure `ν`
at which the pulled-back field is regularized, integrability of `|log Im|` and a strip bound
(`CoordReg.StripBound`). Here we prove them for the measures `ν = μ.map (revMap V t)` that the
composition law (RC-COMP) needs, with `μ` a folded circle (touching or crossing `ℝ` allowed) or
a measure carried by a compact subset of `ℍ`.

* `stripBound_foldedCircle`: every folded circle `fc(w,r)` satisfies `StripBound` with exponent
  `1/4` and constant `200/√r` (from the strip mass bound `TwoPoint.foldedCircle_strip_le` and
  the logarithmic layer-cake bound `TwoPoint.lintegral_logRatio_le`).
* `stripBound_map`, `integrable_abs_log_im_map`: both properties pass to `μ.map Φ` whenever
  `Im z ≤ Im Φ z` (and `Im Φ z ≤ M`) on the support. The reverse Loewner flow increases
  imaginary parts (`im_le_im_revMap`), so no boundary behaviour of `revMap` near `ℝ` is needed.
* `stripBound_of_compact`: a finite measure carried by a compact subset of `ℍ`.

All proofs are own elementary arguments (cost rule of `AGENT_GUIDE.md`): no published source
treats these bookkeeping estimates; the analytic input is Duplantier–Sheffield, *Liouville
quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 (via RC3-general).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace CoordRegComp

open CoordReg

/-- Strip bound for a folded circle (own elementary proof). -/
theorem stripBound_foldedCircle (w : ℂ) {r : ℝ} (hr : 0 < r) :
    StripBound (foldedCircle w r) (200 / Real.sqrt r) (1 / 4) := by
  intro s hs hs1
  set μ := foldedCircle w r with hμ
  set S : Set ℂ := {x : ℂ | |x.im| < 2 * s} with hSdef
  set gf : ℂ → ℝ := fun u => max (Real.log (s / |u.im|)) 0 with hgf
  have hgm : Measurable gf :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hg0 : ∀ u, 0 ≤ gf u := fun u => le_max_right _ _
  have hgl := TwoPoint.lintegral_logRatio_le w hr hs
  have hgi : Integrable gf μ :=
    ⟨hgm.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
      exact lt_of_le_of_lt hgl ENNReal.ofReal_lt_top⟩
  have hgI : ∫ u, gf u ∂μ ≤ 36 * Real.sqrt (s / r) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hgl
  have hSm : MeasurableSet S :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).measurableSet
  have hSμ : μ.real S ≤ 18 * Real.sqrt (2 * s / r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (TwoPoint.foldedCircle_strip_le w hr (by linarith : (0 : ℝ) < 2 * s))
  set L := 1 + |Real.log s| with hL
  have hL0 : 0 ≤ L := by positivity
  have hpt : ∀ᵐ u ∂μ, {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) u ≤
      S.indicator (fun _ => L) u + gf u := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr] with u hu
    have hu0 : 0 < u.im := hu
    by_cases h : u.im ≤ s
    · have hS' : u ∈ S := by
        show |u.im| < 2 * s
        rw [abs_of_pos hu0]; linarith
      rw [indicator_of_mem (show u ∈ {z : ℂ | z.im ≤ s} from h), indicator_of_mem hS']
      have e1 : Real.log (s / |u.im|) = Real.log s - Real.log u.im := by
        rw [abs_of_pos hu0, Real.log_div hs.ne' hu0.ne']
      have e2 : |Real.log u.im| = -Real.log u.im :=
        abs_of_nonpos (Real.log_nonpos hu0.le (h.trans hs1))
      have e3 : |Real.log s| = -Real.log s := abs_of_nonpos (Real.log_nonpos hs.le hs1)
      have e4 : Real.log (s / |u.im|) ≤ gf u := le_max_left _ _
      rw [hL]
      linarith
    · rw [indicator_of_notMem (show u ∉ {z : ℂ | z.im ≤ s} from h)]
      exact add_nonneg (indicator_nonneg (fun _ _ => hL0) _) (hg0 u)
  have hle : ∫ u, {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) u ∂μ ≤
      ∫ u, (S.indicator (fun _ => L) u + gf u) ∂μ := integral_mono_of_nonneg
    (ae_of_all _ fun u => indicator_nonneg (fun z _ => by positivity) u)
    ((((integrable_const L).indicator hSm).add hgi :
      Integrable (fun u => S.indicator (fun _ => L) u + gf u) μ)) hpt
  rw [integral_add ((integrable_const L).indicator hSm) hgi, integral_indicator_const L hSm,
    smul_eq_mul] at hle
  refine hle.trans ?_
  -- numerics
  set q := s ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hs.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one hs.le hs1 (by norm_num)
  have hsq : Real.sqrt s = q * q := by
    rw [Real.sqrt_eq_rpow, hq, ← Real.rpow_add hs]; norm_num
  have hlog : |Real.log s| * q ≤ 4 := by
    have := Real.abs_log_mul_self_rpow_lt s (1 / 4) hs hs1 (by norm_num)
    rw [abs_mul, abs_of_nonneg hq0] at this
    norm_num at this; linarith
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have e1 : Real.sqrt (2 * s / r) = Real.sqrt 2 * (q * q) / Real.sqrt r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), hsq]
  have e2 : Real.sqrt (s / r) = q * q / Real.sqrt r := by
    rw [Real.sqrt_div hs.le, hsq]
  have key : 18 * (Real.sqrt 2 * (q * q)) * L + 36 * (q * q) ≤ 200 * q := by
    have a1 : q * q ≤ q := by nlinarith
    have a2 : q * L ≤ 5 := by rw [hL]; nlinarith
    have a3 : 18 * (Real.sqrt 2 * (q * q)) * L = 18 * Real.sqrt 2 * q * (q * L) := by ring
    have a4 : 18 * Real.sqrt 2 * q * (q * L) ≤ 18 * (3 / 2) * q * 5 := by
      have : 0 ≤ q * L := by positivity
      have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      calc 18 * Real.sqrt 2 * q * (q * L) ≤ 18 * (3 / 2) * q * (q * L) := by gcongr
        _ ≤ 18 * (3 / 2) * q * 5 := by gcongr
    nlinarith
  calc μ.real S * L + ∫ u, gf u ∂μ ≤ 18 * Real.sqrt (2 * s / r) * L + 36 * Real.sqrt (s / r) :=
        add_le_add (mul_le_mul_of_nonneg_right hSμ hL0) hgI
    _ = (18 * (Real.sqrt 2 * (q * q)) * L + 36 * (q * q)) / Real.sqrt r := by
        rw [e1, e2]; field_simp
    _ ≤ 200 * q / Real.sqrt r := div_le_div_of_nonneg_right key hr0.le
    _ = 200 / Real.sqrt r * s ^ (1 / 4 : ℝ) := by rw [hq]; ring

theorem measurable_abs_log_im : Measurable fun z : ℂ => |Real.log z.im| :=
  continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)

theorem measurable_stripFun (s : ℝ) :
    Measurable fun z : ℂ => {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) z :=
  (measurable_const.add measurable_abs_log_im).indicator
    (measurableSet_le Complex.measurable_im measurable_const)

/-- Strip bounds pass to images under maps increasing the imaginary part (own elementary
proof). -/
theorem stripBound_map {μ : Measure ℂ} {Φ : ℂ → ℂ} (hΦ : Measurable Φ)
    (hμ : ∀ᵐ z ∂μ, z ∈ H ∧ z.im ≤ (Φ z).im)
    (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ) [IsFiniteMeasure μ] {c γ : ℝ}
    (hS : StripBound μ c γ) : StripBound (μ.map Φ) c γ := by
  intro s hs hs1
  rw [integral_map hΦ.aemeasurable (measurable_stripFun s).aestronglyMeasurable]
  refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun z =>
    indicator_nonneg (fun z _ => add_nonneg zero_le_one (abs_nonneg _)) _) (((integrable_const 1).add hl).indicator
      (measurableSet_le Complex.measurable_im measurable_const)) ?_) (hS s hs hs1)
  filter_upwards [hμ] with z ⟨hz, hle⟩
  have hz0 : 0 < z.im := hz
  by_cases h : (Φ z).im ≤ s
  · have hz' : z.im ≤ s := hle.trans h
    rw [indicator_of_mem (show Φ z ∈ {z : ℂ | z.im ≤ s} from h),
      indicator_of_mem (show z ∈ {z : ℂ | z.im ≤ s} from hz')]
    have e1 : |Real.log (Φ z).im| = -Real.log (Φ z).im :=
      abs_of_nonpos (Real.log_nonpos (hz0.trans_le hle).le (h.trans hs1))
    have e2 : |Real.log z.im| = -Real.log z.im := abs_of_nonpos (Real.log_nonpos hz0.le (hz'.trans hs1))
    have e3 := Real.log_le_log hz0 hle
    show 1 + |Real.log (Φ z).im| ≤ 1 + |Real.log z.im|
    linarith
  · rw [indicator_of_notMem (show Φ z ∉ {z : ℂ | z.im ≤ s} from h)]
    exact indicator_nonneg (fun z _ => add_nonneg zero_le_one (abs_nonneg _)) _

/-- Integrability of `|log Im|` passes to images under maps increasing the imaginary part with
bounded image (own elementary proof). -/
theorem integrable_abs_log_im_map {μ : Measure ℂ} [IsFiniteMeasure μ] {Φ : ℂ → ℂ}
    (hΦ : Measurable Φ) {M : ℝ} (hμ : ∀ᵐ z ∂μ, z ∈ H ∧ z.im ≤ (Φ z).im ∧ (Φ z).im ≤ M)
    (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ) :
    Integrable (fun z : ℂ => |Real.log z.im|) (μ.map Φ) := by
  have hm : Measurable fun z : ℂ => |Real.log z.im| := measurable_abs_log_im
  rw [integrable_map_measure hm.aestronglyMeasurable hΦ.aemeasurable]
  refine (hl.add (integrable_const |Real.log M|)).mono' (hm.comp hΦ).aestronglyMeasurable
    (hμ.mono fun z ⟨hz, h1, h2⟩ => ?_)
  have hz0 : 0 < z.im := hz
  have hf0 : 0 < (Φ z).im := hz0.trans_le h1
  have l1 := Real.log_le_log hz0 h1
  have l2 := Real.log_le_log hf0 h2
  simp only [Function.comp, Real.norm_eq_abs, abs_abs, Pi.add_apply]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log M), neg_abs_le (Real.log z.im),
    le_abs_self (Real.log z.im), neg_abs_le (Real.log M)]

/-- A finite measure carried by a compact subset of `ℍ` has a strip bound (exponent `1`) and
integrable `|log Im|` (own elementary proof). -/
theorem stripBound_of_compact {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) (hϖ : ϖ Kᶜ = 0) :
    ∃ c : ℝ, StripBound ϖ c 1 ∧ Integrable (fun z : ℂ => |Real.log z.im|) ϖ := by
  obtain ⟨c₀, hc₀, hlo⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z ∈ K, c₀ ≤ z.im := by
    rcases K.eq_empty_or_nonempty with hKe | hne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    obtain ⟨z₁, hz₁K, hz₁⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    exact ⟨z₁.im, hKH hz₁K, fun z hz => hz₁ hz⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  set B₀ := |Real.log c₀| + |Real.log (max M c₀)| with hB₀
  have hae : ∀ᵐ z ∂ϖ, z ∈ K := ae_iff.2 hϖ
  have hbd : ∀ z ∈ K, |Real.log z.im| ≤ B₀ := by
    intro z hz
    have h1 := hlo z hz
    have h2 : z.im ≤ max M c₀ :=
      ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM z hz)).trans (le_max_left _ _)
    have l1 := Real.log_le_log hc₀ h1
    have l2 := Real.log_le_log (hc₀.trans_le h1) h2
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log (max M c₀)), neg_abs_le (Real.log c₀),
      abs_nonneg (Real.log c₀), abs_nonneg (Real.log (max M c₀))]
  have hm : Measurable fun z : ℂ => |Real.log z.im| := measurable_abs_log_im
  have hint : Integrable (fun z : ℂ => |Real.log z.im|) ϖ :=
    Integrable.of_bound hm.aestronglyMeasurable B₀ (hae.mono fun z hz => by
      rw [Real.norm_eq_abs, abs_abs]; exact hbd z hz)
  have hB0 : 0 ≤ B₀ := by positivity
  refine ⟨ϖ.real univ * ((1 + B₀) / c₀), fun s hs _ => ?_, hint⟩
  have hpt : ∀ᵐ z ∂ϖ, {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) z ≤
      (1 + B₀) / c₀ * s := by
    filter_upwards [hae] with z hz
    by_cases h : z.im ≤ s
    · rw [indicator_of_mem (show z ∈ {z : ℂ | z.im ≤ s} from h)]
      have hcs : c₀ ≤ s := (hlo z hz).trans h
      have : 1 + B₀ ≤ (1 + B₀) / c₀ * s := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
        exact mul_le_mul_of_nonneg_left hcs (by positivity)
      linarith [hbd z hz]
    · rw [indicator_of_notMem (show z ∉ {z : ℂ | z.im ≤ s} from h)]
      positivity
  calc ∫ z, {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) z ∂ϖ
      ≤ ∫ _z, (1 + B₀) / c₀ * s ∂ϖ :=
        integral_mono_of_nonneg (ae_of_all _ fun z => indicator_nonneg
          (fun z _ => by positivity) z) (integrable_const _) hpt
    _ = ϖ.real univ * ((1 + B₀) / c₀) * s ^ (1 : ℝ) := by
        rw [integral_const, smul_eq_mul, Real.rpow_one]; ring

end CoordRegComp
end QuantumZipper
