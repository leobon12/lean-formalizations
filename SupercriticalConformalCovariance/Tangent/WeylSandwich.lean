import SupercriticalConformalCovariance.Tangent.DiskFunctional
import SupercriticalConformalCovariance.Lemma31.Realized

/-!
# Lemma 3.3, step 2: the Weyl correction and the smooth-average restoration

Paper l. 214–217: "The restoration of the smooth average multiplies metric lengths by a random
factor tending to one in probability. Moreover, `Q log |(ψ_n⁻¹)′| + Q log |a| → 0` uniformly on
compact sets, so the remaining Weyl correction has vanishing multiplicative effect."

`ae_sandwich_confined` is the samplewise statement for one `n`: the target metric on the closed
disk `K = B̄_S` of a realized field `h̄ + f` is sandwiched, with factors `e^{ξ(c + ℓ ∓ ε)}`, around
the closed-disk metric of the whole-plane field `G = h̄ + χ(f − L) − c`, whenever `|L − ℓ| ≤ ε` on
`K` (here `L = Q log |(ψ⁻¹)′|`, `ℓ = −Q log |a|`, `c` the smooth average).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC addFun ofCont IsGFFPlusCont)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf)
open SupercriticalConformalCovariance (weylScaleOn)
open SupercriticalConformalCovariance.Domain (confined resC cutF exW exW_subset cutF_eq ae_weylScaleOn_eq_internal
  isGFFPlusCont_addFun_of_measurable measurable_cutExt weylScaleOn_add_le le_weylScaleOn_add
  addFun_zero)

theorem measurable_cutF_sub {V : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {fr : Ω → C(V, ℝ)}
    (hfr : Measurable fr) (m : ℕ) (L : C(V, ℝ)) {c : Ω → ℝ} (hc : Measurable c) :
    Measurable fun ω => cutF V m (fr ω) - cutF V m L - ContinuousMap.const ℂ (c ω) := by
  have h1 : Measurable fun ω => cutF V m (fr ω) := measurable_cutExt V.isOpen _ hfr
  rw [ContinuousMap.measurable_iff_eval] at h1 ⊢
  intro x
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
  exact ((h1 x).sub measurable_const).sub hc

/-- **The samplewise Weyl sandwich** (one `n`). -/
theorem ae_sandwich_confined {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) {V : Opens ℂ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {hbar : Ω → DistC} (hhb : IsGFFPlusCont hbar P)
    {fr : Ω → C(V, ℝ)} (hfr : Measurable fr) (m : ℕ) {S : ℝ}
    (hSm : closedBall (0 : ℂ) S ⊆ exW V m) (L : C(V, ℝ)) {c : Ω → ℝ} (hc : Measurable c)
    (ℓ ε : ℝ) (hLε : ∀ z (hz : z ∈ closedBall (0 : ℂ) S),
      |L ⟨z, exW_subset V m (hSm hz)⟩ - ℓ| ≤ ε) :
    ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * (c ω + ℓ - ε))) *
          closedBallPathInf (D (addFun (hbar ω)
            (cutF V m (fr ω) - cutF V m L - ContinuousMap.const ℂ (c ω)))) 0 S q.1 q.2 ≤
        confined (ξ : ℝ) (D (hbar ω)) (hSm.trans (exW_subset V m)) (fr ω) q ∧
      confined (ξ : ℝ) (D (hbar ω)) (hSm.trans (exW_subset V m)) (fr ω) q ≤
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * (c ω + ℓ + ε))) *
          closedBallPathInf (D (addFun (hbar ω)
            (cutF V m (fr ω) - cutF V m L - ContinuousMap.const ℂ (c ω)))) 0 S q.1 q.2 := by
  set K : Set ℂ := closedBall (0 : ℂ) S with hK
  have hKV : K ⊆ V := hSm.trans (exW_subset V m)
  set Gf : Ω → DistC := fun ω =>
    addFun (hbar ω) (cutF V m (fr ω) - cutF V m L - ContinuousMap.const ℂ (c ω)) with hGf
  set G' : Ω → DistC := fun ω => addFun (hbar ω) (cutF V m (fr ω)) with hG'
  have hGfc : IsGFFPlusCont Gf P :=
    isGFFPlusCont_addFun_of_measurable hhb (measurable_cutF_sub hfr m L hc)
  have hG'c : IsGFFPlusCont G' P :=
    isGFFPlusCont_addFun_of_measurable hhb (measurable_cutExt V.isOpen _ hfr)
  have hξ : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  filter_upwards [ae_weylScaleOn_eq_internal hD P hhb, ae_weylScaleOn_eq_internal hD P hGfc]
    with ω hx hxG q
  have hpos : ∀ t : ℝ, ENNReal.ofReal (Real.exp t) ≠ 0 := fun t =>
    (ENNReal.ofReal_pos.2 (Real.exp_pos t)).ne'
  by_cases hq : q.1 ∈ K ∧ q.2 ∈ K
  · set p : K × K := (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩) with hp
    -- the correction on `K`, as a continuous function on `K`
    set gK : C(K, ℝ) := ⟨fun z => L ⟨z, hKV z.2⟩ + c ω,
      (L.continuous.comp ((continuous_inclusion hKV))).add continuous_const⟩ with hgK
    have hcorr : ∀ z (hz : z ∈ K),
        (cutF V m L + ContinuousMap.const ℂ (c ω)) z = gK ⟨z, hz⟩ := by
      intro z hz
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, hgK, ContinuousMap.coe_mk]
      rw [cutF_eq V m L z (hSm hz)]
    -- the target metric through `Gf`
    have hT : confined (ξ : ℝ) (D (hbar ω)) hKV (fr ω) q = weylScaleOn (ξ : ℝ) gK (D (Gf ω)) p := by
      unfold confined
      rw [dif_pos hq]
      have h1 := hx K (resC hKV (fr ω)) (cutF V m (fr ω))
        (fun z hz => cutF_eq V m (fr ω) z (hSm hz)) p
      have h2 := hxG K gK (cutF V m L + ContinuousMap.const ℂ (c ω)) hcorr p
      have hfield : addFun (Gf ω) (cutF V m L + ContinuousMap.const ℂ (c ω)) =
          addFun (hbar ω) (cutF V m (fr ω)) := by
        rw [hGf]
        dsimp only
        rw [SupercriticalConformalCovariance.Lemma31.addFun_addFun]
        congr 1
        ext z
        simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply]
        ring
      rw [h1, h2, hfield]
    -- the closed-disk metric of `Gf`
    have hC : closedBallPathInf (D (Gf ω)) 0 S q.1 q.2 = weylScaleOn (ξ : ℝ) 0 (D (Gf ω)) p := by
      rw [closedBallPathInf_eq_extInternal]
      unfold extInternal
      rw [dif_pos hq]
      have h3 := hxG K 0 0 (fun z hz => rfl) p
      rw [h3, addFun_zero]
    have hlow : ∀ z : K, c ω + ℓ - ε ≤ gK z := by
      intro z
      have := hLε z z.2
      simp only [hgK, ContinuousMap.coe_mk]
      have := (abs_le.1 this).1
      linarith
    have hupp : ∀ z : K, gK z ≤ c ω + ℓ + ε := by
      intro z
      have := hLε z z.2
      simp only [hgK, ContinuousMap.coe_mk]
      have := (abs_le.1 this).2
      linarith
    rw [hT, hC]
    have hA := le_weylScaleOn_add (D₀ := D (Gf ω)) hξ 0 gK hlow p
    have hB := weylScaleOn_add_le (D₀ := D (Gf ω)) hξ 0 gK hupp p
    rw [zero_add] at hA hB
    exact ⟨hA, hB⟩
  · have hT : confined (ξ : ℝ) (D (hbar ω)) hKV (fr ω) q = ⊤ := by
      unfold confined; rw [dif_neg hq]
    have hC : closedBallPathInf (D (Gf ω)) 0 S q.1 q.2 = ⊤ := by
      rw [closedBallPathInf_eq_extInternal]; unfold extInternal; rw [dif_neg hq]
    rw [hT, hC]
    exact ⟨le_top, by rw [ENNReal.mul_top (hpos _)]⟩

end SupercriticalConformalCovariance.Tangent
