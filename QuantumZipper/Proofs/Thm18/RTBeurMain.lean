import QuantumZipper.Proofs.Thm18.RTBeurMass
import QuantumZipper.Proofs.Thm18.R18RTCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-BEURLING: the Beurling mass bound for pulled-back circles (`R18.PullMassBoundStmt`)

Source: the Beurling estimate (Lawler, *Schramm–Loewner evolution*, Park City notes,
arXiv:0712.3256, Thm 2.10, p. 18), used as in Johansson Viklund–Lawler arXiv:0911.3983 p. 12:
`Im f(z) ≤ C dist(z, curve)^{1/2}` on bounded sets, so the points of a circle whose pullback comes
near the curve lie in a thin strip around `ℝ`, which a circle charges little. The harmonic-measure
form of Beurling used is `LWFar.beurlingHarmStmt_holds` (proved).

Deterministic argument for a good driver (`pointwise_det`), with the circle at distance `δ₀`
(after folding) from the unzipped remaining curve `f_s(η[s,∞))`:

1. `z = f_s⁻¹(v)` is bounded (`exists_norm_fwdMapInv_sub_le`).
2. Choose `σ > 0` so small that the driver moves by `≤ δ₀/96` on `[s, s+σ]` and `8√σ ≤ δ₀/4`,
   and put `T = s + σ`. Transience gives `T₂` beyond which the curve is far; uniform continuity
   of `f_s` near the compact arc `η[T, T₂]` (Heine–Cantor) gives `ρ₁`.
3. If `z` is within `ρ ≤ ρ₀` of `η` (or its reflection), the nearby curve point is `η(t)` with
   `t ≤ T` (else `v` would be within `δ₀` of `f_s(η(t))` or `z` would be far), and `z ∉ K_T`.
4. Beurling at time `T` (`im_fwdMap_le_near`): `Im f_T(z) ≤ C' ρ^{1/2}`;
   small-time comparison (`im_fwdMap_ge_shift`, as `|v| ≥ δ₀`): `Im v ≤ e^{8σ/δ₀²} Im f_T(z)`.
5. `mass_of_pointwise` and `circleUnif_strip_le` turn `Im v ≤ A √ρ` into the geometric bound.

Steps 2–5 are our own assembly (the paper and the cited sources state the bound without these
details); logged as an own argument.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal ComplexConjugate NNReal

namespace QuantumZipper
namespace RTBeur

open Thm18Asm.LWFar

/-- **Pointwise strip bound** for a good driver. -/
theorem pointwise_det {W : ℝ → ℝ} (hRG : RS.RadialGood W) (hsc : IsSimpleChord (trace W))
    (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t) {s a : ℝ} (hs : 0 ≤ s)
    (ha : 0 < a) {d : ℂ} {r δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hmarg : ∀ v : ℂ, (dist v d = r ∨ dist v (conj d) = r) → ∀ w : ℂ, 0 ≤ w.im →
      dist w v < δ₀ → w ∉ R18.unzCurve W s a) :
    ∃ Rr A ρ₀ : ℝ, 0 ≤ A ∧ 0 < ρ₀ ∧
      (∀ v : ℂ, 0 ≤ v.im → (dist v d = r ∨ dist v (conj d) = r) → ‖fwdMapInv W s v‖ ≤ Rr) ∧
      (∀ v : ℂ, 0 ≤ v.im → (dist v d = r ∨ dist v (conj d) = r) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        min (infDist (fwdMapInv W s v) (curveOf W))
          (infDist (fwdMapInv W s v) (conj '' curveOf W)) ≤ ρ →
        v.im ≤ A * Real.sqrt ρ) := by
  have hWc := hRG.1
  have hW0 := hRG.2.1
  have hG : GoodChord W := ⟨hWc, hW0, hsc, hhull⟩
  obtain ⟨Cb, hCb0, hB⟩ := im_fwdMap_le_near
  obtain ⟨Cinv, hCinv⟩ := R18.exists_norm_fwdMapInv_sub_le hWc hW0 hs
  set R₀ : ℝ := ‖d‖ + |r| + |Cinv| with hR₀
  have hvnorm : ∀ v : ℂ, (dist v d = r ∨ dist v (conj d) = r) → ‖v‖ ≤ ‖d‖ + r := by
    intro v hv
    rcases hv with hv | hv
    · have := norm_le_norm_add_norm_sub' v d
      rw [← dist_eq_norm, hv] at this; exact this
    · have := norm_le_norm_add_norm_sub' v (conj d)
      rw [← dist_eq_norm, hv, Complex.norm_conj] at this; exact this
  have hzb : ∀ v : ℂ, 0 ≤ v.im → (dist v d = r ∨ dist v (conj d) = r) →
      ‖fwdMapInv W s v‖ ≤ R₀ := by
    intro v hv0 hvc
    have h1 := hvnorm v hvc
    rcases hv0.eq_or_lt with him | himpos
    · rw [fwdMapInv_of_im_nonpos hWc hs him.symm.le, norm_zero]
      linarith [norm_nonneg v, abs_nonneg Cinv, le_abs_self r]
    · have h2 := hCinv v himpos
      have h3 := norm_le_norm_add_norm_sub' (fwdMapInv W s v) v
      linarith [le_abs_self Cinv, le_abs_self r]
  have htH : ∀ t : ℝ, s < t → trace W t ∈ H \ fwdHull W s := by
    intro t hst
    refine ⟨hsc.2.2.2.1 t (by linarith), ?_⟩
    rw [hhull s hs]
    rintro ⟨r', hr', hrt⟩
    have := hsc.2.2.1 (mem_Ici.2 hr'.1.le) (mem_Ici.2 (by linarith)) hrt
    linarith [hr'.2]
  -- the short time `σ`
  obtain ⟨η₁, hη₁, hη₁W⟩ := Metric.continuous_iff.1 hWc s (δ₀ / 96) (by positivity)
  set σ : ℝ := min (η₁ / 2) ((δ₀ / 32) ^ 2) with hσdef
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hM : ∀ t ∈ Icc (0 : ℝ) σ, |W (s + t) - W s| ≤ δ₀ / 96 := by
    intro t ht
    have hd : dist (s + t) s < η₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg ht.1]
      linarith [ht.2, min_le_left (η₁ / 2) ((δ₀ / 32) ^ 2)]
    have := hη₁W (s + t) hd
    rw [Real.dist_eq] at this
    exact this.le
  have hsmall : 24 * (δ₀ / 96) + 8 * Real.sqrt σ ≤ δ₀ / 2 := by
    have : Real.sqrt σ ≤ δ₀ / 32 := by
      calc Real.sqrt σ ≤ Real.sqrt ((δ₀ / 32) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
        _ = δ₀ / 32 := Real.sqrt_sq (by positivity)
    linarith
  set T : ℝ := s + σ with hTdef
  have hT : 0 < T := by linarith
  -- transience
  obtain ⟨T2', hT2'⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hsc.2.2.2.2 (R₀ + 2))
  set T2 : ℝ := max T2' T with hT2def
  -- the Beurling scale
  set ρ' : ℝ := ‖trace W T‖ / 2 with hρ'def
  have hρ' : 0 < ρ' := by
    have := lt_of_lt_of_le (hsc.2.2.2.1 T hT) (Complex.im_le_norm _)
    positivity
  -- uniform continuity of `f_s` near `η[T, T₂]`
  have hKc : IsCompact (trace W '' Icc T T2) :=
    isCompact_Icc.image_of_continuousOn (hsc.2.1.mono fun x hx => le_trans hT.le hx.1)
  have hcont : ∀ p ∈ trace W '' Icc T T2, ContinuousAt (fwdMap W s) p := by
    rintro _ ⟨t, ht, rfl⟩
    exact RS.continuousAt_fwdMap_of_mem_complHull hWc hs (htH t (by linarith [ht.1]))
  have hU := hKc.uniformContinuousAt_of_continuousAt (fwdMap W s) hcont
    (Metric.dist_mem_uniformity hδ₀)
  obtain ⟨ρ₁, hρ₁, hρ₁U⟩ := Metric.mem_uniformity_dist.1 hU
  set ρ₀ : ℝ := min (ρ₁ / 3) (min (1 / 3) (ρ' / 3)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set c : ℝ := -2 * σ / (δ₀ / 2) ^ 2 with hc
  set A : ℝ := Real.exp (-c) * ((R₀ + ρ') * (Cb * Real.sqrt (3 / ρ'))) with hAdef
  refine ⟨R₀, A, ρ₀, by positivity, hρ₀, hzb, ?_⟩
  intro v hv0 hvc ρ hρ hρρ₀ hΦ
  rcases hv0.eq_or_lt with him | himpos
  · rw [← him]; positivity
  have hvH : v ∈ H := himpos
  set z := fwdMapInv W s v with hzdef
  have hzs : z ∈ H \ fwdHull W s := RS.fwdMapInv_mem_compl_fwdHull hWc hW0 hs hvH
  have hfz : fwdMap W s z = v := RS.fwdMap_fwdMapInv hWc hW0 hs hvH
  have hzR : ‖z‖ ≤ R₀ := hzb v hv0 hvc
  rw [hρ₀def] at hρρ₀
  have hρ3a : 3 * ρ ≤ ρ₁ := by linarith [min_le_left (ρ₁ / 3) (min (1 / 3) (ρ' / 3))]
  have hρ3b : 3 * ρ ≤ 1 := by
    linarith [min_le_right (ρ₁ / 3) (min (1 / 3) (ρ' / 3)), min_le_left (1 / 3 : ℝ) (ρ' / 3)]
  have hρ3c : 3 * ρ ≤ ρ' := by
    linarith [min_le_right (ρ₁ / 3) (min (1 / 3) (ρ' / 3)), min_le_right (1 / 3 : ℝ) (ρ' / 3)]
  have hη_im : ∀ t : ℝ, 0 ≤ t → 0 ≤ (trace W t).im := by
    intro t ht
    rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0, hsc.1]; simp
    · exact (hsc.2.2.2.1 t hpos).le
  -- a nearby curve point
  have hb : ∃ t : ℝ, 0 ≤ t ∧ dist z (trace W t) < 3 * ρ := by
    have hne : (range fun q : ℚ≥0 => trace W (q : ℝ)).Nonempty := ⟨_, 0, rfl⟩
    rcases min_le_iff.1 hΦ with h1 | h1
    · unfold curveOf at h1
      rw [infDist_closure] at h1
      obtain ⟨p, ⟨q, rfl⟩, hp⟩ := (infDist_lt_iff hne).1 (h1.trans_lt (by linarith : ρ < 3 * ρ))
      exact ⟨q, by positivity, hp⟩
    · have hne2 : (conj '' curveOf W).Nonempty := (hne.mono subset_closure).image _
      obtain ⟨p, ⟨p₁, hp₁, rfl⟩, hp⟩ :=
        (infDist_lt_iff hne2).1 (h1.trans_lt (by linarith : ρ < 2 * ρ))
      obtain ⟨y, ⟨q, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hp₁ ρ hρ
      refine ⟨q, by positivity, ?_⟩
      have e : dist (conj p₁) (conj (trace W (q : ℝ))) = dist p₁ (trace W (q : ℝ)) :=
        Complex.dist_conj_conj _ _
      calc dist z (trace W (q : ℝ)) ≤ dist z (conj (trace W (q : ℝ))) :=
            dist_le_dist_conj hzs.1.le (hη_im q (by positivity))
        _ ≤ dist z (conj p₁) + dist (conj p₁) (conj (trace W (q : ℝ))) := dist_triangle _ _ _
        _ < 3 * ρ := by rw [e]; linarith
  obtain ⟨t, ht0, htz⟩ := hb
  -- the nearby point is on `η[0, T]`
  have htT : t ≤ T := by
    by_contra htT
    push Not at htT
    by_cases ht2 : T2 ≤ t
    · have h1 := hT2' t (le_trans (le_max_left _ _) ht2)
      have h2 := norm_le_norm_add_norm_sub' (trace W t) z
      rw [← dist_eq_norm, dist_comm] at h2
      linarith
    · push Not at ht2
      have hmemK : trace W t ∈ trace W '' Icc T T2 := ⟨t, ⟨htT.le, ht2.le⟩, rfl⟩
      have h1 := hρ₁U (a := trace W t) (b := z) (by rw [dist_comm]; linarith) hmemK
      simp only [mem_setOf_eq] at h1
      rw [hfz] at h1
      have hwim : 0 ≤ (fwdMap W s (trace W t)).im :=
        (RS.im_fwdMap_le_of_le hWc hs le_rfl (htH t (by linarith))).2.le
      exact hmarg v hvc _ hwim h1 (fwdMap_trace_mem_unzCurve hRG hsc hhull hs ha (by linarith))
  -- `z` is not swallowed by time `T`
  have hzT : z ∈ H \ fwdHull W T := by
    refine ⟨hzs.1, fun hzK => ?_⟩
    rw [hhull T hT.le] at hzK
    obtain ⟨t', ht', hzt'⟩ := hzK
    by_cases hts : t' ≤ s
    · exact hzs.2 (by rw [hhull s hs]; exact ⟨t', ⟨ht'.1, hts⟩, hzt'⟩)
    · push Not at hts
      have hmem := fwdMap_trace_mem_unzCurve hRG hsc hhull hs ha hts
      rw [hzt', hfz] at hmem
      exact hmarg v hvc v hv0 (by rw [dist_self]; exact hδ₀) hmem
  -- Beurling at time `T`
  have hfar : ∃ r' ∈ Icc (0 : ℝ) T, ρ' ≤ dist z (trace W r') := by
    by_cases h0 : ρ' ≤ dist z (trace W 0)
    · exact ⟨0, ⟨le_rfl, hT.le⟩, h0⟩
    · refine ⟨T, ⟨hT.le, le_rfl⟩, ?_⟩
      push Not at h0
      rw [hsc.1, dist_zero_right] at h0
      have h2 := norm_le_norm_add_norm_sub' (trace W T) z
      rw [← dist_eq_norm, dist_comm] at h2
      linarith
  have hbeur := hB W hG T ρ' (3 * ρ) hT.le (by positivity) hρ3c z hzT
    ⟨t, ⟨ht0, htT⟩, htz.le⟩ hfar
  have hrp : (3 * ρ / ρ') ^ (1 / 2 : ℝ) = Real.sqrt (3 / ρ') * Real.sqrt ρ := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    congr 1; ring
  rw [hrp] at hbeur
  have hb2 : (fwdMap W T z).im ≤ (R₀ + ρ') * (Cb * (Real.sqrt (3 / ρ') * Real.sqrt ρ)) :=
    hbeur.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  -- comparison with time `s`
  have hvfar : δ₀ ≤ ‖fwdMap W s z‖ := by
    rw [hfz]
    by_contra hlt
    push Not at hlt
    exact hmarg v hvc 0 le_rfl (by rw [dist_comm, dist_zero_right]; exact hlt)
      (zero_mem_unzCurve hWc s a)
  have hcmp := im_fwdMap_ge_shift hWc hs hσ hδ₀ hM hsmall hzT hvfar
  rw [hfz] at hcmp
  have hexp : v.im = v.im * Real.exp c * Real.exp (-c) := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [hexp]
  calc v.im * Real.exp c * Real.exp (-c)
      ≤ (R₀ + ρ') * (Cb * (Real.sqrt (3 / ρ') * Real.sqrt ρ)) * Real.exp (-c) :=
        mul_le_mul_of_nonneg_right (hcmp.trans hb2) (Real.exp_pos _).le
    _ = A * Real.sqrt ρ := by rw [hAdef]; ring

/-- **RT-BEURLING: the Beurling mass bound for pulled-back circles.** -/
theorem pullMassBoundStmt_holds : R18.PullMassBoundStmt := by
  intro γ Ω _ P _ B Y hS hIn
  have hκ : 0 < γ ^ 2 := by have := hS.1; positivity
  have hκ4 : γ ^ 2 < 4 := by have := hS.1; have := hS.2.1; nlinarith
  filter_upwards [RS.ae_radialGood_drive hS.2.2.1 hκ (by linarith), hIn.2.2] with ω hRG hω
  intro s hs a ha d k₀ hoff
  have hsc : IsSimpleChord (trace (drive (γ ^ 2) B ω)) := hω.1
  have hhull : ∀ t : ℝ, 0 ≤ t →
      fwdHull (drive (γ ^ 2) B ω) t = trace (drive (γ ^ 2) B ω) '' Ioc 0 t := hω.2.1
  obtain ⟨δ₀, hδ₀, hmarg⟩ := margin_of_circleOff hoff
  obtain ⟨Rr, A, ρ₀, hA, hρ₀, hsupp, hkey⟩ := pointwise_det hRG hsc hhull hs ha hδ₀ hmarg
  have hr : 0 < radius k₀ := by unfold radius; positivity
  obtain ⟨Cm, q, hCm, hq0, hq1, h1, h2⟩ := mass_of_pointwise
    (measurable_fwdMapInv_rt hRG.1 hRG.2.1 hs)
    (Φ := fun w => min (infDist w (curveOf (drive (γ ^ 2) B ω)))
      (infDist w (conj '' curveOf (drive (γ ^ 2) B ω))))
    ((continuous_infDist_pt _).min (continuous_infDist_pt _)) hr hA hρ₀ hsupp hkey
  exact ⟨Rr, Cm, q, hCm, hq0, hq1, h1, h2⟩

end RTBeur
end QuantumZipper
