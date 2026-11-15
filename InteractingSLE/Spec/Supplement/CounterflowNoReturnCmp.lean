/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowNoReturnFirst

/-!
# No return of a counterflow: the zero-side comparison at a seed collision

Packet PROVE-CFNORETURN. At a first return `u` through the right seed (`first_return`: `V_k(u) = W(u)` with `x_k = 0`,
`(0, ∞)` unvisited before `u`), the comparison picture of PROVE-CFBARRIER3 (`Sec5.CfJunction.GenCmpPath` with the
zero-side reference weights `Sec5.CfLocalCmp.zeroSideWeight`) holds at some rational restart time:

* `genCmpPath_of_first_collision` (one path): the tail of `Sec5.CfLocalCmp.genCmpPath_of_zeroSide_visit` (its steps
  (4)–(5)), stated from a first collision of the mark `k` at `T₁ > 0` with every left mark and every right mark beyond
  `x_k` off the driver at `T₁`;
* `exists_genCmpPath_of_return_right` (one path): at a first return through the right seed these hypotheses hold —
  an earlier collision of the seed would put the tip at a real point `≥ 0` (`Sec5.CfLocalCmp.tip_ge_of_collision_right`),
  i.e. at an unvisited positive point or at `0` before `u`; a mark beyond `0` colliding at `u` would put the tip at a
  positive real point, not at `0`; the left marks are left of the right seed (`IsIntegratedSLEPath.vL_lt_vR_of_pos`).

When the seed group's weight is at least `κ/2 − 2` the comparison picture is null for every restart time
(`ae_forall_not_genCmpPath_right`, from `Sec5.CfJunction.measure_genCmp_eq_zero` and
`Sec5.CfLocalCmp.ae_zeroSide_drift_ge`): the gap `V_k − W` is a Bessel-type process of dimension `≥ 2` under the
reference weights.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace CfNoReturn

open Sec5.CfJunction Sec5.CfLocalCmp

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- **The zero-side comparison picture at a first collision of a mark** (one path): if the right mark `k` collides
with the driver at `T₁ > 0` and not on `(0, T₁)`, the marks strictly before `x_k` have weight `0`, and every left
mark and every right mark beyond `x_k` is off the driver at `T₁`, then `GenCmpPath` holds for the zero-side reference
weights at some rational restart time. -/
theorem genCmpPath_of_first_collision (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ)
    {k : Fin nR} (hzero : ∀ j, xR j < xR k → ρR j = 0) {T₁ : ℝ≥0} (hT₁0 : 0 < T₁)
    (hT₁ζ : (T₁ : ℝ≥0∞) < ζ) (hkT₁ : vR k T₁ = w T₁) (hkne : ∀ t : ℝ≥0, 0 < t → t < T₁ → vR k t ≠ w t)
    (hR : ∀ j, xR k < xR j → 0 < vR j T₁ - w T₁) (hL : ∀ i, 0 < w T₁ - vL i T₁) :
    ∃ q : ℚ, GenCmpPath ρL ρR (zeroSideWeight xR ρR k) w vL vR ζ k (q : ℝ).toNNReal := by
  classical
  have h := hp.isForcePath
  have hwc := h.continuousOn_w
  -- (4) by continuity, the gaps stay above half their values near `T₁`
  have hopen : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} ∈ 𝓝 T₁ :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hT₁ζ
  have hcw : ContinuousAt w T₁ := hwc.continuousAt hopen
  have hev : ∀ᶠ t in 𝓝 T₁, (∀ i, (w T₁ - vL i T₁) / 2 < w t - vL i t) ∧
      ∀ j, xR k < xR j → (vR j T₁ - w T₁) / 2 < vR j t - w t := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun j => ?_)
    · have hc : ContinuousAt (fun t => w t - vL i t) T₁ := hcw.sub ((h.continuousOn_vL i).continuousAt hopen)
      exact hc.eventually (lt_mem_nhds (by linarith [hL i]))
    · by_cases hj : xR k < xR j
      · have hc : ContinuousAt (fun t => vR j t - w t) T₁ := ((h.continuousOn_vR j).continuousAt hopen).sub hcw
        exact (hc.eventually (lt_mem_nhds (by linarith [hR j hj]))).mono fun t ht _ => ht
      · exact Eventually.of_forall fun t ht => absurd ht hj
  obtain ⟨ε, hε, hεev⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((T₁ : ℝ) - ε) 0 < T₁ from
    max_lt (by linarith) (NNReal.coe_pos.2 hT₁0))
  have hq0 : (0 : ℝ) < q := (le_max_right _ _).trans_lt hq1
  have hqT : (T₁ : ℝ) - ε < q := (le_max_left _ _).trans_lt hq1
  set qN : ℝ≥0 := (q : ℝ).toNNReal with hqN
  have hqN' : (qN : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hnear : ∀ t : ℝ≥0, qN ≤ t → t < T₁ → (∀ i, (w T₁ - vL i T₁) / 2 < w t - vL i t) ∧
      ∀ j, xR k < xR j → (vR j T₁ - w T₁) / 2 < vR j t - w t := fun t hqt htT => by
    refine hεev ?_
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 htT.le))]
    have : (q : ℝ) ≤ t := hqN' ▸ NNReal.coe_le_coe.2 hqt
    linarith
  -- (5) the comparison picture on `[q, T₁)`
  set M : ℝ := (∑ i, |ρL i| * (2 / (w T₁ - vL i T₁))) +
    ∑ j, if xR k < xR j then |ρR j| * (2 / (vR j T₁ - w T₁)) else 0 with hMdef
  have hbound : ∀ s : ℝ, (q : ℝ) ≤ s → s < T₁ →
      |(∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)| ≤ M := by
    intro s hqs hsT
    have hs0 : 0 ≤ s := hq0.le.trans hqs
    have hsN : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs0
    have hnear' := hnear s.toNNReal (by rw [← NNReal.coe_le_coe, hsN, hqN']; exact hqs)
      (by rw [← NNReal.coe_lt_coe, hsN]; exact hsT)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have hpos : 0 < w T₁ - vL i T₁ := hL i
      have hgap := hnear'.1 i
      have hgpos : 0 < w s.toNNReal - vL i s.toNNReal := by linarith
      rw [abs_div, abs_neg, abs_of_pos hgpos, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [inv_le_comm₀ hgpos (by positivity), inv_div]
      linarith
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      unfold zeroSideWeight
      by_cases hj : xR k < xR j
      · simp only [not_le.2 hj, hj, ↓reduceIte, zero_sub, abs_div, abs_neg]
        have hpos : 0 < vR j T₁ - w T₁ := hR j hj
        have hgap := hnear'.2 j hj
        have hgpos : 0 < vR j s.toNNReal - w s.toNNReal := by linarith
        rw [show w s.toNNReal - vR j s.toNNReal = -(vR j s.toNNReal - w s.toNNReal) by ring, abs_neg,
          abs_of_pos hgpos, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [inv_le_comm₀ hgpos (by positivity), inv_div]
        linarith
      · simp only [not_lt.1 hj, hj, ↓reduceIte, sub_self, zero_div, abs_zero, le_refl]
  refine ⟨q, T₁, ?_, hT₁ζ.le, fun t hqt htT => ⟨fun i _ => ?_, fun j hj => ?_⟩, ⟨M ^ 2 * T₁, fun t hqt htT => ?_⟩, ?_⟩
  · rw [← NNReal.coe_lt_coe, hqN']
    exact hq2
  · have := (hnear t hqt htT).1 i
    have hpos := hL i
    exact fun he => by linarith
  · have ht0 : 0 < t := lt_of_lt_of_le (by rw [← NNReal.coe_pos, hqN']; exact hq0) hqt
    have htζ : (t : ℝ≥0∞) < ζ := (ENNReal.coe_lt_coe.2 htT).trans hT₁ζ
    rcases lt_trichotomy (xR j) (xR k) with hlt | heq | hgt
    · exfalso
      rcases hj with hj | hj | hj
      · exact hj (hzero j hlt)
      · exact hj (by simp only [zeroSideWeight, hlt.le, ↓reduceIte, hzero j hlt])
      · exact (ne_of_lt hlt) (by rw [hj])
    · have hjk : vR j t = vR k t :=
        Sec2.Assembly.vR_eq_of_eq h htζ (by rw [h.vR_zero j, h.vR_zero k, heq]) ⟨zero_le, le_rfl⟩
      rw [hjk]
      exact fun he => hkne t ht0 htT he.symm
    · have := (hnear t hqt htT).2 j hgt
      have hpos := hR j hgt
      exact fun he => by linarith
  · have hqt' : (q : ℝ) ≤ t := hqN' ▸ NNReal.coe_le_coe.2 hqt
    have hle : ∀ s ∈ Set.uIoc (qN : ℝ) t, ‖((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
        ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2‖ ≤ M ^ 2 := by
      intro s hs
      rw [Set.uIoc_of_le (hqN'.symm ▸ hqt'), hqN'] at hs
      have hb := hbound s hs.1.le (hs.2.trans_lt (NNReal.coe_lt_coe.2 htT))
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rw [hqN', abs_of_nonneg (sub_nonneg.2 hqt')] at hint
    have h1 : (t : ℝ) - q ≤ T₁ := by linarith [NNReal.coe_lt_coe.2 htT]
    rw [hqN']
    calc (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
          ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2)
        ≤ ‖∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (w s.toNNReal - vL i s.toNNReal)) +
          ∑ j, (zeroSideWeight xR ρR k j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2‖ := Real.le_norm_self _
      _ ≤ M ^ 2 * ((t : ℝ) - q) := hint
      _ ≤ M ^ 2 * T₁ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · have hc : ContinuousAt (fun t => vR k t - w t) T₁ := ((h.continuousOn_vR k).continuousAt hopen).sub hcw
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio T₁))
    simpa [hkT₁] using this


/-- **At a first return through the right seed the comparison picture holds** at some rational restart time. -/
theorem exists_genCmpPath_of_return_right (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ⊤)
    (hord : IsOrderedForceWord xL xR) (hγ : IsGeneratingTrace w ⊤ γ) {k : Fin nR} (hk : xR k = 0)
    {u : ℝ≥0} (hu0 : 0 < u) (hu : γ u = 0) (hfirst : ∀ s : ℝ≥0, 0 < s → s < u → γ s ≠ 0)
    (hvR : vR k u = w u) (hoff : ∀ s : ℝ≥0, s < u → ∀ x : ℝ, 0 < x → γ s ≠ x) :
    ∃ q : ℚ, GenCmpPath ρL ρR (zeroSideWeight xR ρR k) w vL vR ⊤ k (q : ℝ).toNNReal := by
  have h := hp.isForcePath
  have hzero : ∀ j, xR j < xR k → ρR j = 0 := fun j hj =>
    absurd hj (by rw [hk]; exact not_lt.2 (hord.2.2.2 j))
  refine genCmpPath_of_first_collision hp hzero hu0 ENNReal.coe_lt_top hvR ?_ ?_ ?_
  · intro t ht0 htu hcol
    obtain ⟨x, hx, hxk⟩ := tip_ge_of_collision_right h hγ ENNReal.coe_lt_top hcol
    rw [hk] at hxk
    rcases hxk.lt_or_eq with hpos | hzero'
    · exact hoff t htu x hpos hx
    · exact hfirst t ht0 htu (by rw [hx, ← hzero', Complex.ofReal_zero])
  · intro j hj
    refine sub_pos.2 (lt_of_le_of_ne (h.w_le_vR ENNReal.coe_lt_top j) fun hcol => ?_)
    obtain ⟨x, hx, hxj⟩ := tip_ge_of_collision_right h hγ ENNReal.coe_lt_top hcol.symm
    rw [hu] at hx
    have hx0 : x = 0 := by exact_mod_cast hx.symm
    rw [hk] at hj
    linarith
  · intro i
    have := hp.vL_lt_vR_of_pos hord hu0 ENNReal.coe_lt_top i k
    linarith

end Path

section Null

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The comparison picture at a barrier seed is null** for every rational restart time. -/
theorem ae_forall_not_genCmpPath_right (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k : Fin nR} (hk : xR k = 0)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, ¬ GenCmpPath ρL ρR (zeroSideWeight xR ρR k) (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω) k (q : ℝ).toNNReal := by
  have hzero : ∀ j, xR j < xR k → ρR j = 0 := fun j hj =>
    absurd hj (by rw [hk]; exact not_lt.2 (hord.2.2.2 j))
  have hnull : P (⋃ q : ℚ, {ω | GenCmpPath ρL ρR (zeroSideWeight xR ρR k) (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω) k (q : ℝ).toNNReal}) = 0 :=
    measure_iUnion_null fun q => measure_genCmp_eq_zero hκ hE (ae_zeroSide_drift_ge hE hzero hS) _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω q hq
  exact hω (mem_iUnion.2 ⟨q, hq⟩)

end Null

end CfNoReturn

end InteractingSLE
