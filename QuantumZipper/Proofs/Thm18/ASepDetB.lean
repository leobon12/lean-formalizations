import QuantumZipper.Proofs.Thm18.ASepDetA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-DET (b): uniform convergence and continuity of the deterministic part at `τ' = 0`

For the A-sep family at `τ' = 0` (centre measure `ν_p = σ.map (w ↦ f_{p 0}((p 1) w))`,
`σ = foldedCircle d r`):

* `det_unif_A0`: `detGen W (p 0) a' g₁ Q ν_p j → detLimA0 W a' g₁ Q d r p` uniformly on a
  parameter set inside the box `[0,T] × [a₀,a₁]` (input `hdet` of `ASep.GenInputsDep`);
* `continuousOn_detLimA0`: continuity of the limit (input `hdetc`).

Route: `G4Core.det_unif_gen` with the fixed source `σ` and the maps of `geo_piecewise` /
`geo_fwdMap_scaled`; continuity by dominated convergence with the modulus (C2)
`norm_fwdMap_sub_le`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif UnzipInvariance F1

/-- The solvability hypothesis of `genFam_muA0`, restricted to the folded sphere. -/
theorem hgood0_of_hgood {W : ℝ → ℝ} {T : ℝ} {d : ℂ} {r a₀ a₁ δ : ℝ}
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u) :
    ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u := by
  intro a ha w hw
  refine hgood a ha w ⟨Metric.self_subset_cthickening _ hw, ?_⟩
  obtain ⟨y, -, rfl⟩ := hw
  show 0 ≤ (foldH y).im
  rw [TwoPoint.im_foldH]; exact abs_nonneg _

/-- **Geometry of the A-sep maps on the box.** -/
theorem exists_geo_A0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {d : ℂ} {r a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u) :
    ∃ (m c Rb : ℝ) (g : (Fin 2 → ℝ) → ℂ → ℂ), 0 < m ∧ 0 < c ∧
      (∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖) ∧
      ∀ p : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T → p 1 ∈ Icc a₀ a₁ →
        Measurable (g p) ∧
        (∀ w ∈ H, ‖w‖ ≤ ‖d‖ + r → g p w ∈ H ∧ c * w.im ≤ (g p w).im ∧ ‖g p w‖ ≤ Rb) ∧
        ∀ w ∈ foldSph d r, g p w = fwdMap W (p 0) ((p 1 : ℂ) * w) := by
  classical
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  obtain ⟨m, hm, hlow⟩ := exists_fwdMap_lower hW hW0 hT (isCompact_scaledSph d r a₀ a₁) hsol
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set Ra : ℝ := ‖d‖ + r with hRa
  set c : ℝ := min 1 (a₀ * Real.exp (-2 * T / m ^ 2)) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  set Rb : ℝ := max Ra (a₁ * Ra + M + 2 * T / m) with hRb
  refine ⟨m, c, Rb, fun p => (foldSph d r).piecewise (gA W d r (p 0) (p 1)) id, hm, hc0, hlow,
    fun p hτ ha => ?_⟩
  have hgm := measurable_gA hW hW0 hm hgood0 hlow hτ ha
  have hgeo : ∀ w ∈ foldSph d r, w ∈ H → ‖w‖ ≤ Ra →
      gA W d r (p 0) (p 1) w ∈ H ∧ c * w.im ≤ (gA W d r (p 0) (p 1) w).im ∧
        ‖gA W d r (p 0) (p 1) w‖ ≤ Rb := by
    intro w hwN hw hwR
    rw [gA_of_mem hwN]
    obtain ⟨h1, h2, h3⟩ := geo_fwdMap_scaled hW hm ha₀ ha.1 hτ hw (hgood0 _ ha w hwN)
      (fun s hs => hlow _ (mem_scaledSph ha hwN) s hs)
    have hwim : (0 : ℝ) ≤ w.im := le_of_lt hw
    refine ⟨h1, le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hwim) h2, ?_⟩
    refine h3.trans (le_trans ?_ (le_max_right _ _))
    have hWt := hM _ hτ
    have ha0 : 0 ≤ p 1 := ha₀.le.trans ha.1
    have : p 1 * ‖w‖ ≤ a₁ * Ra :=
      mul_le_mul ha.2 hwR (norm_nonneg _) (ha0.trans ha.2)
    linarith
  obtain ⟨hm1, hm2, -⟩ := geo_piecewise (isCompact_foldSph d r).isClosed.measurableSet hgm
    (min_le_left _ _) (le_max_left _ _) hgeo
  refine ⟨hm1, hm2, fun w hw => ?_⟩
  simp only [piecewise_eq_of_mem _ _ _ hw, gA_of_mem hw]

/-- **Uniform convergence of the deterministic part (input `hdet`).** -/
theorem det_unif_A0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {d : ℂ} {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁) {δ : ℝ}
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ p ∈ S,
      |Thm18Asm.G4Core.detGen W (p 0) a' g₁ Q
          ((foldedCircle d r).map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) j -
        detLimA0 W a' g₁ Q d r p| < ε := by
  obtain ⟨m, c, Rb, g, hm, hc, -, hg⟩ := exists_geo_A0 hW hW0 hT ha₀ (hgood0_of_hgood hgood)
  obtain ⟨A, hA0, hA⟩ := Gdet_logBound hW hW0 T (Rb + 1) hT a' hg₁ Q
  set B : ℝ := |a'| + |Q| with hB
  have hB0 : 0 ≤ B := by positivity
  have hmap : ∀ p ∈ S, (foldedCircle d r).map (g p) =
      (foldedCircle d r).map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w) := fun p hp =>
    Measure.map_congr ((ae_mem_foldSph d hr.le).mono fun w hw =>
      ((hg p (hSb p hp).1 (hSb p hp).2).2.2 w hw))
  have key := Thm18Asm.G4Core.det_unif_gen (continuousOn_Gdet_joint hW hW0 T a' hg₁ Q)
    hA0 hB0 hA (fun t ht j => (continuous_integral_Gdet hW hW0 ht.1 a' hg₁ Q
      (radius_pos j)).measurable) S (fun p => p 0) (fun p hp => (hSb p hp).1)
    (fun _ => foldedCircle d r) g (fun p hp => (hg p (hSb p hp).1 (hSb p hp).2).1)
    (Ra := ‖d‖ + r) hc
    (fun p _ => by
      filter_upwards [foldedCircle_ae_mem_H d hr, foldedCircle_ae_norm_le d hr.le] with w h1 h2
      exact ⟨h1, h2⟩)
    (fun p hp => (hg p (hSb p hp).1 (hSb p hp).2).2.1)
    (fun p _ => (integrable_log_im_foldedCircle d hr).abs) (K₁ := 200 / Real.sqrt r) (β := 1 / 4) (by norm_num)
    (fun p _ => CoordRegComp.stripBound_foldedCircle d hr)
  intro ε hε
  obtain ⟨J, hJ⟩ := key ε hε
  refine ⟨J, fun j hj p hp => ?_⟩
  have h := hJ j hj p hp
  simp only [hmap p hp] at h
  rw [detGen_eq_Gdet hW hW0 (hSb p hp).1.1 a' hg₁ Q]
  exact h

/-- **Continuity of the limit of the deterministic part (input `hdetc`).** -/
theorem continuousOn_detLimA0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {d : ℂ} {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    {S : Set (Fin 2 → ℝ)} (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁) {δ : ℝ}
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ContinuousOn (detLimA0 W a' g₁ Q d r) S := by
  have hgood0 := hgood0_of_hgood hgood
  have hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  obtain ⟨m, c, Rb, g, hm, hc, hlow, hg⟩ := exists_geo_A0 hW hW0 hT ha₀ hgood0
  obtain ⟨A, hA0, hA⟩ := Gdet_logBound hW hW0 T (Rb + 1) hT a' hg₁ Q
  set B : ℝ := |a'| + |Q| with hB
  have hB0 : 0 ≤ B := by positivity
  have hGc := continuousOn_Gdet_joint hW hW0 T a' hg₁ Q
  set σ := foldedCircle d r with hσ
  set F : (Fin 2 → ℝ) → ℂ → ℝ :=
    fun p w => Gdet W a' g₁ Q (p 0) (fwdMap W (p 0) ((p 1 : ℂ) * w)) with hF
  have hsrc : ∀ᵐ w ∂σ, w ∈ foldSph d r ∧ w ∈ H ∧ ‖w‖ ≤ ‖d‖ + r := by
    filter_upwards [ae_mem_foldSph d hr.le, foldedCircle_ae_mem_H d hr,
      foldedCircle_ae_norm_le d hr.le] with w h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hmap : ∀ p ∈ S, σ.map (g p) = σ.map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w) :=
    fun p hp => Measure.map_congr (hsrc.mono fun w hw =>
      ((hg p (hSb p hp).1 (hSb p hp).2).2.2 w hw.1))
  have hGA : ∀ p ∈ S, AEStronglyMeasurable (Gdet W a' g₁ Q (p 0)) (σ.map (g p)) := by
    intro p hp
    have hgp := hg p (hSb p hp).1 (hSb p hp).2
    have hcH : ContinuousOn (fun v => Gdet W a' g₁ Q (p 0) v) H :=
      hGc.comp (f := fun v : ℂ => (p 0, v)) (continuousOn_const.prodMk continuousOn_id)
        fun v hv => ⟨(hSb p hp).1, hv⟩
    have haeH : ∀ᵐ v ∂(σ.map (g p)), v ∈ H :=
      (ae_map_iff hgp.1.aemeasurable isOpen_H.measurableSet).2
        (hsrc.mono fun w hw => (hgp.2.1 w hw.2.1 hw.2.2).1)
    have := hcH.aestronglyMeasurable (μ := σ.map (g p)) isOpen_H.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeH] at this
  have hint : EqOn (detLimA0 W a' g₁ Q d r) (fun p => ∫ w, F p w ∂σ) S := by
    intro p hp
    have hgp := hg p (hSb p hp).1 (hSb p hp).2
    show ∫ z, Gdet W a' g₁ Q (p 0) z ∂(σ.map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) = _
    rw [← hmap p hp, integral_map hgp.1.aemeasurable (hGA p hp)]
    exact integral_congr_ae (hsrc.mono fun w hw => by
      simp only [hF]; rw [hgp.2.2 w hw.1])
  refine ContinuousOn.congr ?_ hint
  set L : ℝ := max (Real.log Rb) 0 with hL
  refine continuousOn_of_dominated
    (bound := fun w => A + B * (|Real.log w.im| + |Real.log c| + L)) ?_ ?_ ?_ ?_
  · intro p hp
    have hgp := hg p (hSb p hp).1 (hSb p hp).2
    refine (((hGA p hp).comp_measurable hgp.1)).congr ?_
    exact hsrc.mono fun w hw => by
      simp only [Function.comp, hF]; rw [hgp.2.2 w hw.1]
  · intro p hp
    have hgp := hg p (hSb p hp).1 (hSb p hp).2
    filter_upwards [hsrc] with w hw
    obtain ⟨h1, h2, h3⟩ := hgp.2.1 w hw.2.1 hw.2.2
    have e := hgp.2.2 w hw.1
    rw [e] at h1 h2 h3
    have hw0 : 0 < w.im := hw.2.1
    have hcw : 0 < c * w.im := mul_pos hc hw0
    have hz0 : 0 < (fwdMap W (p 0) ((p 1 : ℂ) * w)).im := hcw.trans_le h2
    have a1 := Real.log_le_log hcw h2
    have a2 := Real.log_le_log hz0 ((Complex.im_le_norm _).trans h3)
    rw [Real.log_mul hc.ne' hw0.ne'] at a1
    have hlz : |Real.log (fwdMap W (p 0) ((p 1 : ℂ) * w)).im| ≤
        |Real.log w.im| + |Real.log c| + L := by
      refine abs_le.2 ⟨?_, ?_⟩
      · linarith [neg_abs_le (Real.log w.im), neg_abs_le (Real.log c), le_max_right (Real.log Rb) 0]
      · linarith [le_max_left (Real.log Rb) 0, abs_nonneg (Real.log w.im), abs_nonneg (Real.log c)]
    rw [Real.norm_eq_abs]
    refine (hA (p 0) (hSb p hp).1 _ h1 (by linarith)).trans ?_
    gcongr
  · exact (integrable_const A).add
      ((((integrable_log_im_foldedCircle d hr).abs.add (integrable_const _)).add
        (integrable_const _)).const_mul B)
  · filter_upwards [hsrc] with w hw
    have hcf : ContinuousOn (fun p : Fin 2 → ℝ => fwdMap W (p 0) ((p 1 : ℂ) * w)) S := by
      intro p hp
      set Ψ : (Fin 2 → ℝ) → ℝ := fun p' => Real.exp (2 * T / m ^ 2) *
          ‖(p' 1 : ℂ) * w - (p 1 : ℂ) * w‖ + |W (p' 0) - W (p 0)| + 2 * |p' 0 - p 0| / m
        with hΨ
      have hbd : ∀ p' ∈ S, ‖fwdMap W (p' 0) ((p' 1 : ℂ) * w) - fwdMap W (p 0) ((p 1 : ℂ) * w)‖
          ≤ Ψ p' := fun p' hp' =>
        norm_fwdMap_sub_le hW hW0 hT hm hsol hlow (mem_scaledSph (hSb p' hp').2 hw.1)
          (mem_scaledSph (hSb p hp).2 hw.1) (hSb p' hp').1 (hSb p hp).1
      have hΨc : Continuous Ψ := by
        have h0 : Continuous fun p' : Fin 2 → ℝ => p' 0 := continuous_apply 0
        have h1 : Continuous fun p' : Fin 2 → ℝ => p' 1 := continuous_apply 1
        exact ((continuous_const.mul
          (((Complex.continuous_ofReal.comp h1).mul continuous_const).sub continuous_const).norm).add
          ((hW.comp h0).sub continuous_const).abs).add
          ((continuous_const.mul (h0.sub continuous_const).abs).div_const _)
      have hΨ0 : Ψ p = 0 := by simp [hΨ]
      rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (eventually_nhdsWithin_of_forall hbd) ?_
      have := (hΨc.continuousWithinAt (s := S) (x := p))
      rwa [ContinuousWithinAt, hΨ0] at this
    show ContinuousOn (fun p : Fin 2 → ℝ => Gdet W a' g₁ Q (p 0) (fwdMap W (p 0) ((p 1 : ℂ) * w))) S
    refine ContinuousOn.comp (g := fun q : ℝ × ℂ => Gdet W a' g₁ Q q.1 q.2)
      (f := fun p : Fin 2 → ℝ => (p 0, fwdMap W (p 0) ((p 1 : ℂ) * w))) hGc
      ((continuous_apply 0).continuousOn.prodMk hcf) fun p hp => ⟨(hSb p hp).1, ?_⟩
    have hgp := hg p (hSb p hp).1 (hSb p hp).2
    show fwdMap W (p 0) ((p 1 : ℂ) * w) ∈ H
    rw [← hgp.2.2 w hw.1]
    exact (hgp.2.1 w hw.2.1 hw.2.2).1

end ASep
end QuantumZipper
