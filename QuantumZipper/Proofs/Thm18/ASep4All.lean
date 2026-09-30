import QuantumZipper.Proofs.Thm18.ASep4Run
import QuantumZipper.Proofs.Thm18.ASep2Conj1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 8): the scale run at every good parameter; conjuncts 1 and 2 for a general base field

* `ae_scale_run_all`: almost surely, for every scale `s > 0` and every good parameter `p`, the two
  outputs of `ae_scale_run_box` hold for `coordChange (rescale X Q s) f_τ⁻¹ Q` (countable cover of
  the open set `ScaleGood` by rational boxes);
* `conj1_add_gen`, `conj2_add_gen` (deterministic): the bodies of `ae_conj1_add_good`,
  `ae_conj2_add_good` (ASep2Conj1/ASep2Conj2) for an arbitrary regular base field `x` in place of
  the free-field sample, with the probabilistic inputs (joint witness at the time `τ`,
  continuous-radius limit, dyadic convergence to the raw value, pushed-circle convergence) as
  hypotheses.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont TwoPoint CoordReg GenUC

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **The scale run at every good parameter and every scale.** -/
theorem ae_scale_run_all [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {W : ℝ → ℝ} (hWg : DrvGood W) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ p ∈ GoodSet W d r,
      (∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (coordChange (rescale (X ω) (Qc γ) s)
        (fwdMapInv W (p 0)) (Qc γ)) (foldedCircle v ρ) ∂nuA0 W d r p) (𝓝[>] 0) (𝓝 L)) ∧
      Tendsto (fun j : ℕ => ∫ v, avgReg (coordChange (rescale (X ω) (Qc γ) s)
        (fwdMapInv W (p 0)) (Qc γ)) j v ∂nuA0 W d r p) atTop
        (𝓝 (coordChange (rescale (X ω) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ) (nuA0 W d r p))) := by
  have hall : ∀ᵐ ω ∂P, ∀ ab : (Fin 3 → ℚ) × (Fin 3 → ℚ), ratBox ab.1 ab.2 ⊆ ScaleGood W d r →
      ∀ q ∈ ratBox ab.1 ab.2,
        (∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (xS X W (Qc γ) q ω) (foldedCircle v ρ)
          ∂nuA0 W d r (Fin.init q)) (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto (fun j : ℕ => ∫ v, avgReg (xS X W (Qc γ) q ω) j v ∂nuA0 W d r (Fin.init q))
          atTop (𝓝 (xS X W (Qc γ) q ω (nuA0 W d r (Fin.init q)))) := by
    refine ae_all_iff.2 fun ab => ?_
    by_cases hsub : ratBox ab.1 ab.2 ⊆ ScaleGood W d r
    · filter_upwards [ae_scale_run_box hX γ hWg hd hr hsub] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun ω h' => absurd h' hsub
  filter_upwards [hall] with ω hω s hs p hp
  have hq : (Fin.snoc p s : Fin 3 → ℝ) ∈ ScaleGood W d r := by
    refine ⟨?_, ?_⟩
    · rw [Fin.init_snoc]; exact hp
    · rw [Fin.snoc_last]; exact hs
  obtain ⟨lo, hi, hqab, hsub⟩ := exists_ratBox_subset (isOpen_scaleGood W d r) hq
  have h := hω (lo, hi) hsub _ hqab
  simp only [xS, Fin.init_snoc, Fin.snoc_last] at h
  exact h

/-- **Conjunct 1 for `profile + x`, general regular base field** (deterministic). -/
theorem conj1_add_gen (γ : ℝ) {W : ℝ → ℝ} (hWg : DrvGood W) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ}
    (hr : 0 < r) {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {p : Fin 2 → ℝ} (hp : p ∈ GoodSet W d r) {Z : ℂ × ℝ → ℝ}
    (hZτ : IsRegularWith (coordChange x (fwdMapInv W (p 0)) (Qc γ)) Z)
    (hLω : ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (coordChange x (fwdMapInv W (p 0)) (Qc γ))
      (foldedCircle v ρ) ∂nuA0 W d r p) (𝓝[>] 0) (𝓝 L))
    (hψ : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, Tendsto (fun j => ∫ z, avgReg x j z
      ∂νT W c (radius k) (p 0)) atTop (𝓝 (evalReg x (νT W c (radius k) (p 0)))))
    {g : ℂ → ℝ} (hg : Continuous g) :
    evalReg (rescale (coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ)) (Qc γ) (p 1))
        ((foldedCircle d r).map
          (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) =
      rescale (coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ)) (Qc γ) (p 1)
        ((foldedCircle d r).map
          (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) := by
  have hW := hWg.1
  have hW0 := hWg.2.1
  have hR : (0 : ℝ) ≤ ‖d‖ + r := by positivity
  have hK : foldSph d r ⊆ closedBall 0 (‖d‖ + r) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]; exact norm_le_of_mem_foldSph hx
  have hU : IsOpen (GoodSet W d r) := isOpen_parGood hR hK
  obtain ⟨lo, hi, hpab, hsub⟩ := exists_ratBox_subset hU hp
  obtain ⟨T, a₀, a₁, δ, hT, ha₀, hδ, -, hSb, hgood, hsep⟩ := boxData_A0 hr hsub ⟨p, hpab⟩
  have hτ : 0 ≤ p 0 := (hSb p hpab).1.1
  have ha : 0 < p 1 := ha₀.trans_le (hSb p hpab).2.1.1
  have hSb' : ∀ q ∈ ratBox lo hi, q 0 ∈ Icc (0 : ℝ) T ∧ q 1 ∈ Icc a₀ a₁ := fun q hq =>
    ⟨(hSb q hq).1, (hSb q hq).2.1⟩
  have hUg := isRegularWith_add_of (Uh := coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ))
    hZτ (isRegularWith_Dg hW hτ hg) fun n j z => by
      rw [RegUnif.raw_eq_foldH (coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ)) n j z,
        RegUnif.raw_eq_foldH (coordChange (x) (fwdMapInv W (p 0)) (Qc γ)) n j z]
      exact coordChange_ofFun_add_cont hF hg hW hW0 hτ (Qc γ) _ (radius_pos j)
        (hψ _ (RegUnif.foldH_dyadicRoundC_mem_Dy n z) j)
  obtain ⟨R₁, -, hν⟩ := nuA0_facts hW hW0 hT.le hr ha₀ hSb' hgood
  obtain ⟨hνP, hsupp, hνH⟩ := hν p hpab
  have := hνP
  obtain ⟨L, hL⟩ := hLω
  have hL' : Tendsto (fun ρ => ∫ v, Z (v, ρ) ∂nuA0 W d r p) (𝓝[>] 0) (𝓝 L) :=
    hL.congr' (eventually_nhdsWithin_of_forall fun ρ hρ => integral_congr_ae
      (hνH.mono fun v hv => hZτ.evalReg_fc_of_mem (show (0 : ℝ) ≤ v.im from le_of_lt hv) hρ))
  have hdet := det_unif_A0_rho hW hW0 hT.le hr ha₀ hSb' hgood 0 hg 0
  have hdetT : Tendsto (fun ρ => ∫ z, Dfix W 0 g 0 (p 0, (z, ρ)) ∂nuA0 W d r p) (𝓝[>] 0)
      (𝓝 (detLimA0 W 0 g 0 d r p)) := by
    refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_
    obtain ⟨ρ₀, hρ₀, h⟩ := hdet ε hε
    refine ⟨ρ₀, hρ₀, fun {ρ} hρ hρd => ?_⟩
    have hρ' : (0 : ℝ) < ρ := hρ
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ'] at hρd
    rw [Real.dist_eq]
    exact h ρ hρ' hρd.le p hpab
  have hint : ∀ G : ℂ × ℝ → ℝ, ContinuousOn G (Hbar ×ˢ Ioi 0) → ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun v => G (v, ρ)) (nuA0 W d r p) := fun G hG ρ hρ =>
    FrostmanReg.integrable_of_continuousOn_frostman (CircleFubini.isCompact_ballH R₁)
      inter_subset_right hsupp (RegClosure.continuousOn_slice hG hρ)
  have hLs : Tendsto (fun ρ => ∫ v, (Z (v, ρ) + Dfix W 0 g 0 (p 0, (v, ρ)))
      ∂nuA0 W d r p) (𝓝[>] 0) (𝓝 (L + detLimA0 W 0 g 0 d r p)) :=
    (hL'.add hdetT).congr' (eventually_nhdsWithin_of_forall fun ρ hρ =>
      (integral_add (hint _ hZτ.1 ρ hρ)
        (hint _ (isRegularWith_Dg hW hτ hg).1 ρ hρ)).symm)
  have hψm : Measurable (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1) :=
    Cor15Group.measurable_revMapInv (continuous_backDrv hW (p 0) 0 (p 1))
      (show 0 ≤ (p 0 - 0) / p 1 ^ 2 from div_nonneg (by linarith) (sq_nonneg _))
  have hprob : IsProbabilityMeasure ((foldedCircle d r).map
      (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) :=
    (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  have hgood0 := hgood0_of_hgood hgood
  obtain ⟨m, -, -, -, hm, -, hlow, -⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  obtain ⟨-, hgd, -, -, -, -, -⟩ :=
    pfacts_A0 hW hW0 hr ha₀ hm hδ hgood0 hlow (hSb p hpab).1 (hSb p hpab).2.2 (hSb p hpab).2.1
      (hsep p hpab) 0 hg
  have hμν : ((foldedCircle d r).map
      (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)).map
        (fun z => (p 1 : ℂ) * z) = nuA0 W d r p := by
    rw [Measure.map_map (measurable_const_mul _) hψm,
      nuA0_eq_map_psi hW hW0 hτ ha (hgd.mono fun w hw => ⟨hw.1, hw.2.1⟩)]
    rfl
  have hμH : ∀ᵐ z ∂(foldedCircle d r).map
      (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1), z ∈ Hbar := by
    refine (ae_map_iff hψm.aemeasurable isClosed_Hbar.measurableSet).2 ?_
    filter_upwards [hgd] with w hw
    have e := mul_revMapInv_revDrv0_eq hW hW0 hτ ha hw.2.1 hw.1
    have hawH : (p 1 : ℂ) * w ∈ H := by
      show 0 < ((p 1 : ℂ) * w).im
      simpa using mul_pos ha hw.1
    have hf : 0 < (fwdMap W (p 0) ((p 1 : ℂ) * w)).im :=
      FwdHolo.mapsTo_fwdMap hW hτ ⟨hawH, hw.2.2⟩
    rw [← e] at hf
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hf
    exact le_of_lt (pos_of_mul_pos_right hf ha.le)
  exact conj1_of_limit hUg (Qc γ) ha hμν hμH hsupp hLs

/-- **Conjunct 2 for `profile + x`, general regular base field** (deterministic). -/
theorem conj2_add_gen (γ : ℝ) {W : ℝ → ℝ} (hWg : DrvGood W) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ}
    (hr : 0 < r) {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {p : Fin 2 → ℝ} (hp : p ∈ GoodSet W d r) {Z : ℂ × ℝ → ℝ}
    (hZτ : IsRegularWith (coordChange x (fwdMapInv W (p 0)) (Qc γ)) Z)
    (hT0 : Tendsto (fun j : ℕ => ∫ v, avgReg (coordChange x (fwdMapInv W (p 0)) (Qc γ)) j v
      ∂nuA0 W d r p) atTop (𝓝 (coordChange x (fwdMapInv W (p 0)) (Qc γ) (nuA0 W d r p))))
    (hψ : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, Tendsto (fun j => ∫ z, avgReg x j z
      ∂νT W c (radius k) (p 0)) atTop (𝓝 (evalReg x (νT W c (radius k) (p 0)))))
    {g : ℂ → ℝ} (hg : Continuous g) :
    evalReg (coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ)) (nuA0 W d r p) =
      coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ) (nuA0 W d r p) := by
  have hW := hWg.1
  have hW0 := hWg.2.1
  have e0 : ∀ (y : FieldSample) (t : ℝ),
      coordChange (ofFun (fun v => 0 * Real.log ‖v‖ + (fun _ : ℂ => (0 : ℝ)) v) + y)
        (fwdMapInv W t) (Qc γ) = coordChange y (fwdMapInv W t) (Qc γ) := fun y t => by
    rw [ofFun_zero_add]
  have hR : (0 : ℝ) ≤ ‖d‖ + r := by positivity
  have hK : foldSph d r ⊆ closedBall 0 (‖d‖ + r) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]; exact norm_le_of_mem_foldSph hx
  have hU : IsOpen (GoodSet W d r) := isOpen_parGood hR hK
  obtain ⟨lo, hi, hpab, hsub⟩ := exists_ratBox_subset hU hp
  obtain ⟨T, a₀, a₁, δ, hT, ha₀, hδ, -, hSb, hgood, hsep⟩ := boxData_A0 hr hsub ⟨p, hpab⟩
  have hτ : 0 ≤ p 0 := (hSb p hpab).1.1
  have ha : 0 < p 1 := ha₀.trans_le (hSb p hpab).2.1.1
  have hSb' : ∀ q ∈ ratBox lo hi, q 0 ∈ Icc (0 : ℝ) T ∧ q 1 ∈ Icc a₀ a₁ := fun q hq =>
    ⟨(hSb q hq).1, (hSb q hq).2.1⟩
  obtain ⟨R₁, -, hnu⟩ := nuA0_facts hW hW0 hT.le hr ha₀ hSb' hgood
  obtain ⟨hPM, hMball, -⟩ := hnu p hpab
  have hdet := det_unif_A0 hW hW0 hT.le hr ha₀ hSb' hgood 0 hg 0
  have hdetT : Tendsto (fun j => ∫ z, Dfix W 0 g 0 (p 0, (z, radius j)) ∂nuA0 W d r p) atTop
      (𝓝 (detLimA0 W 0 g 0 d r p)) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨J, hJ⟩ := hdet ε hε
    exact ⟨J, fun j hj => by rw [Real.dist_eq]; exact hJ j hj p hpab⟩
  -- raw value at `ν_p`
  have hgood0 := hgood0_of_hgood hgood
  obtain ⟨m, -, -, -, hm, -, hlow, -⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  obtain ⟨hmeas, hgd, hint1, -, hI2, -, -⟩ :=
    pfacts_A0 hW hW0 hr ha₀ hm hδ hgood0 hlow (hSb p hpab).1 (hSb p hpab).2.2 (hSb p hpab).2.1
      (hsep p hpab) 0 hg
  have eL := detLimA0_eq_raw hW hW0 0 hg 0 hτ ha hmeas hgd hint1 hI2
  have eg := raw_id_A0 γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep 0 hg hpab hF
  have e00 := raw_id_A0 γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep 0
    (continuous_const (y := (0 : ℝ))) hpab hF
  rw [e0] at e00
  have eofg : ofFun (fun v => 0 * Real.log ‖v‖ + g v) = ofFun g := by
    congr 1; funext v; simp
  rw [eofg] at eg
  refine conj2_add_of (U0 := coordChange (x) (fwdMapInv W (p 0)) (Qc γ))
    (D := fun q => Dfix W 0 g 0 (p 0, q)) hZτ ?_ ?_ (CircleFubini.isCompact_ballH R₁)
    inter_subset_right (mem_ae_iff.2 hMball) hT0 hdetT ?_
  · intro n j z
    rw [RegUnif.raw_eq_foldH (coordChange (ofFun g + x) (fwdMapInv W (p 0)) (Qc γ)) n j z,
      RegUnif.raw_eq_foldH (coordChange (x) (fwdMapInv W (p 0)) (Qc γ)) n j z]
    exact coordChange_ofFun_add_cont hF hg hW hW0 hτ (Qc γ) _ (radius_pos j)
      (hψ _ (RegUnif.foldH_dyadicRoundC_mem_Dy n z) j)
  · intro j
    have := continuousOn_Dfix hW hW0 (T := T) hT.le 0 hg 0
    exact this.comp (Continuous.continuousOn (by fun_prop)) fun c hc =>
      ⟨(hSb p hpab).1, hc, radius_pos j⟩
  · rw [eg, e00, eL]
    simp only [zero_mul, zero_add, integral_zero]
    ring

end ASep
end QuantumZipper
