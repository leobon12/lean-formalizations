import QuantumZipper.Proofs.LQG.CoordChangeAreaTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the quantum area measure, local form (COORD-CHANGE, D98)

Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Proposition 2.1 (arXiv:0808.1560, p. 12): for a conformal map `ψ` and
`h̃ = h ∘ ψ + Q log|ψ'|`, a.s. `μ_{h̃} = ψ^* μ_h`. Here in the local form needed for fields of
GFF type that are only known near the image of the chart: a free, mixed or zero-boundary GFF,
plus a continuous function, possibly plus a log singularity at a boundary point — all of which
agree, on the dyadic circles inside an open set `W` avoiding the singular points, with a free
field `y` plus a function `φ` continuous on `W` (`Prop16Area.G.CircAgree W x (y + φ)`, e.g.
`Prop16MixedFreeLocCouplingStmt` for the mixed GFF, `Prop16Asm.palmPsi` for the Palm shift).

* `CoordChangeArea.isVagueLimitOn_coordChange_of_circAgree` (deterministic): if the area
  approximations of `y ∘ ψ + Q log|ψ'|` converge vaguely on `ℍ` to `μ` and the pushed averages of
  `y` are regular (`PushRegular`), then on every open `U ⊆ ℍ` with `ψ(U) ⊆ W` the area
  approximations of `x ∘ ψ + Q log|ψ'|` converge vaguely to `e^{γ φ∘ψ} μ|_U`;
* `CoordChangeArea.ae_qAreaMeasureOn_coordChange` (**main theorem**): for the free field `X` and
  a deterministic conformal map `ψ : ℍ → ℍ`, almost surely, **simultaneously for every** field
  sample `x`, open `W`, continuous `φ` on `W` with `CircAgree W x (X ω + φ)`, and open `U ⊆ ℍ`
  with `ψ(U) ⊆ W`:
  `qAreaMeasureOn γ (coordChange x ψ Q) U = e^{γ φ∘ψ} · (ψ^* μ_{X ω})|_U`,
  i.e. the local area measure of `x ∘ ψ + Q log|ψ'|` is the pullback of the local area measure
  `e^{γφ} μ_{X ω}` of `x` (DS11 Prop. 2.1, local form).

The multiplicative tilt is `GoodSample.tendsto_integral_exp_mul` (DS11 §6 locality). Own
bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

/-- Regularity of the pushed averages of `y` along `ψ` on compact subsets of `ℍ` (a.s. for the
free field, `ae_pushRegular`). -/
def PushRegular (y : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  ∀ K, IsCompact K → K ⊆ H → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (∀ d ∈ K, Tendsto (fun j => ∫ u, avgReg y j u ∂((foldedCircle d (radius k)).map ψ)) atTop
      (𝓝 (evalReg y ((foldedCircle d (radius k)).map ψ)))) ∧
    ContinuousOn (fun d => evalReg y ((foldedCircle d (radius k)).map ψ)) K

/-- The circle average of `y ∘ ψ + Q log|ψ'|` is the pushed value plus `Q log|ψ'|`. -/
theorem avgReg_coordChange_eq_push {y : FieldSample} {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ u ∈ H, deriv ψ u ≠ 0) {K₂ : Set ℂ}
    (hK₂H : K₂ ⊆ H) (Q : ℝ) {k : ℕ}
    (hC : ContinuousOn (fun d => evalReg y ((foldedCircle d (radius k)).map ψ)) K₂)
    {z : ℂ} (hB : closedBall z (2 * radius k) ⊆ K₂) :
    avgReg (coordChange y ψ Q) k z =
      evalReg y ((foldedCircle z (radius k)).map ψ) + Q * Real.log ‖deriv ψ z‖ := by
  have hr := radius_pos k
  have hzK : z ∈ K₂ := hB (mem_closedBall_self (by positivity))
  have him := two_mul_le_im_of_closedBall_subset hr.le (hB.trans hK₂H)
  have hdyMem : ∀ᶠ n in atTop, dyadicRoundC n z ∈ K₂ :=
    (a7_dyadic_small hr).mono fun n hn => hB (hn.1 (mem_closedBall_self hr.le))
  have hdz : Tendsto (fun n => dyadicRoundC n z) atTop (𝓝[K₂] z) :=
    tendsto_nhdsWithin_iff.2 ⟨RegClosure.tendsto_dyadicRoundC z, hdyMem⟩
  exact a7_avgReg_eq isOpen_H hψd hψ0 (hB.trans hK₂H) him (((hC z hzK).tendsto).comp hdz)

set_option maxHeartbeats 800000 in
/-- **Local coordinate change of the area approximations** (deterministic). -/
theorem isVagueLimitOn_coordChange_of_circAgree {γ : ℝ} {x y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {ψ : ℂ → ℂ} (hψm : Measurable ψ)
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hpush : PushRegular y ψ)
    {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ (coordChange y ψ (Qc γ))) μ)
    {W : Set ℂ} (hWo : IsOpen W) {φ : ℂ → ℝ} (hφ : ContinuousOn φ W)
    (hag : Prop16Area.G.CircAgree W x (y + ofFun φ)) {U : Set ℂ} (hUo : IsOpen U)
    (hUH : U ⊆ H) (hUW : MapsTo ψ U W) (hUH' : MapsTo ψ U Hbar) :
    IsVagueLimitOn U (areaApprox γ (coordChange x ψ (Qc γ)))
      ((μ.restrict U).withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ (ψ z)))) := by
  have hψc : ContinuousOn ψ H := hψd.continuousOn
  have hφψ : ContinuousOn (fun z => φ (ψ z)) U := hφ.comp (hψc.mono hUH) hUW
  have hdC : ContinuousOn (fun z => Real.exp (γ * φ (ψ z))) U :=
    (continuousOn_const.mul hφψ).rexp
  refine ⟨withDensity_absolutelyContinuous _ _ ?_, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hUo.measurableSet.compl, compl_inter_self, measure_empty]
  · exact withDensity_lt_top hK ((Measure.restrict_apply_le _ _).trans_lt
      (hμ.2.1 K hK (hKU.trans hUH))) (hdC.mono hKU)
  -- the support, its neighbourhoods and the extension of `φ ∘ ψ`
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hfU
  set ε : ℝ := ε₀ / 2 with hεdef
  have hε : 0 < ε := by positivity
  set K₂ := cthickening ε₀ K with hK₂def
  set K₁ := cthickening ε K with hK₁def
  have hK₂ : IsCompact K₂ := hK.cthickening
  have hK₁ : IsCompact K₁ := hK.cthickening
  have hK₂H : K₂ ⊆ H := hε₀U.trans hUH
  have hK₁K₂ : K₁ ⊆ K₂ := cthickening_mono (by linarith) K
  obtain ⟨g, hgc, hgeq⟩ := exists_continuous_extension isClosed_cthickening (hφψ.mono hε₀U)
  obtain ⟨k₀, hk₀⟩ := hpush K₂ hK₂ hK₂H
  have hrad : ∀ᶠ k in atTop, k₀ ≤ k ∧ 2 * radius k ≤ ε :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 2)) |>.mono
      fun k hk => by linarith)
  have hball : ∀ k : ℕ, 2 * radius k ≤ ε → ∀ z ∈ K₁, closedBall z (2 * radius k) ⊆ K₂ := by
    intro k hk z hz
    refine (closedBall_subset_cthickening hz _).trans ?_
    refine (cthickening_cthickening_subset (by linarith [radius_pos k]) hε.le K).trans
      (cthickening_mono (by linarith) K)
  -- the key identity on `K₁`
  have key : ∀ᶠ k in atTop, ∀ z ∈ K₁, avgReg (coordChange x ψ (Qc γ)) k z =
      avgReg (coordChange y ψ (Qc γ)) k z + smoothFun g z (radius k) := by
    filter_upwards [hrad] with k hk z hz
    exact avgReg_coordChange_eq_add hWo hF hφ hag hψm hψd hψ0 hK₂ hK₂H
      (hUW.mono_left hε₀U) (hUH'.mono_left hε₀U) hgc hgeq (Qc γ) (hk₀ k hk.1).1
      (hk₀ k hk.1).2 (hball k hk.2 z hz)
  -- continuity of the averages of `y ∘ ψ` on `K₁`
  have hlog : ContinuousOn (fun w => Real.log ‖deriv ψ w‖) H := fun w hw => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv w hw).continuousAt.norm.log
      (norm_ne_zero_iff.2 (hψ0 w hw))).continuousWithinAt
  have hyC : ∀ k : ℕ, k₀ ≤ k → 2 * radius k ≤ ε →
      ContinuousOn (fun z => avgReg (coordChange y ψ (Qc γ)) k z) K₁ := by
    intro k hk hk2
    have hc : ContinuousOn (fun z => evalReg y ((foldedCircle z (radius k)).map ψ) +
        Qc γ * Real.log ‖deriv ψ z‖) K₁ :=
      ((hk₀ k hk).2.mono hK₁K₂).add
        ((continuousOn_const (c := Qc γ)).mul (hlog.mono (hK₁K₂.trans hK₂H)))
    refine hc.congr fun z hz => ?_
    exact avgReg_coordChange_eq_push hψd hψ0 hK₂H (Qc γ) (hk₀ k hk).2 (hball k hk2 z hz)
  have hU₀H : thickening ε K ⊆ H :=
    (thickening_subset_cthickening _ _).trans (hK₁K₂.trans hK₂H)
  have hfin : ∀ᶠ k in atTop, ∀ K', IsCompact K' → K' ⊆ thickening ε K →
      areaApprox γ (coordChange y ψ (Qc γ)) k K' < ⊤ := by
    filter_upwards [hrad] with k hk K' _ hK'U
    have hsub : K' ⊆ K₁ := hK'U.trans (thickening_subset_cthickening _ _)
    refine (measure_mono hsub).trans_lt ?_
    show ((volume.restrict H).withDensity fun z => ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * avgReg (coordChange y ψ (Qc γ)) k z))) K₁ < ⊤
    refine withDensity_lt_top hK₁ ((Measure.restrict_apply_le _ _).trans_lt hK₁.measure_lt_top) ?_
    exact continuousOn_const.mul ((continuousOn_const.mul (hyC k hk.1 hk.2)).rexp)
  have ht := tendsto_integral_exp_mul (X := ℂ) (L := atTop) (U := thickening ε K)
    isOpen_thickening (νs := fun k => areaApprox γ (coordChange y ψ (Qc γ)) k) (ν := μ) hfin
    (fun f' hf' hf'c hf'U => hμ.2.2 f' hf' hf'c (hf'U.trans hU₀H))
    (v := fun k z => γ * smoothFun g z (radius k)) (v0 := fun z => γ * g z)
    (continuous_const.mul hgc).continuousOn
    (Eventually.of_forall fun k =>
      (continuous_const.mul (continuous_smoothFun hgc.continuousOn _)).continuousOn)
    (fun K' hK' hK'U ε' hε' => by
      have hs := RegClosure.tendsto_radius_nhdsGT.eventually (smooth_unif hgc.continuousOn hK'
        (fun z hz => H_subset_Hbar (hU₀H (hK'U hz))) (ε' / (|γ| + 1)) (by positivity))
      filter_upwards [hs] with k hk z hz
      show |γ * smoothFun g z (radius k) - γ * g z| < ε'
      rw [← mul_sub, abs_mul]
      calc |γ| * |smoothFun g z (radius k) - g z| ≤ |γ| * (ε' / (|γ| + 1)) :=
            mul_le_mul_of_nonneg_left (hk z hz).le (abs_nonneg _)
        _ < ε' := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [abs_nonneg γ])
    hf hfc (self_subset_thickening hε K)
  -- identify the two sides
  have hL : ∫ z, f z ∂((μ.restrict U).withDensity fun z =>
      ENNReal.ofReal (Real.exp (γ * φ (ψ z)))) = ∫ t, Real.exp (γ * g t) * f t ∂μ := by
    have hdm : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (γ * φ (ψ z)))) (μ.restrict U) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hdC.aemeasurable hUo.measurableSet)
    rw [integral_withDensity_eq_integral_toReal_smul₀ hdm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    rw [setIntegral_congr_fun hUo.measurableSet (g := fun t => Real.exp (γ * g t) * f t)
      fun z hz => ?_]
    · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
        rw [image_eq_zero_of_notMem_tsupport fun h => ht (hfU h), mul_zero]
    · simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
      by_cases hzK : z ∈ K
      · rw [hgeq (self_subset_cthickening K hzK)]
      · rw [image_eq_zero_of_notMem_tsupport hzK, mul_zero, mul_zero]
  rw [hL]
  refine ht.congr' ?_
  filter_upwards [key] with k hk
  rw [E6.integral_areaApprox_eq, E6.integral_areaApprox_eq]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  by_cases htK : t ∈ K
  · unfold E6.areaDensK
    rw [hk t (self_subset_cthickening K htK), mul_add, Real.exp_add]
    ring
  · rw [image_eq_zero_of_notMem_tsupport htK]
    simp

theorem recR_subset_succ (n : ℕ) : recR n ⊆ recR (n + 1) := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hq : 1 / ((n + 1 : ℕ) + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity); push_cast; linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast at * <;> linarith

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **The pushed averages of the free field are regular**, a.s., on every compact of `ℍ`. -/
theorem ae_pushRegular [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψH : MapsTo ψ H H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) : ∀ᵐ ω ∂P, PushRegular (X ω) ψ := by
  have h : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ k : ℕ,
      (∀ d ∈ recR (n + 1), Tendsto (fun j => ∫ u, avgReg (X ω) j u
          ∂((foldedCircle d (radius (k + k₀))).map ψ)) atTop
        (𝓝 (evalReg (X ω) ((foldedCircle d (radius (k + k₀))).map ψ)))) ∧
      ContinuousOn (fun d => evalReg (X ω) ((foldedCircle d (radius (k + k₀))).map ψ))
        (recR (n + 1)) := by
    intro n
    have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    obtain ⟨ρ, M, m, hρ, hm, hcl⟩ := exists_areaClass hψd hψi hψH hψ0
      (a := -((n + 1 : ℕ) : ℝ)) (b := ((n + 1 : ℕ) : ℝ)) (d := ((n + 1 : ℕ) : ℝ))
      (c := 1 / (((n + 1 : ℕ) : ℝ) + 1)) (by positivity)
    have hy : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact ae_pushed_regular hX (by linarith) (by positivity) hy hρ hm hcl
  choose k₀ hk₀ using h
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ k : ℕ,
      (∀ d ∈ recR (n + 1), Tendsto (fun j => ∫ u, avgReg (X ω) j u
          ∂((foldedCircle d (radius (k + k₀ n))).map ψ)) atTop
        (𝓝 (evalReg (X ω) ((foldedCircle d (radius (k + k₀ n))).map ψ)))) ∧
      ContinuousOn (fun d => evalReg (X ω) ((foldedCircle d (radius (k + k₀ n))).map ψ))
        (recR (n + 1)) := ae_all_iff.2 hk₀
  filter_upwards [hall] with ω hω K hK hKH
  obtain ⟨n, hn⟩ := exists_recR hK hKH
  have hKR : K ⊆ recR (n + 1) := hn.trans (interior_subset.trans (recR_subset_succ n))
  refine ⟨k₀ n, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + k₀ n := ⟨k - k₀ n, by omega⟩
  obtain ⟨h1, h2⟩ := hω n j
  exact ⟨fun d hd => h1 d (hKR hd), h2.mono hKR⟩

/-- **Coordinate change, local form, free-field coupling** (vague form). -/
theorem ae_isVagueLimitOn_coordChange_local [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H)
    (hψH : MapsTo ψ H H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ (x : FieldSample) (W : Set ℂ) (φ : ℂ → ℝ) (U : Set ℂ), IsOpen W →
      ContinuousOn φ W → Prop16Area.G.CircAgree W x (X ω + ofFun φ) → IsOpen U → U ⊆ H →
      MapsTo ψ U W →
      IsVagueLimitOn U (areaApprox γ (coordChange x ψ (Qc γ)))
        (((pullMu (qAreaMeasure γ (X ω)) ψ).restrict U).withDensity
          fun z => ENNReal.ofReal (Real.exp (γ * φ (ψ z)))) := by
  filter_upwards [RegSample.ae_isRegularSample hX, ae_pushRegular hX hψd hψi hψH hψ0,
    ae_isVagueLimitOn_coordChange_free hX hγ hγ2 hψd hψi hψH hψ0]
    with ω hreg hpush hμ x W φ U hWo hφ hag hUo hUH hUW
  obtain ⟨F, hF⟩ := hreg
  exact isVagueLimitOn_coordChange_of_circAgree hF hψm hψd hψ0 hpush hμ hWo hφ hag hUo hUH hUW
    fun z hz => H_subset_Hbar (hψH (hUH hz))

/-- **Coordinate change of the quantum area measure, local form** (DS11 Prop. 2.1). For the
free field `X` on `ℍ` and a deterministic conformal map `ψ : ℍ → ℍ` (holomorphic, injective,
`ψ' ≠ 0`, measurable): almost surely, for every field sample `x` agreeing on the dyadic circles
in an open `W` with `X ω + φ` (`φ` continuous on `W`) and every open `U ⊆ ℍ` with `ψ(U) ⊆ W`,
the local area measure of `x ∘ ψ + Q log|ψ'|` on `U` is `e^{γ φ∘ψ} · (ψ^* μ_{X ω})|_U`. -/
theorem ae_qAreaMeasureOn_coordChange [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H)
    (hψH : MapsTo ψ H H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ (x : FieldSample) (W : Set ℂ) (φ : ℂ → ℝ) (U : Set ℂ), IsOpen W →
      ContinuousOn φ W → Prop16Area.G.CircAgree W x (X ω + ofFun φ) → IsOpen U → U ⊆ H →
      MapsTo ψ U W →
      qAreaMeasureOn γ (coordChange x ψ (Qc γ)) U =
        ((pullMu (qAreaMeasure γ (X ω)) ψ).restrict U).withDensity
          fun z => ENNReal.ofReal (Real.exp (γ * φ (ψ z))) := by
  filter_upwards [ae_isVagueLimitOn_coordChange_local hX hγ hγ2 hψm hψd hψi hψH hψ0]
    with ω h x W φ U hWo hφ hag hUo hUH hUW
  exact LocalRule.qAreaMeasureOn_eq hUo (h x W φ U hWo hφ hag hUo hUH hUW)

end CoordChangeArea
end QuantumZipper
