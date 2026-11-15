/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptJump
import InteractingSLE.Spec.Sec5.Aux61KernelTop
import InteractingSLE.Spec.Sec7.FanTipFiber

/-!
# The landing of a window excursion: the open step of ruling R103 at the landing point

Packet PROVE-AUX61-CAPTURE. Almost surely on the physical window event (`SourceSetting.windowEvent`) the excursion's
landing coordinate `x₁` in the counterflow chart `Ψ` satisfies everything the component counterflow access
`CfAccessC` asks of the landing itself:

* `x₁` lies right of the right junction and is **not a jump of the returned counterflow word**;
* its physical point `cfBdry x₁` (read with the retained regularized counterflow driver `cfW`) **is the flow line's
  landing point** `η(u₀)`, which lies in `ℍ`;
* a ball about it misses every earlier own prefix `η([0, r])`, `r < u₀` (injectivity of the flow line).

With the component form of `Aux61CptGerm` no pinch-point condition is needed: the two halves of R103's open step
("not a jump", "not a pinch point with prime ends outside every small counterflow collar") are discharged at the
landing (`ae_windowEvent_landing`). The deterministic core is `cfBdry_eq_of_landing`.

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord MartChar.RealFlow CrossCond.Word49 Aux61Cmp LawUnique
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Kernel Aux61GAlign
universe u

/-- **The physical point of a landing coordinate is the landing point** (deterministic): if the excursion of a
proper arc in `ℍ ∖ R(K_s)` on `(t, u₀)` lands at the chart point `x₁ ≠ 0` as `u ↑ u₀`, then the boundary value of
the inverse chart at `x₁` is `η(u₀)`. -/
theorem cfBdry_eq_of_landing {w : ℝ → ℝ} {β η : ℝ → ℂ} {s t u₀ x₁ : ℝ} (hη : IsProperArc η)
    (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s) (ht0 : 0 ≤ t)
    (htu : t < u₀) (hD : ∀ u ∈ Ioo t u₀, η u ∈ H \ negInv '' fwdHull w s) (hx₁ : x₁ ≠ 0)
    (hland : Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (x₁ : ℂ))) :
    cfBdry w s x₁ = η u₀ := by
  have hu₀ : 0 < u₀ := ht0.trans_lt htu
  have hev : ∀ᶠ u in 𝓝[<] u₀, u ∈ Ioo t u₀ := Ioo_mem_nhdsLT htu
  have hηu₀ : η u₀ ∈ H := hη.mem_H u₀ hu₀
  have hη0 : η u₀ ≠ 0 := fun h => by
    have h' : 0 < (η u₀).im := hηu₀
    rw [h, Complex.zero_im] at h'
    exact lt_irrefl _ h'
  -- the path converges to its landing point from the left
  have hcont : Tendsto η (𝓝[<] u₀) (𝓝 (η u₀)) := by
    have h1 : ContinuousWithinAt η (Ici 0) u₀ := hη.cont u₀ (le_of_lt hu₀)
    have hmem : Ici (0 : ℝ) ∈ 𝓝[<] u₀ := by
      filter_upwards [Ioo_mem_nhdsLT hu₀] with v hv
      exact le_of_lt hv.1
    exact h1.tendsto.mono_left (nhdsWithin_le_of_mem hmem)
  -- the chart image lands at `x₁` inside `ℍ`
  have hx₁' : (x₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx₁
  have hN : Tendsto (fun u => negInv (revChart w s (η u))) (𝓝[<] u₀) (𝓝[H] (negInv (x₁ : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_negInv hx₁').tendsto.comp hland, ?_⟩
    filter_upwards [hev] with u hu
    exact negInv_mem_H (revChart_mem_H hw hs (hD u hu))
  have hbar : negInv (x₁ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (negInv_ofReal_im x₁)
  have hlim1 := ((hβ.hasBdryLimits hw hw0 hs).tendsto hbar).comp hN
  have heq : ∀ᶠ u in 𝓝[<] u₀, (fwdMapInv w s ∘ fun u => negInv (revChart w s (η u))) u = negInv (η u) := by
    filter_upwards [hev] with u hu
    have h := congrArg negInv (revChartInv_revChart hw hw0 hs (hD u hu))
    rw [revChartInv, negInv_negInv'] at h
    exact h
  have hlim2 : Tendsto (fun u => negInv (η u)) (𝓝[<] u₀) (𝓝 (negInv (η u₀))) :=
    (continuousAt_negInv hη0).tendsto.comp hcont
  have hne : (𝓝[<] u₀).NeBot := nhdsLT_neBot u₀
  have hval := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  rw [cfBdry, hval, negInv_negInv']

/-- On a good counterflow history the retained regularized driver agrees with the counterflow driver up to `s`. -/
theorem eqOn_cfW_cfDrv (S : SourceSetting.{u}) {p : S.Ω × HistorySpace 0 0} (hp : p.2 ∈ CfRegQ.goodCfSet) :
    EqOn (cfW S p) (Prop411Q.cfDrv p.2) (Icc 0 (rationalTime S.s : ℝ)) := by
  have heq : cfW S p = YuanCorollary13.extDrive (Prop411Q.cfDrv p.2) (rationalTime S.s : ℝ) := by
    funext r
    simp only [cfW, Ito.rpath, regPath_cfStop_of_mem_goodCfSet hp, YuanCorollary13.extDrive,
      CfRegQ.cfDrv_eq_hDrv, toNNReal_min_coe]
  intro r hr
  rw [heq, YuanCorollary13.extDrive, min_eq_left hr.2]

/-- **The landing of the window excursion** (R103's open step at the landing point): almost surely on the window
event the excursion lands at a chart point `x₁` right of the right junction which is not a jump of the returned
counterflow word, whose physical point (read with the retained driver `cfW`) is the flow line's landing point
`η(u₀) ∈ ℍ`, and a ball about it misses every earlier own prefix. -/
theorem ae_windowEvent_landing (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∃ u₀ x₁ : ℝ, (S.t : ℝ) < u₀ ∧
      Tendsto (fun u => revChart (Prop411Q.cfDrv p.2) S.s (S.path p.1 u.toNNReal)) (𝓝[<] u₀)
        (𝓝 (x₁ : ℂ)) ∧
      ((S.windowCode.2.1 : ℚ) : ℝ) < x₁ ∧ x₁ < ((S.windowCode.2.2.1 : ℚ) : ℝ) ∧
      junR (Prop411Q.cfDrv p.2) S.s < x₁ ∧
      cfBdry (cfW S p) (rationalTime S.s) x₁ = S.path p.1 u₀.toNNReal ∧
      S.path p.1 u₀.toNNReal ∈ H ∧
      x₁ ∉ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
        (rationalTime S.s) p.2 ∧
      ∀ r < u₀, ∃ ρ > 0, Disjoint (ball (S.path p.1 u₀.toNNReal) ρ)
        ((fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 r) := by
  filter_upwards [S.physical_path, Aux61Asm2.ae_mem_goodCfSet S, ae_cfW_trace S] with p hp hgood hcfp hwin
  obtain ⟨-, hw, hw0, hβ⟩ := CfRegQ.reg_of_mem_goodCfSet hgood
  obtain ⟨hcW0, γ, hγ⟩ := hcfp
  have hcW : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  obtain ⟨hW, u₀, hE, -⟩ := hwin
  have hE₂ := hE
  obtain ⟨-, -, htu, hin, x₁, hland⟩ := hE₂
  have hmem := WindowExcursion.landing_mem hW hE hland
  have hs : (0 : ℝ) ≤ (S.s : ℝ) := by exact_mod_cast S.s_pos.le
  have ht : (0 : ℝ) < (S.t : ℝ) := by exact_mod_cast S.t_pos
  have hx₁ : 0 < x₁ := (junR_nonneg hw hs).trans_lt (hW.east.trans hmem.1)
  have harc := hp.2.2
  have hphys := cfBdry_eq_of_landing harc hw hw0 hβ hs ht.le htu (fun u hu => (hin u hu).1) hx₁.ne' hland
  have hrs : ((rationalTime S.s : ℝ≥0) : ℝ) = (S.s : ℝ) := Aux61R1C.coe_rationalTime S.s_pos.le
  have hcf : cfBdry (cfW S p) (rationalTime S.s) x₁ = S.path p.1 u₀.toNNReal := by
    have hEq := eqOn_cfW_cfDrv S hgood
    rw [hrs] at hEq
    have hc := Sec7.extendFrom_fwdMapInv_congr hcW hcW0 hw hw0 hs hEq
    simp only [cfBdry, hrs, hc]
    exact hphys
  have hu₀ : 0 < u₀ := ht.trans htu
  have hH : S.path p.1 u₀.toNNReal ∈ H := harc.mem_H u₀ hu₀
  refine ⟨u₀, x₁, htu, hland, hmem.1, hmem.2, hW.east.trans hmem.1, hcf, hH, ?_, ?_⟩
  · intro hJ
    have him := im_cfBdry_eq_zero_of_mem_returnedCfJumps hcW hcW0 hγ hx₁.ne' hJ
    rw [hcf] at him
    have hpos : 0 < (S.path p.1 u₀.toNNReal).im := hH
    rw [him] at hpos
    exact lt_irrefl _ hpos
  · intro r hr
    set η : ℝ → ℂ := fun t : ℝ => S.path p.1 t.toNNReal
    have hK : IsCompact (η '' Icc 0 r) := by
      rcases lt_or_ge r 0 with hr0 | hr0
      · rw [Icc_eq_empty (not_le.2 hr0), image_empty]
        exact isCompact_empty
      · exact isCompact_Icc.image_of_continuousOn (harc.cont.mono fun v hv => hv.1)
    have hnot : η u₀ ∉ η '' Icc 0 r := by
      rintro ⟨v, hv, hveq⟩
      have := harc.inj hv.1 (le_of_lt hu₀) hveq
      linarith [hv.2]
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl (η u₀) hnot
    exact ⟨ρ, hρ, Set.disjoint_left.2 fun z hz hzK => hball hz hzK⟩

end InteractingSLE.Sec5.Aux61Cpt
