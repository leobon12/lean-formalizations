/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCfCollar
import InteractingSLE.Spec.Sec5.Aux61CmpCounter
import InteractingSLE.Spec.Sec5.Aux61CmpComponent

/-! # The counterflow side of the cover from a counterflow collar access

`CfAccess S F i p b`: the chart point `b` is the boundary value of
`c ∘ Ψ_s⁻¹` at a real point `x` of a counterflow collar (`Aux61CmpCfCollar`)
whose physical preimages all lie in the collar, `x` is a regular point of the
returned counterflow word, and the reference height at `b` is the returned
height plus `θχ` plus `χ` times the inherited relative phase.

`counterGerm_of_cfAccess`: a.s. on the selected records such points are
counterflow germ points (`CounterGerm`), given the counterflow trace on the
retained record (`hcf`). `normalizedComparisons_of_collars`: the `C` input of
`Aux61Wnd.dyCover_of_normalized_capture` when every window point of every
selected record is an own collar point or a counterflow collar access.
Conditional on that access hypothesis (R101) and `hcf`; no source statement
is replaced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cmp
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61ChLoc LawUnique GlueCond
open WangWu Cond44Ref Aux61GWord Aux61Restart Aux61SlitWX Aux61Asm2
universe u

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- **A counterflow collar access** of the chart point `b` at the sample `p`. -/
def CfAccess (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι)
    (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ ξ₀ δ x : ℝ, 0 < δ ∧ (x : ℂ) ∈ ball (ξ₀ : ℂ) δ ∧
    MapsTo (revChartInv (cfW S p) (rationalTime S.s)) (H ∩ ball (ξ₀ : ℂ) δ)
      ((S.marksData F).chart i p).dom ∧
    (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
      extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
      cfBdry (cfW S p) (rationalTime S.s) x' ≠ 1) ∧
    (∀ y : ℝ, extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) y =
        extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x : ℂ)) →
      (y : ℂ) ≠ 0 ∧ negInv (y : ℂ) ∈ ball (ξ₀ : ℂ) δ) ∧
    Tendsto (fun z => ((S.marksData F).chart i p).1 (revChartInv (cfW S p) (rationalTime S.s) z))
      (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) ∧
    b ≠ 0 ∧ b ∉ (F.data i).JR ∧
    x ∉ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (rationalTime S.s) p.2 ∧
    ∀ phase : ℝ, Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
        (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
        (𝓝[H] (b : ℂ)) (𝓝 phase) →
      (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
        (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 x + S.θ * chiC S.κ + chiC S.κ * phase

/-- **Counterflow collar accesses are counterflow germ points**, almost surely
on the selected records, given the counterflow trace of the retained record. -/
theorem counterGerm_of_cfAccess
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i → ∀ b : ℝ,
      CfAccess S F i p b → CounterGerm S F i p b := by
  filter_upwards [hgeometry, S.physical_path, hR.physical_stop i, source_zero_alive_iff S F hR i, hcf]
    with p hg hp hstop halive hcfp hB b hacc
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0 :=
    ⟨hB, by rw [ENNReal.coe_zero]; exact halive.2 hsel⟩
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hgeo := hg he
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ cfHullQ (rationalTime S.s) p.2 :=
    fun z hz => ⟨(hgeo.retained hz).1, fun hK => (hgeo.retained hz).2 (Or.inl hK)⟩
  have hKsub : negInv '' fwdHull (cfW S p) (rationalTime S.s) ⊆ cfHullQ (rationalTime S.s) p.2 :=
    image_mono (fwdHull_subset_hullAt (rationalTime S.s) p.2)
  have hsubK : (((S.marksData F).chart i p).dom : Set ℂ) ⊆
      H \ negInv '' fwdHull (cfW S p) (rationalTime S.s) :=
    fun z hz => ⟨(hsub hz).1, fun hK => (hsub hz).2 (hKsub hK)⟩
  obtain ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, hpre, hxb, hb0, hbJ, hξ, hword⟩ := hacc
  obtain ⟨⟨n, hn⟩, hland⟩ := cfCollar_limits hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin ha
    hgeo.lift hx hxb
  have hT := tendsto_cfTransition hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin hx hxb
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_inter_subset_dom_cf hw hw0 hγ hs hcol (hfin x hx).2.1 hpre
  have hz₀ : cfBdry (cfW S p) (rationalTime S.s) x ∈ cfHullQ (rationalTime S.s) p.2 ∪ {z : ℂ | z.im = 0} := by
    rcases cfBdry_mem_hull_or_real hw hw0 hγ hs x with h | h
    · exact Or.inl (hKsub h)
    · exact Or.inr h
  exact counterGerm_of_transition hc hsub hlive hb0 hbJ hξ hT hn (hword _ hn) hz₀ hland
    ⟨ρ, hρ, fun w hw' => hball ⟨hw'.1, hw'.2.1, fun hK => hw'.2.2 (hKsub hK)⟩⟩

theorem toNNReal_min_coe (r : ℝ) (t : ℝ≥0) : (min r (t : ℝ)).toNNReal = min r.toNNReal t := by
  rcases le_total r 0 with hr | hr
  · rw [min_eq_left (hr.trans t.coe_nonneg), Real.toNNReal_of_nonpos hr]
    simp
  · rcases le_total r t with hrt | hrt
    · rw [min_eq_left hrt, min_eq_left (Real.toNNReal_le_iff_le_coe.2 hrt)]
    · rw [min_eq_right hrt, Real.toNNReal_coe, min_eq_right]
      exact (Real.le_toNNReal_iff_coe_le hr).2 hrt

/-- **The counterflow trace of the retained record** (`hcf`): on the good
counterflow histories the retained driver is the counterflow driver frozen
at `s`, which has the frozen-slit trace. -/
theorem ae_cfW_trace (S : SourceSetting.{u}) :
    ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ := by
  filter_upwards [Aux61Asm2.ae_mem_goodCfSet S] with p hp
  obtain ⟨-, hw, hw0, hγ⟩ := CfRegQ.reg_of_mem_goodCfSet hp
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have heq : cfW S p = YuanCorollary13.extDrive (Prop411Q.cfDrv p.2) (rationalTime S.s : ℝ) := by
    funext r
    simp only [cfW, Ito.rpath, regPath_cfStop_of_mem_goodCfSet hp, YuanCorollary13.extDrive,
      CfRegQ.cfDrv_eq_hDrv, toNNReal_min_coe]
  refine ⟨?_, YuanCorollary13.extTrace (Prop411Q.cfDrv p.2) (histLine p.2) (rationalTime S.s : ℝ), ?_⟩
  · rw [heq]
    simp only [YuanCorollary13.extDrive, min_eq_left hs]
    exact hw0
  · rw [heq]
    exact (WangWu.isLoewnerTraceLT_of_isLoewnerTrace hγ ((rationalTime S.s : ℝ) + 1)).isLoewnerTrace_ext
      hw hw0 hs (by linarith)

variable (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)

/-- **The `C` input of `Aux61Wnd.dyCover_of_normalized_capture` from collar
accesses on both sides**: the seed heights of the installed words, the
counterflow trace of the retained record, and, almost surely on each
selected record, every window point an own collar point or a counterflow
collar access. -/
def normalizedComparisons_of_collars (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPoint S (normSource D h) i p b ∨ CfAccess S (normSource D h) i p b) :
    ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i :=
  normalizedComparisons_of_access D h R hTip V hExit hleft hright fun i => by
    have hR := Aux61GCaptureNext.normalized_cut_restart D h R hTip V hExit
    have hgeo : ∀ᵐ p ∂S.μ, p ∈ (normSource D h).event i →
        SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1)
          (fun t => S.path p.1 t.toNNReal) (cfHullQ (rationalTime S.s) p.2)
          ((normSource D h).start i)
          (sourceChart (normSource D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
      filter_upwards [R.ae_geometry h i] with p hp he
      exact hp he.1
    filter_upwards [haccess i, counterGerm_of_cfAccess hR i hgeo hcf] with p hacc hcg hB b hb
    rcases hacc hB b hb with h' | h'
    · exact Or.inl h'
    · exact Or.inr (hcg hB b h')

/-- **The `C` input of `Aux61Wnd.dyCover_of_normalized_capture`**, with the
counterflow trace discharged (`ae_cfW_trace`): only the installed words' seed
heights and the R101 collar-access hypothesis remain. -/
def normalizedComparisons (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPoint S (normSource D h) i p b ∨ CfAccess S (normSource D h) i p b) :
    ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i :=
  normalizedComparisons_of_collars D h R hTip V hExit hleft hright (ae_cfW_trace S) haccess

end InteractingSLE.Sec5.Aux61Cmp
