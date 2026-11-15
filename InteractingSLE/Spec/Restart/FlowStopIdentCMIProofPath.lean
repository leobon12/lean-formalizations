/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofTop
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.Spec.Sec5.CrossRestartLawTopo
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Restart.FlowStopIdentLLCont
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Sec2.TerminalEvolution

/-!
# The pathwise data at a stop, along one path

Packet PROVE-L1-CMI (continuation). The facts `StopPathData` consumed by the per-stop identification
`ae_condExp_shift_eq_ref`, for one path of the `b`-coupling, at a time `τ` before the exit time `e` from the buffer `V`,
and a continuous driver `w₁` agreeing with the `b`-driver before `e`:

* **`cmiStopDataStatement`**: the named input `CMIStopDataStatement` **proved**, with the `b`-driver stopped at the
  exit time (`LocalExt.stopVal`; continuous through a finite exit time by continuity before the lifetime or by the
  terminal limit of Aux. lemma 3, `IsIntegratedSLEEvolution.ae_tendsto_threshold`);
* **`stopPathData_det`**: continuity and start of `w₁`; agreement on `[0, t₂]` for some `t₂ ∈ (τ, e)`; the `b`-marks at
  the geometric images of `w₁` (`SideHeight.vL_eq_neg_rightImg_frozenDrive`, `GB6.rightImg_congr`); the hull closure in
  the chart buffer (the trace up to `τ` stays in `V`, its translate fills the translated hull,
  `CrossRestart.isFilling_image_add`, and `FlowStopIdentCM.subset_shiftHullSet`); the fill of the hulls by the trace
  (`CrossRestart.fwdHull_eq_fillH_of_isFilling`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar fwdHull)

/-- Real translations preserve the open half-plane. -/
theorem add_real_mem_H_iff {z : ℂ} (y : ℝ) : z + (y : ℂ) ∈ H ↔ z ∈ H := by
  show (0 : ℝ) < (z + (y : ℂ)).im ↔ (0 : ℝ) < z.im
  simp

/-- A filling only depends on the points of the filled set in `ℍ`. -/
theorem isFilling_of_inter_H {K A B : Set ℂ} (hAB : A ∩ H = B ∩ H) (h : IsFilling K A) : IsFilling K B := by
  have e : H \ A = H \ B := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨hz, fun hzB => hzA (((Set.ext_iff.1 hAB z).2 ⟨hzB, hz⟩).1)⟩
    · rintro ⟨hz, hzB⟩
      exact ⟨hz, fun hzA => hzB (((Set.ext_iff.1 hAB z).1 ⟨hzA, hz⟩).1)⟩
  obtain ⟨⟨z, hz, hcc⟩, hb⟩ := h
  exact ⟨⟨z, hz, by rw [← e]; exact hcc⟩, hb⟩

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {y θ : ℝ}

/-- **The pathwise data at a time `τ` before the exit time**, along one path of the `b`-coupling. -/
theorem stopPathData_det {N V : Set ℂ} (hVb : Bornology.IsBounded V) {a c : ℝ}
    (hVa : ∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) (hsN : FlowStopIdentCM.shiftHullSet V a c ⊆ N)
    {w₀ w₁ : ℝ≥0 → ℝ} {vL : Fin (flowLineNL b J y) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR b J y) → ℝ≥0 → ℝ}
    {β : ℝ≥0 → ℝ} {U : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
      (flowLineRhoR κ b J y θ) w₀ vL vR β U)
    {η : ℝ≥0 → ℂ} (hg : IsGeneratingTrace w₀ U fun t => η t - y) (hw₁ : Continuous w₁)
    (hw₁e : ∀ t : ℝ≥0, (t : ℝ≥0∞) < RLC.exitTime V η U → w₁ t = w₀ t) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < RLC.exitTime V η U) :
    w₁ 0 = 0 ∧
    (∃ t₂ : ℝ, (τ : ℝ) < t₂ ∧ ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath w₁ r = Ito.rpath w₀ r) ∧
    (∀ i, vL i τ - w₀ τ = geomL (Ito.rpath w₁) τ (flowLineXL b J y i)) ∧
    (∀ j, vR j τ - w₀ τ = geomR (Ito.rpath w₁) τ (flowLineXR b J y j)) ∧
    closure (fwdHull (Ito.rpath w₁) τ) ⊆ (fun z => z + y) ⁻¹' N ∧
    (0 < τ → ∃ η' : ℝ → ℂ, ContinuousOn η' (Icc 0 (τ : ℝ)) ∧
      ∀ r ∈ Ioc (0 : ℝ) τ, fwdHull (Ito.rpath w₁) r = fillH (η' '' Icc 0 r)) := by
  have heU : RLC.exitTime V η U ≤ U := min_le_left _ _
  have hτU : (τ : ℝ≥0∞) < U := hτ.trans_le heU
  obtain ⟨t₂, hτt₂, ht₂e⟩ := exists_real_btwn_of_lt hτ
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg τ).trans hτt₂.le
  have ht₂U : ENNReal.ofReal t₂ < U := ht₂e.trans_le heU
  have hag : ∀ r ∈ Icc (0 : ℝ) t₂, Ito.rpath w₁ r = Ito.rpath w₀ r := fun r hr => by
    simp only [Ito.rpath]
    refine hw₁e _ (lt_of_le_of_lt ?_ ht₂e)
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hr.1]
    exact ENNReal.ofReal_le_ofReal hr.2
  have hw₁c : Continuous (Ito.rpath w₁) := hw₁.comp continuous_real_toNNReal
  have hw00 : w₀ 0 = 0 := hp.1
  have hτ0 : (0 : ℝ) ≤ τ := τ.coe_nonneg
  have hw₀cU : ContinuousOn w₀ {s | (s : ℝ≥0∞) < U} := hp.2.2.2.1
  -- the hulls of the two drivers agree up to `t₂`
  have hKeq : ∀ r : ℝ, 0 ≤ r → r < t₂ → fwdHull (Ito.rpath w₁) r = fwdHull (Ito.rpath w₀) r := fun r hr hrt =>
    fwdHull_eq_of_eqOn hr hrt fun s hs => hag s hs
  refine ⟨?_, ⟨t₂, hτt₂, hag⟩, fun i => ?_, fun j => ?_, ?_, fun hτpos => ?_⟩
  · rw [hw₁e 0 (lt_of_le_of_lt (by simp) hτ), hw00]
  · -- left marks
    have h1 := Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive hp ht₂U hτt₂.le i
    have h2 : MartChar.RealFlow.rightImg (fun s => -frozenDrive w₀ t₂ s) (-flowLineXL b J y i) τ =
        MartChar.RealFlow.rightImg (fun s => -Ito.rpath w₁ s) (-flowLineXL b J y i) τ :=
      Supp8.GB6.rightImg_congr hw₁c.neg hτ0 fun r hr => by
        show -frozenDrive w₀ t₂ r = -Ito.rpath w₁ r
        rw [frozenDrive_eq ⟨hr.1, hr.2.trans hτt₂.le⟩, hag r ⟨hr.1, hr.2.trans hτt₂.le⟩]
        rfl
    have h3 : Ito.rpath w₁ τ = w₀ τ := by
      rw [hag τ ⟨hτ0, hτt₂.le⟩]; simp [Ito.rpath]
    rw [h1, h2, geomL, h3]
  · -- right marks
    have h1 := Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp ht₂U hτt₂.le j
    have h2 : MartChar.RealFlow.rightImg (frozenDrive w₀ t₂) (flowLineXR b J y j) τ =
        MartChar.RealFlow.rightImg (Ito.rpath w₁) (flowLineXR b J y j) τ :=
      Supp8.GB6.rightImg_congr hw₁c hτ0 fun r hr => by
        rw [frozenDrive_eq ⟨hr.1, hr.2.trans hτt₂.le⟩, hag r ⟨hr.1, hr.2.trans hτt₂.le⟩]
        rfl
    have h3 : Ito.rpath w₁ τ = w₀ τ := by
      rw [hag τ ⟨hτ0, hτt₂.le⟩]; simp [Ito.rpath]
    rw [h1, h2, geomR, h3]
  · -- the hull closure lies in the chart buffer
    set A : Set ℂ := (fun t => η t - y) '' Icc 0 τ with hA
    set A' : Set ℂ := η '' Icc 0 τ with hA'
    have hKf : IsFilling (fwdHull (Ito.rpath w₁) τ) A := by
      rw [hKeq τ hτ0 hτt₂]
      exact hg.2.2 τ hτU
    have hHP : IsHPHull (fwdHull (Ito.rpath w₁) τ) := isHPHull_fwdHull hw₁c hτ0
    have htr := Sec5.CrossRestart.isFilling_image_add hHP y hKf
    have hηc : ContinuousOn η (Icc 0 τ) := by
      have h := hg.2.1.mono fun t (ht : t ∈ Icc 0 τ) => show (t : ℝ≥0∞) ≤ U from
        (ENNReal.coe_le_coe.2 ht.2).trans hτU.le
      exact (h.add (continuousOn_const (c := (y : ℂ)))).congr fun t _ => by simp
    have hA'c : IsCompact A' := isCompact_Icc.image_of_continuousOn hηc
    have hAA' : ((fun z : ℂ => z + y) '' (A ∩ H)) ∩ H = A' ∩ H := by
      ext z
      simp only [hA, hA', mem_inter_iff, mem_image]
      constructor
      · rintro ⟨⟨w, ⟨⟨t, ht, rfl⟩, -⟩, rfl⟩, hz⟩
        exact ⟨⟨t, ht, by ring⟩, hz⟩
      · rintro ⟨⟨t, ht, rfl⟩, hz⟩
        refine ⟨⟨η t - y, ⟨⟨t, ht, rfl⟩, ?_⟩, by ring⟩, hz⟩
        have := (add_real_mem_H_iff (z := η t - y) y).1 (by simpa using hz)
        exact this
    have hfill' := isFilling_of_inter_H hAA' htr
    have hmemV : ∀ t ∈ Icc (0 : ℝ≥0) τ, η t ∈ V := fun t ht =>
      FlowStopIdentG.mem_of_lt_exitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hτ)
    have hAV : A' ⊆ closure V ∩ {w | 0 ≤ w.im} := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨subset_closure (hmemV t ht), ?_⟩
      have hH := Sec7.IsGeneratingTrace.mem_Hbar hg hw₀cU hw00
        (show ((t : ℝ≥0) : ℝ≥0∞) ≤ U from (ENNReal.coe_le_coe.2 ht.2).trans hτU.le)
      have : (0 : ℝ) ≤ (η t - y).im := hH
      simpa using this
    have hAJ : ∀ w ∈ A', w.im = 0 → w.re ∈ Icc a c := by
      rintro _ ⟨t, ht, rfl⟩ h0
      exact hVa _ (subset_closure (hmemV t ht)) h0
    have hsub := FlowStopIdentCM.subset_shiftHullSet hA'c hAV hAJ hfill'
    have hKH : fwdHull (Ito.rpath w₁) τ ⊆ H := (QuantumZipper.fwdHull_mono (W := Ito.rpath w₁)).2 τ
    have hK'N : (fun z : ℂ => z + y) '' fwdHull (Ito.rpath w₁) τ ⊆ FlowStopIdentCM.shiftHullSet V a c := by
      rintro _ ⟨z, hz, rfl⟩
      exact hsub ⟨⟨z, hz, rfl⟩, (add_real_mem_H_iff y).2 (hKH hz)⟩
    have hclosed : IsClosed (FlowStopIdentCM.shiftHullSet V a c) :=
      (FlowStopIdentCM.isCompact_shiftHullSet hVb a c).isClosed
    intro z hz
    have h1 : z + (y : ℂ) ∈ closure ((fun z : ℂ => z + y) '' fwdHull (Ito.rpath w₁) τ) :=
      image_closure_subset_closure_image (continuous_id.add continuous_const) ⟨z, hz, rfl⟩
    exact hsN (closure_minimal hK'N hclosed h1)
  · -- the trace fills the hulls
    refine ⟨fun s : ℝ => η s.toNNReal - y, ?_, fun r hr => ?_⟩
    · have h := hg.2.1.comp (s := Icc (0 : ℝ) τ) continuous_real_toNNReal.continuousOn
        fun (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ) => show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ U from
          (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hτU.le
      exact h
    · have hr0 : 0 ≤ r := hr.1.le
      have hrU : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < U :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hτU
      have hfil : IsFilling (fwdHull (Ito.rpath w₀) (r.toNNReal : ℝ)) ((fun t => η t - y) '' Icc 0 r.toNNReal) :=
        hg.2.2 r.toNNReal hrU
      rw [Real.coe_toNNReal _ hr0] at hfil
      have hcA : IsCompact ((fun t => η t - y) '' Icc 0 r.toNNReal) := by
        have h := hg.2.1.mono fun t (ht : t ∈ Icc 0 r.toNNReal) => show (t : ℝ≥0∞) ≤ U from
          (ENNReal.coe_le_coe.2 ht.2).trans hrU.le
        exact isCompact_Icc.image_of_continuousOn h
      rw [hKeq r hr0 (hr.2.trans_lt hτt₂), Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hcA hfil,
        image_toNNReal_Icc (fun t => η t - y) hr0]


universe u

/-- **The pathwise data at every stop before the exit time: `CMIStopDataStatement` holds**, with `W₁` the `b`-driver
stopped at the exit time. -/
theorem cmiStopDataStatement : CMIStopDataStatement.{u} := by
  intro κ hκ b J hb N hN V hV hVb hVN a c hVa hsN y θ S _ Q₀ _ Γ U h' 𝓕₀ W₀ VL₀ VR₀ B₀ hC hgen hX
  set e : S → ℝ≥0∞ := fun ω => RLC.exitTime V (Γ ω) (U ω) with he
  refine ⟨LocalExt.stopVal W₀ (fun ω => (e ω : WithTop ℝ≥0)), fun τ hτ hτe => ?_⟩
  filter_upwards [hC.1.ae_isIntegratedSLEPath, hC.1.ae_tendsto_threshold hκ, hgen, hτe] with ω hp hlim hg hτω
  set W₁ := LocalExt.stopVal W₀ (fun ω => (e ω : WithTop ℝ≥0)) with hW₁
  have hτ' : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < e ω := FlowStopIdentCM.coe_untopD_lt hτω
  have hw₁e : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W₁ t ω = W₀ t ω := fun t ht =>
    FlowStopIdentLL.stopVal_of_lt (ζ := e) ht
  have hwc : ContinuousOn (W₀ · ω) {s | (s : ℝ≥0∞) < U ω} := hp.2.2.2.1
  have heU : e ω ≤ U ω := min_le_left _ _
  have hcont : Continuous (W₁ · ω) := by
    rcases eq_top_or_lt_top (e ω) with htop | hfin
    · have hU : U ω = ⊤ := top_le_iff.1 (htop ▸ heU)
      have e1 : (W₁ · ω) = (W₀ · ω) := funext fun t => hw₁e t (by rw [htop]; exact ENNReal.coe_lt_top)
      rw [e1]
      refine continuousOn_univ.1 (hwc.mono fun t _ => ?_)
      show (t : ℝ≥0∞) < U ω
      rw [hU]; exact ENNReal.coe_lt_top
    · set T : ℝ≥0 := (e ω).toNNReal with hTdef
      have hT : (T : ℝ≥0∞) = e ω := ENNReal.coe_toNNReal hfin.ne
      have hT0 : 0 < T := by
        have h1 : (0 : ℝ≥0∞) < e ω := lt_of_le_of_lt bot_le hτ'
        rw [← hT] at h1
        exact_mod_cast h1
      have hS : (fun ω => (e ω : WithTop ℝ≥0)) ω = (T : WithTop ℝ≥0) := hT.symm
      have hc : ContinuousOn (W₀ · ω) (Iio T) := hwc.mono fun s hs => by
        show (s : ℝ≥0∞) < U ω
        exact lt_of_lt_of_le (by rw [← hT]; exact_mod_cast hs) heU
      obtain ⟨c₁, hlimT⟩ : ∃ c₁, Tendsto (W₀ · ω) (𝓝[<] T) (𝓝 c₁) := by
        rcases heU.lt_or_eq with hlt | heq
        · have hTU : (T : ℝ≥0∞) < U ω := hT ▸ hlt
          refine ⟨W₀ T ω, ?_⟩
          have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < U ω} :=
            isOpen_lt ENNReal.continuous_coe continuous_const
          exact ((hwc T hTU).continuousAt (hopen.mem_nhds hTU)).tendsto.mono_left nhdsWithin_le_nhds
        · obtain ⟨w₀, vL₀, vR₀, hl, -⟩ := hlim T hT0 (hT.trans heq)
          exact ⟨w₀, (continuous_fst.tendsto _).comp hl⟩
      exact FlowStopIdentLL.continuous_stopVal_of_tendsto hT0 hS hc hlimT
  obtain ⟨h0, ht₂, hL, hR, hK, hη⟩ := stopPathData_det hVb hVa hsN hp hg hcont hw₁e hτ'
  exact ⟨hcont, h0, ht₂, hL, hR, hK, hη⟩


/-- **The explicit-shift (L1) from the converse assembly alone** (the pathwise data are proved). -/
theorem flowLineStopIdentCMIStatement_of_converse (h2 : CMIConverseStatement.{u}) :
    FlowLineStopIdentCMIStatement.{u} :=
  flowLineStopIdentCMIStatement_of_inputs cmiStopDataStatement h2

end FlowStopIdentCMI

end Restart

/-- **Lemma G3 in the source's form from the converse assembly** (`CMIConverseStatement`), the WFS kernel target for
`0 < κ < 4` and Theorems 1.2 (param) / 1.3. -/
theorem RLC.g3SourceStatement_of_CMIConverse (h2 : Restart.FlowStopIdentCMI.CMIConverseStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    RLC.G3SourceStatement.{0} :=
  RLC.g3SourceStatement_of_CMI (Restart.FlowStopIdentCMI.flowLineStopIdentCMIStatement_of_converse h2) hT h12p h13

end InteractingSLE
