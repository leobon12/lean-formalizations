/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfChartTransfer
import InteractingSLE.Spec.Sec5.Lemma47AngleHit

/-!
# Lemma 4.7: the killed image word of the counterflow is not killed

Packet PROVE-CFCHART (PROVE-CFGIVEN §3, step 3). On the glued space the counterflow's image word in the chart of the
flow prefix is killed at its first contact with the prefix (`qT`). Almost surely `qT = ∞`: the restart extension of
PROVE-CFRESTART5 gives a continuous transient image trace on `[0, ∞)` agreeing with the killed one before `qT` and
never meeting `ℝ ∖ {0}`; if the capacity clock stayed bounded on the pre-contact interval, the image of the
counterflow would converge to a point of `ℍ ∪ {0}`, which pulls back to a point off the prefix — against the first
contact (or the transience) of the counterflow. This is the first half of the proof of
`CrossRestart.KernelQ.isFirstHitQ_of_imgFull`, stated separately (`not_bddAbove_of_imgFull`).

## Main results

* `not_bddAbove_of_imgFull` (deterministic);
* `ae_qT_eq_top_glueGood47`: `qT = ∞` almost surely on the glued space (good set `glueGood47`), from Zhan's Part A;
* `qT_congr_of_mem`, **`ae_qT_eq_top`**: the same for any good set of full glued measure.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfChart

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar WholeField CrossCond.Theta
open Prop49Exit Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Lemma47Angle

/-! ### The bounded-clock alternative is impossible (deterministic) -/

section Det

variable {Wβ : ℝ → ℝ} {α : ℝ → ℂ} {q : ℝ}

/-- **The capacity clock of the image is unbounded on the pre-contact interval** (the bounded-clock half of
`CrossRestart.KernelQ.isFirstHitQ_of_imgFull`): with the hypotheses of that lemma except the flow-line ones, the
clock `a` is unbounded on the pre-contact times of the counterflow `α` with `G = R(K_q)`. -/
theorem not_bddAbove_of_imgFull (hW : Continuous Wβ)
    (hW0 : Wβ 0 = 0) (hq : 0 < q) (hGc : IsClosed (negInv '' fwdHull Wβ q))
    (hαc : Continuous α) (hα0 : α 0 = 0) (hαH : ∀ v, 0 < v → α v ∈ H)
    (hαtr : Tendsto (fun v => ‖α v‖) atTop atTop)
    {a : ℝ → ℝ≥0} (ha : MonotoneOn a (preContact α (negInv '' fwdHull Wβ q)))
    {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) (hγR : ∀ (r : ℝ≥0) (x : ℝ), x ≠ 0 → γ r ≠ x)
    (hagree : ∀ u ∈ preContact α (negInv '' fwdHull Wβ q), 0 < u → γ (a u) = revChart Wβ q (α u)) :
    ¬ BddAbove (a '' preContact α (negInv '' fwdHull Wβ q)) := by
  classical
  set G := negInv '' fwdHull Wβ q with hGdef
  set P := preContact α G with hPdef
  have hGH : G ⊆ H := image_negInv_subset_H fun z hz => hz.1
  have h0G : α 0 ∉ G := fun h => by rw [hα0] at h; exact ne_zero_of_mem_H (hGH h) rfl
  obtain ⟨δ, hδ, hδP⟩ := exists_pos_mem_preContact hαc hGc h0G
  have hPne : P.Nonempty := ⟨δ, hδP⟩
  have hPmem : ∀ u ∈ P, 0 < u → α u ∈ H \ G := fun u hu hu0 => ⟨hαH u hu0, hu.2 u ⟨hu.1, le_rfl⟩⟩
  -- a filter running up the pre-contact interval
  obtain ⟨L, hLne, hLP, hLS, hcase⟩ : ∃ L : Filter ℝ, L.NeBot ∧ (∀ᶠ u in L, u ∈ P ∧ 0 < u) ∧
      (∀ S ∈ P, ∀ᶠ u in L, S ≤ u) ∧
      ((∃ u₀ : ℝ, 0 < u₀ ∧ α u₀ ∈ G ∧ L = 𝓝[<] u₀ ∧ (∀ u, 0 < u → u < u₀ → u ∈ P)) ∨
        Tendsto (fun u => ‖α u‖) L atTop) := by
    by_cases hbdd : BddAbove P
    · set u₀ := sSup P with hu₀def
      have hnot := sSup_notMem_preContact hαc hGc hbdd
      have hu₀G := mem_of_sSup_preContact hαc hGc hPne hbdd
      have hu₀ : 0 < u₀ := lt_of_lt_of_le hδ (le_csSup hbdd hδP)
      have hlow : ∀ u, 0 ≤ u → u < u₀ → u ∈ P := fun u hu0 hu => by
        obtain ⟨u', hu', huu'⟩ := exists_lt_of_lt_csSup hPne hu
        exact mem_preContact_of_le hu' hu0 huu'.le
      refine ⟨𝓝[<] u₀, inferInstance, ?_, fun S hS => ?_,
        Or.inl ⟨u₀, hu₀, hu₀G, rfl, fun u h0 h1 => hlow u h0.le h1⟩⟩
      · filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
        exact ⟨hlow u hu.1.le hu.2, hu.1⟩
      · have hSu : S < u₀ := lt_of_le_of_ne (le_csSup hbdd hS) fun h => hnot (show u₀ ∈ P by rw [← h]; exact hS)
        filter_upwards [Ioo_mem_nhdsLT hSu] with u hu using hu.1.le
    · have hall : ∀ u, 0 ≤ u → u ∈ P := fun u hu => by
        rw [not_bddAbove_iff] at hbdd
        obtain ⟨u', hu', huu'⟩ := hbdd u
        exact mem_preContact_of_le hu' hu huu'.le
      refine ⟨atTop, inferInstance, ?_, fun S _ => eventually_ge_atTop S, Or.inr hαtr⟩
      filter_upwards [eventually_gt_atTop 0] with u hu using ⟨hall u hu.le, hu⟩
  -- the path has no limit off `G` along `L`
  have hnolim : ∀ z : ℂ, z ∉ G → ¬ Tendsto α L (𝓝 z) := by
    intro z hz hlim
    rcases hcase with ⟨u₀, -, hu₀G, rfl, -⟩ | htr
    · have h2 : Tendsto α (𝓝[<] u₀) (𝓝 (α u₀)) := hαc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact hz (tendsto_nhds_unique hlim h2 ▸ hu₀G)
    · exact not_tendsto_atTop_of_tendsto_nhds hlim.norm htr
  have hΨ : ∀ᶠ u in L, revChart Wβ q (α u) ∈ H ∧ γ (a u) = revChart Wβ q (α u) ∧ α u ∈ H \ G := by
    filter_upwards [hLP] with u hu
    exact ⟨revChart_mem_H hW hq.le (hPmem u hu.1 hu.2), hagree u hu.1 hu.2, hPmem u hu.1 hu.2⟩
  intro hab
  set S := sSup (a '' P) with hSdef
  have haS : Tendsto (fun u => a u) L (𝓝 S) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hbu₁⟩ := exists_lt_of_lt_csSup (hPne.image a) hb
      filter_upwards [hLP, hLS u₁ hu₁] with u hu hu₁u
      exact lt_of_lt_of_le hbu₁ (ha hu₁ hu.1 hu₁u)
    · filter_upwards [hLP] with u hu
      exact lt_of_le_of_lt (le_csSup hab ⟨u, hu.1, rfl⟩) hb
  have hγS : Tendsto (fun u => revChart Wβ q (α u)) L (𝓝 (γ S)) :=
    ((hγc.tendsto S).comp haS).congr' (hΨ.mono fun u hu => hu.2.1)
  have hHlim : Tendsto (fun u => revChart Wβ q (α u)) L (𝓝[H] (γ S)) :=
    tendsto_nhdsWithin_iff.2 ⟨hγS, hΨ.mono fun u hu => hu.1⟩
  have him : 0 ≤ (γ S).im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hγS) (hΨ.mono fun u hu => le_of_lt hu.1)
  rcases him.lt_or_eq with hpos | hzero
  · have hc := (continuousOn_revChartInv hW hW0 hq.le) (γ S) hpos
    have h1 := hc.tendsto.comp hHlim
    have h2 : Tendsto α L (𝓝 (revChartInv Wβ q (γ S))) :=
      h1.congr' (hΨ.mono fun u hu => revChartInv_revChart hW hW0 hq.le hu.2.2)
    exact hnolim _ (revChartInv_mem hW hW0 hq.le hpos).2 h2
  · have hreal : γ S = ((γ S).re : ℂ) := Complex.ext rfl (by simp [← hzero])
    have hre0 : (γ S).re = 0 := by
      by_contra hne
      exact hγR S _ hne hreal
    have hS0 : γ S = 0 := by rw [hreal, hre0]; simp
    rw [hS0] at hHlim
    have h1 := (GlueImg.tendsto_revChartInv_nhdsWithin_zero hW hW0 hq.le).comp hHlim
    have h2 : Tendsto α L (𝓝 0) :=
      h1.congr' (hΨ.mono fun u hu => revChartInv_revChart hW hW0 hq.le hu.2.2)
    exact hnolim 0 (fun h => ne_zero_of_mem_H (hGH h) rfl) h2

end Det

/-! ### The killing time only depends on the good set through membership -/

section Congr

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0}

theorem qT_congr_of_mem {E₁ E₂ : Set (Ω × HistorySpace 0 0)} {p : Ω × HistorySpace 0 0} (h₁ : p ∈ E₁)
    (h₂ : p ∈ E₂) : qT W VL VR ζ s E₁ p = qT W VL VR ζ s E₂ p := by
  simp only [qT, qgCurve, qgPre, h₁, h₂, ↓reduceIte]

end Congr

/-! ### Almost surely the killing time is infinite -/

section Main

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The killing time of the counterflow's image word is almost surely infinite** (good set `glueGood47`; the
restart extension of PROVE-CFRESTART5 and `not_bddAbove_of_imgFull`). -/
theorem ae_qT_eq_top_glueGood47 (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) p = ⊤ := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hNR := CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA_of_clearance.{u} hA
  have hae := ae_isGood47_angle hNR hκ hκ4 hF h44 hθb hC hcf hlaw k hk
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have hX := hC.2.2.2.1
  have hxo := isOrderedForceWord_qx_angle κ θ ρL ρR xL xR
  obtain ⟨-, hK, hWa, hVLa, hVRa, -, -, -, -, hζq⟩ :=
    filtClauses47 (μ := μ) (s := s) hX hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hs hae
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, Bi, hB, hBc, hEnt⟩ :=
    exists_isWordEntrance_q_angle hκ hκ4 hF h44 hθb hC hcf hlaw k hk hae hs
  set 𝓖 := qFilt μ (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E with h𝓖
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × Ω₀ | (q : ℝ≥0∞) < (qT W VL VR ζ s E p.1 : ℝ≥0∞)} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hthr : ∀ᵐ p ∂(μ.prod P₀), ¬ ForceWord.ThresholdCondition (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
      (qW W VL VR ζ s E 0 p.1) (fun i => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i 0 p.1)
      (fun j => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j 0 p.1) := by
    have h1 : ∀ᵐ p ∂μ, ¬ ForceWord.ThresholdCondition (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
        (qW W VL VR ζ s E 0 p) (fun i => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i 0 p)
        (fun j => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j 0 p) := by
      filter_upwards [ae_mem_glueGood47 hae] with p hp
      exact not_threshold_q_angle hκ hθb hEg hp hs
    exact Measure.quasiMeasurePreserving_fst.ae h1
  -- the seed marks `0⁻`, `0⁺` of the counterflow word
  set i₀L : Fin (flowLineNL (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0) := ⟨0, Nat.succ_pos _⟩ with hi₀L
  set i₀R : Fin (flowLineNR (Sec7.StripSysField.counterflowData κ (bDataT ρL ρR xL xR θ κ))
      (Sec7.StripSysField.counterflowJumps (Cond44Ref.forceJumpFinset xL xR)) 0) := ⟨0, Nat.succ_pos _⟩ with hi₀R
  have hx₀L : qxLT κ θ ρL ρR xL xR i₀L = 0 := rfl
  have hx₀R : qxRT κ θ ρL ρR xL xR i₀R = 0 := rfl
  have hk' : 0 < 16 / κ := by positivity
  have hR := Prop49Exit.ae_restart_code (P := μ.prod P₀) (𝓘 := WholeField.prodFiltration 𝓖 𝓦) hk' hB hBc
    (W := fun t p => qW W VL VR ζ s E t p.1) (VL := fun i t p => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i t p.1)
    (VR := fun j t p => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j t p.1)
    (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
    (fun j => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) (T := fun p => (qT W VL VR ζ s E p.1 : ℝ≥0∞)) hTq'
    (fun p => (isKilledCurve_qgCurve hEg p.1).zero_lt_kcLife)
    (measurableSet_avCode47 (Fin.castSucc i₀L) (Fin.castSucc i₀R))
    (fun st hsep hFo => codeLaw_compl_avCode47_eq_zero hA hκ hκ4 (prefix_iwL_angle hκ hκ4 hθ₂ hθb)
      (prefix_iwR_angle hκ hκ4 hθ₁ hθb) _ _ st hsep hFo)
    hEnt (fun p t ht htT i => hK.sepL p.1 t ht htT i) (fun p t ht htT j => hK.sepR p.1 t ht htT j) hthr
  have h2 := Measure.ae_ae_of_ae_prod hR
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have htrans := cfGlueAE_mem_goodTransSet_angle.{u} θ hA κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B
    ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [h2, ae_mem_glueGood47 hae, htrans] with p hpR hpE hpT
  obtain ⟨ω₀, hpω⟩ := hpR.exists
  have hg := hEg p hpE
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  -- a positive rational image time before the killing
  obtain ⟨S, hSP, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  have hcS : 0 < capClock (qgCurve W s E p) S := by
    rw [← hγ.capClock_zero]; exact hγ.strictMonoOn_capClock hγ.zero_mem hSP hS0
  obtain ⟨q', hq'0, hq'S⟩ := exists_rat_btwn hcS
  have hq'0' : (0 : ℚ) < q' := by exact_mod_cast hq'0
  set r : ℝ≥0 := (q' : ℝ).toNNReal with hrdef
  have hr0 : 0 < r := Real.toNNReal_pos.2 hq'0
  have hrT : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hq'S.le)) (hγ.lt_kcLife hSP)
  obtain ⟨x, hxC, hxS, -, hxag⟩ := hpω q' hq'0' hrT
  -- the restarted canonical solution: a transient trace with real values between the seed marks
  obtain ⟨hxF, -⟩ := mem_cRelF_iff.2 hxC
  obtain ⟨hcwc, hcw0⟩ := Prop49Exit.cw_props_of_mem_cRelF hxF
  obtain ⟨hζx, htrSet, hAvQ⟩ := (mem_avCode47_iff hxC).1 hxS
  rw [hζx] at hcwc
  have hcwc' : Continuous (cw x) := continuousOn_univ.1 (hcwc.mono fun t _ => ENNReal.coe_lt_top)
  obtain ⟨η, hη, hηtr⟩ := (mem_traceSet_iff hcwc'.continuousOn hcw0 (fun _ h => absurd h (lt_irrefl _))).1 htrSet
  have heqη : ∀ t, LP.traceAt t (cw x) = η t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hη hcwc'.continuousOn hcw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have htrc : Continuous fun t => LP.traceAt t (cw x) := by
    have e : (fun t => LP.traceAt t (cw x)) = η := funext heqη
    rw [e]; exact hηc
  -- a frozen trace of the killed word beyond `r`
  obtain ⟨S', hS'P, hrS'⟩ := hγ.lt_kcLife_iff_exists.1 hrT
  have hcS'0 : 0 ≤ capClock (qgCurve W s E p) S' := hγ.capClock_nonneg hS'P
  obtain ⟨V, α', hV, hV0, hα', hEqV, hα'H⟩ := hγ.exists_frozenTrace (hγ.lt_kcLife hS'P)
  rw [Real.coe_toNNReal _ hcS'0] at hEqV hα'H
  have hL := qVL_seed_sub (x := qxLT κ θ ρL ρR xL xR) hpE hx₀L hrT hV hEqV hrS'.le
  have hR' := qVR_seed_sub (x := qxRT κ θ ρL ρR xL xR) hpE hx₀R hrT hV hEqV hrS'.le
  have hηR : ∀ t (y : ℝ), η t = y → chartAL V r ≤ y ∧ y ≤ chartAR V r := by
    intro t y hy
    have := avoid_of_avQ47 hAvQ htrc t y (by rw [heqη]; exact hy)
    simp only [stAt] at this
    rw [hL, hR'] at this
    exact this
  -- the full image trace
  have hwc := hK.contW p
  have hw0 := hK.w_zero p
  obtain ⟨Γ, hΓc, hΓγ, hΓR, hΓtr⟩ := fullTrace_of_restart (T := (qT W VL VR ζ s E p : ℝ≥0∞)) hwc hw0
    (γ := qTr W VL VR ζ s E p) (fun s' hs' => by
      obtain ⟨T', hs'T', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs'
      exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc (isGeneratingTrace_qTr hEg p hT')
        (hwc.mono fun t ht => lt_trans ht hT') hw0 hs'T')
    (fun t ht0 ht => hγ.kcTr_mem_H ht0 ht) hr0 hrT hcwc' hcw0 (fun t ht => (hxag t ht).1) hη (hηtr rfl) hηR
    (fun y h1 h2 => extendFrom_base_q (c := capClock (qgCurve W s E p) S') hrS' hV hV0 hα'
      (fun u hu => hα'H u ⟨hu.1, hu.2.trans hrS'.le⟩) hEqV y h1 h2)
  -- the clock is unbounded on the pre-contact interval, so the killing time is infinite
  have hpre : preContact (histLine p.2) (negInv '' fwdHull (fDrv W p) s) = qgPre W VL VR ζ s E p := by
    rw [qgPre_of_mem hpE, qObs_of_good hg]
  have hGc : IsClosed (negInv '' fwdHull (fDrv W p) s) := by
    rw [← qObs_of_good (q := s) hg]; exact isClosed_qObs hg
  have hnb := not_bddAbove_of_imgFull (α := histLine p.2) (continuous_fDrv hg) (fDrv_zero hg) (NNReal.coe_pos.2 hs) hGc
    ((Prop49Exit.continuous_traceAt_of_mem_goodCfSet hg.2.2.1.1).comp continuous_real_toNNReal)
    (histLine_zero hg) (fun v hv => histLine_mem_H hg hv) (GlueCond.tendsto_histLine_of_mem_goodTransSet hpT)
    (a := fun u => (capClock (qgCurve W s E p) u).toNNReal) ?_ hΓc hΓR ?_
  · rw [hpre] at hnb
    by_contra hT
    obtain ⟨T, hT'⟩ := WithTop.ne_top_iff_exists.1 hT
    refine hnb ⟨T, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hlt : (((capClock (qgCurve W s E p) u).toNNReal : ℝ≥0) : WithTop ℝ≥0) < qT W VL VR ζ s E p :=
      hγ.lt_kcLife hu
    rw [← hT'] at hlt
    exact (WithTop.coe_lt_coe.1 hlt).le
  · rw [hpre]
    intro u hu v hv huv
    exact Real.toNNReal_le_toNNReal (hγ.strictMonoOn_capClock.monotoneOn hu hv huv)
  · rw [hpre]
    intro u hu hu0
    rw [hΓγ _ (hγ.lt_kcLife hu), qTr_capClock hEg hpE hu, imgCurve_of_pos hu0]


/-- **The killing time of the counterflow's image word is almost surely infinite**, for any good set `E` of full
glued measure. -/
theorem ae_qT_eq_top (hθ₁ : -(π / 2) ≤ θ) (hθ₂ : θ ≤ π / 2)
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) (E : Set (Ω × HistorySpace 0 0))
    (hEae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ E) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      qT W VL VR ζ s E p = ⊤ := by
  have hNR := CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA_of_clearance.{u} hA
  have hae := ae_isGood47_angle hNR hκ hκ4 hF h44 hθb hC hcf hlaw k hk
  filter_upwards [ae_qT_eq_top_glueGood47 hθ₁ hθ₂ hA hκ hκ4 hF h44 hθb hC hcf hlaw k hk hs, hEae,
    ae_mem_glueGood47 hae] with p h1 h2 h3
  rw [qT_congr_of_mem h2 h3]
  exact h1

end Main

end InteractingSLE.Sec5.CfChart
