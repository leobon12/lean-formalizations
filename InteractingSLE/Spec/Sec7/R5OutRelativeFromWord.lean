import InteractingSLE.Spec.Sec7.R5OutSelfWire

/-! # The deterministic relative-cover binder from the source phase word -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out
open WholeField PocketWordPerQ PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketCoupling
  R7Outer R7Leaves StripPocketConfig RefWire HOuter OuterCont Sec6 PocketMarks
universe u

/-- The unchanged relative-cover interface follows from the proved source
phase word, using a current-chart reference at every deterministic capacity. -/
theorem r7OuterRelativeCoverMRemaining_of_phaseWord {k rL rR c c' : ℝ}
    (hWord : R7OuterPhaseWordMRemaining.{u} k rL rR c c') :
    R7OuterRelativeCoverMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hPWord, hIWord⟩ := hWord P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD
    u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  exact ⟨twoSeedRelativeCoverInput_of_phaseWord_outer hV.R_cont hV.L_cont hV.R_meas hV.L_meas hV.η_meas hGp
      (fun ω hω => hcfgP ω hω.1 hω.2) hPWord,
    twoSeedRelativeCoverInputInf_of_phaseWord_outer hV.R_cont hV.L_cont hV.R_meas hV.L_meas hV.η_meas hG0
      hcfgI' hIWord⟩

end InteractingSLE.Sec7.R5Out
