/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6NestGeom
import InteractingSLE.Spec.Sec7.SideVisR7
import InteractingSLE.Spec.Sec7.R7OuterConfig
import InteractingSLE.Spec.Sec7.R7LeavesExtremal

/-!
# R.6's nested pockets on every R.7 configuration

PROVE-R6-NESTED. Supplement pp. 476–477: on an outer two-seed pocket `C` of Theorem R.7, at a certified visit (the
tip is in `C` and off both certified frontiers) the tip lies in a nested pocket `U ⊂ C` whose walls are the inner
pair

* `β_R` instead of the right arm when the right arm is outer (`d < r_L`), the right arm otherwise;
* `β_L` instead of the left arm when the left arm is outer (`d < r_R`), the left arm otherwise.

So `U` is the `β_R`–`γ` pocket of a mixed pocket and the extremal `β_R`–`β_L` pocket for two outer arms; its seed
weights `(min(r_L, d), min(r_R, d))` are in Aux. 122's bounded sector. `U` is a change pocket at a **rational**
parameter, so these pockets form a countable family (`nestEvent`).

`ae_exists_nestEvent(Inf)`: almost surely, every certified visit at the time `t` lies in `nestEvent … s t` for some
rational `s`. Inputs: the R.7 configuration and versions; `Prop55HalfPlaneStatement` (R48-safe; it orders the inner
pairs of the mixed shapes). R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Nest

open WangWu PocketCoord PocketJordan Lemma71I R7Outer

section Defs

variable {Ω : Type*}

open Classical in
/-- **The inner right wall** of R.6: the certified frontier `β_R` when the right arm is outer (`d < r_L`, i.e.
`θ_R < −π/2`), the right arm `R` otherwise (also used for the lifetimes and Borel maps of the lines). -/
def innerRight {X : Sort*} (k rL : ℝ) (R βR : X) : X := if k / 2 - 4 < rL then βR else R

open Classical in
/-- **The inner left wall** of R.6: the certified frontier `β_L` when the left arm is outer (`d < r_R`, i.e.
`θ_L > π/2`), the left arm `L` otherwise. -/
def innerLeft {X : Sort*} (k rR : ℝ) (L βL : X) : X := if k / 2 - 4 < rR then βL else L

/-- **The nested-pocket event** at the original time `t`: the inner pair `(R', L')` is in global order with change
parameter `rt s`, the tip lies in its change pocket (counterflow chart), and that pocket is contained in the outer
pocket `C = cfPocket R L r`. -/
def nestEvent (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (R' L' : Ω → ℝ≥0 → ℂ) (s : ℚ) (t : ℝ) : Set Ω :=
  {ω | IsChangeConfig (R' ω) (L' ω) (StripSys.rt s) ∧ η ω t ∈ cfPocket (R' ω) (L' ω) (StripSys.rt s) ∧
    cfPocket (R' ω) (L' ω) (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r}

end Defs

section Cover

open R7Leaves

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- An order of simple proper curves (`β` in the closed left side of `γ`) keeps `β` off the right side of `γ`. -/
theorem disjoint_rightSideOf_of_closedLeftSide {γ β : ℝ≥0 → ℂ} (hγ : IsSimpleProper γ)
    (hβ : range β ⊆ closedLeftSide γ) : Disjoint (range β) (rightSideOf (range γ)) :=
  disjoint_rightSideOf_of_subset_closedLeftSide hγ.isProperCurve hγ.2.2.1 hβ

/-- **Every certified visit lies in a nested inner pocket** (supplement pp. 476–477), on every R.7 configuration
(bounded outer pocket): almost surely, if the counterflow is complete and the walls form a change configuration, a
certified visit at the original time `t` lies in `nestEvent` of the inner pair for some rational parameter. -/
theorem ae_exists_nestEvent (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hL : -2 < rL) (hR : -2 < rR) (hc : 0 ≤ c) (hc' : 0 ≤ c') [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) (r : ℝ≥0) (t : ℝ) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → IsChangeConfigInc (R ω) (L ω) r → ω ∈ SideVis.visitEvent R L r η βR βL t →
      ∃ s : ℚ, ω ∈ nestEvent R L r η (innerRight k rL R βR) (innerLeft k rR L βL) s t := by
  have hRβL : ∀ᵐ ω ∂P, range (βL ω) ⊆ closedLeftSide (αR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
      (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL
  have hβRL : ∀ᵐ ω ∂P, range (αL ω) ⊆ closedLeftSide (βR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
      (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL
  filter_upwards [hcfg.regular, hcfg.order, hcfg.avoid, hV.R_ae, hV.L_ae, hV.η_trace, hRβL, hβRL] with
    ω hreg hord havoid hRe hLe htr h1 h2 hζ hinc hvis
  obtain ⟨hαRp, hβRp, hβLp, hαLp, -⟩ := hreg
  obtain ⟨⟨htI, htC⟩, hβ⟩ := hvis
  have ht0 : 0 ≤ t := (Real.sInf_nonneg fun _ hu => hu.1).trans htI.1.le
  have hav := havoid hζ (fun s : ℝ≥0 => η ω s) htr t.toNNReal
  rw [Real.coe_toNNReal t ht0] at hav
  set z := negInv (η ω t) with hz
  have hRp : IsSimpleProper (R ω) := hRe ▸ hαRp
  have hLp : IsSimpleProper (L ω) := hLe ▸ hαLp
  have hcfgRL : IsChangeConfig (R ω) (L ω) r :=
    ⟨hinc.right, hinc.left, by rw [hRe, hLe]; exact disjoint_rightSideOf_of_closedLeftSide hαRp hord.2.1,
      hinc.pos, hinc.off⟩
  have hzC : z ∈ changePocket (R ω) (L ω) r := mem_cfPocket_iff.1 htC
  obtain ⟨⟨hzH, hzRL⟩, hzR, hzL⟩ :=
    (Lemma71Pin.isBetweenPt_iff hRp hLp).1 (isBetweenPt_of_mem_changePocket hcfgRL hzC)
  have key : ∀ {R' L' : ℝ≥0 → ℂ}, IsSimpleProper R' → IsSimpleProper L' →
      Disjoint (range L') (rightSideOf (range R')) →
      (∀ w ∈ range (R ω), w ∈ H → w ∈ rightSideOf (range R') ∪ range R') →
      (∀ w ∈ range (L ω), w ∈ H → w ∈ leftSideOf (range L') ∪ range L') →
      z ∉ range R' ∪ range L' → z ∉ rightSideOf (range R') → z ∉ leftSideOf (range L') →
      ∃ s : ℚ, IsChangeConfig R' L' (StripSys.rt s) ∧ η ω t ∈ cfPocket R' L' (StripSys.rt s) ∧
        cfPocket R' L' (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r := by
    intro R' L' hR' hL' hord' hRout hLout hz' hzR' hzL'
    obtain ⟨s, -, hs, hmem, hsub⟩ :=
      exists_rat_nested_cfPocket hinc hR' hL' hord' hRout hLout htC hz' hzR' hzL'
    exact ⟨s, hs, hmem, hsub⟩
  have hRout : k / 2 - 4 < rL → ∀ w ∈ range (R ω), w ∈ H → w ∈ rightSideOf (range (βR ω)) ∪ range (βR ω) :=
    fun hd w hw _ => (hord.2.2.1 ((R7.d_lt_rL_iff hk4).1 hd)).1 (hRe ▸ hw)
  have hLout : k / 2 - 4 < rR → ∀ w ∈ range (L ω), w ∈ H → w ∈ leftSideOf (range (βL ω)) ∪ range (βL ω) :=
    fun hd w hw _ => (hord.2.2.2.1 ((R7.d_lt_rR_iff hk4).1 hd)).1 (hLe ▸ hw)
  show ∃ s : ℚ, IsChangeConfig (innerRight k rL R βR ω) (innerLeft k rR L βL ω) (StripSys.rt s) ∧
    η ω t ∈ cfPocket (innerRight k rL R βR ω) (innerLeft k rR L βL ω) (StripSys.rt s) ∧
    cfPocket (innerRight k rL R βR ω) (innerLeft k rR L βL ω) (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r
  by_cases hdL : k / 2 - 4 < rL <;> by_cases hdR : k / 2 - 4 < rR <;>
    simp only [innerRight, innerLeft, hdL, hdR, ↓reduceIte]
  · exact key hβRp hβLp (disjoint_rightSideOf_of_closedLeftSide hβRp hord.1) (hRout hdL) (hLout hdR) hβ
      (fun h' => hav (Or.inl h')) (fun h' => hav (Or.inr h'))
  · exact key hβRp hLp (by rw [hLe]; exact disjoint_rightSideOf_of_closedLeftSide hβRp h2) (hRout hdL)
      (fun w hw _ => Or.inr hw) (fun h' => h'.elim (fun h'' => hβ (Or.inl h'')) (fun h'' => hzRL (Or.inr h'')))
      (fun h' => hav (Or.inl h')) hzL
  · exact key hRp hβLp (by rw [hRe]; exact disjoint_rightSideOf_of_closedLeftSide hαRp h1)
      (fun w hw _ => Or.inr hw) (hLout hdR)
      (fun h' => h'.elim (fun h'' => hzRL (Or.inl h'')) (fun h'' => hβ (Or.inr h''))) hzR
      (fun h' => hav (Or.inr h'))
  · exact key hRp hLp hcfgRL.ord (fun w hw _ => Or.inr hw) (fun w hw _ => Or.inr hw) hzRL hzR hzL

/-- **Every certified visit lies in a nested inner pocket** (supplement pp. 476–477), on every R.7 configuration
(pocket opening at the flow seed): almost surely, if the counterflow is complete and the walls form a change
configuration, a certified visit at the original time `t` lies in `nestEvent` of the inner pair for some rational
parameter. -/
theorem ae_exists_nestEventInf (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hL : -2 < rL) (hR : -2 < rR) (hc : 0 ≤ c) (hc' : 0 ≤ c') [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) (r : ℝ≥0) (t : ℝ) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → IsChangeConfigInc (R ω) (L ω) r → ω ∈ SideVis.visitEventInf R L r η βR βL t →
      ∃ s : ℚ, ω ∈ nestEvent R L r η (innerRight k rL R βR) (innerLeft k rR L βL) s t := by
  have hRβL : ∀ᵐ ω ∂P, range (βL ω) ⊆ closedLeftSide (αR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
      (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL
  have hβRL : ∀ᵐ ω ∂P, range (αL ω) ⊆ closedLeftSide (βR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
      (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL
  filter_upwards [hcfg.regular, hcfg.order, hcfg.avoid, hV.R_ae, hV.L_ae, hV.η_trace, hRβL, hβRL] with
    ω hreg hord havoid hRe hLe htr h1 h2 hζ hinc hvis
  obtain ⟨hαRp, hβRp, hβLp, hαLp, -⟩ := hreg
  obtain ⟨⟨htI, htC⟩, hβ⟩ := hvis
  have ht0 : 0 ≤ t := (Real.sInf_nonneg fun _ hu => hu.1).trans htI.le
  have hav := havoid hζ (fun s : ℝ≥0 => η ω s) htr t.toNNReal
  rw [Real.coe_toNNReal t ht0] at hav
  set z := negInv (η ω t) with hz
  have hRp : IsSimpleProper (R ω) := hRe ▸ hαRp
  have hLp : IsSimpleProper (L ω) := hLe ▸ hαLp
  have hcfgRL : IsChangeConfig (R ω) (L ω) r :=
    ⟨hinc.right, hinc.left, by rw [hRe, hLe]; exact disjoint_rightSideOf_of_closedLeftSide hαRp hord.2.1,
      hinc.pos, hinc.off⟩
  have hzC : z ∈ changePocket (R ω) (L ω) r := mem_cfPocket_iff.1 htC
  obtain ⟨⟨hzH, hzRL⟩, hzR, hzL⟩ :=
    (Lemma71Pin.isBetweenPt_iff hRp hLp).1 (isBetweenPt_of_mem_changePocket hcfgRL hzC)
  have key : ∀ {R' L' : ℝ≥0 → ℂ}, IsSimpleProper R' → IsSimpleProper L' →
      Disjoint (range L') (rightSideOf (range R')) →
      (∀ w ∈ range (R ω), w ∈ H → w ∈ rightSideOf (range R') ∪ range R') →
      (∀ w ∈ range (L ω), w ∈ H → w ∈ leftSideOf (range L') ∪ range L') →
      z ∉ range R' ∪ range L' → z ∉ rightSideOf (range R') → z ∉ leftSideOf (range L') →
      ∃ s : ℚ, IsChangeConfig R' L' (StripSys.rt s) ∧ η ω t ∈ cfPocket R' L' (StripSys.rt s) ∧
        cfPocket R' L' (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r := by
    intro R' L' hR' hL' hord' hRout hLout hz' hzR' hzL'
    obtain ⟨s, -, hs, hmem, hsub⟩ :=
      exists_rat_nested_cfPocket hinc hR' hL' hord' hRout hLout htC hz' hzR' hzL'
    exact ⟨s, hs, hmem, hsub⟩
  have hRout : k / 2 - 4 < rL → ∀ w ∈ range (R ω), w ∈ H → w ∈ rightSideOf (range (βR ω)) ∪ range (βR ω) :=
    fun hd w hw _ => (hord.2.2.1 ((R7.d_lt_rL_iff hk4).1 hd)).1 (hRe ▸ hw)
  have hLout : k / 2 - 4 < rR → ∀ w ∈ range (L ω), w ∈ H → w ∈ leftSideOf (range (βL ω)) ∪ range (βL ω) :=
    fun hd w hw _ => (hord.2.2.2.1 ((R7.d_lt_rR_iff hk4).1 hd)).1 (hLe ▸ hw)
  show ∃ s : ℚ, IsChangeConfig (innerRight k rL R βR ω) (innerLeft k rR L βL ω) (StripSys.rt s) ∧
    η ω t ∈ cfPocket (innerRight k rL R βR ω) (innerLeft k rR L βL ω) (StripSys.rt s) ∧
    cfPocket (innerRight k rL R βR ω) (innerLeft k rR L βL ω) (StripSys.rt s) ⊆ cfPocket (R ω) (L ω) r
  by_cases hdL : k / 2 - 4 < rL <;> by_cases hdR : k / 2 - 4 < rR <;>
    simp only [innerRight, innerLeft, hdL, hdR, ↓reduceIte]
  · exact key hβRp hβLp (disjoint_rightSideOf_of_closedLeftSide hβRp hord.1) (hRout hdL) (hLout hdR) hβ
      (fun h' => hav (Or.inl h')) (fun h' => hav (Or.inr h'))
  · exact key hβRp hLp (by rw [hLe]; exact disjoint_rightSideOf_of_closedLeftSide hβRp h2) (hRout hdL)
      (fun w hw _ => Or.inr hw) (fun h' => h'.elim (fun h'' => hβ (Or.inl h'')) (fun h'' => hzRL (Or.inr h'')))
      (fun h' => hav (Or.inl h')) hzL
  · exact key hRp hβLp (by rw [hRe]; exact disjoint_rightSideOf_of_closedLeftSide hαRp h1)
      (fun w hw _ => Or.inr hw) (hLout hdR)
      (fun h' => h'.elim (fun h'' => hzRL (Or.inl h'')) (fun h'' => hβ (Or.inr h''))) hzR
      (fun h' => hav (Or.inr h'))
  · exact key hRp hLp hcfgRL.ord (fun w hw _ => Or.inr hw) (fun w hw _ => Or.inr hw) hzRL hzR hzL

end Cover

end InteractingSLE.Sec7.R6Nest
