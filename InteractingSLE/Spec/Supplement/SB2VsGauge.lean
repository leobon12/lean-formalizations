/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsBadM
import InteractingSLE.Spec.Supplement.SB2DrvCells

/-!
# SB2(1)'s stop gauge and its record (D19)

Packet PROVE-AUX61-NOJUMP (decision D19). The stop gauge, at a relative point `z`, is the minimum of
* `Aph F (g z)`: the (capped) distance of the physical point `g z` to the physical closed bad set `F` (D10's rule);
* `Bph (g z) = 1/(1 + |g z|)`: vanishing at physical infinity (an infinite lifetime);
* `relGauge`: the (capped) distance of `z` to the relative closed bad set of the cell word (D19's cap, D3a's device),
where `g` is the inverse of the relative chart, centred at `u`.

* **`gaugeFun c u F κ ψ cw types ω z`** (on `ℍ`, read from the chart's inverse) and **`gaugeExt`** (any extension `g`);
* **`sb2Record`**: its grid code; **`measurable_sb2Record`**: measurable for any σ-algebra for which the chart is a
  measurable random chart and the word is measurable (`measurable_inv_of_isMeasChart`,
  `measurable_infEDist_badSet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.StagedLaw Lv Supp8.Q3Stop

/-- The capped distance to the physical bad set. -/
def Aph (F : Set ℂ) (x : ℂ) : ℝ≥0∞ := min (infEDist x F) 1

/-- The physical decay at infinity. -/
def Bph (x : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + ‖x‖))

theorem continuous_Aph (F : Set ℂ) : Continuous (Aph F) := continuous_infEDist.min continuous_const

theorem continuous_Bph : Continuous Bph :=
  ENNReal.continuous_ofReal.comp (continuous_const.div (continuous_const.add continuous_norm) fun x => by
    positivity)

section Rel

variable {Ω : Type*} (κ ψ : ℝ) (cw : Ω → Restart.BoundaryWord) (types : Set WordType)

/-- The capped distance to the relative closed bad set of the word of the type `w`. -/
def cellGauge (w : WordType) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  min (infEDist z (closure (badSet (cellXL κ ψ cw w ω) (cellXR κ ψ cw w ω) (typedRhoL w) (typedRhoR w)))) 1

open Classical in
/-- **The relative part of the gauge**: the cell gauge of the sample's own type (if listed), else `1`. -/
def relGauge (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  min 1 (⨅ w ∈ types, if angleWordType κ ψ (cw ω) = w then cellGauge κ ψ cw w ω z else 1)

open Classical in
theorem relGauge_eq {ω : Ω} {w : WordType} (hw : w ∈ types) (hcell : angleWordType κ ψ (cw ω) = w) (z : ℂ) :
    relGauge κ ψ cw types ω z = cellGauge κ ψ cw w ω z := by
  unfold relGauge
  have hle : cellGauge κ ψ cw w ω z ≤ 1 := min_le_right _ _
  have hinf : (⨅ w' ∈ types, if angleWordType κ ψ (cw ω) = w' then cellGauge κ ψ cw w' ω z else 1) =
      cellGauge κ ψ cw w ω z := by
    refine le_antisymm (iInf₂_le_of_le w hw (by simp only [hcell, ↓reduceIte, le_refl]))
      (le_iInf₂ fun w' _ => ?_)
    by_cases h : angleWordType κ ψ (cw ω) = w'
    · have hw' : w' = w := h.symm.trans hcell
      subst hw'
      simp only [hcell, ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]; exact hle
  rw [hinf, min_eq_right hle]

theorem relGauge_le_one (ω : Ω) (z : ℂ) : relGauge κ ψ cw types ω z ≤ 1 := min_le_left _ _

/-- The relative gauge is `1`-Lipschitz in the point, hence continuous. -/
theorem continuous_cellGauge (w : WordType) (ω : Ω) : Continuous (cellGauge κ ψ cw w ω) :=
  continuous_infEDist.min continuous_const

open Classical in
theorem continuous_relGauge (ω : Ω) : Continuous (relGauge κ ψ cw types ω) := by
  by_cases h : angleWordType κ ψ (cw ω) ∈ types
  · have e : relGauge κ ψ cw types ω = cellGauge κ ψ cw (angleWordType κ ψ (cw ω)) ω :=
      funext fun z => relGauge_eq κ ψ cw types h rfl z
    rw [e]; exact continuous_cellGauge κ ψ cw _ ω
  · have e : relGauge κ ψ cw types ω = fun _ => 1 := funext fun z => by
      unfold relGauge
      have : (⨅ w ∈ types, if angleWordType κ ψ (cw ω) = w then cellGauge κ ψ cw w ω z else 1) =
          ⨅ w ∈ types, (1 : ℝ≥0∞) := by
        refine iInf_congr fun w => iInf_congr fun hw => ?_
        simp only [show ¬ angleWordType κ ψ (cw ω) = w from fun he => h (he ▸ hw), ↓reduceIte]
      rw [this]
      exact min_eq_left (le_iInf₂ fun _ _ => le_rfl)
    rw [e]; exact continuous_const

open Classical in
theorem measurable_relGauge {m : MeasurableSpace Ω} (hcw : Measurable[m] cw) (htypes : types.Countable)
    (z : ℂ) : Measurable[m] fun ω => relGauge κ ψ cw types ω z := by
  have hcell : ∀ w, Measurable[m] fun ω => cellGauge κ ψ cw w ω z := fun w =>
    ((measurable_infEDist_badSet (typedRhoL w) (typedRhoR w) z).comp
      ((measurable_cellXL hcw w).prodMk (measurable_cellXR hcw w))).min measurable_const
  have hset : ∀ w, MeasurableSet[m] {ω | angleWordType κ ψ (cw ω) = w} := fun w =>
    ((measurable_angleWordType κ ψ).comp hcw) (measurableSet_singleton w)
  have hinf : Measurable[m] fun ω =>
      ⨅ w ∈ types, if angleWordType κ ψ (cw ω) = w then cellGauge κ ψ cw w ω z else 1 := by
    have e : (fun ω => ⨅ w ∈ types, if angleWordType κ ψ (cw ω) = w then cellGauge κ ψ cw w ω z else 1) =
        fun ω => ⨅ w : types, if angleWordType κ ψ (cw ω) = (w : WordType) then cellGauge κ ψ cw w ω z else 1 := by
      funext ω; rw [iInf_subtype']
    rw [e]
    have := htypes.to_subtype
    exact Measurable.iInf fun w => Measurable.ite (hset w) (hcell w) measurable_const
  exact measurable_const.min hinf

end Rel

section Gauge

variable {Ω : Type*} (c : Ω → Chart) (u : ℝ) (F : Set ℂ) (κ ψ : ℝ) (cw : Ω → Restart.BoundaryWord)
  (types : Set WordType)

/-- **The gauge for an extension `g` of the inverse chart.** -/
def gaugeExt (g : ℂ → ℂ) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  min (min (Aph F (g z)) (Bph (g z))) (relGauge κ ψ cw types ω z)

open Classical in
/-- **The gauge read from the chart** (on `ℍ`; `1` off `ℍ`). -/
def gaugeFun (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  if z ∈ H then gaugeExt F κ ψ cw types (fun w => (c ω).2.1 w - u) ω z else 1

/-- **SB2(1)'s stop record**: the grid code of the gauge. -/
def sb2Record (ω : Ω) : RecData := (recFun fun z => (gaugeFun c u F κ ψ cw types ω z).toReal, 0, false)

theorem gaugeExt_le_one (g : ℂ → ℂ) (ω : Ω) (z : ℂ) : gaugeExt F κ ψ cw types g ω z ≤ 1 :=
  (min_le_right _ _).trans (relGauge_le_one κ ψ cw types ω z)

theorem continuousOn_gaugeExt {g : ℂ → ℂ} (hg : ContinuousOn g {z | 0 ≤ z.im}) (ω : Ω) :
    ContinuousOn (gaugeExt F κ ψ cw types g ω) {z | 0 ≤ z.im} :=
  continuous_min.comp_continuousOn ((continuous_min.comp_continuousOn
    (((continuous_Aph F).comp_continuousOn hg).prodMk (continuous_Bph.comp_continuousOn hg))).prodMk
    (continuous_relGauge κ ψ cw types ω).continuousOn)

theorem continuousOn_toReal_gaugeExt {g : ℂ → ℂ} (hg : ContinuousOn g {z | 0 ≤ z.im}) (ω : Ω) :
    ContinuousOn (fun z => (gaugeExt F κ ψ cw types g ω z).toReal) {z | 0 ≤ z.im} := by
  refine (ENNReal.continuousOn_toReal.comp (continuousOn_gaugeExt F κ ψ cw types hg ω) fun z _ => ?_)
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (gaugeExt_le_one F κ ψ cw types g ω z)

open Classical in
/-- **Decoding the record** at a point of the closed half-plane gives the gauge of any continuous extension `g` of the
inverse chart that agrees with it on `ℍ`. -/
theorem decode_sb2Record {ω : Ω} {g : ℂ → ℂ} (hg : ContinuousOn g {z | 0 ≤ z.im})
    (hgH : ∀ w ∈ H, g w = (c ω).2.1 w - u) {z : ℂ} (hz : 0 ≤ z.im) :
    decode (sb2Record c u F κ ψ cw types ω) z = (gaugeExt F κ ψ cw types g ω z).toReal := by
  refine decode_eq hz ((continuousOn_toReal_gaugeExt F κ ψ cw types hg ω) z hz) fun p hp => ?_
  have hpH : gridPt p ∈ H := by
    show 0 < (gridPt p).im
    rw [gridPt_im]; exact hp
  simp only [sb2Record]
  rw [recFun_code]
  simp only [gaugeFun, hpH, ↓reduceIte]
  unfold gaugeExt
  rw [hgH _ hpH]

open Classical in
theorem measurable_sb2Record {m : MeasurableSpace Ω} (hc : WalkInf.IsMeasChart m c) (hcw : Measurable[m] cw)
    (htypes : types.Countable) : Measurable[m] (sb2Record c u F κ ψ cw types) := by
  refine (measurable_recFun fun z => ?_).prodMk measurable_const
  by_cases hz : z ∈ H
  · simp only [gaugeFun, hz, ↓reduceIte, gaugeExt]
    have hinv : Measurable[m] fun ω => (c ω).2.1 z - u :=
      (measurable_inv_of_isMeasChart hc hz).sub_const _
    exact ENNReal.measurable_toReal.comp ((((continuous_Aph F).measurable.comp hinv).min
      (continuous_Bph.measurable.comp hinv)).min (measurable_relGauge κ ψ cw types hcw htypes z))
  · simp only [gaugeFun, hz, ↓reduceIte]
    exact measurable_const

end Gauge

end InteractingSLE.Theorem14.SB.Vs
