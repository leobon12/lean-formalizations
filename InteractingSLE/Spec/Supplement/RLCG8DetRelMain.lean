/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRelChart
import InteractingSLE.Spec.Supplement.RLCG8DetNHPositivity

/-!
# G8's relative representation from explicit late-cut geometry

Packet PROVE-G8-DET. The conditional result below constructs every field of
`G8RelativeChart`: Aux. 8's continuous driver and capacity clock, the old
tip's characteristic, swallowing of the marked point and the canonical chart
identifications. The exact remaining input is `LateCutGeometryNHStatement`,
whose fields involve only the original chain and its fixed cut maps.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap IsForwardSol)

universe u

namespace InteractingSLE.RLC

namespace G8Det.LateCutGeometry

/-- Construct the full relative representation. The auxiliary driver is
centered at its actual initial value; this changes neither chart gaps nor
characteristic equations. -/
theorem nonempty_relativeChart {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {σ r : ℝ≥0}
    (d : LateCutGeometry α β w σ r) (hcα : Continuous α) (hcβ : Continuous β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (hw : Continuous w)
    (hact : ∀ᶠ u in 𝓝[<] σ, α u ∈ closure (activeDomain α u β r) ∧
      β r ∈ closure (activeDomain α u β r) ∧ (1 : ℂ) ∈ closure (activeDomain α u β r)) :
    Nonempty (G8RelativeChart α β σ r) := by
  obtain ⟨e⟩ := d.exists_image hcα hcβ hα0 hβ0 hw
  let c := e.driver 0
  let W : ℝ → ℝ := fun s => e.driver s - c
  let b : ℝ → ℝ := fun s => (fwdMap e.driver s d.left).re + e.driver s - c
  let U := e.clock ((σ : ℝ) - d.cut)
  have hc : c = d.seed := d.driver_zero e hcα hcβ hα0 hβ0 hw
  have hU : 0 < U := e.clock_pos d.time_pos
  obtain ⟨vL, hvL⟩ := d.left_alive e hcα hcβ hα0 hβ0 hw
  have hleft : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol e.driver (d.left : ℂ) s v :=
    fun s hs => ⟨vL, QuantumZipper.isForwardSol_restrict hvL hs.1 hs.2.le⟩
  have hchar := left_characteristic e.continuous_driver (by change d.left < c; rw [hc]; exact d.left_lt_seed)
    hleft
  have hsw := d.right_swallow e hcα hcβ hα0 hβ0 hw
  have hsw' : RealSwallowAt W (d.right - c) U := by
    simpa only [RealSwallowAt, W, ofReal_sub, QuantumZipper.ASep.GC.isForwardSol_sub_const] using hsw
  have hclock : Tendsto (fun u : ℝ≥0 => e.clock ((u : ℝ) - d.cut))
      (𝓝[<] σ) (𝓝[<] U) := by
    apply (e.tendsto_clock d.time_pos).comp
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((NNReal.continuous_coe.sub continuous_const).tendsto σ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_lt_sub_right (show (u : ℝ) < σ by exact_mod_cast hu) _
  refine ⟨{
    W := W
    U := U
    x := d.right - c
    s₀ := 0
    b := b
    clock := fun u => e.clock ((u : ℝ) - d.cut)
    continuous_W := e.continuous_driver.sub continuous_const
    W_zero := sub_self _
    x_pos := sub_pos.2 (by rw [hc]; exact d.seed_lt_right)
    swallow := hsw'
    cut_nonneg := le_refl 0
    cut_lt := hU
    tip_lt := fun s hs => sub_lt_sub_right (hchar s hs).1 c
    characteristic := ?_
    integrable := ?_
    clock_tendsto := hclock
    chart_eq := ?_ }⟩
  · intro s hs
    simpa only [b, W, sub_sub_sub_cancel_right] using (hchar s hs).2.1
  · intro s hs
    simpa only [b, W, sub_sub_sub_cancel_right] using (hchar s hs).2.2
  · filter_upwards [hact, Ioo_mem_nhdsLT d.cut_lt] with u ha hu
    have ht := d.time_mem ⟨hu.1.le, hu.2.le⟩
    have htime : e.clock ((u : ℝ) - d.cut) ∈ Ico 0 U :=
      ⟨e.clock_nonneg ht, e.strictMono_clock ht ⟨d.time_pos.le, le_rfl⟩
        (sub_lt_sub_right (by exact_mod_cast hu.2) _)⟩
    obtain ⟨vB, hvB⟩ := hleft _ htime
    obtain ⟨vR, hvR⟩ := hsw.2.1 _ htime
    have hbval := fwdMap_eq_ofReal_re e.continuous_driver hvB
      ⟨htime.1, le_rfl⟩
    have hrval := fwdMap_eq_ofReal_re e.continuous_driver hvR
      ⟨htime.1, le_rfl⟩
    have hb := d.mapOut_passive e hcα hcβ hα0 hβ0 hw ⟨hu.1.le, hu.2.le⟩
      d.left_limit ⟨vB, hvB⟩
    have hr := d.mapOut_passive e hcα hcβ hα0 hβ0 hw ⟨hu.1.le, hu.2.le⟩
      d.right_limit ⟨vR, hvR⟩
    rw [hbval, ← ofReal_add] at hb
    rw [hrval, ← ofReal_add] at hr
    have htip := d.mapOut_tip e hcα hcβ hα0 hβ0 hw hu
    have hpt := chartPt_retFwd_of_tendsto ha.2.1 ha.1 hb htip
    have hpr := chartPt_retFwd_of_tendsto ha.2.1 ha.2.2 hb hr
    refine ⟨?_, ?_⟩
    · rw [hpt]
      dsimp only [W, b]
      ring
    · rw [hpr]
      dsimp only [W, b]
      rw [ofReal_sub, QuantumZipper.ASep.GC.fwdMap_sub_const]
      ring

end G8Det.LateCutGeometry

/-- Exact remaining original-chart geometry for G8. The full Lean type of
each obligation is in `G8Det.LateCutGeometry`; no relative driver or clock is
assumed. This proposition is not asserted unconditionally. -/
def LateCutGeometryNHStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (σ r : ℝ≥0) (q : ℝ),
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Continuous w → w 0 = 0 → IsGeneratingTrace w ⊤ α →
    RealSwallowAt (fun s : ℝ => w s.toNNReal) 1 σ → 1 < q → α σ = q →
    β r ∈ H → β r ∉ α '' Icc 0 σ → (∀ t ≤ r, ‖β t‖ < 1 / 2) →
    (∀ t < σ, (α t).im = 0 → 0 ≤ (α t).re) →
      Nonempty (G8Det.LateCutGeometry α β w σ r)

/-- Aux. 8 constructs G8's relative chart from the remaining explicit
original-chart geometry. Joint activity is supplied by the proved side lemma. -/
theorem g8RelativeChartNHStatement_of_lateCutGeometry (hGeo : LateCutGeometryNHStatement) :
    G8RelativeChartNHStatement := by
  intro α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH
  obtain ⟨d⟩ := hGeo α β w σ r q hcop hα0 hβ0 hw hw0 hgen hsw hq hασ hβH hβoff hsmall hNH
  obtain ⟨t₀, ht₀, hact⟩ := G8Det.exists_final_activity_of_nonneg_real hcop hα0 hβ0 hw hw0 hgen
    hsw hq hασ hsmall hβH hβoff (G8Det.nonneg_real_le_of_before hNH hq hασ)
  apply d.nonempty_relativeChart hcop.1 hcop.2.2.2.2.1 hα0 hβ0 hw
  filter_upwards [Ioo_mem_nhdsLT ht₀] with u hu
  obtain ⟨_, _, hα, hβ, _, h1⟩ := hact u hu.1 hu.2
  exact ⟨hα, hβ, h1⟩

/-- The R63 frame follows from the same original-chart geometric input. -/
theorem g8DetFrameNHStatement_of_lateCutGeometry (hGeo : LateCutGeometryNHStatement) :
    G8DetFrameNHStatement :=
  g8DetFrameNHStatement_of_relative (g8RelativeChartNHStatement_of_lateCutGeometry hGeo)

/-- G8 positivity, with the source's no-negative-contact premise supplied by
the already proved boundary nonhitting criterion. -/
theorem g8PositivityStatement_of_lateCutGeometry (hW0b : Supp9.W0bStatement.{u})
    (hGeo : LateCutGeometryNHStatement) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_detNH hW0b (g8DetFrameNHStatement_of_lateCutGeometry hGeo)

/-- G8's retained-frame wiring with the remaining geometry stated explicitly. -/
theorem g8FrameStatement_of_lateCutGeometry_inputs (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetHistStatement.{0})
    (hGeo : LateCutGeometryNHStatement) : G8FrameStatement.{0} :=
  g8FrameStatement_of_relative_nh_inputs h75 href h12p h13 hD
    (g8RelativeChartNHStatement_of_lateCutGeometry hGeo)

end InteractingSLE.RLC
