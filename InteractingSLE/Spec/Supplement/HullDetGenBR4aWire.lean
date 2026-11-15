/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGenMob

/-!
# BR4a's relative coupling from its relative chain

Packet PROVE-HULLDET. `HullDetGen.BR4aRelCouplingStatement` (K2's inputs (S), (L) for the target-changed
counterflow) is reduced to **`BR4aRelChainStatement`**, which contains no conditional law: for the original
coupling `(h', W', …)` of the infinity-source field, a monotone family of stopping times `ℓ q` of its driving
filtration (the inverse relative clock), a globally continuous driver `W` adapted to the stopped σ-algebras at `ℓ q`,
measurable versions of the hulls at `ℓ q`, an admissible seed, and almost surely: an infinite threshold time, the
active-domain identity `mob (−v) (ℍ ∖ K̃_q) = ℍ ∖ K'_{ℓ q}`, the pointwise mean identity through the target-change
chart `brChart v`, and the hull identity at the relative clock times. The reduction is
`HullDetGen.hasSafeLaw_of_timeChange` and `hasSafeMembers_of_timeChange` for the chart `brChart v`, whose transport
of `h'` is the recentred field's infinity-source field (`eq_chartTransport_brChart`).

* `stoppedFiltration`: the filtration of stopped σ-algebras of a monotone family of stopping times;
* **`BR4aRelChainStatement`** (named input) and **`br4aRelCouplingStatement_of_relChain`**;
* **`br4aHullDetStatement_of_relChain`**: BR4a's hull identity from the relative chain and Theorems 1.2–1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.HullDetGen

open Restart Restart.FCDet Restart.DomainMarkov Restart.DomainMarkov.K2 Sec2.Assembly Sec7.PocketTraversal
  Theorem14.BR4aPath

/-! ### The stopped filtration of a monotone family of stopping times -/

/-- The filtration `q ↦ 𝓕_{ℓ q}` of a monotone family of stopping times. -/
def stoppedFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {ℓ : ℝ≥0 → Ω → WithTop ℝ≥0} (hℓ : ∀ q, IsStoppingTime 𝓖 (ℓ q)) (hℓm : ∀ ω, Monotone fun q => ℓ q ω) :
    Filtration ℝ≥0 mΩ where
  seq q := (hℓ q).measurableSpace
  mono' q q' hqq' := (hℓ q).measurableSpace_mono (hℓ q') fun ω => hℓm ω hqq'
  le' q := (hℓ q).measurableSpace_le

theorem stoppedFiltration_apply {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {ℓ : ℝ≥0 → Ω → WithTop ℝ≥0} (hℓ : ∀ q, IsStoppingTime 𝓖 (ℓ q)) (hℓm : ∀ ω, Monotone fun q => ℓ q ω)
    (q : ℝ≥0) : stoppedFiltration hℓ hℓm q = (hℓ q).measurableSpace := rfl

/-! ### The relative chain and the reduction -/

/-- **Named input: BR4a's relative chain** (pathwise and measurability content of the target change; no conditional
law). For the original coupling `(h', W', VL, VR, …)` of the infinity-source field `h'` of `h` (BR4a's setting) and
a sorted word `c` of the target-change transport `X = chartTransport (brChart v) 1 0 χ' h'`: there are a monotone
family `ℓ` of stopping times of the original driving filtration, before the original lifetime, a globally continuous
driver `W` from `0` adapted to `q ↦ 𝓕_{ℓ q}`, hitting-measurable relatively closed versions `Bs s` of the original
hulls at `ℓ s`, with the flow-line seed of `c` admissible and almost surely: the threshold time of `W` (with the
geometric images of the flow-line marks of `c`) is infinite; `mob (−v)` carries `ℍ ∖ K̃_q` onto `ℍ ∖ K'_{ℓ q}`; the
coupling mean of the original chain at `ℓ q`, read through `brChart v`, is the coupling mean of `W` at `q` on
`ℍ ∖ K̃_q`; and `W` generates `mob v (K'_t)` at the relative times `clock v W' t`, `t < T_v`. -/
def BR4aRelChainStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v : ℝ, v ≠ 0 → (∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' →
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
        (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W' VL VR B ζ' h' →
    ∀ hX : IsMeasurableKilledDriving W' VL VR ζ',
    ∀ c : BoundaryWord, c.IsSorted →
      IsGFFWithBoundaryData P (fun ω => Chart.chartTransport (isConformal_brChart v) 1 0 (chiC (16 / κ)) (h' ω))
        c.fn c.jumps →
      ∃ (ℓ : ℝ≥0 → Ω → WithTop ℝ≥0) (hℓ : ∀ q, IsStoppingTime (drivingFiltration P hX) (ℓ q))
        (hℓm : ∀ ω, Monotone fun q => ℓ q ω) (W : ℝ≥0 → Ω → ℝ) (Bs : ℝ≥0 → Ω → Set ℂ),
        (∀ q, ∀ᵐ ω ∂P, ((ℓ q ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ' ω) ∧
        (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted (stoppedFiltration hℓ hℓm) W ∧
        ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
          (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) ∧
        (∀ s, Measurable[mΩ, hittingSigma] (Bs s)) ∧ (∀ s ω, Bs s ω ⊆ H ∧ IsOpen (H \ Bs s ω)) ∧
        (∀ s, ∀ᵐ ω ∂P, Bs s ω = fwdHull (fun r : ℝ => W' r.toNNReal ω) ((ℓ s ω).untopD 0 : ℝ≥0)) ∧
        (∀ᵐ ω ∂P, thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
          (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω = ⊤) ∧
        (∀ q : ℝ≥0, ∀ᵐ ω ∂P, mobInv v '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) =
          H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) ((ℓ q ω).untopD 0 : ℝ≥0)) ∧
        (∀ q : ℝ≥0, ∀ᵐ ω ∂P, ∀ w ∈ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q,
          couplingMean (16 / κ) (fun s : ℝ => W' s.toNNReal ω) ((ℓ q ω).untopD 0 : ℝ≥0)
              (bheProc (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0) W' VL VR ω
                ((ℓ q ω).untopD 0)) (mobInv v w) + 0 + chiC (16 / κ) * (brChart v).2.2 (mobInv v w) =
            couplingMean (16 / κ) (fun s : ℝ => W s.toNNReal ω) q
              (bheProc (16 / κ) (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
                (geomLW W fun _ => flowLineXL c.fn c.jumps 0) (geomRW W fun _ => flowLineXR c.fn c.jumps 0) ω q) w) ∧
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} →
          fwdHull (fun s : ℝ => W s.toNNReal ω) (clock v (fun s : ℝ => W' s.toNNReal ω) t) =
            mob v '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t

/-- **BR4a's relative coupling from its relative chain** (conditional helper with a distinct name; the named input is
`BR4aRelChainStatement`). -/
theorem br4aRelCouplingStatement_of_relChain (hR : BR4aRelChainStatement.{u}) : BR4aRelCouplingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' v hv0 hvis hv htr X hXtr c hcs hX
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  obtain ⟨b', J', h', hb', htr', hfl⟩ := hcf
  have hWreg := Supp8.GB6.ae_driver_zero_continuousOn hfl
  obtain ⟨h'', 𝓕, VL, VR, B, htr0, hC⟩ := hfl
  have hh'' : h'' = h' := funext fun ω => Theorem14.BRLeaf.eq_of_isTranslateAddConst_zero_mul (htr0 ω)
  subst hh''
  obtain ⟨hXd, -⟩ := hC.2.2.2
  have hXeq : X = fun ω => Chart.chartTransport (isConformal_brChart v) 1 0 (chiC (16 / κ)) (h'' ω) :=
    funext fun ω => eq_chartTransport_brChart v _ _ _ (htr' ω) (htr ω) (hXtr ω)
  subst hXeq
  obtain ⟨ℓ, hℓ, hℓm, W, Bs, hℓζ, hW0, hWc, hWa, hseed, hBm, hBc, hBK, hthr, hK, hmean, hhull⟩ :=
    hR κ hκ hκ4 b jumps hb P h hh W' ζ' hζ' v hv0 hvis b' J' h'' hb' htr' 𝓕 VL VR B hC hXd c hcs hX
  have hreg : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → Mean.IsDrvReg W
      (thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
        (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0)) ω :=
    Eventually.of_forall fun ω _ => ⟨(hWc ω).continuousOn, hW0 ω⟩
  have hK' : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) →
      (q : ℝ≥0∞) < thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
        (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω →
      (brChart v).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) q) =
        H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) ((ℓ q ω).untopD 0 : ℝ≥0) := fun q =>
    (hK q).mono fun ω h _ _ => h
  have hmean' := fun q => (hmean q).mono fun ω h (_ : ω ∈ (univ : Set Ω)) (_ : (q : ℝ≥0∞) < thr
    (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
      (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω) => h
  have hlaw := hasSafeLaw_of_timeChange hC hWreg hXd hℓ hℓζ (𝓗 := stoppedFiltration hℓ hℓm) (fun q => le_rfl)
    (isConformal_brChart v) (continuousOn_brChart_lift v) 0 (chiC (16 / κ)) hreg hK' hmean'
  have hmem := hasSafeMembers_of_timeChange hκ' hC hXd hℓ hℓζ (𝓗 := stoppedFiltration hℓ hℓm) (fun q => le_rfl)
    (isConformal_brChart v) (continuousOn_brChart_lift v) (harmonicOnNhd_brChart_lift v) 0 (chiC (16 / κ)) hreg
    hK' Bs hBm hBc hBK
  exact ⟨stoppedFiltration hℓ hℓm, W, hW0, hWc, hWa, hseed, hlaw, hmem, hthr.and hhull⟩

/-- **BR4a's hull identity from its relative chain** (conditional helper; named input `BR4aRelChainStatement`;
Theorems 1.2–1.3 at universes `u` and `0` are permitted roots of Theorem 1.4, R48). -/
theorem br4aHullDetStatement_of_relChain (hR : BR4aRelChainStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : BR4aHullDetStatement.{u} :=
  br4aHullDetStatement_of_relCoupling (br4aRelCouplingStatement_of_relChain hR) h12 h13 h12₀ h13₀

end InteractingSLE.Supp8.HullDetGen
