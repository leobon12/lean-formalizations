/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefAmbientCover
import InteractingSLE.Spec.Sec7.R5SameCover
import InteractingSLE.Spec.Sec7.SideC4Current

/-!
# R.5's ambient cover on the late side tests: the geometric part of `Wire.VisitReferenceAmbientCoverPosExc`

Packet PROVE-R5-REFCHART. The late side tests (`Wire.Current.SideTest`, Ready) carry the same pocket objects as the
R.7 tests (`cfPocket`, `travAll(Inf)`, the Jordan coordinate `j.chart`, the base chart `pChart`); their original-time
reference charts `j.referenceVisitChart i d ω t` are this packet's `refChart` at the rational original times. This
file transfers the R.7 ambient cover (`R5Ref.exists_ambient_cover(Inf)`) to them:

* `lateExc` (def): the exceptional physical set `refExc` / `refExcInf` of the test's pocket (finite: `lateExc_finite`);
* **`late_exists_ambient_cover`**: at a positive live relative capacity, every real current coordinate whose landing
  is a point of the pocket off `lateExc` has a rational original visit `t = rationalOriginalTime r` with every
  geometric conjunct of `Wire.VisitReferenceAmbientCoverPosExc` — the visit, `visitCapacity ≤ q`, the unfilled collar
  and the transition limit, the landing in `domain ∩ regHull t`, the old landing, the old approach in the reference
  complement, the ambient image `x′` off the ambient force jumps and `f_t ∘ old⁻¹ → x′`; the force processes follow
  the coupling's path (`hp`).

* `VisitReferenceAmbientCoverPosExcHull` (def): `Wire.VisitReferenceAmbientCoverPosExc` restricted to coordinates
  whose landing lies in the pocket — the late statement asks for `z₀ ∈ domain` at every coordinate, which fails at
  landings on the unvisited sides (`R5Ref.not_ambient_landing_of_notMem`);
* `LateAmbientLiftWord` (def): the lift-difference limit `ℓ` and the word identity on every selected collar (the input
  left to PROVE-R5-LIFT);
* **`visitReferenceAmbientCoverPosExcHull_of_liftWord`**: references at the rational original times, exceptional set
  `lateExc ∪ X`: the corrected late cover from the lift input.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Ref

open Wire Wire.Current Wire.Current.SideTest
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketWordAssembly
  PocketSeedOpen PocketCoord PocketJordan PocketStopField PocketStopWallsFin R5Phase MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)
open QuantumZipper (chiC logDerivFwd)
open LocalSets Aux119Heights WholeField

variable {Ω : Type} [MeasurableSpace Ω]

/-- **R.5's exceptional physical set on a late side test**: `refExc` (bounded pocket) or `refExcInf` (pocket opening
at the flow seed) of its pocket. -/
def lateExc (j : SideTest Ω) (d : WordObjects Ω) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  if j.infinite then refExcInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω
  else refExc d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω

theorem lateExc_finite (j : SideTest Ω) (d : WordObjects Ω) (q : ℝ≥0) (ω : Ω) : (lateExc j d q ω).Finite := by
  unfold lateExc
  split_ifs
  · exact refExcInf_finite _ _ _ _ _ _ _
  · exact refExc_finite _ _ _ _ _ _ _

/-- **The geometric part of the late ambient cover** (both pocket shapes; references at the rational original
times): see the module docstring. -/
theorem late_exists_ambient_cover {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event)
    (hp : IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω) (fun a t => d.forceL a t ω)
      (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∉ lateExc j d q ω)
    (hC : extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∈
      (j.target i d).domain ω) :
    ∃ (r : ℕ) (x ε x' : ℝ),
      d.curve ω (rationalOriginalTime r) ∈ (j.target i d).domain ω ∧
      (j.visitCapacity d ω (rationalOriginalTime r)).toNNReal ≤ q ∧ 0 < ε ∧
      (j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).dom : Set ℂ) ∧
      Tendsto (fun z => (j.referenceVisitChart i d ω (rationalOriginalTime r)).1
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∈
        (j.target i d).domain ω ∩ regHull d.driver d.lifetime (rationalOriginalTime r) ω ∧
      Tendsto (j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ)) ∧
      (∀ᶠ y in 𝓝[H] (x : ℂ), (j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 y ∈
        H \ j.capacityReference i d (rationalOriginalTime r) ω) ∧
      x' ∉ forceJumpSet (fun a => d.forceL a (rationalOriginalTime r) ω - d.driver (rationalOriginalTime r) ω)
        (fun a => d.forceR a (rationalOriginalTime r) ω - d.driver (rationalOriginalTime r) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r)
        ((j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  have hpc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hω' : ω ∈ j.event := by rwa [target_event] at hω
  have hCompl := fun t => compl_capacityReference (j := j) (i := i) (d := d) hω t
  rw [target_domain] at hpc hC hCompl ⊢
  rw [target_chart] at hpc
  obtain ⟨-, -, -, hG, hlife, hcfgP, hcfgI, -, hAG, -, hJ, -⟩ := hj
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
    have hωG := hAG hω'
    have hcfg := hcfgP ω hωG.1 hωG.2
    have hψ := hJ ω hω'
    have hζ := hlife ω hωG.1
    have hγ := (hcfg.isDrivenCurve hψ).1
    have hV : Continuous fun t : ℝ≥0 => d.driver t ω := by
      have h := hcfg.continuous_W.comp NNReal.continuous_coe
      simpa only [Function.comp_def, Real.toNNReal_coe] using h
    obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp hζ hV fun _ => rfl
    have hcurve : (j.target i d).curve =
        travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hI, Bool.false_eq_true, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hI, Bool.false_eq_true, ↓reduceIte]
      rfl
    have href : ∀ t, j.referenceVisitChart i d ω t = relChart (j.target i d).baseChart
        (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t).toNNReal ω := by
      intro t
      rw [SideTest.referenceVisitChart, hcurve, hvc]
    rw [hcurve] at hq hX hC ⊢
    simp only [href, hvc]
    simp only [lateExc, hI, Bool.false_eq_true, ↓reduceIte] at hX
    obtain ⟨r, x, ε, x', hM, hv, hcol, hz, -, -, hjump, -, hold⟩ :=
      exists_ambient_cover (A := (j.target i d).event) (c := (j.target i d).baseChart) (W' := d.driver)
        (ζ' := d.lifetime) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hζ (fun a t => hL a t) (fun b t => hR b t) hq ξ
        hX hC
    have hOldAll := reference_chart_at_visit (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) hω hcfg hψ hpc.1
      hpc.2.1 hpc.2.2.1 hv hM.2.2.2.2 hM.2.1 hM.2.2.2.1
    have hdomEq : ((relChart (j.target i d).baseChart
        (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω
          (rationalOriginalTime r)).toNNReal ω).dom : Set ℂ) =
        cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) ∩
          (H \ regHull d.driver d.lifetime (rationalOriginalTime r) ω) := by
      rw [hOldAll.2.2, H_diff_liveExt_zero hω hγ]
      rfl
    refine ⟨r, x, ε, x', hv, hM.2.2.2.1, hcol.1, hcol.2.1, hcol.2.2.1, hz,
      (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1, eventually_nhdsWithin_of_forall fun y hy => ?_, hjump, hold⟩
    rw [hCompl, ← hdomEq]
    exact hOldAll.1.inv_mem_dom hy
  · simp only [hI, ↓reduceIte] at hAG hJ
    have hωG := hAG hω'
    have hcfg := hcfgI ω hωG.1 (le_antisymm (not_lt.1 hωG.2) ((hG ω hωG.1).1.changeCorner_props.1.1))
    have hψ := hJ ω hω'
    have hζ := hlife ω hωG.1
    have hγ := (hcfg.isDrivenCurve hψ).1
    have hV : Continuous fun t : ℝ≥0 => d.driver t ω := by
      have h := hcfg.continuous_W.comp NNReal.continuous_coe
      simpa only [Function.comp_def, Real.toNNReal_coe] using h
    obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp hζ hV fun _ => rfl
    have hcurve : (j.target i d).curve =
        travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hI, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hI, ↓reduceIte]
      rfl
    have href : ∀ t, j.referenceVisitChart i d ω t = relChart (j.target i d).baseChart
        (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t).toNNReal ω := by
      intro t
      rw [SideTest.referenceVisitChart, hcurve, hvc]
    rw [hcurve] at hq hX hC ⊢
    simp only [href, hvc]
    simp only [lateExc, hI, ↓reduceIte] at hX
    obtain ⟨r, x, ε, x', hM, hv, hcol, hz, -, -, hjump, -, hold⟩ :=
      exists_ambient_coverInf (A := (j.target i d).event) (c := (j.target i d).baseChart) (W' := d.driver)
        (ζ' := d.lifetime) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hζ (fun a t => hL a t) (fun b t => hR b t) hq ξ
        hX hC
    have hOldAll := reference_chart_at_visitInf (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) hω hcfg hψ hpc.1
      hpc.2.1 hpc.2.2.1 hv hM.2.2.2.2 hM.2.1 hM.2.2.2.1
    have hdomEq : ((relChart (j.target i d).baseChart
        (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω
          (rationalOriginalTime r)).toNNReal ω).dom : Set ℂ) =
        cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) ∩
          (H \ regHull d.driver d.lifetime (rationalOriginalTime r) ω) := by
      rw [hOldAll.2.2, H_diff_liveExt_zero hω hγ]
      rfl
    refine ⟨r, x, ε, x', hv, hM.2.2.2.1, hcol.1, hcol.2.1, hcol.2.2.1, hz,
      (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1, eventually_nhdsWithin_of_forall fun y hy => ?_, hjump, hold⟩
    rw [hCompl, ← hdomEq]
    exact hOldAll.1.inv_mem_dom hy

/-- **The late ambient cover at hull landings** (the corrected form of `Wire.VisitReferenceAmbientCoverPosExc`): the
same conclusion, required only at coordinates whose landing lies in the pocket (`target.domain`). -/
def VisitReferenceAmbientCoverPosExcHull {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω →
        ∃ (r : ℕ) (x ε x' ℓ : ℝ) (z₀ : ℂ), let old := j.referenceVisitChart i d ω (s j r);
          let w : ℝ → ℝ := fun t => d.driver t.toNNReal ω;
          d.curve ω (s j r) ∈ target.domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧ 0 < ε ∧
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
          Tendsto (fun z => old.1 (current.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          z₀ ∈ target.domain ω ∩ regHull d.driver d.lifetime (s j r) ω ∧
          Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 z₀) ∧
          (∀ᶠ y in 𝓝[H] (x : ℂ), old.2.1 y ∈ H \ j.capacityReference i d (s j r) ω) ∧
          x' ∉ forceJumpSet (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
            (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) ∧
          Tendsto (fun y => fwdMap w (s j r) (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) ∧
          Tendsto (fun y => old.2.2 (old.2.1 y) - (logDerivFwd w (s j r) (old.2.1 y)).im)
            (𝓝[H] (x : ℂ)) (𝓝 ℓ) ∧
          forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
              (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) x' + chiC i.kappa * ℓ =
            forceBoundaryData target.kappa target.rhoL target.rhoR
              (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
                target.marksL a q ω - segDriver (target.curve ω) q)
              (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
                target.marksR a q ω - segDriver (target.curve ω) q)
              ξ + e.phase q ω * (Ioo
                (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                  segDriver (target.curve ω) q)
                (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                  segDriver (target.curve ω) q)).indicator 1 ξ - e.offset

/-- **The lift-difference limit and the word identity on every selected late ambient collar** (the input left to
PROVE-R5-LIFT): for every reference with every geometric conjunct of `VisitReferenceAmbientCoverPosExcHull`, the limit
`ℓ` of "old lift − ambient lift" along the old approach and the word identity. -/
def LateAmbientLiftWord {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω →
        ∀ (r : ℕ) (x ε x' : ℝ), let old := j.referenceVisitChart i d ω (s j r);
          let w : ℝ → ℝ := fun t => d.driver t.toNNReal ω;
          d.curve ω (s j r) ∈ target.domain ω →
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q → 0 < ε →
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) →
          Tendsto (fun z => old.1 (current.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
          extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω ∩ regHull d.driver d.lifetime (s j r) ω →
          Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 (extendFrom H current.2.1 (ξ : ℂ))) →
          (∀ᶠ y in 𝓝[H] (x : ℂ), old.2.1 y ∈ H \ j.capacityReference i d (s j r) ω) →
          x' ∉ forceJumpSet (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
            (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) →
          Tendsto (fun y => fwdMap w (s j r) (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
          ∃ ℓ : ℝ,
          Tendsto (fun y => old.2.2 (old.2.1 y) - (logDerivFwd w (s j r) (old.2.1 y)).im)
            (𝓝[H] (x : ℂ)) (𝓝 ℓ) ∧
          forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
              (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) x' + chiC i.kappa * ℓ =
            forceBoundaryData target.kappa target.rhoL target.rhoR
              (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
                target.marksL a q ω - segDriver (target.curve ω) q)
              (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
                target.marksR a q ω - segDriver (target.curve ω) q)
              ξ + e.phase q ω * (Ioo
                (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                  segDriver (target.curve ω) q)
                (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                  segDriver (target.curve ω) q)).indicator 1 ξ - e.offset

/-- **`VisitReferenceAmbientCoverPosExcHull` at the rational original times from the lift input**: exceptional set
`lateExc ∪ X`; the force processes follow the coupling's paths. -/
theorem visitReferenceAmbientCoverPosExcHull_of_liftWord (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLW : LateAmbientLiftWord i d side (fun _ => rationalOriginalTime) X) :
    VisitReferenceAmbientCoverPosExcHull i d side (fun _ => rationalOriginalTime)
      (fun j q ω => lateExc j d q ω ∪ X j q ω) := by
  intro j hj target e zL zR q hq0
  filter_upwards [hCoupling.1.2.2.2.2, hLW j hj q hq0] with ω hp hlw hω hlive current ξ hξ hXω hCω
  obtain ⟨r, x, ε, x', hv, hQ, hε, hcol, htr, hz, hland, hev, hjump, hold⟩ :=
    late_exists_ambient_cover hj hRc (hLc j.seed) hω hp hlive ξ (fun h => hXω (Or.inl h)) hCω
  obtain ⟨ℓ, hℓ, hword⟩ :=
    hlw hω hlive ξ hξ (fun h => hXω (Or.inr h)) hCω r x ε x' hv hQ hε hcol htr hz hland hev hjump hold
  exact ⟨r, x, ε, x', ℓ, _, hv, hQ, hε, hcol, htr, hz, hland, hev, hjump, hold, hℓ, hword⟩

end InteractingSLE.Sec7.R5Ref
