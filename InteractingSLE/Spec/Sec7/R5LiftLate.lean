/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftHull
import InteractingSLE.Spec.Sec7.R5RefLate

/-!
# Lemma R.5's common phase on the late side tests: `R5Ref.LateAmbientLiftWord` (ruling R86)

Packet PROVE-R5-LIFT. The late hull-landing cover `R5Ref.VisitReferenceAmbientCoverPosExcHull` reduces (R5-REFCHART,
`R5Ref.visitReferenceAmbientCoverPosExcHull_of_liftWord`) to `R5Ref.LateAmbientLiftWord`: on every selected collar of
every interior-visit reference at a rational original time, the limit `ℓ` of "old lift − ambient lift" along the old
approach and the word identity with the side data's PRESCRIBED phase `e.phase q ω` and offset `e.offset`.

* `LateLiftGeom` (def, **named pathwise input**): almost surely on every live late test, the ambient driver is
  continuous, every interior-visit reference avoids the ambient hull at its time and reflects against it on `J`, the
  references are directed, and every selected collar has its collar point in `J` with the exposed-side position data;
* `LateLiftGeomCore` (def, **named pathwise input**): the same without the driver continuity and the reference
  domains, which follow from `Ready` (**`late_ref_facts`**, **`lateLiftGeom_of_core`**);
* `withLiftPhase` (def): the side data with phase `χ·2πM + offset` (all other fields unchanged);
* **`exists_lateAmbientLiftWord`**: an integer field `N` such that `R5Ref.LateAmbientLiftWord` holds for every side
  data whose phase is `χ·2πN + offset`; **`lateAmbientLiftWord_withLiftPhase`**: in particular for
  `fun j => withLiftPhase (side j) κ (N j)`.

The proof is the generic core `R5Lift.exists_int_common_pathwise` (the reference's own lattice limit on its reflecting
set equals the common integer of the current chart) and `R5Lift.word_identity_exposed_indicator`, with
`(j.target i d).kappa = i.kappa` (`Late.target_kappa`). Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open Wire Wire.Current Wire.Current.SideTest
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketWordAssembly
  PocketSeedOpen PocketCoord PocketJordan PocketStopField PocketStopWallsFin R5Phase R5Ref

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The pathwise geometry of R.5's common phase on the late side tests** (named input; see the module docstring).
The references are the interior visits at the times `s j r` with visit capacity at most `q`. -/
def LateLiftGeom (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (J : SideTest Ω → ℝ≥0 → ℕ → Ω → Set ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) →
      Continuous (fun t : ℝ => d.driver t.toNNReal ω) ∧
      (∀ r, d.curve ω (s j r) ∈ (j.target i d).domain ω → (j.visitCapacity d ω (s j r)).toNNReal ≤ q →
        ((j.referenceVisitChart i d ω (s j r)).dom : Set ℂ) ⊆
          H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (s j r) ∧
        IsAmbReflecting (j.referenceVisitChart i d ω (s j r)) (fun t : ℝ => d.driver t.toNNReal ω) (s j r)
          (J j q r ω)) ∧
      IsDirectedRefs (fun r => d.curve ω (s j r) ∈ (j.target i d).domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q)
        (fun r => j.referenceVisitChart i d ω (s j r)) (relChart (j.target i d).baseChart (j.target i d).curve q ω)
        (fun r => J j q r ω) (fun t : ℝ => d.driver t.toNNReal ω) (fun r => (s j r : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
            segDriver ((j.target i d).curve ω) q)
          (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a q ω -
            segDriver ((j.target i d).curve ω) q) →
        extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉ X j q ω →
        extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∈
          (j.target i d).domain ω →
        ∀ (r : ℕ) (x ε x' : ℝ),
          d.curve ω (s j r) ∈ (j.target i d).domain ω →
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q → 0 < ε →
          (j.referenceVisitChart i d ω (s j r)).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆
            ((relChart (j.target i d).baseChart (j.target i d).curve q ω).dom : Set ℂ) →
          Tendsto (fun z => (j.referenceVisitChart i d ω (s j r)).1
            ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
          extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∈
            (j.target i d).domain ω ∩ regHull d.driver d.lifetime (s j r) ω →
          Tendsto (j.referenceVisitChart i d ω (s j r)).2.1 (𝓝[H] (x : ℂ))
            (𝓝 (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ))) →
          (∀ᶠ y in 𝓝[H] (x : ℂ), (j.referenceVisitChart i d ω (s j r)).2.1 y ∈
            H \ j.capacityReference i d (s j r) ω) →
          x' ∉ forceJumpSet (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
            (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) →
          Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (s j r)
            ((j.referenceVisitChart i d ω (s j r)).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
          x ∈ J j q r ω ∧
          (∀ a, geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω ≤
            geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL (Late.leftZero i d j) q ω) ∧
          (∀ b, geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
              (Late.rightZero i d j) q ω ≤
            geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR b q ω) ∧
          ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
              (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
            (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
              (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q) ∧
          (x' < 0 → ∀ a, d.forceL a (s j r) ω - d.driver (s j r) ω ≤ x') ∧
          (0 ≤ x' → ∀ a, x' < d.forceR a (s j r) ω - d.driver (s j r) ω) ∧
          (ξ < 0 ↔ x' < 0)

/-- **The late references' Loewner facts from `Ready`**: on the test, the ambient driver is continuous, and the chart of
every interior visit at an original time `t` with visit capacity at most a live `q` avoids the ambient hull at `t`
(`R5Phase.reference_chart_at_visit(Inf)` with the hull itself as reference set, `R5Phase.H_diff_liveExt_zero`). -/
theorem late_ref_facts {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) :
    Continuous (fun t : ℝ => d.driver t.toNNReal ω) ∧
    ∀ t : ℝ≥0, d.curve ω t ∈ (j.target i d).domain ω → (j.visitCapacity d ω t).toNNReal ≤ q →
      ((j.referenceVisitChart i d ω t).dom : Set ℂ) ⊆ H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) t := by
  have hpc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hω' : ω ∈ j.event := by rwa [target_event] at hω
  rw [target_domain] at hpc ⊢
  rw [target_chart] at hpc
  obtain ⟨-, -, -, hG, -, hcfgP, hcfgI, -, hAG, -, hJ, -⟩ := hj
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
    have hωG := hAG hω'
    have hcfg := hcfgP ω hωG.1 hωG.2
    have hψ := hJ ω hω'
    have hγ := (hcfg.isDrivenCurve hψ).1
    have hcurve : (j.target i d).curve =
        travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hI, Bool.false_eq_true, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hI, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [hcurve] at hq
    refine ⟨hcfg.continuous_W, fun t hv hcap => ?_⟩
    rw [hvc] at hcap
    have hOld := reference_chart_at_visit (W := fun ω (s : ℝ) => d.driver s.toNNReal ω)
      (F := fun ω => fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hv rfl hq hcap
    have hdomEq : ((j.referenceVisitChart i d ω t).dom : Set ℂ) =
        H \ liveExt (j.target i d).event
          (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
          (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (fun ω => fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) 0 ω := by
      rw [SideTest.referenceVisitChart, hcurve, hvc]
      exact hOld.2.2
    intro z hz
    rw [hdomEq, H_diff_liveExt_zero hω hγ] at hz
    exact hz.2
  · simp only [hI, ↓reduceIte] at hAG hJ
    have hωG := hAG hω'
    have hcfg := hcfgI ω hωG.1 (le_antisymm (not_lt.1 hωG.2) ((hG ω hωG.1).1.changeCorner_props.1.1))
    have hψ := hJ ω hω'
    have hγ := (hcfg.isDrivenCurve hψ).1
    have hcurve : (j.target i d).curve =
        travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hI, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hI, ↓reduceIte]
      rfl
    rw [hcurve] at hq
    refine ⟨hcfg.continuous_W, fun t hv hcap => ?_⟩
    rw [hvc] at hcap
    have hOld := reference_chart_at_visitInf (W := fun ω (s : ℝ) => d.driver s.toNNReal ω)
      (F := fun ω => fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hv rfl hq hcap
    have hdomEq : ((j.referenceVisitChart i d ω t).dom : Set ℂ) =
        H \ liveExt (j.target i d).event
          (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
          (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (fun ω => fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) 0 ω := by
      rw [SideTest.referenceVisitChart, hcurve, hvc]
      exact hOld.2.2
    intro z hz
    rw [hdomEq, H_diff_liveExt_zero hω hγ] at hz
    exact hz.2

/-- **The geometric core of `LateLiftGeom`** (named input): `LateLiftGeom` without the driver continuity and the
reference domains, which follow from `Ready` (`late_ref_facts`, `lateLiftGeom_of_core`). -/
def LateLiftGeomCore (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (J : SideTest Ω → ℝ≥0 → ℕ → Ω → Set ℝ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) →
      (∀ r, d.curve ω (s j r) ∈ (j.target i d).domain ω → (j.visitCapacity d ω (s j r)).toNNReal ≤ q →
        IsAmbReflecting (j.referenceVisitChart i d ω (s j r)) (fun t : ℝ => d.driver t.toNNReal ω) (s j r)
          (J j q r ω)) ∧
      IsDirectedRefs (fun r => d.curve ω (s j r) ∈ (j.target i d).domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q)
        (fun r => j.referenceVisitChart i d ω (s j r)) (relChart (j.target i d).baseChart (j.target i d).curve q ω)
        (fun r => J j q r ω) (fun t : ℝ => d.driver t.toNNReal ω) (fun r => (s j r : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
            segDriver ((j.target i d).curve ω) q)
          (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a q ω -
            segDriver ((j.target i d).curve ω) q) →
        extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉ X j q ω →
        extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∈
          (j.target i d).domain ω →
        ∀ (r : ℕ) (x ε x' : ℝ),
          d.curve ω (s j r) ∈ (j.target i d).domain ω →
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q → 0 < ε →
          (j.referenceVisitChart i d ω (s j r)).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆
            ((relChart (j.target i d).baseChart (j.target i d).curve q ω).dom : Set ℂ) →
          Tendsto (fun z => (j.referenceVisitChart i d ω (s j r)).1
            ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
          extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∈
            (j.target i d).domain ω ∩ regHull d.driver d.lifetime (s j r) ω →
          Tendsto (j.referenceVisitChart i d ω (s j r)).2.1 (𝓝[H] (x : ℂ))
            (𝓝 (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ))) →
          (∀ᶠ y in 𝓝[H] (x : ℂ), (j.referenceVisitChart i d ω (s j r)).2.1 y ∈
            H \ j.capacityReference i d (s j r) ω) →
          x' ∉ forceJumpSet (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
            (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) →
          Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (s j r)
            ((j.referenceVisitChart i d ω (s j r)).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
          x ∈ J j q r ω ∧
          (∀ a, geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω ≤
            geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL (Late.leftZero i d j) q ω) ∧
          (∀ b, geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
              (Late.rightZero i d j) q ω ≤
            geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR b q ω) ∧
          ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
              (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
            (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
              (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q) ∧
          (x' < 0 → ∀ a, d.forceL a (s j r) ω - d.driver (s j r) ω ≤ x') ∧
          (0 ≤ x' → ∀ a, x' < d.forceR a (s j r) ω - d.driver (s j r) ω) ∧
          (ξ < 0 ↔ x' < 0)

/-- **`LateLiftGeom` from its geometric core** and the walls' continuity. -/
theorem lateLiftGeom_of_core {i : BothLow} {d : WordObjects Ω} {s : SideTest Ω → ℕ → ℝ≥0}
    {X : SideTest Ω → ℝ≥0 → Ω → Set ℂ} {J : SideTest Ω → ℝ≥0 → ℕ → Ω → Set ℝ}
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (h : LateLiftGeomCore i d s X J) : LateLiftGeom i d s X J := by
  intro j hj q hq
  filter_upwards [h j hj q hq] with ω hω hE hlive
  obtain ⟨hrefl, hdir, hpos⟩ := hω hE hlive
  obtain ⟨hW, hK⟩ := late_ref_facts (i := i) hj hRc (hLc j.seed) hE hlive
  exact ⟨hW, fun r hv hcap => ⟨hK (s j r) hv hcap, hrefl r hv hcap⟩, hdir, hpos⟩

/-- **Late side data with the lift phase**: the phase `χ·2πM + offset`, every other field unchanged. -/
def withLiftPhase (e : Late.SideData Ω) (κ : ℝ) (M : ℝ≥0 → Ω → ℤ) : Late.SideData Ω :=
  { e with phase := fun q ω => chiC κ * (2 * Real.pi * M q ω) + e.offset }

omit [MeasurableSpace Ω] in
theorem withLiftPhase_phase (e : Late.SideData Ω) (κ : ℝ) (M : ℝ≥0 → Ω → ℤ) (q : ℝ≥0) (ω : Ω) :
    (withLiftPhase e κ M).phase q ω = chiC κ * (2 * Real.pi * M q ω) + e.offset := rfl

omit [MeasurableSpace Ω] in
theorem withLiftPhase_offset (e : Late.SideData Ω) (κ : ℝ) (M : ℝ≥0 → Ω → ℤ) :
    (withLiftPhase e κ M).offset = e.offset := rfl

/-- **`R5Ref.LateAmbientLiftWord` from the common-phase geometry**: one integer field `N` such that the late lift
input holds for every side data whose phase is `χ·2πN + offset`. -/
theorem exists_lateAmbientLiftWord (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) {J : SideTest Ω → ℝ≥0 → ℕ → Ω → Set ℝ} (h : LateLiftGeom i d s X J) :
    ∃ N : SideTest Ω → ℝ≥0 → Ω → ℤ, ∀ side : SideTest Ω → Late.SideData Ω,
      (∀ j q ω, (side j).phase q ω = chiC i.kappa * (2 * Real.pi * N j q ω) + (side j).offset) →
      LateAmbientLiftWord i d side s X := by
  classical
  set Φ : SideTest Ω → ℝ≥0 → Ω → ℤ → Prop := fun j q ω n => ∀ (r : ℕ) (x : ℝ),
    (d.curve ω (s j r) ∈ (j.target i d).domain ω ∧ (j.visitCapacity d ω (s j r)).toNNReal ≤ q) →
    (∃ ξ : ℝ, IsGoodRef (j.referenceVisitChart i d ω (s j r))
      (relChart (j.target i d).baseChart (j.target i d).curve q ω) (J j q r ω) ξ) → x ∈ J j q r ω →
    Tendsto (fun y => (j.referenceVisitChart i d ω (s j r)).2.2 ((j.referenceVisitChart i d ω (s j r)).2.1 y) -
      (logDerivFwd (fun t : ℝ => d.driver t.toNNReal ω) (s j r) ((j.referenceVisitChart i d ω (s j r)).2.1 y)).im)
      (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) with hΦ
  have hex : ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → ∃ n, Φ j q ω n := by
    intro j hj q hq
    filter_upwards [h j hj q hq] with ω hω hE hlive
    obtain ⟨hW, hQ, hdir, -⟩ := hω hE hlive
    obtain ⟨⟨hcc, hℓ, hlift⟩, -, -⟩ := baseChart_aux29Facts (i := i) hj hE
    have hγ := isDrivenCurve_target (i := i) hj ω hE
    obtain ⟨n, -, hn⟩ := exists_int_common_pathwise (c := (j.target i d).baseChart) (γ := (j.target i d).curve)
      (ω := ω) (p := fun r => (j.visitCapacity d ω (s j r)).toNNReal)
      (Q := fun r => d.curve ω (s j r) ∈ (j.target i d).domain ω ∧ (j.visitCapacity d ω (s j r)).toNNReal ≤ q)
      (W := fun t : ℝ => d.driver t.toNNReal ω) (σ := fun r => (s j r : ℝ)) (J := fun r => J j q r ω)
      hcc hγ hlive hℓ hlift hW (fun r => (s j r).coe_nonneg)
      (fun r hr => ⟨hr.2, (hQ r hr.1 hr.2).1, (hQ r hr.1 hr.2).2⟩) hdir
    exact ⟨n, fun r x hr hgood hx => hn r hr hgood x hx⟩
  set N : SideTest Ω → ℝ≥0 → Ω → ℤ := fun j q ω =>
    if hh : j.Ready d ∧ 0 < q ∧ ω ∈ (j.target i d).event ∧ (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) ∧
      ∃ n, Φ j q ω n then Classical.choose hh.2.2.2.2 else 0 with hN
  refine ⟨N, fun side hside => ?_⟩
  intro j hj target e zL zR q hq
  filter_upwards [hex j hj q hq, h j hj q hq] with ω hexω hω hE hlive current ξ hξ hX hC r x ε x' old w hv hcap
    hε hcol htr hland hinv hev hx' hfo
  have hh : j.Ready d ∧ 0 < q ∧ ω ∈ (j.target i d).event ∧ (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) ∧
      ∃ n, Φ j q ω n := ⟨hj, hq, hE, hlive, hexω hE hlive⟩
  have hNspec : Φ j q ω (N j q ω) := by
    rw [hN]; simp only [hh, and_self, ↓reduceDIte]
    exact Classical.choose_spec hh.2.2.2.2
  obtain ⟨hxJ, hvL, hvR, hξI, hVL, hVR, hsd⟩ :=
    (hω hE hlive).2.2.2 ξ hξ hX hC r x ε x' hv hcap hε hcol htr hland hinv hev hx' hfo
  have hlim := hNspec r x ⟨hv, hcap⟩ ⟨ξ, x, ε, hxJ, hε, hcol, htr⟩ hxJ
  refine ⟨2 * Real.pi * N j q ω, hlim, ?_⟩
  have htg : target = j.target i d := rfl
  have hk : (j.target i d).kappa = i.kappa := by
    rw [Late.target_kappa]
    have := i.kappa_gt_four
    field_simp
  have hph : e.phase q ω = chiC i.kappa * (2 * Real.pi * N j q ω) + e.offset := hside j q ω
  rw [hph, show target.kappa = i.kappa from hk]
  exact word_identity_exposed_indicator (κ := i.kappa) _ _ _ _
    (vL := fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
      segDriver ((j.target i d).curve ω) q)
    (vR := fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a q ω -
      segDriver ((j.target i d).curve ω) q)
    (fun a => sub_le_sub_right (hvL a) _) (fun b => sub_le_sub_right (hvR b) _) hξI hVL hVR hsd
    (2 * Real.pi * N j q ω) e.offset

/-- **`R5Ref.LateAmbientLiftWord` for the side data with the lift phase**: given the common-phase geometry, the
integer field `N` of `exists_lateAmbientLiftWord` and any side data `side`, the lift input holds for
`fun j => withLiftPhase (side j) i.kappa (N j)` (only the phase is changed). -/
theorem exists_lateAmbientLiftWord_withLiftPhase (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) {J : SideTest Ω → ℝ≥0 → ℕ → Ω → Set ℝ} (h : LateLiftGeom i d s X J) :
    ∃ N : SideTest Ω → ℝ≥0 → Ω → ℤ, ∀ side : SideTest Ω → Late.SideData Ω,
      LateAmbientLiftWord i d (fun j => withLiftPhase (side j) i.kappa (N j)) s X := by
  obtain ⟨N, hN⟩ := exists_lateAmbientLiftWord i d s X h
  exact ⟨N, fun side => hN _ fun j q ω => rfl⟩

end InteractingSLE.Sec7.R5Lift
