/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefLate
import InteractingSLE.Spec.Sec7.R5WallOuterGeomInf
import InteractingSLE.Spec.Sec7.ColCovHeight

/-!
# The geometry of the late exposed landings on the pocket walls (ruling R86a)

Packet PROVE-COLLAR-COVER. R5-WALL's pathwise geometry of an exposed wall landing on an R.7 test
(`R5Wall.exists_outer_cover`, `R5Wall.exists_outer_coverInf`) transferred to the late side tests, as R5-REFCHART's
`R5Ref.late_exists_ambient_cover` transfers the hull-landing geometry:

* `lateOuterExc` (def): R5-WALL's exceptional set `outerExc` / `outerExcInf` of the test's pocket (the first- or
  last-visit attachments and `0`; finite: `lateOuterExc_finite`);
* **`eventually_old_mem_freeNear`** (generic topology): if the current approach of an unfilled collar eventually lies
  in an `E`-free component of `(ℍ ∖ K) ∩ B(p, ρ)` and the old chart's domain misses `K`, the OLD approach at the collar
  point eventually lies there too (the old image of a small half-disc is connected and contains current points);
* **`late_exists_outer_cover`**: at a positive live relative capacity, every exposed current coordinate whose landing
  lies outside the pocket, off `lateExc ∪ lateOuterExc`, has a rational original visit `t` with an `IsRefCollar`
  collar, the landing in `K_t`, the OLD approach eventually in an `E`-free component of `(ℍ ∖ K_t) ∩ B(p, ρ)`, and an
  ambient image `x′` off the ambient jumps reached by `f_t` along the current and the old approach.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketWordAssembly
  PocketSeedOpen PocketCoord PocketJordan PocketStopField PocketStopWallsFin R5Phase R5Ref MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)
open LocalSets Aux119Heights WholeField
open Theorem14.SB.FinRel (freeNear)

/-! ### Generic topology -/

/-- **The old approach of a collar inherits the `freeNear` property of the current approach**: for conformal charts
with `cur.dom ⊆ old.dom ⊆ ℍ ∖ K`, if the transition `old⁻¹ ∘ cur` tends to `x` at `ξ`, the old chart lands at `p` from
`x`, and the current approach is eventually in `freeNear E K p ρ`, then so is the old approach at `x`. -/
theorem eventually_old_mem_freeNear {old cur : Chart} (hold : old.IsConformal) (hcur : cur.IsConformal)
    (hincl : (cur.dom : Set ℂ) ⊆ old.dom) {E K : Set ℂ} (hK : (old.dom : Set ℂ) ⊆ H \ K) {ξ x : ℝ} {p : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (htr : Tendsto (fun z => old.1 (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    (hland : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (hfree : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ freeNear E K p ρ) :
    ∀ᶠ y in 𝓝[H] (x : ℂ), old.2.1 y ∈ freeNear E K p ρ := by
  have hb : ∀ᶠ y in 𝓝[H] (x : ℂ), old.2.1 y ∈ ball p ρ := hland (ball_mem_nhds p hρ)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hb
  set S := old.2.1 '' (H ∩ ball (x : ℂ) δ) with hS
  have hSsub : S ⊆ (H \ K) ∩ ball p ρ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hK (hold.inv_mem_dom hy.1), hsub ⟨hy.2, hy.1⟩⟩
  have hconv : Convex ℝ (H ∩ ball (x : ℂ) δ) :=
    (convex_halfSpace_gt Complex.imLm.isLinear 0).inter (convex_ball _ _)
  have hSconn : IsPreconnected S := hconv.isPreconnected.image _ (hold.1.continuousOn.mono inter_subset_left)
  have hev : ∀ᶠ z in 𝓝[H] (ξ : ℂ), z ∈ H ∧ old.1 (cur.2.1 z) ∈ ball (x : ℂ) δ ∧
      cur.2.1 z ∈ freeNear E K p ρ :=
    (show ∀ᶠ z in 𝓝[H] (ξ : ℂ), z ∈ H from self_mem_nhdsWithin).and
      ((show ∀ᶠ z in 𝓝[H] (ξ : ℂ), old.1 (cur.2.1 z) ∈ ball (x : ℂ) δ from htr (ball_mem_nhds _ hδ)).and hfree)
  have := R5Lift.nhdsWithin_H_neBot ξ
  obtain ⟨z, hzH, hzb, hzF⟩ := hev.exists
  have hzdom : cur.2.1 z ∈ (old.dom : Set ℂ) := hincl (hcur.inv_mem_dom hzH)
  have hzS : cur.2.1 z ∈ S := ⟨old.1 (cur.2.1 z), ⟨hold.fwd_mem hzdom, hzb⟩, hold.inv_fwd hzdom⟩
  have hSC : S ⊆ connectedComponentIn ((H \ K) ∩ ball p ρ) (cur.2.1 z) :=
    hSconn.subset_connectedComponentIn hzS hSsub
  have hmem : ∀ᶠ y in 𝓝[H] (x : ℂ), y ∈ H ∩ ball (x : ℂ) δ :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ))
  filter_upwards [hmem] with y hy
  have hyS : old.2.1 y ∈ S := mem_image_of_mem _ hy
  refine ⟨hSsub hyS, ?_⟩
  rw [← connectedComponentIn_eq (hSC hyS)]
  exact hzF.2

/-! ### The late exceptional set -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- **R5-WALL's exceptional physical set at the exposed wall landings of a late side test**: `outerExc` (bounded
pocket) or `outerExcInf` (pocket opening at the flow seed) of its pocket. -/
def lateOuterExc (j : SideTest Ω) (d : WordObjects Ω) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  if j.infinite then R5Wall.outerExcInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω
  else R5Wall.outerExc d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω

theorem lateOuterExc_finite (j : SideTest Ω) (d : WordObjects Ω) (q : ℝ≥0) (ω : Ω) :
    (lateOuterExc j d q ω).Finite := by
  unfold lateOuterExc
  split_ifs
  · exact R5Wall.outerExcInf_finite _ _ _ _ _ _ _
  · exact R5Wall.outerExc_finite _ _ _ _ _ _ _

/-- The late seed interval is the seed interval of the single-seed marks. -/
theorem late_seed_interval_eq (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (W : ℝ≥0 → Ω → ℝ) (q : ℝ≥0)
    (ω : Ω) (c : ℝ) :
    Ioo (geomLW W (j.target i d).marksL (Late.leftZero i d j) q ω - c)
        (geomRW W (j.target i d).marksR (Late.rightZero i d j) q ω - c) =
      Ioo (geomLW W (fun _ : Ω => (![0] : Fin (0 + 1) → ℝ)) 0 q ω - c)
        (geomRW W (fun _ : Ω => (![0] : Fin (0 + 1) → ℝ)) 0 q ω - c) := by
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
  simp only [geomLW, geomRW, hmL, hmR, Matrix.cons_val_zero]

/-! ### The late outer cover geometry -/

/-- **The pathwise geometry of a late exposed landing on the pocket walls** (both pocket shapes; references at the
rational original times): see the module docstring. -/
theorem late_exists_outer_cover {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event)
    (hp : IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω) (fun a t => d.forceL a t ω)
      (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∉ lateExc j d q ω)
    (hO : extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∉ lateOuterExc j d q ω)
    (hI : ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
          (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
        (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
          (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q))
    (hC : extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∉
      (j.target i d).domain ω) :
    ∃ (r : ℕ) (x ε x' ρ : ℝ),
      d.curve ω (rationalOriginalTime r) ∈ (j.target i d).domain ω ∧
      (j.visitCapacity d ω (rationalOriginalTime r)).toNNReal ≤ q ∧
      R5Ref.IsRefCollar (j.referenceVisitChart i d ω (rationalOriginalTime r))
        (relChart (j.target i d).baseChart (j.target i d).curve q ω) ξ
        (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∈
        regHull d.driver d.lifetime (rationalOriginalTime r) ω ∧ 0 < ρ ∧
      (∀ᶠ y in 𝓝[H] (x : ℂ), (j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 y ∈
        freeNear (eventFilled j.event (j.target i d).domain (fun _ => ∅) ω)
          (regHull d.driver d.lifetime (rationalOriginalTime r) ω)
          (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ) ρ) ∧
      x' ∉ forceJumpSet (fun a => d.forceL a (rationalOriginalTime r) ω - d.driver (rationalOriginalTime r) ω)
        (fun a => d.forceR a (rationalOriginalTime r) ω - d.driver (rationalOriginalTime r) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r)
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r)
        ((j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  have hpc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  obtain ⟨-, hcExt, -⟩ := baseChart_aux29Facts (i := i) hj hω
  have hω' : ω ∈ j.event := by rwa [target_event] at hω
  have hI' := hI
  rw [late_seed_interval_eq] at hI'
  rw [target_domain] at hpc hC ⊢
  rw [target_chart] at hpc
  obtain ⟨-, -, -, hG, hlife, hcfgP, hcfgI, -, hAG, -, hJ, -⟩ := hj
  cases hIf : j.infinite
  · simp only [hIf, Bool.false_eq_true, ↓reduceIte] at hAG hJ
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
      simp only [target_curve, hIf, Bool.false_eq_true, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hIf, Bool.false_eq_true, ↓reduceIte]
      rfl
    have href : ∀ t, j.referenceVisitChart i d ω t = relChart (j.target i d).baseChart
        (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t).toNNReal ω := by
      intro t
      rw [SideTest.referenceVisitChart, hcurve, hvc]
    rw [hcurve] at hq hX hO hC hI' ⊢
    simp only [href, hvc]
    simp only [lateExc, lateOuterExc, hIf, Bool.false_eq_true, ↓reduceIte] at hX hO
    have hS : R5Wall.exposedOuterSel (j.target i d).baseChart
        (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (fun _ : Ω => (![0] : Fin (0 + 1) → ℝ)) (fun _ : Ω => (![0] : Fin (0 + 1) → ℝ)) q ω ξ :=
      ⟨fun h => h hI', hC⟩
    obtain ⟨r, x, ε, x', ρ, hM, hv, hcol, hpK, -, hρ, hfree, hjump, hcur, hold⟩ :=
      R5Wall.exists_outer_cover (A := (j.target i d).event) (c := (j.target i d).baseChart) (W' := d.driver)
        (ζ' := d.lifetime) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hcExt hζ (fun a t => hL a t) (fun b t => hR b t)
        rfl rfl hq ξ hX hO hS
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
    have hE : R5Same.pocketExt (j.target i d).event
        (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) ω =
        eventFilled j.event (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (fun _ => ∅) ω := by
      rw [R5Same.pocketExt, liveExt_of_live ⟨hω, PocketPhaseMeans.capLife_pos hγ⟩, eventFilled, ite_eq_left hω']
    rw [hE] at hfree
    have hcurC := isConformal_relChart_of_driven (c := (j.target i d).baseChart) hγ hq hpc.1
    have hfreeOld := eventually_old_mem_freeNear hOldAll.1 hcurC hOldAll.2.1
      (by rw [hdomEq]; exact inter_subset_right) hρ hcol.2.2.1 (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1 hfree
    exact ⟨r, x, ε, x', ρ, hv, hM.2.2.2.1, hcol, hpK, hρ, hfreeOld, hjump, hcur, hold⟩
  · simp only [hIf, ↓reduceIte] at hAG hJ
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
      simp only [target_curve, hIf, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hIf, ↓reduceIte]
      rfl
    have href : ∀ t, j.referenceVisitChart i d ω t = relChart (j.target i d).baseChart
        (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t).toNNReal ω := by
      intro t
      rw [SideTest.referenceVisitChart, hcurve, hvc]
    rw [hcurve] at hq hX hO hC hI' ⊢
    simp only [href, hvc]
    simp only [lateExc, lateOuterExc, hIf, ↓reduceIte] at hX hO
    have hS : R5Wall.exposedOuterSel (j.target i d).baseChart
        (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
        (fun _ : Ω => (![0] : Fin (0 + 1) → ℝ)) (fun _ : Ω => (![0] : Fin (0 + 1) → ℝ)) q ω ξ :=
      ⟨fun h => h hI', hC⟩
    obtain ⟨r, x, ε, x', ρ, hM, hv, hcol, hpK, -, hρ, hfree, hjump, hcur, hold⟩ :=
      R5Wall.exists_outer_coverInf (A := (j.target i d).event) (c := (j.target i d).baseChart) (W' := d.driver)
        (ζ' := d.lifetime) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hcExt hζ (fun a t => hL a t) (fun b t => hR b t)
        rfl rfl hq ξ hX hO hS
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
    have hE : R5Same.pocketExt (j.target i d).event
        (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) ω =
        eventFilled j.event (fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))
          (fun _ => ∅) ω := by
      rw [R5Same.pocketExt, liveExt_of_live ⟨hω, PocketPhaseMeans.capLife_pos hγ⟩, eventFilled, ite_eq_left hω']
    rw [hE] at hfree
    have hcurC := isConformal_relChart_of_driven (c := (j.target i d).baseChart) hγ hq hpc.1
    have hfreeOld := eventually_old_mem_freeNear hOldAll.1 hcurC hOldAll.2.1
      (by rw [hdomEq]; exact inter_subset_right) hρ hcol.2.2.1 (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1 hfree
    exact ⟨r, x, ε, x', ρ, hv, hM.2.2.2.1, hcol, hpK, hρ, hfreeOld, hjump, hcur, hold⟩

end InteractingSLE.Sec7.ColCov
