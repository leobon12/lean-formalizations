/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfWord
import InteractingSLE.Spec.Sec7.R5LiftLate
import InteractingSLE.Spec.Sec7.SideC11Marks
import InteractingSLE.Spec.Sec7.SideC7Seeds

/-!
# Lemma R.5's common phase on the late side tests from the current chart alone

Packet PROVE-R5-LIFT2. The late lift input `R5Ref.LateAmbientLiftWord` reads the lift difference along the OLD
approach at the collar point `x`. Here it is obtained from the current chart, as for R.7 (`R5LfWord`):

* **`ref_old_lift_side_of_cur`**: for relative charts at capacities `p ≤ q` (`dom = C ∩ (ℍ ∖ K_s)` and
  `C ∩ (ℍ ∖ K_T)`), at a collar of the old chart whose landing lies in `C`: if the current lift minus `arg f_T′` tends
  to `2πn` at `ξ`, then the OLD lift minus `arg f_s′` tends to `2πn` at `x` (the old transition reflects at `x`, so the
  old limit is some `2πm`, and the collar carries it to the current chart, where it is `2πn`); the sides agree as in
  `R5Lift.ref_lift_side_of_cur`;
* `lateLeftStop` (def): the left stop `T⁰(q)` of the late target's pocket (either shape);
* **`late_cur_dom`**: the late current domain is `C ∩ (ℍ ∖ K_{T⁰(q)})`;
* `LateLiftCurGeom` (def, **named pathwise input**): the late analogue of `R5Lift.R7LiftCurGeom`;
* **`exists_lateAmbientLiftWord_of_cur`**: one integer field `N` such that `R5Ref.LateAmbientLiftWord` holds for
  every side data whose phase is `χ·2πN + offset` (the seed and ambient positions are proved here, from the signed
  initial marks of `Ready` and ordered ambient marks).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide

/-- **A reference's own lift limit from the current chart.** Relative charts of one driven curve at capacities
`p ≤ q` with domains `C ∩ (ℍ ∖ K_s)` (old) and `C ∩ (ℍ ∖ K_T)` (current); an unfilled old collar at `x` with
transition limit `x` at `ξ`, landing in `C`; `f_s ∘ old⁻¹ → x′ ≠ 0` at `x`. If the current lift minus `arg f_T′` tends
to `2πn` at `ξ` and the side of `ξ` is the side of its ambient image at time `T`, then the OLD lift minus `arg f_s′`
tends to `2πn` at `x`, the side of `ξ` is the side of `x′`, and `f_s ∘ cur⁻¹ → x′` at `ξ`. -/
theorem ref_old_lift_side_of_cur {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω} {p q : ℝ≥0}
    (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q)
    {ℓ : ℂ → ℂ} (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom) (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im)
    {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) {C : Set ℂ} (hCo : IsOpen C)
    (hCH : C ⊆ H) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hcurdom : ((relChart c γ q ω).dom : Set ℂ) = C ∩ (H \ fwdHull W T))
    (holddom : ((relChart c γ p ω).dom : Set ℂ) = C ∩ (H \ fwdHull W s)) {ξ x ε x' : ℝ} (hε : 0 < ε)
    (hcol : (relChart c γ p ω).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (relChart c γ q ω).dom)
    (htr : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    (hξC : extendFrom H (relChart c γ q ω).2.1 ξ ∈ C)
    (hland : Tendsto (relChart c γ p ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 (extendFrom H (relChart c γ q ω).2.1 ξ)))
    (hx'0 : x' ≠ 0)
    (hfo : Tendsto (fun y => fwdMap W s ((relChart c γ p ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ))) {n : ℤ}
    (hn : Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
      (logDerivFwd W T ((relChart c γ q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)))
    (hside : ∀ y : ℝ, Tendsto (fun z => fwdMap W T ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) →
      (ξ < 0 ↔ y < 0)) :
    Tendsto (fun y => (relChart c γ p ω).2.2 ((relChart c γ p ω).2.1 y) -
      (logDerivFwd W s ((relChart c γ p ω).2.1 y)).im) (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) ∧
      (ξ < 0 ↔ x' < 0) ∧
      Tendsto (fun y => fwdMap W s ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
  have hp : (p : ℝ≥0∞) < capLife (γ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hpq) hq
  have hcur := isConformal_relChart_of_driven (c := c) hγ hq hc
  have hold := isConformal_relChart_of_driven (c := c) hγ hp hc
  have hincl := relChart_dom_antitone hc hγ hq hpq
  obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := c) (γ := γ) hγ hq hE hEc
  obtain ⟨Fo, hFo, hFoc, -⟩ := exists_relative_inverse_extension (c := c) (γ := γ) (q := p) hγ hp hE hEc
  have hξC' : Fc ξ ∈ C := by rw [(tendsto_of_ext hFc hFcc ξ).2]; exact hξC
  have hxC : Fo x ∈ C := by
    have := nhdsWithin_H_neBot x
    rw [tendsto_nhds_unique (tendsto_of_ext hFo hFoc x).1 hland]; exact hξC
  -- the ambient image along the current approach
  have hfx : Tendsto (fun y => fwdMap W s ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr' : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ))
        (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨htr, eventually_nhdsWithin_of_forall fun z hz =>
        hold.fwd_mem (hincl (hcur.inv_mem_dom hz))⟩
    refine (hfo.comp htr').congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    simp only [Function.comp_apply]
    rw [hold.inv_fwd (hincl (hcur.inv_mem_dom hz))]
  obtain ⟨hcurlim, hsd⟩ := ref_lift_side_of_cur hcur hold hFc hFcc hFo hFoc hCo hCH hη hW hW0 hs hT hcurdom
    holddom hincl hε hcol hξC' hxC hx'0 hfx hfo (A := (relChart c γ q ω).2.2) hn hside
  -- the reference's own lattice limit
  obtain ⟨Lo, hLo, hlo⟩ := Aux29Cor.exists_isDerivLog_relChart (c := c) hγ hp hc hℓ hlift
  have hKs : ((relChart c γ p ω).dom : Set ℂ) ⊆ H \ fwdHull W s := by rw [holddom]; exact inter_subset_right
  obtain ⟨ρ, hρ, hlandK⟩ := exists_ball_landing_mem_hull hold hFo hFoc hCo hCH holddom hxC
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_hull_landing hold hFo hFoc hη hW hW0 hs hKs hρ hlandK
  obtain ⟨m, hm⟩ := exists_int_tendsto_lift_sub hold hLo hlo (isDerivLog_fwdMap hW hs) hρ
    (fun y hy => hKs (hold.inv_mem_dom hy.1)) hder hb
  -- through the collar the current limit is `2πm`
  have hcm := tendsto_relChart_lift_sub_of_old (A := fun z => (logDerivFwd W s z).im) hc hγ hq hpq hε hcol htr hm
  have := nhdsWithin_H_neBot ξ
  have hmn : (2 * Real.pi * m : ℝ) = 2 * Real.pi * n := tendsto_nhds_unique hcm hcurlim
  refine ⟨?_, hsd, hfx⟩
  rw [← hmn]
  exact hm

section Late

open Wire Wire.Current Wire.Current.SideTest
open PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan PocketStopField PocketStopWallsFin R5Phase R5Ref
  MartChar.RealFlow

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The left stop `T⁰(q)` of a late target's pocket** (bounded pocket or pocket opening at the flow seed). -/
def lateLeftStop (j : SideTest Ω) (d : WordObjects Ω) (q : ℝ≥0) (ω : Ω) : ℝ :=
  if j.infinite then leftStopInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω
  else leftStop d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω

/-- **The late current domain**: on a ready late test at a live relative capacity `q`, the ambient driver is a
continuous Loewner driver of the counterflow with infinite lifetime, `T⁰(q) ≥ 0`, and the current domain is
`C ∩ (ℍ ∖ K_{T⁰(q)})` (`R5Ref.current_dom_eq(Inf)`). -/
theorem late_cur_dom {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) :
    IsLoewnerTrace (fun t : ℝ => d.driver t.toNNReal ω) (d.curve ω) ∧
      Continuous (fun t : ℝ => d.driver t.toNNReal ω) ∧ (fun t : ℝ => d.driver t.toNNReal ω) 0 = 0 ∧
      d.lifetime ω = ⊤ ∧ 0 ≤ lateLeftStop j d q ω ∧
      ((relChart (j.target i d).baseChart (j.target i d).curve q ω).dom : Set ℂ) =
        (j.target i d).domain ω ∩ (H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (lateLeftStop j d q ω)) := by
  have hpc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hω' : ω ∈ j.event := by rwa [target_event] at hω
  rw [target_domain] at hpc ⊢
  rw [target_chart] at hpc
  obtain ⟨-, -, -, hG, hlife, hcfgP, hcfgI, -, hAG, -, hJ, -⟩ := hj
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
    have hωG := hAG hω'
    have hcfg := hcfgP ω hωG.1 hωG.2
    have hψ := hJ ω hω'
    have hcurve : (j.target i d).curve =
        travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hI, Bool.false_eq_true, ↓reduceIte]
    have hT : lateLeftStop j d q ω =
        leftStop d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω := by
      simp only [lateLeftStop, hI, Bool.false_eq_true, ↓reduceIte]
    rw [hcurve] at hq ⊢
    rw [hT]
    have h0 := leftStop_nonneg (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) hcfg hψ q
    refine ⟨hcfg.trace, hcfg.continuous_W, hcfg.W_zero, hlife ω hωG.1, h0, ?_⟩
    rw [current_dom_eq (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hq,
      ← hcfg.trace.2.2 _ h0]
  · simp only [hI, ↓reduceIte] at hAG hJ
    have hωG := hAG hω'
    have hcfg := hcfgI ω hωG.1 (le_antisymm (not_lt.1 hωG.2) ((hG ω hωG.1).1.changeCorner_props.1.1))
    have hψ := hJ ω hω'
    have hcurve : (j.target i d).curve =
        travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hI, ↓reduceIte]
    have hT : lateLeftStop j d q ω =
        leftStopInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω := by
      simp only [lateLeftStop, hI, ↓reduceIte]
    rw [hcurve] at hq ⊢
    rw [hT]
    have h0 := leftStopInf_nonneg (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) hcfg hψ q
    refine ⟨hcfg.trace, hcfg.continuous_W, hcfg.W_zero, hlife ω hωG.1, h0, ?_⟩
    rw [current_dom_eqInf (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) hω hcfg hψ hpc.1 hpc.2.1 hpc.2.2.1 hq,
      ← hcfg.trace.2.2 _ h0]

/-- **The remaining pathwise geometry of R.5's common phase on the late side tests, in the current chart** (named
input; the late analogue of `R5Lift.R7LiftCurGeom`): on every ready late test, at every positive live relative
capacity `q`, almost surely every coordinate `u` of the current open seed interval lands in `ℍ`, and if it lands in
the pocket, every real limit `y` of `f_T ∘ cur⁻¹` at `u` (`T = T⁰(q)`) lies on the side of `u`. -/
def LateLiftCurGeom (i : BothLow) (d : WordObjects Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) →
      ∀ u ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
            (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
          (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
            (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q),
        extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 u ∈ H ∧
        (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 u ∈
            (j.target i d).domain ω →
          ∀ y : ℝ, Tendsto (fun z => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (lateLeftStop j d q ω)
            ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) →
            (u < 0 ↔ y < 0))

/-- **`R5Ref.LateAmbientLiftWord` from the current chart's geometry**: with continuous walls, the coupling's integrated
path and ordered ambient marks, one integer field `N` such that the late lift input holds for every side data whose
phase is `χ·2πN + offset` (the seed and ambient positions of `R5Lift.LateLiftGeomCore` are proved here). -/
theorem exists_lateAmbientLiftWord_of_cur (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hpath : ∀ᵐ ω ∂d.measure, IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω)
      (fun a t => d.forceL a t ω) (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b) (h : LateLiftCurGeom i d) :
    ∃ N : SideTest Ω → ℝ≥0 → Ω → ℤ, ∀ side : SideTest Ω → Late.SideData Ω,
      (∀ j q ω, (side j).phase q ω = chiC i.kappa * (2 * Real.pi * N j q ω) + (side j).offset) →
      LateAmbientLiftWord i d side s X := by
  classical
  set Φ : SideTest Ω → ℝ≥0 → Ω → ℤ → Prop := fun j q ω n => ∀ u ∈ Ioo
      (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
        (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
      (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
        (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q),
    Tendsto (fun y => (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.2
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y) -
      (logDerivFwd (fun t : ℝ => d.driver t.toNNReal ω) (lateLeftStop j d q ω)
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y)).im) (𝓝[H] (u : ℂ))
      (𝓝 (2 * Real.pi * n)) with hΦ
  -- the integer of the current chart
  have hex : ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → ∃ n, Φ j q ω n := by
    intro j hj q hq
    filter_upwards [h j hj q hq] with ω hω hE hlive
    obtain ⟨⟨hcc, hℓ, hlift⟩, ⟨E, hE', hEc⟩, -⟩ := baseChart_aux29Facts (i := i) hj hE
    have hγ := isDrivenCurve_target (i := i) hj ω hE
    obtain ⟨hη, hW, hW0, -, hT, hd⟩ := late_cur_dom hj hRc (hLc j.seed) hE hlive
    have hcdom : (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω :=
      ((isPocketChartOn hj hRc (hLc j.seed) (i := i)).1 ω hE).2.1
    obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := (j.target i d).baseChart)
      (γ := (j.target i d).curve) hγ hlive hE' hEc
    obtain ⟨Lc, hLc', hlc⟩ := Aux29Cor.exists_isDerivLog_relChart (c := (j.target i d).baseChart) hγ hlive hcc hℓ
      hlift
    have hcur := isConformal_relChart_of_driven (c := (j.target i d).baseChart) hγ hlive hcc
    obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
    refine exists_int_forall_tendsto_cur hcur hLc' hlc hFc hFcc hη hW hW0 hT
      (by rw [hd]; exact inter_subset_right) fun u hu => ?_
    obtain ⟨hlim, hFu⟩ := tendsto_of_ext hFc hFcc u
    refine landing_mem_hull_of_mem_seed_interval hmL hmR hcc hγ hlive hq hE' hEc hcdom
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hT) hd hu hlim ?_
    rw [hFu]; exact ((hω hE hlive) u hu).1
  set N : SideTest Ω → ℝ≥0 → Ω → ℤ := fun j q ω =>
    if hh : j.Ready d ∧ 0 < q ∧ ω ∈ (j.target i d).event ∧ (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) ∧
      ∃ n, Φ j q ω n then Classical.choose hh.2.2.2.2 else 0 with hN
  refine ⟨N, fun side hside => ?_⟩
  intro j hj target e zL zR q hq
  filter_upwards [hex j hj q hq, h j hj q hq, hpath] with ω hexω hω hp hE hlive current ξ hξ hX hC r x ε x' old w
    hv hcap hε hcol htr hland hinv hev hx' hfo
  have hh : j.Ready d ∧ 0 < q ∧ ω ∈ (j.target i d).event ∧ (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) ∧
      ∃ n, Φ j q ω n := ⟨hj, hq, hE, hlive, hexω hE hlive⟩
  have hNspec : Φ j q ω (N j q ω) := by
    rw [hN]; simp only [hh, and_self, ↓reduceDIte]
    exact Classical.choose_spec hh.2.2.2.2
  -- the data of the sample
  obtain ⟨⟨hcc, hℓ, hlift⟩, ⟨E, hE', hEc⟩, -⟩ := baseChart_aux29Facts (i := i) hj hE
  have hγ := isDrivenCurve_target (i := i) hj ω hE
  obtain ⟨hη, hW, hW0, hζ, hT, hd⟩ := late_cur_dom hj hRc (hLc j.seed) hE hlive
  have hcdom : (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω :=
    ((isPocketChartOn hj hRc (hLc j.seed) (i := i)).1 ω hE).2.1
  have hCo := isOpen_domain (i := i) hj ω hE
  have hCH : (j.target i d).domain ω ⊆ H := by rw [← hcdom]; exact hcc.dom_subset
  have hs0 : (0 : ℝ) ≤ (s j r : ℝ) := (s j r).coe_nonneg
  have hDC := isDomainChart_referenceVisitChart hj hRc (hLc j.seed) hE hη hs0 hv
  have holddom : ((j.referenceVisitChart i d ω (s j r)).dom : Set ℂ) =
      (j.target i d).domain ω ∩ (H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (s j r)) := by
    rw [hDC.coe_dom, ← hη.2.2 _ hs0]
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := (j.target i d).baseChart)
    (γ := (j.target i d).curve) hγ hlive hE' hEc
  have hcurland := (tendsto_of_ext hFc hFcc ξ)
  rw [hcurland.2] at hcurland
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
  have hξI := mem_seed_interval_of_landing (iL := Late.leftZero i d j) (iR := Late.rightZero i d j) hmL hmR hcc
    hγ hlive hcurland.1 (show _ ∈ (((j.target i d).baseChart ω).dom : Set ℂ) by rw [hcdom]; exact hC)
  obtain ⟨hlim, hsd, hfx⟩ := ref_old_lift_side_of_cur hcc hγ hlive hcap hℓ hlift hE' hEc hCo hCH hη hW hW0 hs0
    hT hd holddom hε hcol htr hC hinv hx'0 hfo (hNspec ξ hξI) ((hω hE hlive ξ hξI).2 hC)
  refine ⟨2 * Real.pi * N j q ω, hlim, ?_⟩
  -- the current seeds are innermost
  obtain ⟨Wl, hWl, -, q', hqq', hWeq, -⟩ := exists_relChart_eq_loewner (c := (j.target i d).baseChart) hγ hlive
  have hEq : EqOn (fun r : ℝ => (fun t ω => segDriver ((j.target i d).curve ω) t) r.toNNReal ω) Wl
      (Icc 0 (q : ℝ)) := fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hWl hEq
  obtain ⟨hsL, hsR⟩ := initial_marks_signed_of_ready hj hE
  have hvL : ∀ a, geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
      segDriver ((j.target i d).curve ω) q ≤ geomLW (fun t ω => segDriver ((j.target i d).curve ω) t)
        (j.target i d).marksL (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q := by
    intro a
    have h1 := congrFun hLeq a
    have h2 := congrFun hLeq (Late.leftZero i d j)
    rw [h1, h2, hmL, neg_zero]
    have := rightImg_mono_index (w := fun r => -Wl r) hWl.neg q.coe_nonneg
      (show (0 : ℝ) ≤ -(j.target i d).marksL ω a by linarith [hsL a])
    linarith
  have hvR : ∀ b, geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
      (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q ≤
        geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR b q ω -
          segDriver ((j.target i d).curve ω) q := by
    intro b
    have h1 := congrFun hReq b
    have h2 := congrFun hReq (Late.rightZero i d j)
    rw [h1, h2, hmR]
    have := rightImg_mono_index hWl q.coe_nonneg (hsR b)
    linarith
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (s j r) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 : (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
        ((j.referenceVisitChart i d ω (s j r)).dom : Set ℂ) :=
      relChart_dom_antitone hcc hγ hlive hcap
        ((isConformal_relChart_of_driven (c := (j.target i d).baseChart) hγ hlive hcc).inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hamb := mem_ambient_seed_interval hη hW hW0 hs0 (hCH hC) hcurland.1 hcurK hfx
  have hV : Continuous fun t : ℝ≥0 => d.driver t ω := by
    have h1 := hW.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h1
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp hζ hV fun _ => rfl
  have hWs : d.driver ((s j r : ℝ)).toNNReal ω = d.driver (s j r) ω := by rw [Real.toNNReal_coe]
  obtain ⟨hVLpos, hVRpos⟩ := ambient_force_positions (VL := fun a => d.forceL a (s j r) ω)
    (VR := fun a => d.forceR a (s j r) ω) (xL := d.xL) (xR := d.xR) hW hs0 hxL₀ hxR₀
    (fun a => hL a (s j r)) (fun b => hR b (s j r)) hamb
  rw [hWs] at hVLpos hVRpos
  -- the word
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
    hvL hvR hξI (fun _ => hVLpos) (fun _ => hVRpos) hsd (2 * Real.pi * N j q ω) e.offset


/-- **`R5Ref.LateAmbientLiftWord` for the side data with the lift phase** from the current chart's geometry: the
integer field `N` of `exists_lateAmbientLiftWord_of_cur`, for `fun j => withLiftPhase (side j) i.kappa (N j)`. -/
theorem exists_lateAmbientLiftWord_withLiftPhase_of_cur (i : BothLow) (d : WordObjects Ω) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hpath : ∀ᵐ ω ∂d.measure, IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω)
      (fun a t => d.forceL a t ω) (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b) (h : LateLiftCurGeom i d) :
    ∃ N : SideTest Ω → ℝ≥0 → Ω → ℤ, ∀ side : SideTest Ω → Late.SideData Ω,
      LateAmbientLiftWord i d (fun j => withLiftPhase (side j) i.kappa (N j)) s X := by
  obtain ⟨N, hN⟩ := exists_lateAmbientLiftWord_of_cur i d s X hRc hLc hpath hxL₀ hxR₀ h
  exact ⟨N, fun side => hN _ fun j q ω => rfl⟩

end Late

end InteractingSLE.Sec7.R5Lift
