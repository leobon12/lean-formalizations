/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfLate
import InteractingSLE.Spec.Sec7.ColCovOuter

/-!
# R.5's common phase on the late side tests: one explicit integer for the hull and the wall landings

Packet PROVE-COLLAR-COVER. R5-LIFT2's `R5Lift.exists_lateAmbientLiftWord_of_cur` gives the late hull lift input
`R5Ref.LateAmbientLiftWord` at an integer field `N` it does not export, while the late cover also needs the outer lift
input (`ColCov.LateOuterLiftWord`, the exposed landings on the walls) at the SAME `N` (one phase per side data). Here
`N` is explicit:

* `lateCurPhaseProp` / `lateCurPhaseInt` (defs): the current integer, `cur lift − arg f_T′ → 2πn` on the whole open
  seed interval (`T = T⁰(q)`), chosen where it exists;
* **`ae_exists_lateCurPhase`**: under `R5Lift.LateLiftCurGeom` it exists almost surely on the live test;
* **`ref_old_lift_side_of_cur_land`**: R5-LIFT2's `ref_old_lift_side_of_cur` with the landing hypotheses
  (current landings near `ξ` in `K_T`, old landings near `x` in `K_s`) in place of "the landing lies in the pocket";
* **`late_word_of_ambient`**: the word identity at an exposed coordinate from the ambient image and the side;
* **`lateAmbientLiftWord_of_curInt`**: `R5Ref.LateAmbientLiftWord` for every side data with phase
  `χ·2π lateCurPhaseInt + offset` (R5-LIFT2's proof at the explicit integer);
* `LateOuterLiftGeom` (def, **named pathwise input**; the late twin of `R5Lift.R7OuterLiftGeom`): at the exposed wall
  landings, the side of every real limit of `f_T ∘ cur⁻¹`, and on every selected collar the old landings near the
  collar point lie in `K_s`;
* **`lateOuterLiftWord_of_curInt`**: `ColCov.LateOuterLiftWord` at the same phase.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide R5Lift

/-! ### The old lift from the current chart, with landing hypotheses -/

/-- **A reference's own lift limit from the current chart, with landing hypotheses** (R5-LIFT2's
`ref_old_lift_side_of_cur` with "landing in the pocket" replaced by: current landings near `ξ` lie in `K_T`, old
landings near `x` lie in `K_s`). -/
theorem ref_old_lift_side_of_cur_land {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω} {p q : ℝ≥0}
    (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q)
    {ℓ : ℂ → ℂ} (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom) (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im)
    {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hKT : ((relChart c γ q ω).dom : Set ℂ) ⊆ H \ fwdHull W T)
    (hKs : ((relChart c γ p ω).dom : Set ℂ) ⊆ H \ fwdHull W s) {ξ x ε x' : ℝ} (hε : 0 < ε)
    (hcol : (relChart c γ p ω).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (relChart c γ q ω).dom)
    (htr : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    (hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ → extendFrom H (relChart c γ q ω).2.1 v ∈ fwdHull W T)
    (hlandS : ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → extendFrom H (relChart c γ p ω).2.1 u ∈ fwdHull W s)
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
  -- the ambient image along the current approach
  have hfx : Tendsto (fun y => fwdMap W s ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr' : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ))
        (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨htr, eventually_nhdsWithin_of_forall fun z hz =>
        hold.fwd_mem (hincl (hcur.inv_mem_dom hz))⟩
    refine (hfo.comp htr').congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    simp only [Function.comp_apply]
    rw [hold.inv_fwd (hincl (hcur.inv_mem_dom hz))]
  obtain ⟨ρT, hρT, hlT⟩ := hlandT
  obtain ⟨ρS, hρS, hlS⟩ := hlandS
  have hlandT' : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ → Fc v ∈ fwdHull W T :=
    ⟨ρT, hρT, fun v hv => by rw [(tendsto_of_ext hFc hFcc v).2]; exact hlT v hv⟩
  have hlandK : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρS → Fo u ∈ fwdHull W s :=
    fun u hu => by rw [(tendsto_of_ext hFo hFoc u).2]; exact hlS u hu
  obtain ⟨hcurlim, hsd⟩ := ref_lift_side_of_cur_land hcur hold hFc hFcc hFo hFoc hη hW hW0 hs hT hKT hKs hincl
    hε hcol hlandT' ⟨ρS, hρS, hlandK⟩ hx'0 hfx hfo (A := (relChart c γ q ω).2.2) hn hside
  -- the reference's own lattice limit
  obtain ⟨Lo, hLo, hlo⟩ := Aux29Cor.exists_isDerivLog_relChart (c := c) hγ hp hc hℓ hlift
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_hull_landing hold hFo hFoc hη hW hW0 hs hKs hρS hlandK
  obtain ⟨m, hm⟩ := exists_int_tendsto_lift_sub hold hLo hlo (isDerivLog_fwdMap hW hs) hρS
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
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The current integer property on a late side test**: the current lift minus `arg f_T′` (`T = T⁰(q)`) tends to
`2πn` at every point of the current open seed interval. -/
def lateCurPhaseProp (i : BothLow) (d : WordObjects Ω) (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) (n : ℤ) : Prop :=
  ∀ u ∈ Ioo
      (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
        (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
      (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
        (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q),
    Tendsto (fun y => (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.2
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y) -
      (logDerivFwd (fun t : ℝ => d.driver t.toNNReal ω) (lateLeftStop j d q ω)
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y)).im) (𝓝[H] (u : ℂ))
      (𝓝 (2 * Real.pi * n))

open Classical in
/-- **The current integer of a late side test** (where it exists; `0` elsewhere). -/
def lateCurPhaseInt (i : BothLow) (d : WordObjects Ω) (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) : ℤ :=
  if h : ∃ n, lateCurPhaseProp i d j q ω n then h.choose else 0

theorem lateCurPhaseInt_spec {i : BothLow} {d : WordObjects Ω} {j : SideTest Ω} {q : ℝ≥0} {ω : Ω}
    (h : ∃ n, lateCurPhaseProp i d j q ω n) : lateCurPhaseProp i d j q ω (lateCurPhaseInt i d j q ω) := by
  simp only [lateCurPhaseInt, h, ↓reduceDIte]
  exact h.choose_spec

/-- **The current integer exists almost surely on the live test** under `R5Lift.LateLiftCurGeom` (every seed-interval
coordinate lands in `ℍ`, hence in the ambient hull `K_T`, and one integer serves the whole interval). -/
theorem ae_exists_lateCurPhase {i : BothLow} {d : WordObjects Ω} (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω)) (h : LateLiftCurGeom i d) :
    ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event →
      (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) → ∃ n, lateCurPhaseProp i d j q ω n := by
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

/-- **The word identity at a late exposed coordinate** from the ambient image: for a ready test, a live capacity, an
exposed coordinate `ξ` landing at `p ∈ ℍ` with the current approach off `K_s`, the ambient image `x′` at time `s` and
the side `ξ < 0 ↔ x′ < 0`: `β_s(x′) + χ·2πn = current word + (χ·2πn + off)·1_I(ξ) − off`. -/
theorem late_word_of_ambient {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hE : ω ∈ (j.target i d).event)
    (hp : IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω) (fun a t => d.forceL a t ω)
      (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b)
    {q : ℝ≥0} (hlive : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) {ξ : ℝ}
    (hξI : ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
          (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
        (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
          (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q))
    {s : ℝ≥0} {p : ℂ} (hpH : p ∈ H)
    (hland : Tendsto (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p))
    (hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) s) {x' : ℝ}
    (hfx : Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) s
      ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)))
    (hsd : ξ < 0 ↔ x' < 0) (n : ℤ) (off : ℝ) :
    forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a s ω - d.driver s ω)
        (fun a => d.forceR a s ω - d.driver s ω) x' + chiC i.kappa * (2 * Real.pi * n) =
      forceBoundaryData (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR
        (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
          segDriver ((j.target i d).curve ω) q)
        (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a q ω -
          segDriver ((j.target i d).curve ω) q)
        ξ + (chiC i.kappa * (2 * Real.pi * n) + off) * (Ioo
          (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
            (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
          (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
            (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q)).indicator 1 ξ - off := by
  have hγ := isDrivenCurve_target (i := i) hj ω hE
  obtain ⟨hη, hW, hW0, hζ, -, -⟩ := late_cur_dom hj hRc hLc hE hlive
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
  -- the current seeds are innermost
  obtain ⟨Wl, hWl, -, q', hqq', hWeq, -⟩ := exists_relChart_eq_loewner (c := (j.target i d).baseChart) hγ hlive
  have hEq : EqOn (fun r : ℝ => (fun t ω => segDriver ((j.target i d).curve ω) t) r.toNNReal ω) Wl
      (Icc 0 (q : ℝ)) := fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver ((j.target i d).curve ω) t)
    (j.target i d).marksL (j.target i d).marksR hWl hEq
  obtain ⟨hsL, hsR⟩ := initial_marks_signed_of_ready hj hE
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
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
  have hamb := mem_ambient_seed_interval hη hW hW0 hs0 hpH hland hcurK hfx
  have hV : Continuous fun t : ℝ≥0 => d.driver t ω := by
    have h1 := hW.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h1
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp hζ hV fun _ => rfl
  have hWs : d.driver ((s : ℝ)).toNNReal ω = d.driver s ω := by rw [Real.toNNReal_coe]
  obtain ⟨hVLpos, hVRpos⟩ := ambient_force_positions (VL := fun a => d.forceL a s ω)
    (VR := fun a => d.forceR a s ω) (xL := d.xL) (xR := d.xR) hW hs0 hxL₀ hxR₀
    (fun a => hL a s) (fun b => hR b s) hamb
  rw [hWs] at hVLpos hVRpos
  have hk : (j.target i d).kappa = i.kappa := by
    rw [Late.target_kappa]
    have := i.kappa_gt_four
    field_simp
  rw [hk]
  exact word_identity_exposed_indicator (κ := i.kappa) _ _ _ _
    (vL := fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
      segDriver ((j.target i d).curve ω) q)
    (vR := fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a q ω -
      segDriver ((j.target i d).curve ω) q)
    hvL hvR hξI (fun _ => hVLpos) (fun _ => hVRpos) hsd (2 * Real.pi * n) off

/-- **`R5Ref.LateAmbientLiftWord` at the explicit current integer** (R5-LIFT2's proof of
`R5Lift.exists_lateAmbientLiftWord_of_cur`, at `N := lateCurPhaseInt`): for every side data with phase
`χ·2π lateCurPhaseInt + offset`, references at the rational original times. -/
theorem lateAmbientLiftWord_of_curInt (i : BothLow) (d : WordObjects Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hpath : ∀ᵐ ω ∂d.measure, IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω)
      (fun a t => d.forceL a t ω) (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b) (h : LateLiftCurGeom i d)
    (side : SideTest Ω → Late.SideData Ω)
    (hside : ∀ j q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side j).offset) :
    LateAmbientLiftWord i d side (fun _ => rationalOriginalTime) X := by
  intro j hj target e zL zR q hq
  filter_upwards [ae_exists_lateCurPhase hRc hLc h j hj q hq, h j hj q hq, hpath] with ω hexω hω hp hE hlive
    current ξ hξ hX hC r x ε x' old w hv hcap hε hcol htr hland hinv hev hx' hfo
  have hNspec := lateCurPhaseInt_spec (hexω hE hlive)
  obtain ⟨⟨hcc, hℓ, hlift⟩, ⟨E, hE', hEc⟩, -⟩ := baseChart_aux29Facts (i := i) hj hE
  have hγ := isDrivenCurve_target (i := i) hj ω hE
  obtain ⟨hη, hW, hW0, -, hT, hd⟩ := late_cur_dom hj hRc (hLc j.seed) hE hlive
  have hcdom : (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω :=
    ((isPocketChartOn hj hRc (hLc j.seed) (i := i)).1 ω hE).2.1
  have hCo := isOpen_domain (i := i) hj ω hE
  have hCH : (j.target i d).domain ω ⊆ H := by rw [← hcdom]; exact hcc.dom_subset
  have hs0 : (0 : ℝ) ≤ (rationalOriginalTime r : ℝ) := (rationalOriginalTime r).coe_nonneg
  have hDC := isDomainChart_referenceVisitChart hj hRc (hLc j.seed) hE hη hs0 hv
  have holddom : ((j.referenceVisitChart i d ω (rationalOriginalTime r)).dom : Set ℂ) =
      (j.target i d).domain ω ∩
        (H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r)) := by
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
  refine ⟨2 * Real.pi * lateCurPhaseInt i d j q ω, hlim, ?_⟩
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 : (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
        ((j.referenceVisitChart i d ω (rationalOriginalTime r)).dom : Set ℂ) :=
      relChart_dom_antitone hcc hγ hlive hcap
        ((isConformal_relChart_of_driven (c := (j.target i d).baseChart) hγ hlive hcc).inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hph : e.phase q ω = chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + e.offset := hside j q ω
  rw [hph]
  exact late_word_of_ambient hj hRc (hLc j.seed) hE hp hxL₀ hxR₀ hlive hξI (hCH hC) hcurland.1 hcurK hfx hsd _
    e.offset

/-- **The outer collars' side and reflection on the late side tests** (named pathwise input; the late twin of
`R5Lift.R7OuterLiftGeom`): almost surely on the live test, at every exposed current coordinate `ξ` off the jumps whose
landing lies outside the pocket (off `X`), every real limit of `f_T ∘ cur⁻¹` at `ξ` (`T = T⁰(q)`) lies on the side of
`ξ`, and on every selected collar of a rational original visit with the landing in `K_s`, the old landings near the
collar point lie in `K_s`. -/
def LateOuterLiftGeom (i : BothLow) (d : WordObjects Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) →
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a q ω -
          segDriver ((j.target i d).curve ω) q)
        (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a q ω -
          segDriver ((j.target i d).curve ω) q) →
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉ X j q ω →
      ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL
            (Late.leftZero i d j) q ω - segDriver ((j.target i d).curve ω) q)
          (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR
            (Late.rightZero i d j) q ω - segDriver ((j.target i d).curve ω) q) →
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∉
        (j.target i d).domain ω →
      (∀ y : ℝ, Tendsto (fun z => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) (lateLeftStop j d q ω)
          ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) →
        (ξ < 0 ↔ y < 0)) ∧
      ∀ (r : ℕ) (x ε : ℝ),
        d.curve ω (rationalOriginalTime r) ∈ (j.target i d).domain ω →
        (j.visitCapacity d ω (rationalOriginalTime r)).toNNReal ≤ q →
        IsRefCollar (j.referenceVisitChart i d ω (rationalOriginalTime r))
          (relChart (j.target i d).baseChart (j.target i d).curve q ω) ξ
          (extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ)) x ε →
        extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 (ξ : ℂ) ∈
          regHull d.driver d.lifetime (rationalOriginalTime r) ω →
        ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
          extendFrom H (j.referenceVisitChart i d ω (rationalOriginalTime r)).2.1 u ∈
            fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r)

/-- **`ColCov.LateOuterLiftWord` at the explicit current integer**: from `R5Lift.LateLiftCurGeom` (the current integer
and the hull landings of the seed interval) and `LateOuterLiftGeom` (the side and the `K_s`-landing at the outer
collars), for every side data with phase `χ·2π lateCurPhaseInt + offset`. -/
theorem lateOuterLiftWord_of_curInt (i : BothLow) (d : WordObjects Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hpath : ∀ᵐ ω ∂d.measure, IsIntegratedSLEPath i.kappa d.xL d.xR d.rhoL d.rhoR (fun t => d.driver t ω)
      (fun a t => d.forceL a t ω) (fun a t => d.forceR a t ω) (fun t => d.brownian t ω) (d.lifetime ω))
    (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b) (h : LateLiftCurGeom i d) (ho : LateOuterLiftGeom i d X)
    (side : SideTest Ω → Late.SideData Ω)
    (hside : ∀ j q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side j).offset) :
    LateOuterLiftWord i d side X := by
  intro j hj target e zL zR q hq
  filter_upwards [ae_exists_lateCurPhase hRc hLc h j hj q hq, h j hj q hq, ho j hj q hq, hpath] with ω hexω hω hoω
    hp hE hlive current ξ hξ hX hI hC r x ε x' s old w hv hcap hcol hpK hx' hcur hfo
  have hNspec := lateCurPhaseInt_spec (hexω hE hlive)
  obtain ⟨⟨hcc, hℓ, hlift⟩, ⟨E, hE', hEc⟩, -⟩ := baseChart_aux29Facts (i := i) hj hE
  have hγ := isDrivenCurve_target (i := i) hj ω hE
  obtain ⟨hη, hW, hW0, -, hT, hd⟩ := late_cur_dom hj hRc (hLc j.seed) hE hlive
  have hcdom : (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω :=
    ((isPocketChartOn hj hRc (hLc j.seed) (i := i)).1 ω hE).2.1
  have hs0 : (0 : ℝ) ≤ (rationalOriginalTime r : ℝ) := (rationalOriginalTime r).coe_nonneg
  have hDC := isDomainChart_referenceVisitChart hj hRc (hLc j.seed) hE hη hs0 hv
  have holddom : ((j.referenceVisitChart i d ω (rationalOriginalTime r)).dom : Set ℂ) =
      (j.target i d).domain ω ∩
        (H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r)) := by
    rw [hDC.coe_dom, ← hη.2.2 _ hs0]
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := (j.target i d).baseChart)
    (γ := (j.target i d).curve) hγ hlive hE' hEc
  have hcurland := (tendsto_of_ext hFc hFcc ξ)
  rw [hcurland.2] at hcurland
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
  obtain ⟨hsideO, hrefl⟩ := hoω hE hlive ξ hξ hX hI hC
  obtain ⟨ρo, hρo, hlandS⟩ := hrefl r x ε hv hcap hcol hpK
  -- current landings near `ξ` lie in `K_T`
  have hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ →
      extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 v ∈
        fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (lateLeftStop j d q ω) := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo ξ hI
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    have hvI := hball (mem_ball_of_ofReal_mem_ball hv)
    obtain ⟨hlim, hFv⟩ := tendsto_of_ext hFc hFcc v
    rw [← hFv]
    refine landing_mem_hull_of_mem_seed_interval hmL hmR hcc hγ hlive hq hE' hEc hcdom
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hT) hd hvI hlim ?_
    rw [hFv]; exact ((hω hE hlive) v hvI).1
  obtain ⟨hlim, hsd, hfx⟩ := ref_old_lift_side_of_cur_land hcc hγ hlive hcap hℓ hlift hE' hEc hη hW hW0 hs0 hT
    (by rw [hd]; exact inter_subset_right)
    (fun z hz => by
      have hz' : z ∈ ((j.referenceVisitChart i d ω (rationalOriginalTime r)).dom : Set ℂ) := hz
      rw [holddom] at hz'
      exact hz'.2) hcol.1 hcol.2.1
    hcol.2.2.1 hlandT ⟨ρo, hρo, hlandS⟩ hx'0 hfo (hNspec ξ hI) hsideO
  refine ⟨2 * Real.pi * lateCurPhaseInt i d j q ω, hlim, ?_⟩
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => d.driver t.toNNReal ω) (rationalOriginalTime r) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 : (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 y ∈
        ((j.referenceVisitChart i d ω (rationalOriginalTime r)).dom : Set ℂ) :=
      relChart_dom_antitone hcc hγ hlive hcap
        ((isConformal_relChart_of_driven (c := (j.target i d).baseChart) hγ hlive hcc).inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hph : e.phase q ω = chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + e.offset := hside j q ω
  rw [hph]
  exact late_word_of_ambient hj hRc (hLc j.seed) hE hp hxL₀ hxR₀ hlive hI hpK.1 hcurland.1 hcurK hfx hsd _
    e.offset

end Late

end InteractingSLE.Sec7.ColCov
