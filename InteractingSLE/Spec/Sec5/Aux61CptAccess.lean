/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptMirror
import InteractingSLE.Spec.Sec5.Aux61CptLanding
import InteractingSLE.Spec.Sec5.Aux61CptGerm

/-!
# Component counterflow accesses from restart-chart data

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). The landing part of a per-outcome selection is certified on the
restart chart's side. `cfAccessC_of_chartBall`: at a sample whose retained counterflow history is good, if on a chart
half-disc `ℍ ∩ B(v, ε)`

* the counterflow-chart image of the inverse chart is bounded (`hbd`), and
* at every real point `t` of the ball the inverse chart has a boundary limit `z(t) ∈ ℍ` off the own prefix (`hz`),

then `v` is a component counterflow access point (`CfAccessC`), up to the three word clauses (`v ≠ 0`, `v` not a word
jump, the height identity `hheight`). The physical points `z(t)` are on the counterflow hull
(`mem_of_mem_closure_component`: a boundary point of a component of `ℍ ∖ (K ∪ η[0, r])` in `ℍ` and off the prefix lies
in `K`), so the mirror reflection (`Aux61CptMirror`) supplies the collar; the landing coordinate is not a returned jump
because its physical point is in `ℍ`. `cfAccessC_of_chartBall'` gives the access at every real point of the ball.

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart Aux61TwoS
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign
universe u

/-- **Boundary points of a retained component lie in the obstacle**: a point of `ℍ` in the closure of a component
of `ℍ ∖ (K ∪ η[0, r])`, outside the component and off the prefix, is in `K`. -/
theorem mem_of_mem_closure_component {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b' z : ℂ} {dom : Set ℂ}
    (hdom : dom = restartComponent K η r b') (hU : IsOpen (retainedDomain K η r))
    (hzH : z ∈ H) (hzη : z ∉ η '' Icc 0 r) (hcl : z ∈ closure dom) (hnot : z ∉ dom) : z ∈ K := by
  by_contra hK
  have hzU : z ∈ retainedDomain K η r := ⟨hzH, by rintro (h | h); exacts [hK h, hzη h]⟩
  have hCo : IsOpen (connectedComponentIn (retainedDomain K η r) z) := hU.connectedComponentIn
  obtain ⟨w, hwC, hwd⟩ := mem_closure_iff_nhds.1 hcl _ (hCo.mem_nhds (mem_connectedComponentIn hzU))
  have hwd' : w ∈ connectedComponentIn (retainedDomain K η r) b' := by rw [← restartComponent, ← hdom]; exact hwd
  have h1 := connectedComponentIn_eq hwC
  have h2 := connectedComponentIn_eq hwd'
  apply hnot
  rw [hdom, restartComponent, h2, ← h1]
  exact mem_connectedComponentIn hzU

/-- A boundary limit of the inverse chart at a real point lies outside the chart domain and in its closure. -/
theorem notMem_dom_of_tendsto {c : Chart} (hc : c.IsConformal) {t : ℝ} {z : ℂ}
    (hz : Tendsto c.2.1 (𝓝[H] (t : ℂ)) (𝓝 z)) :
    z ∉ (c.dom : Set ℂ) ∧ z ∈ closure (c.dom : Set ℂ) := by
  have hne := GlueImg.nhdsWithin_H_neBot t
  refine ⟨fun hzd => ?_, mem_closure_of_tendsto hz
    (eventually_nhdsWithin_of_forall fun y hy => hc.inv_mem_dom hy)⟩
  have hcont : ContinuousAt c.1 z :=
    (hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hzd)).continuousAt
  have h1 : Tendsto (fun y => c.1 (c.2.1 y)) (𝓝[H] (t : ℂ)) (𝓝 (c.1 z)) := hcont.tendsto.comp hz
  have h2 : Tendsto (fun y => c.1 (c.2.1 y)) (𝓝[H] (t : ℂ)) (𝓝 (t : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (hc.2.2 y hy).symm)
  have heq := tendsto_nhds_unique h1 h2
  have hH : (0 : ℝ) < (c.1 z).im := hc.fwd_mem hzd
  rw [heq, Complex.ofReal_im] at hH
  exact lt_irrefl _ hH

/-- On a good counterflow history the reflected hull is read from the retained regularized driver. -/
theorem cfHullQ_eq_cfW (S : SourceSetting.{u}) {p : S.Ω × HistorySpace 0 0}
    (hgood : p.2 ∈ CfRegQ.goodCfSet) :
    cfHullQ (rationalTime S.s) p.2 = negInv '' fwdHull (cfW S p) (rationalTime S.s) := by
  rw [cfHullQ_eq_of_mem_goodCfSet hgood]
  congr 1
  have hw : Continuous (Prop411Q.cfDrv p.2) := (CfRegQ.reg_of_mem_goodCfSet hgood).2.1
  exact (YuanCorollary13.fwdHull_eq_of_eqOn_Icc (Sec4.continuous_rpath_regPath _) hw
    (rationalTime S.s).coe_nonneg fun r hr => eqOn_cfW_cfDrv S hgood hr).symm

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- **The height clause along the produced counterflow collar**: every positive counterflow point `ξ₀` carrying a
collar into the chart domain, with the transition landing at `b` and physical point `z`, has the reference height at
`b` for the inherited phase. -/
def CollarHeight (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι)
    (p : S.Ω × HistorySpace 0 0) (z : ℂ) (b : ℝ) : Prop :=
  ∀ ξ₀ δ : ℝ, 0 < ξ₀ → 0 < δ →
    MapsTo (revChartInv (cfW S p) (rationalTime S.s)) (H ∩ ball (ξ₀ : ℂ) δ) ((S.marksData F).chart i p).dom →
    (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
      extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
      cfBdry (cfW S p) (rationalTime S.s) x' ≠ 1) →
    Tendsto (fun z => ((S.marksData F).chart i p).1 (revChartInv (cfW S p) (rationalTime S.s) z))
      (𝓝[H] (ξ₀ : ℂ)) (𝓝 (b : ℂ)) →
    cfBdry (cfW S p) (rationalTime S.s) ξ₀ = z → ∀ phase : ℝ,
    Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
      (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
      (𝓝[H] (b : ℂ)) (𝓝 phase) →
    (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
      (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 ξ₀ + S.θ * chiC S.κ + chiC S.κ * phase

/-- **A component counterflow access from a chart half-disc** at its centre `v`. -/
theorem cfAccessC_of_chartBall {i : F.ι} {p : S.Ω × HistorySpace 0 0}
    (hgood : p.2 ∈ CfRegQ.goodCfSet)
    (hcfp : cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ)
    (hc : ((S.marksData F).chart i p).IsConformal)
    (hdomc : ∃ b' : ℂ, (((S.marksData F).chart i p).dom : Set ℂ) =
      restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal)
        (F.start i) b')
    (hηc : ContinuousOn (fun t : ℝ => S.path p.1 t.toNNReal) (Icc 0 (F.start i : ℝ)))
    {v ε M : ℝ} (hε : 0 < ε)
    (hbd : ∀ y ∈ H ∩ ball (v : ℂ) ε,
      ‖revChart (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 y)‖ ≤ M)
    (z : ℝ → ℂ)
    (hz : ∀ t : ℝ, (t : ℂ) ∈ ball (v : ℂ) ε →
      Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (t : ℂ)) (𝓝 (z t)) ∧ z t ∈ H ∧
        z t ∉ (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ))
    (hoff : ∃ ρ > 0, Disjoint (ball (z v) ρ) ((fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (hre : ∃ m > 0, ∀ y ∈ H ∩ ball (v : ℂ) ε,
      m ≤ (revChart (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 y)).re)
    (hv0 : v ≠ 0) (hvJ : v ∉ (F.data i).JR)
    (hheight : CollarHeight S F i p (z v) v) :
    CfAccessC S F i p v := by
  set c := (S.marksData F).chart i p with hcdef
  set w := cfW S p with hwdef
  have hw : Continuous w := Sec4.continuous_rpath_regPath _
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hK := cfHullQ_eq_cfW S hgood
  obtain ⟨b', hb'⟩ := hdomc
  have hsubK : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w (rationalTime S.s) := by
    intro y hy
    rw [hb'] at hy
    have hy' := connectedComponentIn_subset _ _ hy
    exact ⟨hy'.1, fun h => hy'.2 (Or.inl (hK ▸ h))⟩
  have hU : IsOpen (retainedDomain (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal)
      (F.start i)) :=
    isOpen_retainedDomain (by rw [hK]; exact WangWu.isOpen_H_diff_negInv_fwdHull hw hs) hηc
  have hzK : ∀ t : ℝ, (t : ℂ) ∈ ball (v : ℂ) ε → z t ∈ negInv '' fwdHull w (rationalTime S.s) := by
    intro t ht
    obtain ⟨hlim, hzH, hzη⟩ := hz t ht
    obtain ⟨hnot, hcl⟩ := notMem_dom_of_tendsto hc hlim
    rw [← hK]
    exact mem_of_mem_closure_component hb' hU hzH hzη hcl hnot
  obtain ⟨ξ₀, δ, hδ, hcol, hfin, hcfv, hxb, hΞ⟩ :=
    mirror_collar hw hw0 hγ hs hc hsubK hε hbd z fun t ht => ⟨hzK t ht, (hz t ht).1⟩
  have hvB : ((v : ℝ) : ℂ) ∈ ball (v : ℂ) ε := mem_ball_self hε
  have hfin' : ∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
      extendFrom H (fwdMapInv w (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
      cfBdry w (rationalTime S.s) x' ≠ 1 := by
    intro x' hx'
    obtain ⟨hx0, hF0, t, ht, hct⟩ := hfin x' hx'
    refine ⟨hx0, hF0, fun h1 => ?_⟩
    have hH : (0 : ℝ) < (z t).im := (hz t ht).2.1
    rw [← hct, h1, Complex.one_im] at hH
    exact lt_irrefl _ hH
  have hξpos : 0 < ξ₀ := by
    obtain ⟨m, hm, hmle⟩ := hre
    have hev : ∀ᶠ y in 𝓝[H] (v : ℂ), m ≤ (revChart w (rationalTime S.s) (c.2.1 y)).re := by
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hvB)] with y hy
      exact hmle y hy
    have := GlueImg.nhdsWithin_H_neBot v
    have hle := ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hΞ) hev
    simp only [Complex.ofReal_re] at hle
    linarith
  refine ⟨ξ₀, δ, ξ₀, hδ, mem_ball_self hδ, hcol, hfin', ?_, hxb, hv0, hvJ, ?_,
    hheight ξ₀ δ hξpos hδ hcol hfin' hxb hcfv⟩
  · rw [hcfv]; exact hoff
  · intro hJ
    have him := im_cfBdry_eq_zero_of_mem_returnedCfJumps hw hw0 hγ (hfin ξ₀ (mem_ball_self hδ)).1 hJ
    rw [hcfv] at him
    have hpos : 0 < (z v).im := (hz v hvB).2.1
    rw [him] at hpos
    exact lt_irrefl _ hpos

/-- **Component counterflow accesses at every real point of a chart half-disc** with a uniform distance `d` of the
physical points from the own prefix. -/
theorem cfAccessC_of_chartBall' {i : F.ι} {p : S.Ω × HistorySpace 0 0}
    (hgood : p.2 ∈ CfRegQ.goodCfSet)
    (hcfp : cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ)
    (hc : ((S.marksData F).chart i p).IsConformal)
    (hdomc : ∃ b' : ℂ, (((S.marksData F).chart i p).dom : Set ℂ) =
      restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal)
        (F.start i) b')
    (hηc : ContinuousOn (fun t : ℝ => S.path p.1 t.toNNReal) (Icc 0 (F.start i : ℝ)))
    {v₀ ε₀ M d : ℝ} (hd : 0 < d)
    (hbd : ∀ y ∈ H ∩ ball (v₀ : ℂ) ε₀,
      ‖revChart (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 y)‖ ≤ M)
    (z : ℝ → ℂ)
    (hz : ∀ t : ℝ, (t : ℂ) ∈ ball (v₀ : ℂ) ε₀ →
      Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (t : ℂ)) (𝓝 (z t)) ∧ z t ∈ H ∧
        ∀ u ∈ (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ), d ≤ dist (z t) u)
    (hre : ∃ m > 0, ∀ y ∈ H ∩ ball (v₀ : ℂ) ε₀,
      m ≤ (revChart (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 y)).re)
    {b : ℝ} (hb : (b : ℂ) ∈ ball (v₀ : ℂ) ε₀) (hb0 : b ≠ 0) (hbJ : b ∉ (F.data i).JR)
    (hheight : CollarHeight S F i p (z b) b) :
    CfAccessC S F i p b := by
  obtain ⟨ε, hε, hsub⟩ := Aux61TwoS.exists_ball_subset_ball hb
  have hoffη : ∀ t : ℝ, (t : ℂ) ∈ ball (v₀ : ℂ) ε₀ →
      z t ∉ (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ) := fun t ht hm => by
    have := (hz t ht).2.2 _ hm
    rw [dist_self] at this
    linarith
  refine cfAccessC_of_chartBall hgood hcfp hc hdomc hηc hε (fun y hy => hbd y ⟨hy.1, hsub hy.2⟩) z
    (fun t ht => ⟨(hz t (hsub ht)).1, (hz t (hsub ht)).2.1, hoffη t (hsub ht)⟩)
    ⟨d, hd, Set.disjoint_left.2 fun u hu hum => ?_⟩
    (by obtain ⟨m, hm, hmle⟩ := hre; exact ⟨m, hm, fun y hy => hmle y ⟨hy.1, hsub hy.2⟩⟩) hb0 hbJ hheight
  have := (hz b hb).2.2 _ hum
  rw [mem_ball, dist_comm] at hu
  linarith

end InteractingSLE.Sec5.Aux61Cpt
