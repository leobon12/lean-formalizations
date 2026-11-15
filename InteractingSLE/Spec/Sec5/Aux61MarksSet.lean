/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksHull
import InteractingSLE.Spec.Sec5.Aux61MarksAlive
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# The marked set is hitting-measurable for the completed rule marks (`baseSets_marks`)

Packet PROVE-AUX61-MARKS. The marked set fixed by CHARTLOC's geometry is the chart set
`chartSet c K = ℍ ∖ c⁻¹(ℍ ∖ K)` (`Aux61MarksUnion`). Its hitting events are reduced to countably many conditions on
the chart, the hull, the retained obstacle and the restarted path, each read from the stopped record:

* **the inner chart domain is detected by one interior point and the boundary pieces** (`subset_chartPull_iff`): for a
  conformal chart whose domain is a connected component of a retained domain `R`, a hull `K` whose relative frontier is
  the chart image of a slit `S` mapped into `K`, and a connected open `B ⊆ ℍ`:
  `B ⊆ c⁻¹(ℍ ∖ K) ⟺ (∃ z ∈ B ∩ Q, z ∈ dom ∧ c z ∉ K) ∧ B ⊆ R ∧ B ∩ S = ∅` (`Q` dense); the relative frontier of a
  filling lies in the closure of the filled set (`mem_closure_of_frontier_isFilling`); for the access code `S` is the
  restarted path up to the code time (`chartSet_inter_nonempty_iff`);
* **hitting measurability from rational balls** (`measurable_hitting_of_ratBalls`, `inter_nonempty_iff_exists_ratBall`)
  and the regularized marked set (`chartSet` on a set `G`, `ℍ` off `G`) (`measurable_markedSet`);
* the record suppliers: slit avoidance at dyadic times (`disjoint_image_Ioc_iff`, `exists_slitAvoid_ruleMarks`), hull
  membership of random points through the regularized record driver (`recDriverPath`, `exists_hullMem_of_ruleMarks`,
  QuantumZipper's tamed-flow `measurableSet_fwdHull_prod`), R1's retained-domain events (`exists_retained_event`);
* **`measurable_markedSet_nullRuleMarks`**: the field `baseSets_marks` of `MarksFacts` for the completed rule marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

/-! ### The inner chart domain -/

section Pull

/-- **The inner chart domain from one interior point and the boundary pieces.** Let `c` be a conformal chart whose
domain is the connected component of an open set `R` through one of its points, `K ⊆ ℍ` a set such that every point of
`K` in the closure of `ℍ ∖ K` is the chart image of a point of a slit `S`, and `S` mapped into `K` on the domain. Then a
connected open `B ⊆ ℍ` lies in the chart pullback `c⁻¹(ℍ ∖ K)` iff it contains a point of a dense set `Q` in the domain
off `c⁻¹ K`, lies in `R`, and avoids `S`. -/
theorem subset_chartPull_iff {c : Chart} (hc : c.IsConformal) {R : Set ℂ} {b : ℂ}
    (hdom : (c.dom : Set ℂ) = connectedComponentIn R b) {K S : Set ℂ} (hKo : IsOpen (H \ K))
    (hfront : ∀ w ∈ H, w ∈ K → w ∈ closure (H \ K) → ∃ z ∈ S, z ∈ (c.dom : Set ℂ) ∧ c.1 z = w)
    (hS : ∀ z ∈ S, z ∈ (c.dom : Set ℂ) → c.1 z ∈ K) {Q : Set ℂ} (hQ : Dense Q) {B : Set ℂ} (hBo : IsOpen B)
    (hBc : IsPreconnected B) (hBne : B.Nonempty) :
    B ⊆ c.2.1 '' (H \ K) ↔
      (∃ z ∈ B ∩ Q, z ∈ (c.dom : Set ℂ) ∧ c.1 z ∉ K) ∧ B ⊆ R ∧ Disjoint B S := by
  have hdomH : (c.dom : Set ℂ) = c.2.1 '' H := hc.coe_dom
  -- points of the domain are the inverse images of their chart images
  have hinv : ∀ z ∈ (c.dom : Set ℂ), c.2.1 (c.1 z) = z ∧ c.1 z ∈ H := by
    intro z hz
    rw [hdomH] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hc.2.2 w hw]
    exact ⟨rfl, hw⟩
  have hmemO : ∀ z, z ∈ c.2.1 '' (H \ K) ↔ z ∈ (c.dom : Set ℂ) ∧ c.1 z ∉ K := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨by rw [hdomH]; exact mem_image_of_mem _ hw.1, ?_⟩
      rw [hc.2.2 w hw.1]
      exact hw.2
    · rintro ⟨hz, hzK⟩
      exact ⟨c.1 z, ⟨(hinv z hz).2, hzK⟩, (hinv z hz).1⟩
  have hDR : (c.dom : Set ℂ) ⊆ R := by
    rw [hdom]
    exact connectedComponentIn_subset _ _
  constructor
  · intro hB
    obtain ⟨z, hzB, hzQ⟩ := hQ.inter_open_nonempty B hBo hBne
    refine ⟨⟨z, ⟨hzB, hzQ⟩, (hmemO z).1 (hB hzB)⟩, fun z hz => hDR ((hmemO z).1 (hB hz)).1, ?_⟩
    refine Set.disjoint_left.2 fun z hzB hzS => ?_
    obtain ⟨hzd, hzK⟩ := (hmemO z).1 (hB hzB)
    exact hzK (hS z hzS hzd)
  · rintro ⟨⟨z₀, ⟨hz₀B, -⟩, hz₀d, hz₀K⟩, hBR, hBS⟩
    -- `B` lies in the domain
    have hBD : B ⊆ (c.dom : Set ℂ) := by
      have hz₀R : z₀ ∈ connectedComponentIn R b := hdom ▸ hz₀d
      rw [hdom, connectedComponentIn_eq hz₀R]
      exact hBc.subset_connectedComponentIn hz₀B hBR
    have hOopen : IsOpen (c.2.1 '' (H \ K)) :=
      SmallGammaGeodesics.CC.isOpen_image_conf hKo (hc.1.mono sdiff_subset) (hc.injOn.mono sdiff_subset)
    refine hBc.subset_of_closure_inter_subset hOopen ⟨z₀, hz₀B, (hmemO z₀).2 ⟨hz₀d, hz₀K⟩⟩ ?_
    rintro z ⟨hzcl, hzB⟩
    have hzd := hBD hzB
    by_contra hzO
    have hzK : c.1 z ∈ K := by
      by_contra h
      exact hzO ((hmemO z).2 ⟨hzd, h⟩)
    -- the chart image of `z` is in the closure of `ℍ ∖ K`
    have hcont : ContinuousAt c.1 z := Aux61FibData.continuousAt_fwd hc hzd
    have hcl : c.1 z ∈ closure (H \ K) := by
      have hmaps : MapsTo c.1 (c.2.1 '' (H \ K)) (H \ K) := by
        rintro _ ⟨w, hw, rfl⟩
        rw [hc.2.2 w hw.1]
        exact hw
      exact closure_mono (image_subset_iff.2 hmaps) (hcont.continuousWithinAt.mem_closure_image hzcl)
    obtain ⟨z', hz'S, hz'd, hz'e⟩ := hfront (c.1 z) (hinv z hzd).2 hzK hcl
    have hzz : z' = z := by
      rw [← (hinv z' hz'd).1, ← (hinv z hzd).1, hz'e]
    exact Set.disjoint_left.1 hBS hzB (hzz ▸ hz'S)

end Pull

/-! ### The relative frontier of a filling; balls -/

/-- **The relative frontier of a filling lies in the closure of the filled set.** -/
theorem mem_closure_of_frontier_isFilling {K A : Set ℂ} (h : IsFilling K A) {w : ℂ} (hwH : w ∈ H) (hwK : w ∈ K)
    (hwc : w ∈ closure (H \ K)) : w ∈ closure A := by
  by_contra hwA
  obtain ⟨z₀, -, hz₀⟩ := h.1
  have hopen : IsOpen (H ∩ (closure A)ᶜ) := QuantumZipper.isOpen_H.inter isClosed_closure.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen w ⟨hwH, hwA⟩
  obtain ⟨z₁, hz₁K, hz₁d⟩ := Metric.mem_closure_iff.1 hwc ε hε
  have hz₁b : z₁ ∈ ball w ε := mem_ball'.2 hz₁d
  have hbsub : ball w ε ⊆ H \ A := fun z hz => ⟨(hball hz).1, fun hzA => (hball hz).2 (subset_closure hzA)⟩
  have hz₁C : z₁ ∈ connectedComponentIn (H \ A) z₀ := hz₀ ▸ hz₁K
  have hsub : ball w ε ⊆ connectedComponentIn (H \ A) z₀ := by
    rw [connectedComponentIn_eq hz₁C]
    exact (convex_ball w ε).isPreconnected.subset_connectedComponentIn hz₁b hbsub
  have hw : w ∈ H \ K := hz₀ ▸ hsub (mem_ball_self hε)
  exact hw.2 hwK

/-- The ball with a rational centre and radius. -/
def ratBall (p : ℚ × ℚ × ℚ) : Set ℂ := ball (⟨p.1, p.2.1⟩ : ℂ) p.2.2

theorem isOpen_ratBall (p : ℚ × ℚ × ℚ) : IsOpen (ratBall p) := isOpen_ball

theorem isPreconnected_ratBall (p : ℚ × ℚ × ℚ) : IsPreconnected (ratBall p) :=
  (convex_ball _ _).isPreconnected

/-- **Hitting events by rational balls**: a set meets an open `U` iff it meets a rational ball inside `U`. -/
theorem inter_nonempty_iff_exists_ratBall {A U : Set ℂ} (hU : IsOpen U) :
    (A ∩ U).Nonempty ↔ ∃ p : ℚ × ℚ × ℚ, ratBall p ⊆ U ∧ (A ∩ ratBall p).Nonempty := by
  constructor
  · rintro ⟨z, hzA, hzU⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show z.re - ε / 4 < z.re + ε / 4 by linarith)
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show z.im - ε / 4 < z.im + ε / 4 by linarith)
    set w : ℂ := ⟨q₁, q₂⟩ with hwdef
    have hdist : dist z w < ε / 2 := by
      calc dist z w ≤ |z.re - w.re| + |z.im - w.im| := by
            rw [dist_eq_norm, ← Complex.sub_re, ← Complex.sub_im]
            exact Complex.norm_le_abs_re_add_abs_im _
        _ < ε / 4 + ε / 4 := by
          refine add_lt_add ?_ ?_
          · rw [abs_lt]; constructor <;> simp only [hwdef] <;> linarith [hq₁.1, hq₁.2]
          · rw [abs_lt]; constructor <;> simp only [hwdef] <;> linarith [hq₂.1, hq₂.2]
        _ = ε / 2 := by ring
    obtain ⟨ρ, hρ⟩ := exists_rat_btwn (show dist z w < ε - dist z w by linarith)
    refine ⟨(q₁, q₂, ρ), fun y hy => hball ?_, z, hzA, ?_⟩
    · have hy' : dist y w < ρ := hy
      calc dist y z ≤ dist y w + dist w z := dist_triangle _ _ _
        _ < (ε - dist z w) + dist z w := by rw [dist_comm w z]; linarith [hρ.2]
        _ = ε := by ring
    · show dist z w < ρ
      exact hρ.1
  · rintro ⟨p, hpU, z, hzA, hzp⟩
    exact ⟨z, hzA, hpU hzp⟩

/-! ### The hitting events of the marked set of the access code -/

section Access

open Aux61FibData Aux61GInst Aux61Fib
open Aux61UnionK (chartHull)
open Aux61SlitW (accessTime)

variable {X : Type*} [MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
include hs hV hV0 hland hinj

/-- **The hitting events of the marked set by countably many conditions.** At a sample alive at the fibre time `r`
whose chart domain is the connected component of a retained domain `R` (R1's chart), for every connected open
nonempty `B ⊆ ℍ` and dense `Q`: the marked set `chartSet c K_r` meets `B` iff it is not the case that `B` contains a
point of `Q` in the domain mapped off `K_r`, lies in `R`, and avoids the restarted path up to the physical code time. -/
theorem chartSet_inter_nonempty_iff (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {x : X} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) {R : Set ℂ} {b : ℂ}
    (hdom : ((cc x).dom : Set ℂ) = connectedComponentIn R b) {Q : Set ℂ} (hQ : Dense Q) {B : Set ℂ}
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBne : B.Nonempty) (hBH : B ⊆ H) :
    (chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x) ∩ B).Nonempty ↔
      ¬ ((∃ z ∈ B ∩ Q, z ∈ ((cc x).dom : Set ℂ) ∧ (cc x).1 z ∉ chartHull (accessExitCode E cc ρ T V a k h) r x) ∧
        B ⊆ R ∧ Disjoint B (ρ x '' Ioc 0 (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r))) := by
  set Y := accessExitCode E cc ρ T V a k h with hYdef
  set K := chartHull Y r x with hKdef
  set A := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r with hAdef
  have hx := mem_exitEv_of_lt_accessLife hr
  have hc : (cc x).IsConformal := hs.conf x hx.1.1
  have hgood := pathGood_accessExitCode hs hV hV0 hland hinj d hdV hℓ hx (a := a) (k := k) (h := h)
  have hfill : IsFilling K ((Y x).trace '' Icc 0 r) := hgood.1.2.2 r hr
  have hKo : IsOpen (H \ K) := Aux61UnionK.isOpen_H_diff_chartHull Y hr
  -- the relative frontier of the hull is the chart image of the restarted path
  have hfront : ∀ w ∈ H, w ∈ K → w ∈ closure (H \ K) →
      ∃ z ∈ ρ x '' Ioc 0 A, z ∈ ((cc x).dom : Set ℂ) ∧ (cc x).1 z = w := by
    intro w hwH hwK hwc
    have hcl := mem_closure_of_frontier_isFilling hfill hwH hwK hwc
    rw [(isCompact_Icc.image (FibCode.continuous_trace (Y x))).isClosed.closure_eq] at hcl
    obtain ⟨v, hv, rfl⟩ := hcl
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [FibCode.trace_zero] at hwH
      exact absurd hwH (by simp [QuantumZipper.H])
    have hvl : (v : ℝ≥0∞) < (Y x).life := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv.2) hr
    have hu : accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x v ∈ Ioc 0 A :=
      ⟨Aux61SlitW.accessTime_pos hs hV hV0 hland hinj hvl (pos_iff_ne_zero.2 hv0),
        accessTime_mono hs hV hV0 hland hinj hr hv.2⟩
    refine ⟨_, mem_image_of_mem _ hu, (chart_mem_chartHull_of_access hs hV hV0 hland hinj d hdV hℓ hr hu).1, ?_⟩
    exact (Aux61SlitW.accessExitCode_trace_eq hs hV hV0 hland hinj hvl (pos_iff_ne_zero.2 hv0)).symm
  have hS : ∀ z ∈ ρ x '' Ioc 0 A, z ∈ ((cc x).dom : Set ℂ) → (cc x).1 z ∈ K := by
    rintro _ ⟨u, hu, rfl⟩ _
    exact (chart_mem_chartHull_of_access hs hV hV0 hland hinj d hdV hℓ hr hu).2
  have hiff := subset_chartPull_iff hc hdom hKo hfront hS hQ hBo hBc hBne
  have hns : (chartSet (cc x) K ∩ B).Nonempty ↔ ¬ B ⊆ (cc x).2.1 '' (H \ K) := by
    constructor
    · rintro ⟨z, ⟨-, hz⟩, hzB⟩ hsub
      exact hz (hsub hzB)
    · intro hn
      obtain ⟨z, hzB, hz⟩ := not_subset.1 hn
      exact ⟨z, ⟨hBH hzB, hz⟩, hzB⟩
  rw [hns, hiff]

end Access

/-! ### Hitting measurability from rational balls; the regularized marked set -/

section Meas

open Aux61FibData Aux61GInst Aux61Fib
open Aux61UnionK (chartHull)
open Aux61SlitW (accessTime)

/-- **Hitting measurability from the rational balls inside `ℍ`.** -/
theorem measurable_hitting_of_ratBalls {X : Type*} {m : MeasurableSpace X} {A : X → Set ℂ}
    (hA : ∀ p : ℚ × ℚ × ℚ, ratBall p ⊆ H → MeasurableSet[m] {x | (A x ∩ ratBall p).Nonempty}) :
    Measurable[m, hittingSigma] A := by
  refine @measurable_generateFrom _ _ m _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : A ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ p : ℚ × ℚ × ℚ, ⋃ (_ : ratBall p ⊆ U), {x | (A x ∩ ratBall p).Nonempty} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, exists_prop]
    exact inter_nonempty_iff_exists_ratBall hU
  rw [e]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun hp => hA p (hp.trans hUH)

variable {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
include hs hV hV0 hland hinj

open scoped Classical in
/-- **The regularized marked set is hitting-measurable** for a σ-algebra `m` once, on a set `G ∈ m` of samples alive at
`r` with R1's chart (domain a component of `R x`): the chart is measurable for `m`; membership of an `m`-measurable
random point in the chart hull is an `m`-event (`hK`); the events "a rational ball lies in `R x`" (`hR`) and "a rational
ball avoids the restarted path up to the code time" (`hS`) are `m`-events. -/
theorem measurable_markedSet (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {r : ℝ≥0}
    {G : Set X} (hGm : MeasurableSet[m] G) {R : X → Set ℂ} {b : X → ℂ}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧
      ((cc x).dom : Set ℂ) = connectedComponentIn (R x) (b x))
    (hcm : @IsMeasChart X m cc)
    (hK : ∀ w : X → ℂ, Measurable[m] w → ∃ K' : Set X, MeasurableSet[m] K' ∧
      ∀ x ∈ G, (w x ∈ chartHull (accessExitCode E cc ρ T V a k h) r x ↔ x ∈ K'))
    (hR : ∀ p : ℚ × ℚ × ℚ, ∃ R' : Set X, MeasurableSet[m] R' ∧ ∀ x ∈ G, (ratBall p ⊆ R x ↔ x ∈ R'))
    (hS : ∀ p : ℚ × ℚ × ℚ, ∃ S' : Set X, MeasurableSet[m] S' ∧ ∀ x ∈ G, (Disjoint (ratBall p)
      (ρ x '' Ioc 0 (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r)) ↔ x ∈ S')) :
    Measurable[m, hittingSigma]
      (G.piecewise (fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x)) fun _ => H) := by
  classical
  set e := TopologicalSpace.denseSeq ℂ with hedef
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq ℂ
  refine measurable_hitting_of_ratBalls fun p hpH => ?_
  by_cases hp : (ratBall p).Nonempty
  swap
  · have e0 : {x | ((G.piecewise (fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x))
        fun _ => H) x ∩ ratBall p).Nonempty} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun ⟨z, _, hz⟩ => hp ⟨z, hz⟩
    rw [e0]
    exact @MeasurableSet.empty X m
  -- the formula
  set Φ : Set X := {x | (∃ n : ℕ, e n ∈ ratBall p ∧ e n ∈ ((cc x).dom : Set ℂ) ∧
      (cc x).1 (e n) ∉ chartHull (accessExitCode E cc ρ T V a k h) r x) ∧ ratBall p ⊆ R x ∧
      Disjoint (ratBall p) (ρ x '' Ioc 0 (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r))}
    with hΦdef
  have hΦm : ∃ Φ' : Set X, MeasurableSet[m] Φ' ∧ ∀ x ∈ G, (x ∈ Φ ↔ x ∈ Φ') := by
    obtain ⟨R', hR'm, hR'⟩ := hR p
    obtain ⟨S', hS'm, hS'⟩ := hS p
    have hw : ∀ n : ℕ, Measurable[m] ({x | e n ∈ ((cc x).dom : Set ℂ)}.indicator fun x => (cc x).1 (e n)) :=
      fun n => @IsMeasChart.fwd X m cc hcm (e n)
    choose K' hK'm hK' using fun n => hK _ (hw n)
    refine ⟨(⋃ n : ℕ, ({_x : X | e n ∈ ratBall p} ∩ ({x | e n ∈ ((cc x).dom : Set ℂ)} ∩ (K' n)ᶜ))) ∩
      (R' ∩ S'), ?_, fun x hxG => ?_⟩
    · exact (MeasurableSet.iUnion fun n => (MeasurableSet.const _).inter
        ((@IsMeasChart.dom X m cc hcm (e n)).inter (hK'm n).compl)).inter (hR'm.inter hS'm)
    · simp only [hΦdef, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_compl_iff, ← hR' x hxG, ← hS' x hxG]
      refine and_congr (exists_congr fun n => ?_) Iff.rfl
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun h4 => h3 ?_⟩
        have := (hK' n x hxG).2 h4
        rwa [indicator_of_mem (show x ∈ {x | e n ∈ ((cc x).dom : Set ℂ)} from h2)] at this
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun h4 => h3 ((hK' n x hxG).1 ?_)⟩
        rwa [indicator_of_mem (show x ∈ {x | e n ∈ ((cc x).dom : Set ℂ)} from h2)]
  obtain ⟨Φ', hΦ'm, hΦ'⟩ := hΦm
  have hset : {x | ((G.piecewise (fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x))
      fun _ => H) x ∩ ratBall p).Nonempty} = (G ∩ Φ'ᶜ) ∪ Gᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases hxG : x ∈ G
    · rw [piecewise_eq_of_mem _ _ _ hxG]
      obtain ⟨hr, hdom⟩ := hG x hxG
      rw [chartSet_inter_nonempty_iff hs hV hV0 hland hinj d hdV hℓ hr hdom he (isOpen_ratBall p)
        (isPreconnected_ratBall p) hp hpH]
      simp only [hxG, true_and, not_true_eq_false, or_false, ← hΦ' x hxG, hΦdef, mem_ofPred_eq]
      refine not_congr (and_congr ?_ Iff.rfl)
      constructor
      · rintro ⟨z, ⟨hzB, n, rfl⟩, hz⟩
        exact ⟨n, hzB, hz⟩
      · rintro ⟨n, hn⟩
        exact ⟨e n, ⟨hn.1, n, rfl⟩, hn.2⟩
    · rw [piecewise_eq_of_notMem _ _ _ hxG]
      simp only [hxG, false_and, not_false_eq_true, or_true, iff_true]
      exact ⟨hp.some, hpH hp.some_mem, hp.some_mem⟩
  rw [hset]
  exact (hGm.inter hΦ'm.compl).union hGm.compl

end Meas

/-! ### The record suppliers of the hitting conditions -/

section Supply

open Aux61FibData Aux61GInst Aux61Fib Aux61ULoc LawUnique Restart.FlowStopIdentG
open Aux61UnionK (chartHull)
open Aux61SlitW (accessTime capacityRule)

/-- **A ball avoids a continuous path on `(0, A]` iff it avoids it at the dyadic times in `(0, A)`.** -/
theorem disjoint_image_Ioc_iff {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {A : ℝ≥0} {B : Set ℂ} (hB : IsOpen B) :
    Disjoint B (γ '' Ioc 0 A) ↔ ∀ q : ℕ × ℕ, 0 < dyadicTime q → dyadicTime q < A → γ (dyadicTime q) ∉ B := by
  constructor
  · intro hd q hq0 hqA hqB
    exact Set.disjoint_left.1 hd hqB (mem_image_of_mem _ ⟨hq0, hqA.le⟩)
  · intro hq
    refine Set.disjoint_left.2 fun z hzB hz => ?_
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hB.preimage hγ) u hzB
    have key : ∀ (y : ℝ) (p : ℝ≥0), y.toNNReal < p → y < p := fun y p hyp => by
      rcases le_or_gt 0 y with hy | hy
      · exact (Real.toNNReal_lt_iff_lt_coe hy).1 hyp
      · exact lt_of_lt_of_le hy p.2
    have hlo : (((u : ℝ) - δ).toNNReal : ℝ≥0∞) < u := by
      rw [ENNReal.coe_lt_coe]
      rcases le_or_gt 0 ((u : ℝ) - δ) with hy | hy
      · exact (Real.toNNReal_lt_iff_lt_coe hy).2 (by linarith)
      · rw [Real.toNNReal_of_nonpos hy.le]
        exact hu.1
    have hlo' : ((0 : ℝ≥0) : ℝ≥0∞) < u := ENNReal.coe_lt_coe.2 hu.1
    obtain ⟨q, hq1, hq2⟩ := exists_dyadicTime_btwn (max_lt hlo hlo')
    have hqu : dyadicTime q < u := ENNReal.coe_lt_coe.1 hq2
    have hq0 : 0 < dyadicTime q := ENNReal.coe_lt_coe.1 (lt_of_le_of_lt (le_max_right _ _) hq1)
    have hqd : (u : ℝ) - δ < dyadicTime q := by
      have := ENNReal.coe_lt_coe.1 (lt_of_le_of_lt (le_max_left _ _) hq1)
      exact key _ _ this
    refine hq q hq0 (lt_of_lt_of_le hqu hu.2) (hball ?_)
    rw [mem_ball, NNReal.dist_eq, abs_lt]
    constructor
    · linarith
    · have : (dyadicTime q : ℝ) < u := hqu
      linarith

variable {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR}
include hs hV hV0 hland hinj

/-- The record stopped at the glued stop of `r`. -/
abbrev stoppedRec (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ r : ℝ≥0) (Y₀ : X → 𝒴) (R₀ : X → HistorySpace nL nR)
    (x : X) : 𝒴 × HistorySpace nL nR :=
  (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x))

omit mX hs hV hV0 hland hinj in
theorem measurable_ruleMarks_stoppedRec (r : ℝ≥0) :
    Measurable[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀] (stoppedRec c t₀ r Y₀ R₀) :=
  measurable_ruleMarks_of_factor (stop := stopRec) (ρ := capacityRule c t₀ r) (Y₀ := Y₀) (R₀ := R₀) measurable_id

/-- On an alive sample, the stopped record has the same rule and the same trace up to the glued stop. -/
theorem stoppedRec_facts {x : X} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) (hchart : cc x = c (Y₀ x, stopRec t₀ (R₀ x)))
    (hρ : ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) :
    recTime c t₀ r (stoppedRec c t₀ r Y₀ R₀ x) = accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r ∧
      ∀ u : ℝ≥0, t₀ + u ≤ t₀ + accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r →
        histTrace 0 (stoppedRec c t₀ r Y₀ R₀ x).2 (t₀ + u) = histTrace 0 (R₀ x) (t₀ + u) := by
  set A := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r with hAdef
  have hcapr : capacityRule c t₀ r (Y₀ x, R₀ x) = ((t₀ + A : ℝ≥0) : ℝ≥0∞) := by
    rcases eq_or_ne r 0 with rfl | hr0
    · rw [Aux61SlitW.capacityRule_zero, hAdef, Aux61SlitW.accessTime_zero hs hV hV0 hland hinj hr, add_zero]
    · exact Aux61SlitW.capacityRule_eq_accessTime hs hV hV0 hland hinj hchart hρ (pos_iff_ne_zero.2 hr0) hr
  have hst : stoppedRec c t₀ r Y₀ R₀ x = (Y₀ x, stopRec (t₀ + A) (R₀ x)) := by
    simp only [stoppedRec, hcapr, stopAt, ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]
  rw [hst]
  refine ⟨?_, fun u hu => histTrace_stopRec_of_le hu 0 (R₀ x)⟩
  have hG : capacityRule c t₀ r (Y₀ x, stopRec (t₀ + A) (R₀ x)) = capacityRule c t₀ r (Y₀ x, R₀ x) :=
    Aux61SlitW.isGalmarinoRule_capacityRule c t₀ r (Y₀ x) (R₀ x) (t₀ + A) (Or.inr hcapr.le)
  rw [recTime, hG, ← recTime, recTime_eq_accessTime hs hV hV0 hland hinj hchart hρ hr]

/-- **The slit-avoidance events from the stopped record**: on samples alive at `r` with the record reading of the chart
and of the restarted path, "a rational ball avoids the restarted path up to the code time" is a rule-mark event. -/
theorem exists_slitAvoid_ruleMarks {r : ℝ≥0} {G : Set X}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧ cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (hc : IsMeasChart c) (p : ℚ × ℚ × ℚ) :
    ∃ S' : Set X, MeasurableSet[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀] S' ∧ ∀ x ∈ G,
      (Disjoint (ratBall p) (ρ x '' Ioc 0 (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r)) ↔
        x ∈ S') := by
  set P : Set (𝒴 × HistorySpace nL nR) := ⋂ q : ℕ × ℕ, ({_p | 0 < dyadicTime q} ∩
    {p' | dyadicTime q < recTime c t₀ r p'})ᶜ ∪ {p' | histTrace 0 p'.2 (t₀ + dyadicTime q) ∉ ratBall p} with hPdef
  have hPm : MeasurableSet P := by
    refine MeasurableSet.iInter fun q => ((MeasurableSet.const _).inter ?_).compl.union ?_
    · exact measurableSet_lt measurable_const (measurable_recTime hc t₀ r)
    · exact (((measurable_histTrace 0 _).comp measurable_snd) (isOpen_ratBall p).measurableSet).compl
  refine ⟨stoppedRec c t₀ r Y₀ R₀ ⁻¹' P, measurable_ruleMarks_stoppedRec r hPm, fun x hxG => ?_⟩
  obtain ⟨hr, hchart, hρ⟩ := hG x hxG
  have hx := mem_exitEv_of_lt_accessLife hr
  obtain ⟨hrec, htr⟩ := stoppedRec_facts hs hV hV0 hland hinj hr hchart hρ
  set A := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x r with hAdef
  have hAe : A < exitNN E cc ρ T V x := (Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hr).1
  rw [disjoint_image_Ioc_iff (hs.contρ x hx.1.1) (isOpen_ratBall p)]
  simp only [hPdef, mem_preimage, mem_iInter, mem_union, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, hrec]
  refine forall_congr' fun q => ?_
  constructor
  · intro hq
    by_cases hc' : 0 < dyadicTime q ∧ dyadicTime q < A
    · right
      rw [htr _ ((add_le_add_iff_left t₀).2 hc'.2.le), ← hρ _ hc'.1 (hc'.2.trans hAe)]
      exact hq hc'.1 hc'.2
    · left
      exact hc'
  · intro hq hq0 hqA
    rcases hq with hq | hq
    · exact absurd ⟨hq0, hqA⟩ hq
    · rw [htr _ ((add_le_add_iff_left t₀).2 hqA.le), ← hρ _ hq0 (hqA.trans hAe)] at hq
      exact hq

/-- The regularized record driver path (frozen after `r`, continuous for every record). -/
def recDriverPath (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ r : ℝ≥0) (t : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : ℝ :=
  QuantumZipper.Thm18Asm.G1Pkg.pathReg (fun u => recDriver c t₀ (min u r) p) t

omit mX hs hV hV0 hland hinj in
theorem measurable_recDriverPath (hc : IsMeasChart c) (r t : ℝ≥0) : Measurable (recDriverPath c t₀ r t) :=
  (measurable_pi_apply t).comp (QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.1.comp
    (measurable_pi_iff.2 fun _ => measurable_recDriver hc t₀ _))

omit mX [MeasurableSpace 𝒴] hs hV hV0 hland hinj in
theorem continuous_recDriverPath (r : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) :
    Continuous fun t => recDriverPath c t₀ r t p :=
  QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.1 _

/-- **The hull-membership events from the stopped record**: on samples alive at `r` with the record reading of the
chart and of the restarted path, membership of an `m`-measurable random point in the chart hull at `r` is an `m`-event,
for every `m` containing the rule marks. -/
theorem exists_hullMem_of_ruleMarks (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {r : ℝ≥0} {G : Set X}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧ cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (hc : IsMeasChart c) (hm : ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀ ≤ m)
    (w : X → ℂ) (hw : Measurable[m] w) :
    ∃ K' : Set X, MeasurableSet[m] K' ∧
      ∀ x ∈ G, (w x ∈ chartHull (accessExitCode E cc ρ T V a k h) r x ↔ x ∈ K') := by
  have hZ := QuantumZipper.NonSwallow.measurableSet_fwdHull_prod (B := fun t p => recDriverPath c t₀ r t p)
    (fun t => measurable_recDriverPath hc r t) (fun p => continuous_recDriverPath r p) 1 (NNReal.coe_nonneg r)
  have hpair : Measurable[m] fun x => (w x, stoppedRec c t₀ r Y₀ R₀ x) :=
    hw.prodMk ((measurable_ruleMarks_stoppedRec r).mono hm le_rfl)
  refine ⟨(fun x => (w x, stoppedRec c t₀ r Y₀ R₀ x)) ⁻¹' {q : ℂ × (𝒴 × HistorySpace nL nR) |
    q.1 ∈ fwdHull (QuantumZipper.drive 1 (fun t p => recDriverPath c t₀ r t p) q.2) r}, hpair hZ, fun x hxG => ?_⟩
  obtain ⟨hr, hchart, hρ⟩ := hG x hxG
  set s := accessExitCode E cc ρ T V a k h x with hsdef
  -- the regularized record driver of the stopped record is the code's driver frozen after `r`
  have hdrv : ∀ v : ℝ≥0, recDriver c t₀ (min v r) (stoppedRec c t₀ r Y₀ R₀ x) = FibCode.driver (min v r) s := by
    intro v
    exact (driver_eq_recDriver_stopAt hs hV hV0 hland hinj hchart hρ d hdV hℓ
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right v r)) hr) (min_le_right v r)).symm
  have hcont : Continuous fun v : ℝ≥0 => FibCode.driver (min v r) s :=
    (FibCode.continuous_driver s).comp (continuous_id.min continuous_const)
  have hreg : ∀ t : ℝ≥0, recDriverPath c t₀ r t (stoppedRec c t₀ r Y₀ R₀ x) = FibCode.driver (min t r) s := by
    intro t
    unfold recDriverPath
    rw [show (fun u => recDriver c t₀ (min u r) (stoppedRec c t₀ r Y₀ R₀ x)) =
      fun u => FibCode.driver (min u r) s from funext hdrv, QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.2 _ hcont]
  have hhull : fwdHull (QuantumZipper.drive 1 (fun t p => recDriverPath c t₀ r t p) (stoppedRec c t₀ r Y₀ R₀ x))
      (r : ℝ) = chartHull (accessExitCode E cc ρ T V a k h) r x := by
    unfold chartHull
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc ?_ ?_ (NNReal.coe_nonneg r) fun t ht => ?_
    · exact continuous_const.mul ((continuous_recDriverPath r _).comp continuous_real_toNNReal)
    · exact (FibCode.continuous_driver s).comp continuous_real_toNNReal
    · simp only [QuantumZipper.drive, Real.sqrt_one, one_mul, hreg]
      congr 1
      exact min_eq_left (Real.toNNReal_le_iff_le_coe.2 ht.2)
  simp only [mem_preimage, mem_ofPred_eq, hhull]

end Supply

/-! ### `baseSets_marks` for the completed rule marks -/

section Final

open Aux61FibData Aux61GInst Aux61Fib Aux61ULoc LawUnique Restart.FlowStopIdentG
open Aux61UnionK (chartHull)
open Aux61SlitW (accessTime capacityRule)

variable {X : Type*} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR}
  {μ : Measure X}
include hs hV hV0 hland hinj

open scoped Classical in
/-- **`baseSets_marks` for the completed rule marks**: the marked set `chartSet c K_r` on a set `G` of samples alive at
`r` (in the completed marks) with the record reading of the chart and of the restarted path and R1's chart domain (a
component of `R x`), and `ℍ` off `G`, is hitting-measurable for the null completion of the rule marks of SLITW's glued
stop `capacityRule c t₀ r`, once the chart is measurable for the completed marks and the events "a rational ball lies
in `R x`" are, on `G`, completed-mark events (R1's retained domain: the counterflow hull's hitting events and the own
prefix at rational times). -/
theorem measurable_markedSet_nullRuleMarks (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (hc : IsMeasChart c)
    (hY₀ : Measurable Y₀) (hR₀ : Measurable R₀) {r : ℝ≥0} {G : Set X}
    (hGm : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] G) {R : X → Set ℂ} {b : X → ℂ}
    (hG : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧ cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      ((cc x).dom : Set ℂ) = connectedComponentIn (R x) (b x))
    (hcm : @IsMeasChart X (nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ) cc)
    (hR : ∀ p : ℚ × ℚ × ℚ, ∃ R' : Set X, MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] R' ∧
      ∀ x ∈ G, (ratBall p ⊆ R x ↔ x ∈ R')) :
    Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ, hittingSigma]
      (G.piecewise (fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x)) fun _ => H) := by
  have hle : ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀ ≤ mX :=
    ruleMarks_le isRecordStop_stopRec (Aux61SlitW.measurable_capacityRule hc t₀ r) hY₀ hR₀
  have hm : ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀ ≤
      nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ := le_nullMarks hle
  have hG' : ∀ x ∈ G, (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life ∧
      cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u) :=
    fun x hx => ⟨(hG x hx).1, (hG x hx).2.1, (hG x hx).2.2.1⟩
  refine measurable_markedSet hs hV hV0 hland hinj d hdV hℓ hGm (R := R) (b := b)
    (fun x hx => ⟨(hG x hx).1, (hG x hx).2.2.2⟩) hcm
    (fun w hw => exists_hullMem_of_ruleMarks hs hV hV0 hland hinj d hdV hℓ hG' hc hm w hw) hR ?_
  intro p
  obtain ⟨S', hS'm, hS'⟩ := exists_slitAvoid_ruleMarks hs hV hV0 hland hinj hG' hc p
  exact ⟨S', hm _ hS'm, hS'⟩

end Final

/-! ### The retained-domain events of R1's chart -/

section Retained

/-- **The retained-domain events**: for R1's retained domain `ℍ ∖ (K₀ ∪ η[0, t₀])` with a hitting-measurable obstacle
`K₀` and an own prefix continuous on `[0, t₀]` (on `G`) and measurable at every time, "a rational ball lies in the
retained domain" is, on `G`, an event of the σ-algebra. -/
theorem exists_retained_event {X : Type*} {m : MeasurableSpace X} {G : Set X} {K₀ : X → Set ℂ}
    (hK₀ : Measurable[m, hittingSigma] K₀) {η : X → ℝ → ℂ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hηc : ∀ x ∈ G, ContinuousOn (η x) (Icc 0 t₀)) (hηm : ∀ v : ℝ, Measurable[m] fun x => η x v)
    (p : ℚ × ℚ × ℚ) :
    ∃ R' : Set X, MeasurableSet[m] R' ∧
      ∀ x ∈ G, (ratBall p ⊆ Aux61Restart.retainedDomain (K₀ x) (η x) t₀ ↔ x ∈ R') := by
  classical
  by_cases hne : (ratBall p).Nonempty
  swap
  · refine ⟨univ, @MeasurableSet.univ X m, fun x _ => ?_⟩
    simp only [mem_univ, iff_true]
    intro z hz
    exact absurd ⟨z, hz⟩ hne
  by_cases hH : ratBall p ⊆ H
  swap
  · refine ⟨∅, @MeasurableSet.empty X m, fun x _ => ?_⟩
    simp only [mem_empty_iff_false, iff_false]
    intro hsub
    exact hH (hsub.trans sdiff_subset)
  -- the obstacle part and the prefix part at rational times
  set R' : Set X := {x | Disjoint (K₀ x) (ratBall p)} ∩
    ⋂ v : ℚ, ({_x : X | 0 ≤ (v : ℝ) ∧ (v : ℝ) ≤ t₀}ᶜ ∪ {x | η x v ∉ ratBall p}) with hR'def
  refine ⟨R', ?_, fun x hxG => ?_⟩
  · refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun v => (MeasurableSet.const _).compl.union ?_)
    · have hgen : MeasurableSet[m] (K₀ ⁻¹' {S : Set ℂ | (S ∩ ratBall p).Nonempty}) :=
        hK₀ (MeasurableSpace.measurableSet_generateFrom ⟨ratBall p, isOpen_ratBall p, hH, rfl⟩)
      have e : {x | Disjoint (K₀ x) (ratBall p)} = (K₀ ⁻¹' {S : Set ℂ | (S ∩ ratBall p).Nonempty})ᶜ := by
        ext x
        simp only [mem_ofPred_eq, mem_compl_iff, mem_preimage, not_nonempty_iff_eq_empty,
          Set.disjoint_iff_inter_eq_empty]
      rw [e]
      exact hgen.compl
    · exact ((hηm v) (isOpen_ratBall p).measurableSet).compl
  · simp only [hR'def, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · intro hsub
      refine ⟨Set.disjoint_right.2 fun z hz hzK => (hsub hz).2 (Or.inl hzK), fun v => ?_⟩
      by_cases hv : 0 ≤ (v : ℝ) ∧ (v : ℝ) ≤ t₀
      · right
        intro hvB
        exact (hsub hvB).2 (Or.inr (mem_image_of_mem _ hv))
      · left
        exact hv
    · rintro ⟨hdisj, hv⟩ z hz
      refine ⟨hH hz, ?_⟩
      rintro (hzK | ⟨u, hu, rfl⟩)
      · exact Set.disjoint_left.1 hdisj hzK hz
      · -- a rational time near `u` is in the ball
        have hcont := hηc x hxG u hu
        obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1
          (hcont.preimage_mem_nhdsWithin ((isOpen_ratBall p).mem_nhds hz))
        have hdense : ∃ v : ℚ, (v : ℝ) ∈ ball u δ ∩ Icc 0 t₀ := by
          rcases eq_or_lt_of_le ht₀ with h0 | hpos
          · have hu0 : u = 0 := le_antisymm (h0 ▸ hu.2) hu.1
            exact ⟨0, by simp [hu0, hδ, ← h0]⟩
          · have hcl : u ∈ closure (Ioo 0 t₀) := by
              rw [closure_Ioo hpos.ne]
              exact hu
            obtain ⟨w, hwb, hwI⟩ := Metric.mem_closure_iff.1 hcl δ hδ
            have ho : IsOpen (ball u δ ∩ Ioo 0 t₀) := isOpen_ball.inter isOpen_Ioo
            obtain ⟨v, hv⟩ := Rat.denseRange_cast.exists_mem_open ho
              ⟨w, by rw [mem_ball, dist_comm]; exact hwI, hwb⟩
            exact ⟨v, hv.1, Ioo_subset_Icc_self hv.2⟩
        obtain ⟨v, hvb, hvI⟩ := hdense
        rcases hv v with hv' | hv'
        · exact hv' hvI
        · exact hv' (hball ⟨hvb, hvI⟩)

end Retained

end InteractingSLE.Sec5.Aux61Marks
