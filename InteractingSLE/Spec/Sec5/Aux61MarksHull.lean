/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksUnion
import InteractingSLE.Spec.Sec5.Aux61SlitWClock

/-!
# The restarted path is mapped into the chart hull: the flow-hull input of the union containment

Packet PROVE-AUX61-MARKS. For the selected-access restart code `Y = accessExitCode E c ρ T V a k h`, alive at the fibre
time `q`, and the physical code time `accessTime x q` (SLITW's inverse capacity clock):

* the restarted path at every physical time `u ∈ (0, accessTime x q]` lies in the chart domain and is mapped by the
  chart into the chart hull `K_q` of the code (`chart_mem_chartHull_of_access`): by SLITW's
  `image_accessExitCode_Ioc` it is a point of the code's trace before capacity `q`, interior (`PathGood`), and the
  code's trace is a generating trace of its driver (`GoodTrace`), so its interior points are in the hull
  (`mem_hull_of_isFilling`);
* hence, for a simple flow line `η` whose restart is `ρ x u = η (t₀ + u)` and whose prefix through `t₀` avoids the chart
  domain, every point of the flow's Loewner hull at the glued stop `t₀ + accessTime x q` in the chart domain is mapped
  into the chart hull (`fwdHull_mapsTo_chartHull_of_access`) — the flow-hull input of
  `ae_unionAt_subset_liveSet_chartSet`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61FibData Aux61GInst Aux61Fib
open Aux61UnionK (chartHull)

/-- **Interior points of a filled set are in its filling.** -/
theorem mem_hull_of_isFilling {K A : Set ℂ} (h : IsFilling K A) {z : ℂ} (hzA : z ∈ A) (hzH : z ∈ H) : z ∈ K := by
  by_contra hzK
  obtain ⟨⟨z₀, -, hz₀⟩, -⟩ := h
  have hz : z ∈ connectedComponentIn (H \ A) z₀ := by
    rw [hz₀]
    exact ⟨hzH, hzK⟩
  exact (connectedComponentIn_subset _ _ hz).2 hzA

/-- **The code's interior trace points before an alive capacity time are in its hull.** -/
theorem trace_mem_chartHull {s : FibCode} (hs : s ∈ GoodTrace) {q v : ℝ≥0} (hq : (q : ℝ≥0∞) < s.life)
    (hv : v ≤ q) (hvH : s.trace v ∈ H) : s.trace v ∈ fwdHull (fun r : ℝ => FibCode.driver r.toNNReal s) q :=
  mem_hull_of_isFilling (hs.2.2 q hq) (mem_image_of_mem _ ⟨zero_le, hv⟩) hvH

section Access

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E c ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E c ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
include hs hV hV0 hland hinj

/-- **The restarted path up to the physical code time is mapped into the chart hull.** At an alive fibre time `q`,
for every physical time `u ∈ (0, accessTime x q]` the restarted path is in the chart domain and its chart image is in
the chart hull of the code at `q`. -/
theorem chart_mem_chartHull_of_access (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) {u : ℝ≥0}
    (hu : u ∈ Ioc 0 (Aux61SlitW.accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q)) :
    ρ x u ∈ ((c x).dom : Set ℂ) ∧ (c x).1 (ρ x u) ∈ chartHull (accessExitCode E c ρ T V a k h) q x := by
  have hx : x ∈ exitEv E c ρ T V := mem_exitEv_of_lt_accessLife hq
  have hsp := Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hq
  have hue : u < exitNN E c ρ T V x := lt_of_le_of_lt hu.2 hsp.1
  have heT : ((exitNN E c ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x := by
    rw [IsRestartSpec.coe_exitNN hx]
    exact IsRestartSpec.exitTime_le x
  have huT : (u : ℝ≥0∞) < T x := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hue) heT
  have hxE : x ∈ E := hx.1.1
  have hdom : ρ x u ∈ ((c x).dom : Set ℂ) := hs.inside x hxE u hu.1 huT
  refine ⟨hdom, ?_⟩
  have hpath : accessExitPath E c ρ T V x u = (c x).1 (ρ x u) := by
    simp only [accessExitPath, hx, ↓reduceIte, hue]
    exact hs.inPath_eq_fwd hxE hu.1 huT
  have himg := Aux61SlitW.image_accessExitCode_Ioc hs hV hV0 hland hinj (a := a) (h := h) d hdV hℓ hq
  have hmem : accessExitPath E c ρ T V x u ∈ (accessExitCode E c ρ T V a k h x).trace '' Ioc 0 q := by
    rw [himg]
    exact mem_image_of_mem _ hu
  obtain ⟨v, hv, hve⟩ := hmem
  have hgood := pathGood_accessExitCode hs hV hV0 hland hinj d hdV hℓ hx (a := a) (k := k) (h := h)
  have hvH : (accessExitCode E c ρ T V a k h x).trace v ∈ H :=
    hgood.2.2.2.2.1 v hv.1 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv.2) hq)
  rw [← hpath, ← hve]
  exact trace_mem_chartHull hgood.1 hq hv.2 hvH

/-- **The flow hull at the glued stop is mapped into the chart hull** (the flow-hull input of
`ae_unionAt_subset_liveSet_chartSet`): for a simple flow line `η` (a Loewner trace of `W`), whose restart is
`ρ x u = η (t₀ + u)` up to the physical code time and whose prefix through `t₀` avoids the chart domain, every point
of the Loewner hull at `t₀ + accessTime x q` in the chart domain is mapped into the chart hull at `q`. -/
theorem fwdHull_mapsTo_chartHull_of_access (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hγ : WangWu.IsProperArc η) {t₀ : ℝ≥0}
    (hrestart : ∀ u : ℝ≥0, 0 < u →
      u ≤ Aux61SlitW.accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q → ρ x u = η ((t₀ : ℝ) + u))
    (hpre : ∀ u ∈ Icc (0 : ℝ) t₀, η u ∉ ((c x).dom : Set ℂ)) :
    ∀ z ∈ fwdHull W ((t₀ + Aux61SlitW.accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q : ℝ≥0) : ℝ),
      z ∈ ((c x).dom : Set ℂ) → (c x).1 z ∈ chartHull (accessExitCode E c ρ T V a k h) q x := by
  set A := Aux61SlitW.accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q with hAdef
  refine flowHull_mapsTo_of_properArc hη hγ (NNReal.coe_nonneg _) hpre fun u hu _ => ?_
  have hpos : 0 < u - t₀ := sub_pos.2 hu.1
  set v : ℝ≥0 := (u - t₀).toNNReal with hvdef
  have hv : (v : ℝ) = u - t₀ := Real.coe_toNNReal _ hpos.le
  have hv0 : 0 < v := by
    rw [← NNReal.coe_pos, hv]
    exact hpos
  have hvA : v ≤ A := by
    rw [← NNReal.coe_le_coe, hv]
    have := hu.2
    push_cast at this
    linarith
  have hηu : η u = ρ x v := by
    rw [hrestart v hv0 hvA, hv]
    ring_nf
  rw [hηu]
  exact (chart_mem_chartHull_of_access hs hV hV0 hland hinj d hdV hℓ hq ⟨hv0, hvA⟩).2

/-- **The union at the glued stop is in the chart set, pointwise on the live event** (the containment of UNIONLOC's
union in the marked set fixed by CHARTLOC's geometry). At a sample alive at `q`, whose glued stop is
`t₀ + accessTime x q`, whose chart domain is inside a retained component of the own prefix through `t₀` (R1's chart)
and avoids the counterflow hull, and whose flow line is simple with restart `ρ x u = η (t₀ + u)`: the union
`ℍ ∩ (K_s ∪ K̃_T)` is in `chartSet c K_q`. -/
theorem unionAt_subset_chartSet_of_access (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {x : X} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < (accessExitCode E c ρ T V a k h x).life) {A₂ : X → Set ℂ} {Wf : X → ℝ → ℝ}
    {η : X → ℝ → ℂ} {Tg : X → ℝ≥0∞} {t₀ : ℝ≥0}
    (hTg : Tg x = ((t₀ + Aux61SlitW.accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q : ℝ≥0) : ℝ≥0∞))
    (hη : IsLoewnerTrace (Wf x) (η x)) (hγ : WangWu.IsProperArc (η x))
    (hrestart : ∀ u : ℝ≥0, 0 < u →
      u ≤ Aux61SlitW.accessTime (E := E) (c := c) (ρ := ρ) (T := T) (V := V) x q → ρ x u = η x ((t₀ : ℝ) + u))
    {K : Set ℂ} {b : ℂ} (hdom : ((c x).dom : Set ℂ) ⊆ Aux61Restart.restartComponent K (η x) t₀ b)
    (hcf : ∀ z ∈ A₂ x, z ∉ ((c x).dom : Set ℂ)) :
    Aux61ULoc.unionAt A₂ (fun r x => fwdHull (Wf x) (r : ℝ)) Tg x ⊆
      chartSet (c x) (chartHull (accessExitCode E c ρ T V a k h) q x) := by
  have hx : x ∈ exitEv E c ρ T V := mem_exitEv_of_lt_accessLife hq
  have hTlt : Tg x < ⊤ := by
    rw [hTg]
    exact ENNReal.coe_lt_top
  refine unionAt_subset_chartSet (hs.conf x hx.1.1) hTlt hcf ?_
  rw [hTg, ENNReal.toNNReal_coe]
  exact fwdHull_mapsTo_chartHull_of_access hs hV hV0 hland hinj d hdV hℓ hq hη hγ hrestart
    fun u hu hd => image_disjoint_restartComponent hu (hdom hd)

end Access

end InteractingSLE.Sec5.Aux61Marks
