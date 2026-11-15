/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aPathField
import InteractingSLE.Spec.Supplement.BR4aPathMeas
import InteractingSLE.Spec.Supplement.GB6PastStep
import InteractingSLE.Spec.Exist.Param12Canonical

/-!
# Corollary BR4a from its hull identity

Packet PROVE-BR4A. Theorem 1.4's leaf `Theorem14.BR4a.BR4aStatement` (Corollary BR4a, supplement p. 610) has a field
half and a pathwise half. The field half is `BR4aPathField.exists_isCenteredCounterflowDriver_recField`: the recentred
field `h(· + v)` has a canonical centred counterflow pair `(Wv, ζv)`. The pathwise half ("The original and transformed
stopped histories recover each other … The clock is continuous, adapted and strictly increasing … makes the relative
lifetime infinite") is, at the level of hulls, the target-change identity

  `K^{Wv}_{a(t)} = mob v (K^{W'}_t)`  for `t < T_v`,  `a(t) = hcap(mob v (K^{W'}_t))/2`,  `ζv = ∞`,

for the canonical pair of the recentred field (`BR4aHullDetStatement`, the named input: the recentred counterflow
retraces the original one up to the first visit to `v`). From it, everything else in BR4a is deterministic or a
measurability statement, and is proved here:

* the clock `ℓ = a⁻¹` (`BR4aPathSample.invClk`, read on rational times from a regularized driver) is measurable at each
  time (`BR4aPathMeas.measurable_invClk_clock`);
* almost surely `ℓ` is continuous, strictly increasing and onto `[0, T_v)`, and the tips of `Wv` read through
  `(id.recenter v).trans ∞` are the tips of `W'` read through `∞` at the clock times
  (`BR4aPathSample.retarget_of_hulls`: the Möbius image theorem, the first visit, the tips).

**`br4aStatement_of_hullDet`**: `BR4aHullDetStatement → Theorem 1.2 → Theorem 1.3 → BR4aStatement` (Theorems 1.2–1.3
at the universe of the sample space; R48 allows them for Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BR4aPath

/-- **Named input: the pathwise half of Corollary BR4a** (supplement p. 610: "The original and transformed stopped
histories recover each other, every force label, and both half-plane-capacity clocks … [the clock] makes the relative
lifetime infinite as in BR4"). In BR4a's setting, for every frozen centred counterflow pair `(Wv, ζv)` of the field
`hv` read in the frame recentred at `v` (by Theorem 1.2 the canonical one): almost surely `ζv = ∞`, and before the
first visit `T_v` of `v` by the original physical tip the hull of `Wv` at the relative capacity time
`a(t) = hcap(mob v (K'_t))/2` is the target-change image `mob v (K'_t)` of the original counterflow hull
(`mob v w = w/(v w + 1)` in counterflow coordinates: `−1/(z − v) = mob v (−1/z)`). -/
def BR4aHullDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v : ℝ, v ≠ 0 → (∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) →
    ∀ hv : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport (Chart.id.recenter v) 1 0 (chiC κ) (h ω) (hv ω)) →
    ∀ (Wv : ℝ≥0 → Ω → ℝ) (ζv : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P hv Wv ζv →
      ∀ᵐ ω ∂P, ζv ω = ⊤ ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} →
          fwdHull (fun s : ℝ => Wv s.toNNReal ω) (clock v (fun s : ℝ => W' s.toNNReal ω) t) =
            mob v '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t

/-- **Corollary BR4a from its pathwise half** (conditional helper with a distinct name; the named input is
`BR4aHullDetStatement`, Theorems 1.2–1.3 at universe `u` are permitted roots of Theorem 1.4). -/
theorem br4aStatement_of_hullDet (hD : BR4aHullDetStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : BR4a.BR4aStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' v hv0 hvis
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨Wv, ζv, hcfv⟩ := exists_isCenteredCounterflowDriver_recField h12p h13 hκ hb hh v
  have htrv : ∀ ω, IsChartTransport (Chart.id.recenter v) 1 0 (chiC κ) (h ω) (recField v (h ω)) :=
    fun ω => isChartTransport_recField _ v (h ω)
  have hDω := hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv0 hvis _ htrv Wv ζv hcfv
  have hreg := GW2Later.ae_counterflow_regular h13 hκ hcf hζ'
  have hζv : ∀ᵐ ω ∂P, ζv ω = ⊤ := hDω.mono fun ω hω => hω.1
  have hregv := GW2Later.ae_counterflow_regular h13 hκ hcfv hζv
  -- the adaptedness of the original driver
  have hadapt : ∃ 𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›, AdaptedBefore 𝓕 ζ' W' := by
    obtain ⟨b', J', h', -, -, h'', 𝓕, VL, VR, B', -, hC⟩ := hcf
    exact ⟨𝓕, hC.1.2.1⟩
  obtain ⟨𝓕, hW'a⟩ := hadapt
  -- a measurable good set and the regularized driver
  obtain ⟨G, hGae, hGm, hGsub⟩ := (hreg.and hζ').exists_measurable_mem
  classical
  set B : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then (if (t : ℝ≥0∞) < ζ' ω then W' t ω else 0) else 0 with hBdef
  have hBeq : ∀ ω ∈ G, (fun t => B t ω) = fun t => W' t ω := by
    intro ω hω
    funext t
    simp only [hBdef, hω, ↓reduceIte, (hGsub ω hω).2, ENNReal.coe_lt_top]
  have hBc : ∀ ω, Continuous fun t => B t ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [hBeq ω hω]
      obtain ⟨⟨γ, -, hWc, -⟩, -⟩ := hGsub ω hω
      exact hWc
    · have : (fun t => B t ω) = fun _ => 0 := by
        funext t
        simp only [hBdef, hω, ↓reduceIte]
      rw [this]
      exact continuous_const
  have hBm : ∀ t, Measurable (B t) := fun t =>
    Measurable.ite hGm (Restart.measurable_ite_of_adaptedBefore hW'a t) measurable_const
  refine ⟨fun ω => recField v (h ω), Wv, ζv, fun ω => invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => B s.toNNReal ω) t)
      (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => B s.toNNReal ω) t)), htrv, hcfv,
    fun u => measurable_invClk_clock hBc hBm hv0 u, ?_⟩
  filter_upwards [hDω, hregv, hvis, hGae] with ω hDωω hregvω hvisω hGω
  obtain ⟨⟨γ, hγ, hWc, hW0, htr⟩, -⟩ := hGsub ω hGω
  obtain ⟨-, -, hUc, hU0, -⟩ := hregvω
  have hBω := hBeq ω hGω
  have hBω' : (fun s : ℝ => B s.toNNReal ω) = fun s : ℝ => W' s.toNNReal ω := by
    funext s
    exact congrFun hBω s.toNNReal
  rw [hBω']
  obtain ⟨hcont, hmono, hrange, htips⟩ := retarget_of_hulls hγ hWc hW0 htr hUc hU0 hv0 hvisω hDωω.2
  exact ⟨hDωω.1, hcont, hmono, hrange, htips⟩

end InteractingSLE.Theorem14.BR4aPath
