/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondThetaMean
import InteractingSLE.Spec.Supplement.SB4SewGermUnion

/-!
# The staged cross-conditioning law: the revealed union of a flow-side set and a glued set

Packet PROVE-CROSSCOND-STAGED. The proof of Proposition 5.9 (spec pp. 142–148), Theorem 1.4's general-stage kernels
(GB9 p. 524, A.5) and SB4's retained tails all condition on the union of a counterflow hull and a multi-piece flow
prefix `α[0, t] = α₁ ∪ ⋯ ∪ α_k ∪ β[0, t']` (pieces of different angles). The single-piece law
(`CrossCond.Theta`, PROVE-CROSSCOND-THETA) proves the conditional mean of this union for one flow line from the root.
Here the flow side is **an arbitrary random set** `A` read from the first coordinate of the glued space (for instance
the hull of a staged prefix) and the other side **an arbitrary set** `G` read from the glued sample (for instance the
counterflow hull `cfHullQ s`):

* **`ae_hasSurvivingWordBoundary_union_glue`** (Proposition 3.8 at prime ends on the glued space): the local-set mean of
  `A ∪ G` has, at every prime end of every complementary component, the boundary value of the individual mean of the
  set the prime end lies on, so a per-sample boundary datum `HasUnionWordBoundary` for the individual means gives the
  surviving-word datum `HasSurvivingWordBoundary` for the union mean. Conditional independence of the two sets given
  the field comes from the glue (`condIndepEv_glue_sets`), not from field determination (contrast with
  `Theorem14.SB.SewGerm.ae_survivingWordBoundary_union`).
* **`ae_condExp_union_glue_add_eq_of_wordBoundary`** (the mean identification): if the union is history-avoidance
  local for marks `ℋ`, then `E[F(φ) | 𝒜_{A ∪ G} ∨ ℋ] + ∫ u₀ φ = ∫ v φ` almost surely, where `v` is the surviving-word
  candidate of the datum (Aux. 28 / Proposition 6.1 uniqueness, `Sec6.ae_eqOn_component_of_tendsto_global`).
* `HasUnionWordBoundary.congr`, `eqOn_of_rep`: the datum only sees the individual means on the joint complement, so it
  may be stated for any harmonic representatives.

The individual means of a staged prefix (its own conditional mean in the chart of the current tip) and the
deterministic datum are the inputs; `Sec5.CrossCondStagedTheta` instantiates this on the θ-glued space of the
counterflow. Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses
Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.Staged

open WangWu hiding ratPt exists_ratPt_dist_lt
open LocalSets
open Theorem14.SB.SewGerm (HasUnionWordBoundary HasSurvivingWordBoundary)

/-! ### Deterministic: the boundary datum sees only the joint complement -/

section Det

/-- Two harmonic representatives of the same distribution on an open subset of `ℍ` agree there. -/
theorem eqOn_of_rep {O : Set ℂ} (hO : IsOpen O) (hOH : O ⊆ H) {g : DistOn upperHalfPlaneOpens} {w w' : ℂ → ℝ}
    (hw : InnerProductSpace.HarmonicOnNhd w O) (hw' : InnerProductSpace.HarmonicOnNhd w' O)
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ = ∫ z, w z * φ z)
    (hrep' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g φ = ∫ z, w' z * φ z) : EqOn w w' O :=
  Sec6.eqOn_of_integral_mul_eq hO hOH hw hw' fun φ hφ => (hrep φ hφ).symm.trans (hrep' φ hφ)

/-- The union datum only evaluates the individual means on the joint complement `ℍ ∖ (A₁ ∪ A₂)`. -/
theorem HasUnionWordBoundary.congr {A₁ A₂ : Set ℂ} {u₀ v w₁ w₂ w₁' w₂' : ℂ → ℝ} {χ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} (h : HasUnionWordBoundary A₁ A₂ u₀ v w₁ w₂ χ b jumps)
    (h₁ : EqOn w₁ w₁' (H \ (A₁ ∪ A₂))) (h₂ : EqOn w₂ w₂' (H \ (A₁ ∪ A₂))) :
    HasUnionWordBoundary A₁ A₂ u₀ v w₁' w₂' χ b jumps := by
  intro z₀ hz₀
  obtain ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, hlim⟩ := h z₀ hz₀
  refine ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, fun q hq hqE => ?_⟩
  have hmem : ∀ ζ ∈ ball (0 : ℂ) 1, f ζ ∈ H \ (A₁ ∪ A₂) := fun ζ hζ =>
    connectedComponentIn_subset _ _ (hf.2.mapsTo hζ)
  have hev : ∀ {w w' : ℂ → ℝ}, EqOn w w' (H \ (A₁ ∪ A₂)) →
      (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ))) =ᶠ[𝓝[ball 0 1] q]
        fun ζ => (w' (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)) := fun {w w'} hww =>
    eventually_nhdsWithin_of_forall fun ζ hζ => by simp only [hww (hmem ζ hζ)]
  rcases hlim q hq hqE with ⟨p, hp, hpA, hr, hs⟩ | ⟨p, hp, hpA, hr, hs⟩
  · exact Or.inl ⟨p, hp, hpA, hr, hs.congr' (hev h₁)⟩
  · exact Or.inr ⟨p, hp, hpA, hr, hs.congr' (hev h₂)⟩

end Det

/-! ### The union on a glued space -/

section Glue

variable {Ω : Type u} {β : Type} {mΩ : MeasurableSpace Ω} [mβ : MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P] {f : Ω → DistOn upperHalfPlaneOpens}
  {k : Kernel (DistOn upperHalfPlaneOpens) β} [IsMarkovKernel k]
  {T T' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}

/-- The field read through `T` is a zero-boundary GFF on the glued space. -/
theorem isZeroBoundaryGFF_glue (hf : Measurable f)
    (hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => T (f ω)) P) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × β => T (f p.1)) (glueMeasure P k f hf) :=
  isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => T (f ω)) (f := Prod.fst) measurable_fst
    (glueMeasure_fst (μ := P) k hf) hF

/-- **Proposition 3.8 at prime ends for a glued union.** For a set `A` read from the first coordinate and a set `G`
read from the glued sample, both local, the local-set mean of `A ∪ G` inherits at every prime end the boundary value of
the individual mean of the set the prime end lies on. Hence the union datum `HasUnionWordBoundary` of the individual
means gives the surviving-word datum `HasSurvivingWordBoundary` of the union mean. Conditional independence of the two
sets given the field is the glue's (`condIndepEv_glue_sets`). -/
theorem ae_hasSurvivingWordBoundary_union_glue (hf : Measurable f) (hT : Measurable T) (hT' : Measurable T')
    (hTT : ∀ g, T' (T g) = g)
    (hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => T (f ω)) P) {A : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) {G : β → Set ℂ} (hGm : Measurable[mβ, hittingSigma] G)
    (hA : IsLocalSet (fun p : Ω × β => A p.1) (fun p => T (f p.1)) (glueMeasure P k f hf))
    (hGl : IsLocalSet (fun p : Ω × β => G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf))
    (hunbA : ∀ᵐ p ∂(glueMeasure P k f hf), ∀ z ∈ lowerUnion (A p.1),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A p.1)) z))
    (hunbG : ∀ᵐ p ∂(glueMeasure P k f hf), ∀ z ∈ lowerUnion (G p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (G p.2)) z))
    {g gA gG : Ω × β → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × β => A p.1 ∪ G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf) g)
    (hgA : IsLocalSetMean (fun p : Ω × β => A p.1) (fun p => T (f p.1)) (glueMeasure P k f hf) gA)
    (hgG : IsLocalSetMean (fun p : Ω × β => G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf) gG)
    (u₀ : ℂ → ℝ) (v : Ω × β → ℂ → ℝ) (χ : ℝ) (b : Ω × β → ℝ → ℝ) (jumps : Ω × β → Finset ℝ)
    {D : Set (Ω × β)}
    (hword : ∀ᵐ p ∂(glueMeasure P k f hf), p ∈ D → ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ A p.1) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A p.1 → gA p φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ G p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ G p.2 → gG p φ = ∫ z, wG z * φ z) →
      HasUnionWordBoundary (A p.1) (G p.2) u₀ (v p) wA wG χ (b p) (jumps p)) :
    ∀ᵐ p ∂(glueMeasure P k f hf), p ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ (A p.1 ∪ G p.2)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A p.1 ∪ G p.2) → g p φ = ∫ z, w z * φ z) →
      HasSurvivingWordBoundary (A p.1 ∪ G p.2) u₀ (v p) w χ (b p) (jumps p) := by
  have hF' := isZeroBoundaryGFF_glue (k := k) hf hF
  have hAm' : Measurable[_, hittingSigma] fun p : Ω × β => A p.1 := hAm.comp measurable_fst
  have hGm' : Measurable[_, hittingSigma] fun p : Ω × β => G p.2 := hGm.comp measurable_snd
  have hci := condIndepEv_glue_sets (P := P) hf k hT hT' hTT hAm hGm
  have hcmp₁ := Sec6.ae_tendsto_comp_sub_of_union_symm hF' hAm' hGm' hci hA hGl hunbA hg hgA
  have hcmp₂ := Sec6.ae_tendsto_comp_sub_of_union hF' hAm' hGm' hci hA hGl hunbG hg hgG
  filter_upwards [hcmp₁, hcmp₂, hgA.2.1, hgG.2.1, hword]
    with p hc₁ hc₂ hgAp hgGp hwp hpD w hw hrep z₀ hz₀
  obtain ⟨wA, hwA, hrepA⟩ := hgAp
  obtain ⟨wG, hwG, hrepG⟩ := hgGp
  obtain ⟨φf, φc, G', L, E, hφf, hφc, hG', hL, hd, hE, hv, hlim⟩ := hwp hpD wA wG hwA hrepA hwG hrepG z₀ hz₀
  refine ⟨φf, φc, G', L, E, hφf, hφc, hG', hL, hd, hE, hv, ?_⟩
  intro q hq hqE
  have hmapsA : MapsTo φf (ball 0 1) (H \ A p.1) := by
    intro ζ hζ
    have hz := connectedComponentIn_subset (H \ (A p.1 ∪ G p.2)) z₀ (hφf.2.mapsTo hζ)
    exact ⟨hz.1, fun h' => hz.2 (Or.inl h')⟩
  have hmapsG : MapsTo φf (ball 0 1) (H \ G p.2) := by
    intro ζ hζ
    have hz := connectedComponentIn_subset (H \ (A p.1 ∪ G p.2)) z₀ (hφf.2.mapsTo hζ)
    exact ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  rcases hlim q hq hqE with ⟨p₀, hp₀, hpA, hr, hs⟩ | ⟨p₀, hp₀, hpA, hr, hs⟩
  · have hc := hc₁ w wA hw hrep hwA hrepA φf q p₀ hmapsA hp₀ hpA hr
    have ht := hc.add hs
    rw [zero_add] at ht
    exact ht.congr fun ζ => by ring
  · have hc := hc₂ w wG hw hrep hwG hrepG φf q p₀ hmapsG hp₀ hpA hr
    have ht := hc.add hs
    rw [zero_add] at ht
    exact ht.congr fun ζ => by ring

/-- **The mean identification for a glued union.** If `A` (first coordinate) and `G` (glued sample) are local, the
union is history-avoidance local for marks `ℋ = σ(Y)|𝔐` (a recorded history), and the individual means satisfy the
per-sample union datum with the candidate `v`, then almost surely on `D`, for every test function `φ` supported off
the union,
`E[F(φ) | 𝒜_{A ∪ G} ∨ ℋ] + ∫ u₀ φ = ∫ v φ`. The union mean is identified on every complementary component by Aux. 28
(`Sec6.ae_eqOn_component_of_tendsto_global`); no boundedness of the local-set mean is assumed. -/
theorem ae_condExp_union_glue_add_eq_of_wordBoundary (hf : Measurable f) (hT : Measurable T)
    (hT' : Measurable T') (hTT : ∀ g, T' (T g) = g)
    (hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => T (f ω)) P) {A : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) {G : β → Set ℂ} (hGm : Measurable[mβ, hittingSigma] G)
    (hA : IsLocalSet (fun p : Ω × β => A p.1) (fun p => T (f p.1)) (glueMeasure P k f hf))
    (hGl : IsLocalSet (fun p : Ω × β => G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf))
    (hunbA : ∀ᵐ p ∂(glueMeasure P k f hf), ∀ z ∈ lowerUnion (A p.1),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A p.1)) z))
    (hunbG : ∀ᵐ p ∂(glueMeasure P k f hf), ∀ z ∈ lowerUnion (G p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (G p.2)) z))
    {gA gG : Ω × β → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean (fun p : Ω × β => A p.1) (fun p => T (f p.1)) (glueMeasure P k f hf) gA)
    (hgG : IsLocalSetMean (fun p : Ω × β => G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf) gG)
    {γ : Type*} {𝔐 : MeasurableSpace γ} [mγ : MeasurableSpace γ] {Y : Ω × β → γ} (hY : Measurable Y)
    (h𝔐 : 𝔐 ≤ mγ)
    (hmark : WholeField.IsHistoryAvoidanceLocal (𝔐.comap Y) (fun p : Ω × β => A p.1 ∪ G p.2)
      (fun p => T (f p.1)) (glueMeasure P k f hf))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    (v : Ω × β → ℂ → ℝ) (χ : ℝ) (b : Ω × β → ℝ → ℝ) (jumps : Ω × β → Finset ℝ) {D : Set (Ω × β)}
    (hword : ∀ᵐ p ∂(glueMeasure P k f hf), p ∈ D → ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ A p.1) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A p.1 → gA p φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ G p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ G p.2 → gG p φ = ∫ z, wG z * φ z) →
      HasUnionWordBoundary (A p.1) (G p.2) u₀ (v p) wA wG χ (b p) (jumps p))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k f hf), p ∈ D → tsupport φ ⊆ H \ (A p.1 ∪ G p.2) →
      (glueMeasure P k f hf)[fun p' => T (f p'.1) φ |
          germSigma (fun p : Ω × β => A p.1 ∪ G p.2) (fun p => T (f p.1)) ⊔ 𝔐.comap Y] p + ∫ z, u₀ z * φ z =
        ∫ z, v p z * φ z := by
  have hF' := isZeroBoundaryGFF_glue (k := k) hf hF
  have hUm : Measurable[_, hittingSigma] fun p : Ω × β => A p.1 ∪ G p.2 :=
    LocalSets.measurable_union_hitting (hAm.comp measurable_fst) (hGm.comp measurable_snd)
  have hloc := IsLocalSet.glue_union hf k hT hT' hTT hF hAm hGm hA hGl
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hF' hUm hloc
  have hℋ : 𝔐.comap Y ≤ (inferInstance : MeasurableSpace (Ω × β)) :=
    (MeasurableSpace.comap_mono h𝔐).trans hY.comap_le
  have hce := IsLocalSetMean.ae_eq_condExp_germSigma_sup hF' hUm hloc hℋ hmark hg φ
  have hsurv := ae_hasSurvivingWordBoundary_union_glue hf hT hT' hTT hF hAm hGm hA hGl hunbA hunbG hg hgA hgG
    u₀ v χ b jumps hword
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hF' hUm hloc hg hu₀ hu₀b χ
  filter_upwards [hce, hg.2.1, hsurv, huniq] with p hcp hgp hsp hup hpD hφ
  obtain ⟨w, hw, hrep⟩ := hgp
  have hS := hsp hpD w hw hrep
  have hid : EqOn (fun z => w z + u₀ z) (v p) (H \ (A p.1 ∪ G p.2)) := by
    intro z hz
    obtain ⟨φf, φc, G', L, E, hφf, hφc, hG', hL, hd, hE, hv, hlim⟩ := hS z hz
    have he := hup z hz w hw hrep φf φc G' L E hφf hφc hG'.1 hG'.2.1 hL hd hE hlim
    exact (he z (mem_connectedComponentIn hz)).trans (hv (mem_connectedComponentIn hz)).symm
  have hwi : Integrable fun z => w z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hw z hz).1.continuousAt.continuousWithinAt) φ hφ
  have hui : Integrable fun z => u₀ z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  rw [← hcp, hrep φ hφ, ← integral_add hwi hui]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero, add_zero]
  · change w z * φ z + u₀ z * φ z = v p z * φ z
    rw [← hid (hφ (subset_tsupport _ hz))]
    ring

/-- **The conditional law given a glued union** (characteristic-function form of
`ae_condExp_union_glue_add_eq_of_wordBoundary`): under the same hypotheses, almost surely on `D`, for every test
function `φ` supported off the union, `E[e^{i F(φ)} | 𝒜_{A ∪ G} ∨ ℋ] = e^{i(∫ v φ − ∫ u₀ φ)} e^{−½ Var}` with `Var` the
zero-boundary Green covariance of the complement: given the revealed union, `F` is the zero-boundary GFF of the
complement plus the surviving-word mean `v − u₀`. -/
theorem ae_condExp_cexp_union_glue_eq_of_wordBoundary (hf : Measurable f) (hT : Measurable T)
    (hT' : Measurable T') (hTT : ∀ g, T' (T g) = g)
    (hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => T (f ω)) P) {A : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) {G : β → Set ℂ} (hGm : Measurable[mβ, hittingSigma] G)
    (hA : IsLocalSet (fun p : Ω × β => A p.1) (fun p => T (f p.1)) (glueMeasure P k f hf))
    (hGl : IsLocalSet (fun p : Ω × β => G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf))
    (hunbA : ∀ᵐ p ∂(glueMeasure P k f hf), ∀ z ∈ lowerUnion (A p.1),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A p.1)) z))
    (hunbG : ∀ᵐ p ∂(glueMeasure P k f hf), ∀ z ∈ lowerUnion (G p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (G p.2)) z))
    {gA gG : Ω × β → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean (fun p : Ω × β => A p.1) (fun p => T (f p.1)) (glueMeasure P k f hf) gA)
    (hgG : IsLocalSetMean (fun p : Ω × β => G p.2) (fun p => T (f p.1)) (glueMeasure P k f hf) gG)
    {γ : Type*} {𝔐 : MeasurableSpace γ} [mγ : MeasurableSpace γ] {Y : Ω × β → γ} (hY : Measurable Y)
    (h𝔐 : 𝔐 ≤ mγ)
    (hmark : WholeField.IsHistoryAvoidanceLocal (𝔐.comap Y) (fun p : Ω × β => A p.1 ∪ G p.2)
      (fun p => T (f p.1)) (glueMeasure P k f hf))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    (v : Ω × β → ℂ → ℝ) (χ : ℝ) (b : Ω × β → ℝ → ℝ) (jumps : Ω × β → Finset ℝ) {D : Set (Ω × β)}
    (hword : ∀ᵐ p ∂(glueMeasure P k f hf), p ∈ D → ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ A p.1) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A p.1 → gA p φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ G p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ G p.2 → gG p φ = ∫ z, wG z * φ z) →
      HasUnionWordBoundary (A p.1) (G p.2) u₀ (v p) wA wG χ (b p) (jumps p))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k f hf), p ∈ D → tsupport φ ⊆ H \ (A p.1 ∪ G p.2) →
      (glueMeasure P k f hf)[fun p' => Complex.exp (Complex.I * (T (f p'.1) φ : ℂ)) |
          germSigma (fun p : Ω × β => A p.1 ∪ G p.2) (fun p => T (f p.1)) ⊔ 𝔐.comap Y] p =
        Complex.exp (Complex.I * (((∫ z, v p z * φ z) - ∫ z, u₀ z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ relClosureH (A p.1 ∪ G p.2)) φ φ) : ℝ) : ℂ) := by
  have hF' := isZeroBoundaryGFF_glue (k := k) hf hF
  have hUm : Measurable[_, hittingSigma] fun p : Ω × β => A p.1 ∪ G p.2 :=
    LocalSets.measurable_union_hitting (hAm.comp measurable_fst) (hGm.comp measurable_snd)
  have hloc := IsLocalSet.glue_union hf k hT hT' hTT hF hAm hGm hA hGl
  have hℋ : 𝔐.comap Y ≤ (inferInstance : MeasurableSpace (Ω × β)) :=
    (MeasurableSpace.comap_mono h𝔐).trans hY.comap_le
  obtain ⟨M, -, hM1, hM2⟩ := WholeField.exists_condExp_germSigma_history hF' hUm hℋ hmark hloc.2.1 φ
  have hid := ae_condExp_union_glue_add_eq_of_wordBoundary hf hT hT' hTT hF hAm hGm hA hGl hunbA hunbG hgA hgG hY
    h𝔐 hmark hu₀ hu₀b v χ b jumps hword φ
  filter_upwards [hM1, hM2, hid] with p h1 h2 h3 hpD hφ
  rw [← h2, h1, ← h3 hpD hφ, add_sub_cancel_right]

end Glue

end InteractingSLE.Sec5.CrossCond.Staged
