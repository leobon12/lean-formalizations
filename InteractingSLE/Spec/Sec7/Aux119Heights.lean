/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Nested
import InteractingSLE.Spec.Sec7.Aux119HeightsSide
import InteractingSLE.Spec.Sec7.Aux2728PocketWall
import InteractingSLE.Spec.Sec7.Lemma71NOuter

/-!
# Aux. lemma 119: the walls' own heights along the change pocket, and the conditional mean of the pocket

Packet PROVE-STRIPSYS25. Specification §7.4, the proof of Aux. lemma 119 (`source/spec/p385-432.md` L33, L50–L52,
pp. 386–387): "Hence the own height `λ − θ_Lχ` on a right side of the left path, and `−λ − θ_Rχ` on a left side of the
right path, become exactly the two heights in (PW13.1) in the final chart. […] Choose the own times from a countable
rational family before selecting a suitable one on a realization. This gives all the boundary identities
simultaneously on one event of probability one. In the `φ` coordinate they are (PW13.1). The only exceptions are
`x₀`, `y₀` and the finitely many angle-change points on the selected arcs. Apply the retained local-set subpower
estimate of Aux. 27 and the conformal finite-exception uniqueness argument of Aux. 28."

The single-path side heights of a wall at a stop `q` (`StripGeom.HasSideHeights`: along every approach to a prefix
point from the unbounded domain of the prefix on which the own chart tends to a positive real, the flattened mean
tends to `λ − θχ`; to `−λ − θχ` for a negative real) become **own heights along the change pocket's approach**: the
pocket lies on the right of the left wall (`changePocket_subset_rightSideOf_left`) and in the unbounded domain of
each prefix, so along every ultrafilter of the pocket approach the own chart tends to a positive real
(`Lemma613.exists_pos_tendsto_of_rightSideOf`); for the right wall the pocket lies on its left and the chart tends to
a negative real (`Lemma71N.exists_neg_tendsto_of_leftSideOf`).

With the nested comparisons of `Aux119Nested` at all rational own times on one event, this supplies both hypotheses
of `Aux2728Pocket.ae_eqOn_changePocket`: **the conditional mean in the change pocket is the bounded Poisson extension
of (PW13.1)** (`ae_eqOn_changePocket_of_sideHeights`), from the walls' Lemma 6.2 inputs and their single-path side
heights at rational own times (the input `hsideL`/`hsideR`, one rational stop per wall point off the angle changes).

## Main results

* `tendsto_ownHeight_left`, `tendsto_ownHeight_right` (deterministic): side heights ⇒ own heights along the pocket;
* **`ae_ownHeights`**: on one probability-one event, the nested comparison and the own height at every wall point off
  the exceptional own times (the two hypotheses of `Aux119Own` / `ae_eqOn_changePocket`);
* **`ae_eqOn_changePocket_of_sideHeights`**: the conditional mean in the change pocket.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux119Heights

open QuantumZipper (H Hbar logDerivFwd fwdMap chiC)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux2728Pocket

/-! ### Side heights become own heights along the pocket -/

section Det

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

theorem sub_ofReal_zero (z : ℂ) : z - ((0 : ℝ) : ℂ) = z := by rw [Complex.ofReal_zero, sub_zero]

/-- The change pocket lies in the unbounded domain of every prefix of the left wall. -/
theorem changePocket_subset_H_diff_fillH_left (hF : IsFlowChart R L r Ψ c) {WL : ℝ≥0 → ℝ}
    (htrL : IsGeneratingTrace WL ⊤ L) (q : ℝ≥0) : changePocket R L r ⊆ H \ fillH (L '' Icc 0 q) := by
  rw [← SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htrL (WithTop.coe_lt_top q)]
  exact hF.isTwoArcFrame.subset_H_diff_fwdHull_left htrL q

/-- The change pocket lies in the unbounded domain of every prefix of the right wall. -/
theorem changePocket_subset_H_diff_fillH_right (hF : IsFlowChart R L r Ψ c) {WR : ℝ≥0 → ℝ}
    (htrR : IsGeneratingTrace WR ⊤ R) (q : ℝ≥0) : changePocket R L r ⊆ H \ fillH (R '' Icc 0 q) := by
  rw [← SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htrR (WithTop.coe_lt_top q)]
  exact hF.isTwoArcFrame.subset_H_diff_fwdHull_right htrR q

/-- **The own height of the left wall along the pocket** ("the own height `λ − θ_Lχ` on a right side of the left
path"): if the left wall has the side heights of angle `θ` at `L s` at the stop `q > s > 0`, its flattened own mean
tends to `λ − θχ` along the pocket approach to `L s`. -/
theorem tendsto_ownHeight_left (hF : IsFlowChart R L r Ψ c) {WL : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L)
    (hWL : Continuous WL) (hWL0 : WL 0 = 0) {κ θ : ℝ} {s q : ℝ≥0} (hs0 : 0 < s) (hsq : s < q) {v u₀ : ℂ → ℝ}
    (hside : HasSideHeights κ θ L 0 WL q (L s) v u₀) :
    Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ => WL t.toNNReal) q z).im)
      (𝓝[changePocket R L r] (L s)) (𝓝 (sleLambda κ - θ * chiC κ)) := by
  have hCr := hF.config.changePocket_subset_rightSideOf_left hF.orient
  have hCf := changePocket_subset_H_diff_fillH_left hF htrL q
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨y, hy, hT⟩ := Lemma613.exists_pos_tendsto_of_rightSideOf hF.config.left hWL hWL0 htrL hs0 hsq U
    (hU.trans (nhdsWithin_mono _ hCr))
  have hT' : Tendsto (fun z => fwdMap (fun r : ℝ => WL r.toNNReal) q (z - ((0 : ℝ) : ℂ))) U (𝓝 (y : ℂ)) := by
    simp only [sub_ofReal_zero]; exact hT
  have h := (hside U inferInstance (hU.trans (nhdsWithin_mono _ hCf)) y hT').1 hy
  simp only [sub_ofReal_zero] at h
  exact h

/-- **The own height of the right wall along the pocket** ("`−λ − θ_Rχ` on a left side of the right path"), when the
pocket lies on the left of the right wall (`changePocket_subset_leftSideOf_iff`: equivalently, the left wall's change
point does; the premise of the flow-chart orientation). -/
theorem tendsto_ownHeight_right (hF : IsFlowChart R L r Ψ c) (hCl : changePocket R L r ⊆ leftSideOf (range R))
    {WR : ℝ≥0 → ℝ} (htrR : IsGeneratingTrace WR ⊤ R) (hWR : Continuous WR) (hWR0 : WR 0 = 0) {κ θ : ℝ}
    {s q : ℝ≥0} (hs0 : 0 < s) (hsq : s < q) {v u₀ : ℂ → ℝ} (hside : HasSideHeights κ θ R 0 WR q (R s) v u₀) :
    Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ => WR t.toNNReal) q z).im)
      (𝓝[changePocket R L r] (R s)) (𝓝 (-sleLambda κ - θ * chiC κ)) := by
  have hCf := changePocket_subset_H_diff_fillH_right hF htrR q
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨y, hy, hT⟩ := Lemma71N.exists_neg_tendsto_of_leftSideOf hF.config.right hWR hWR0 htrR hs0 hsq U
    (hU.trans (nhdsWithin_mono _ hCl))
  have hT' : Tendsto (fun z => fwdMap (fun r : ℝ => WR r.toNNReal) q (z - ((0 : ℝ) : ℂ))) U (𝓝 (y : ℂ)) := by
    simp only [sub_ofReal_zero]; exact hT
  have h := (hside U inferInstance (hU.trans (nhdsWithin_mono _ hCf)) y hT').2 hy
  simp only [sub_ofReal_zero] at h
  exact h

end Det

/-! ### The own heights and nested comparisons on one event -/

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- A harmonic representative of a distribution harmonic on `U`, `0` if there is none. -/
def harmRep (T : DistOn upperHalfPlaneOpens) (U : Set ℂ) : ℂ → ℝ :=
  open Classical in if hT : IsHarmonicDistOn T U then Classical.choose hT else 0

theorem harmRep_spec {T : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hT : IsHarmonicDistOn T U) :
    InnerProductSpace.HarmonicOnNhd (harmRep T U) U ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → T φ = ∫ z, harmRep T U z * φ z := by
  have e : harmRep T U = Classical.choose hT := by simp only [harmRep, hT, ↓reduceDIte]
  rw [e]
  exact Classical.choose_spec hT

/-- **The own heights and the nested comparisons of both walls, on one event** (proof of Aux. lemma 119, p. 387:
"Choose the own times from a countable rational family before selecting a suitable one on a realization. This gives
all the boundary identities simultaneously on one event of probability one"). For two transient walls with Lemma
6.2's inputs, versions `gU` of the union mean and `gL q`, `gR q` of the prefix means, and the single-path side heights
of each wall point off the exceptional own times at some rational stop (angles `θL s`, `θR s`): almost surely, for
every harmonic representative `v` of the union mean and every flow chart of a change pocket of the two walls (the
pocket on the left of the right wall, continuous drivers from `0` generating the walls), the prefix representatives
`vL q`, `vR q` give, at every wall point off the other wall and the exceptional times, an own time `q > s` with the
nested comparison and the own height `λ − θL(s)χ` (left wall), `−λ − θR(s)χ` (right wall) along the pocket. -/
theorem ae_ownHeights (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {Lw Rw : Ω → ℝ≥0 → ℂ}
    (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0) (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lw ω t) =ᵐ[P] fun ω => f (X ω))
    (hLloc : Sec6.IsEntranceHistoryLocal Lw X P) (hLim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Lw ω t).im)
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Rw ω t) =ᵐ[P] fun ω => f (X ω))
    (hRloc : Sec6.IsEntranceHistoryLocal Rw X P) (hRim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Rw ω t).im)
    (htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ))
    {gU : Ω → DistOn upperHalfPlaneOpens} (hgU : IsLocalSetMean (wallUnion Lw Rw) X P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Lw ω '' Icc 0 q ∩ H) X P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Rw ω '' Icc 0 q ∩ H) X P (gR q))
    {κ : ℝ} {u₀ : ℂ → ℝ} {θL θR : ℝ≥0 → ℝ} {SL SR : Set ℝ≥0} {WL WR : Ω → ℝ≥0 → ℝ}
    (hsideL : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → s ∉ SL → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gL q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ (θL s) (Lw ω) 0 (WL ω) q (Lw ω s) v u₀)
    (hsideR : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → s ∉ SR → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gR q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ (θR s) (Rw ω) 0 (WR ω) q (Rw ω s) v u₀) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion Lw Rw ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion Lw Rw ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (Rw ω) (Lw ω) r Ψ c →
      changePocket (Rw ω) (Lw ω) r ⊆ leftSideOf (range (Rw ω)) →
      IsGeneratingTrace (WL ω) ⊤ (Lw ω) → Continuous (WL ω) → WL ω 0 = 0 →
      IsGeneratingTrace (WR ω) ⊤ (Rw ω) → Continuous (WR ω) → WR ω 0 = 0 →
      ∃ vL vR : ℝ≥0 → ℂ → ℝ,
        (∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → s ∉ SL → ∃ q : ℝ≥0, s < q ∧
          Tendsto (fun z => v z - vL q z) (𝓝[changePocket (Rw ω) (Lw ω) r] (Lw ω s)) (𝓝 0) ∧
          Tendsto (fun z => vL q z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ => WL ω t.toNNReal) q z).im)
            (𝓝[changePocket (Rw ω) (Lw ω) r] (Lw ω s)) (𝓝 (sleLambda κ - θL s * chiC κ))) ∧
        (∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → s ∉ SR → ∃ q : ℝ≥0, s < q ∧
          Tendsto (fun z => v z - vR q z) (𝓝[changePocket (Rw ω) (Lw ω) r] (Rw ω s)) (𝓝 0) ∧
          Tendsto (fun z => vR q z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ => WR ω t.toNNReal) q z).im)
            (𝓝[changePocket (Rw ω) (Lw ω) r] (Rw ω s)) (𝓝 (-sleLambda κ - θR s * chiC κ))) := by
  have hgU' : IsLocalSetMean (wallUnion Rw Lw) X P gU := by rw [wallUnion_comm]; exact hgU
  have hnL := ae_tendsto_sub_prefix_rat hX hLc hL0 hLm hLdet hLloc hLim hRc hR0 hRm hRdet hRloc hRim htr hgU hgL
  have hnR := ae_tendsto_sub_prefix_rat hX hRc hR0 hRm hRdet hRloc hRim hLc hL0 hLm hLdet hLloc hLim
    (htr.mono fun _ h => ⟨h.2, h.1⟩) hgU' hgR
  have hrepL : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, IsHarmonicDistOn (gL q ω) (H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H)) :=
    ae_all_iff.2 fun q => (hgL q).2.1
  have hrepR : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, IsHarmonicDistOn (gR q ω) (H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H)) :=
    ae_all_iff.2 fun q => (hgR q).2.1
  filter_upwards [hnL, hnR, hrepL, hrepR, hsideL, hsideR] with ω hωnL hωnR hωrL hωrR hωsL hωsR v hv hgv r Ψ c hF
    hCl htrL hWLc hWL0 htrR hWRc hWR0
  have hAeq : H \ wallUnion Lw Rw ω = H \ (range (Lw ω) ∪ range (Rw ω)) := H_diff_wallUnion Lw Rw ω
  have hAeq' : H \ wallUnion Rw Lw ω = H \ (range (Rw ω) ∪ range (Lw ω)) := H_diff_wallUnion Rw Lw ω
  have hv' : InnerProductSpace.HarmonicOnNhd v (H \ wallUnion Rw Lw ω) := by rwa [wallUnion_comm]
  have hgv' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion Rw Lw ω → gU ω φ = ∫ z, v z * φ z := by
    rw [wallUnion_comm]; exact hgv
  refine ⟨fun q => harmRep (gL q ω) (H \ (Lw ω '' Icc 0 q ∩ H)),
    fun q => harmRep (gR q ω) (H \ (Rw ω '' Icc 0 q ∩ H)), fun s hsR hsS => ?_, fun s hsL hsS => ?_⟩
  · obtain ⟨q, hsq, hq⟩ := hωsL s hsR hsS
    obtain ⟨hvq, hgvq⟩ := harmRep_spec (hωrL q)
    have hs0 : 0 < s := pos_of_ne_zero fun h0 => hsR ⟨0, by rw [h0, hL0, hR0]⟩
    have hsH : Lw ω s ∈ H := hF.config.left.2.2.2.1 s hs0
    refine ⟨q, hsq, ?_, ?_⟩
    · have h1 := hωnL q v _ hv hgv hvq hgvq hF.config.left.2.1 s hsq hsH hsR
      rw [hAeq] at h1
      exact tendsto_sub_changePocket_left hF.config h1
    · exact tendsto_ownHeight_left hF htrL hWLc hWL0 hs0 hsq (hq _ hvq hgvq)
  · obtain ⟨q, hsq, hq⟩ := hωsR s hsL hsS
    obtain ⟨hvq, hgvq⟩ := harmRep_spec (hωrR q)
    have hs0 : 0 < s := pos_of_ne_zero fun h0 => hsL ⟨0, by rw [h0, hR0, hL0]⟩
    have hsH : Rw ω s ∈ H := hF.config.right.2.2.2.1 s hs0
    refine ⟨q, hsq, ?_, ?_⟩
    · have h1 := hωnR q v _ hv' hgv' hvq hgvq hF.config.right.2.1 s hsq hsH hsL
      rw [hAeq'] at h1
      exact tendsto_sub_changePocket_right hF.config h1
    · exact tendsto_ownHeight_right hF hCl htrR hWRc hWR0 hs0 hsq (hq _ hvq hgvq)

/-- **The conditional mean in the change pocket is the bounded Poisson extension of (PW13.1)** (Aux. lemma 119,
p. 385: "the initial conditional field in this chart has the bounded Poisson mean with boundary values `λ − θ_Lχ` on
each left incoming piece, `−λ − θ_Rχ` on each right incoming piece"; proof, p. 387), from the walls' Lemma 6.2 inputs,
the union mean, the prefix means and the single-path side heights at rational stops (`ae_ownHeights`), for a bounded
harmonic deterministic mean `u₀`. Almost surely, for every harmonic representative `v` of the union mean, every flow
chart `c` of a change pocket of the walls (pocket on the left of the right wall), with a lift `c.2.2 = Im ℓ` and the
common lift's integer `n`, continuous drivers from `0` generating the walls, finite exceptional own times, and every
bounded harmonic extension `G` of the transported heights `λ − θL χ` (left), `−λ − θR χ` (right) off the exceptional
chart points: `v + u₀ = G ∘ c.1 − χ (c.2.2 + 2πn)` on the change pocket. -/
theorem ae_eqOn_changePocket_of_sideHeights (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    {Lw Rw : Ω → ℝ≥0 → ℂ}
    (hLc : ∀ ω, Continuous (Lw ω)) (hL0 : ∀ ω, Lw ω 0 = 0) (hLm : ∀ t, Measurable fun ω => Lw ω t)
    (hLdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lw ω t) =ᵐ[P] fun ω => f (X ω))
    (hLloc : Sec6.IsEntranceHistoryLocal Lw X P) (hLim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Lw ω t).im)
    (hRc : ∀ ω, Continuous (Rw ω)) (hR0 : ∀ ω, Rw ω 0 = 0) (hRm : ∀ t, Measurable fun ω => Rw ω t)
    (hRdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Rw ω t) =ᵐ[P] fun ω => f (X ω))
    (hRloc : Sec6.IsEntranceHistoryLocal Rw X P) (hRim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Rw ω t).im)
    (htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ))
    {gU : Ω → DistOn upperHalfPlaneOpens} (hgU : IsLocalSetMean (wallUnion Lw Rw) X P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Lw ω '' Icc 0 q ∩ H) X P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Rw ω '' Icc 0 q ∩ H) X P (gR q))
    {κ : ℝ} {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {θL θR : ℝ≥0 → ℝ} {SL SR : Set ℝ≥0} (hSL : SL.Finite) (hSR : SR.Finite) {WL WR : Ω → ℝ≥0 → ℝ}
    (hsideL : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → s ∉ SL → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Lw ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gL q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ (θL s) (Lw ω) 0 (WL ω) q (Lw ω s) v u₀)
    (hsideR : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → s ∉ SR → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Rw ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          gR q ω φ = ∫ z, v z * φ z) →
        HasSideHeights κ (θR s) (Rw ω) 0 (WR ω) q (Rw ω s) v u₀) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion Lw Rw ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion Lw Rw ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (Rw ω) (Lw ω) r Ψ c → changePocket (Rw ω) (Lw ω) r ⊆ leftSideOf (range (Rw ω)) →
      IsDerivLog c.1 ℓ (changePocket (Rw ω) (Lw ω) r) →
      (∀ z ∈ changePocket (Rw ω) (Lw ω) r, c.2.2 z = (ℓ z).im) → IsPocketBranch (Lw ω) (Rw ω) c n →
      IsGeneratingTrace (WL ω) ⊤ (Lw ω) → Continuous (WL ω) → WL ω 0 = 0 →
      IsGeneratingTrace (WR ω) ⊤ (Rw ω) → Continuous (WR ω) → WR ω 0 = 0 →
      IsBoundedHarmonicExtension
        (chartData (Lw ω) (Rw ω) (fun s => sleLambda κ - θL s * chiC κ) (fun s => -sleLambda κ - θR s * chiC κ) c)
        (exSet (Lw ω) (Rw ω) SL SR c) G →
      ∀ z ∈ changePocket (Rw ω) (Lw ω) r, v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hX hLc hL0 hLm hLdet hLloc hRc hR0 hRm hRdet hRloc htr
  filter_upwards [ae_ownHeights hX hLc hL0 hLm hLdet hLloc hLim hRc hR0 hRm hRdet hRloc hRim htr hgU hgL hgR
      hsideL hsideR, ae_eqOn_changePocket hX hUm hUloc hgU hu₀ hu₀b (chiC κ)]
    with ω hown hmean v hv hgv r Ψ c ℓ n G hF hCl hℓ hlift hn htrL hWLc hWL0 htrR hWRc hWR0 hG
  obtain ⟨vL, vR, hownL, hownR⟩ := hown v hv hgv r Ψ c hF hCl htrL hWLc hWL0 htrR hWRc hWR0
  have hAeq : H \ wallUnion Lw Rw ω = H \ (range (Rw ω) ∪ range (Lw ω)) := by
    rw [H_diff_wallUnion, union_comm]
  exact hmean v hv hgv (Rw ω) (Lw ω) r Ψ c ℓ n (WL ω) (WR ω) vL vR _ _ SL SR G hAeq hF hℓ hlift hn htrL htrR hSL hSR
    hownL hownR hG

end Prob

/-! ### The two-angle heights of the strip walls -/

section TwoAngle

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

/-- The height `a − θ(s)χ` of a two-angle wall (angle `θ₀` before its change time `t₀`, `θ` after) is locally constant
off the change time. -/
theorem eventually_eq_twoAngle (a χ θ₀ θ : ℝ) (t₀ : ℝ≥0) {s : ℝ≥0} (hs : s ∉ ({t₀} : Set ℝ≥0)) :
    ∀ᶠ s' in 𝓝 s, a - (if s' < t₀ then θ₀ else θ) * χ = a - (if s < t₀ then θ₀ else θ) * χ := by
  have hne : s ≠ t₀ := fun h => hs (Set.mem_singleton_iff.2 h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [eventually_lt_nhds hlt] with s' hs'
    simp only [hs', hlt, ↓reduceIte]
  · filter_upwards [eventually_gt_nhds hgt] with s' hs'
    have h1 : ¬ s' < t₀ := not_lt.2 hs'.le
    have h2 : ¬ s < t₀ := not_lt.2 hgt.le
    simp only [h1, h2, ↓reduceIte]

/-- **The bounded Poisson extension of (PW13.1) for two two-angle walls exists** (and is unique on `ℍ`): the left
wall with angles `θL₀`, `θL` and change time `tL`, the right wall with `θR₀`, `θR`, `tR`. -/
theorem exists_isBoundedHarmonicExtension_twoAngle (hF : IsFlowChart R L r Ψ c) (κ θL₀ θL θR₀ θR : ℝ)
    (tL tR : ℝ≥0) :
    ∃ G : ℂ → ℝ, IsBoundedHarmonicExtension
      (chartData L R (fun s => sleLambda κ - (if s < tL then θL₀ else θL) * chiC κ)
        (fun s => -sleLambda κ - (if s < tR then θR₀ else θR) * chiC κ) c) (exSet L R {tL} {tR} c) G := by
  obtain ⟨G, hG, -⟩ := IsFlowChart.exists_isBoundedHarmonicExtension_chartData hF (Set.finite_singleton tL)
    (Set.finite_singleton tR) (fun s hs => eventually_eq_twoAngle _ _ _ _ tL hs)
    (fun s hs => eventually_eq_twoAngle _ _ _ _ tR hs)
  exact ⟨G, hG⟩

end TwoAngle

end InteractingSLE.Sec7.Aux119Heights
