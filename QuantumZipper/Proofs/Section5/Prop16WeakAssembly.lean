import QuantumZipper.Proofs.Section5.Prop16Assembly
import QuantumZipper.Proofs.Section5.Prop16WeakArea

/-!
# Proposition 1.6, top-level assembly with the weak D4 node (D4⁺ʷ, decision D24)

Decision D24 (`DECISIONS.md`) replaces the node `Prop16Asm.Prop16TVStmt` (TV-local convergence of
the canonical zoomed field itself, very likely false for a merely continuous `𝔥₀`, and in any
case not what the paper proves) by `Prop16TVWeakStmt` (D4⁺ʷ): there are fields `Z C` whose local
coordinates converge in total variation to those of a `γ`-quantum wedge, and the area pairings of
the canonical zoomed field are close **in probability** to the local area pairings
`locArea γ R f (Z C)` of `Z C`.

This matches the paper's argument (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25: the
continuous part is "approximately constant" near `x`; the conclusion is weak convergence). The
intended witness is `Z C = canonicalOn` of the zoomed field **without** the continuous remainder
`𝔥₀(x + ·) − 𝔥₀(x)` (TV-local by D3⁺(i)); the remainder changes the area measure by a density
`e^{γφ}` with `φ → 0` and the canonical scale by a factor `→ 1`, both small in probability.

`theorem1_6_of_nodes'` proves `theorem1_6` from `Prop16NuMeasStmt`, `Prop16ZoomAreaStmt`,
`Prop16CanonAreaStmt` and `Prop16TVWeakStmt` through D4-a′
(`Prop16Area.areaConvergesInLawOn_of_tvLocal_close`). The scale node `Prop16ScaleStmt` is not
needed here (it was only used for the goodness-in-probability input of D4-a; it remains an input
of the proof of D4⁺ʷ). `theorem1_6` is not modified.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-- **Node D4⁺ʷ (weak TV-local form of Proposition 1.6, decision D24).** There are a `γ`-quantum
wedge `W` and fields `Z C` on the weighted space such that the local coordinates of `Z C`
converge in total variation to those of `W`, and for every test function `f` supported in
`ball 0 R` the area pairing of the canonical zoomed field is within any `δ > 0` of
`locArea γ R f (Z C)` with probability tending to `1`. -/
def Prop16TVWeakStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ W P' ∧
      ∃ Z : ℝ → Ω × ℝ → FieldSample,
        (∀ C, AEMeasurable (fun p => coords (Z C p)) (prop16Q γ h0 a b P X)) ∧
        (∀ R : ℕ, Tendsto (fun C => tvDist ((prop16Q γ h0 a b P X).map fun p =>
          locField R (Z C p)) (P'.map fun ω => locField R (W ω))) atTop (𝓝 0)) ∧
        ∀ (R : ℕ) (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
          (∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) → ∀ δ > 0,
          Tendsto (fun C => prop16Q γ h0 a b P X {p | δ <
            |∫ z, f z ∂(qAreaMeasureOn γ
                (canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))
                (canonicalDomainOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))) -
              Prop16Area.locArea γ R f (Z C p)|}) atTop (𝓝 0)

/-- **Proposition 1.6 from its nodes, with the weak D4 node (D24).** -/
theorem theorem1_6_of_nodes' (hMeas : Prop16NuMeasStmt) (hZoom : Prop16ZoomAreaStmt)
    (hCanon : Prop16CanonAreaStmt) (hTVw : Prop16TVWeakStmt) : theorem1_6 := by
  intro γ hγ hγ2 D c d a b hDo hDc hDb hDH hcd hfr hhd hab hca hbd h0 hh0 Ω _ P hP X hX
    hpos hfin
  have hdat : Prop16Data γ D c d a b h0 P X :=
    ⟨hγ, hγ2, ⟨hDo, hDc, hDb, hDH, hcd, hfr, hhd⟩, hab, hca, hbd, hh0, hP, hX, hpos, hfin⟩
  have hν := hMeas γ D c d a b h0 P X hdat
  have hQ : IsProbabilityMeasure (prop16Q γ h0 a b P X) :=
    isProbabilityMeasure_prop16Law hν hpos hfin
  obtain ⟨Ω', _, P', W, hP', hW, Z, hZ, hTV, hclose⟩ := hTVw γ D c d a b h0 P X hdat
  exact ⟨Ω', _, P', W, hP', hW,
    Prop16Area.areaConvergesInLawOn_of_tvLocal_close γ (prop16Q γ h0 a b P X) _ _ Z P' W hZ
      (wedge_coords_aemeasurable hγ hγ2 hW) hTV hclose (wedge_ae_exists_vague hγ hγ2 hW)
      (Eventually.of_forall fun C f hf hfc =>
        Prop16Area.Meas.aemeasurable_integral_prop16Y γ C h0 hDo hDH hX.measurable_coord
          (Prop16Area.Meas.nullMeasurableSet_of_ae (hZoom γ D c d a b h0 P X hdat C))
          (Prop16Area.Meas.nullMeasurableSet_of_ae (hCanon γ D c d a b h0 P X hdat C)) hf hfc)⟩

end Prop16Asm

end QuantumZipper
