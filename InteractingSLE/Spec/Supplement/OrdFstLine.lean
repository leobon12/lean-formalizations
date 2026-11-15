/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdFstSlit

/-!
# Leaf 3, the first continuation: the later-line facts (III-a) and (III-b) in the charts shifted to the first tip

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3, `RLC.RetOrdDetFstStatement`; supplement p. 497, Lemma G7 for the first
current tip; Aux. lemma 79, pp. 289–290).

The safe law (S) of K2 for a retained continuation is assembled from line facts (`RetAux79.hasSafeLaw_of_retLines`,
hypothesis `hline`). For the first continuation the K2 runs in the retained charts recentred at the first tip's chart
point (`(d.chart ω).recenter τ₀` at the stop line, `(d'.chart ω).recenter τ₁` at the later line `(u + t, r)`), with
the recentred words `shiftW τ β`. This file proves the line facts there, for every pair of mean-identified words, with
no named input:

* **`ae_retLine_facts_fst`**: almost surely, for every chart path `γ` of the first continuation from the seed `τ₀` and
  every chart point `τ₁` of the later first tip (injective first prefix, later first tip off the second prefix), if
  the later word has the SIDED outer word `IsRetainedWordFst` relative to `τ₁`, then
  (III-a) the later recentred chart is the stop-line recentred chart followed by `f_Q` (`retChart_trans_fst`), with the
  lift chain rule; and (III-b) the force data of the recentred stop-line word, flowed to `Q`, are the recentred later
  word plus `θ₁χ` off a finite set (Aux. lemma 79 in recentred charts, `ae_fn_eq_of_trans_shift`, on the old boundary;
  the slit heights `∓λ − θ₁χ` from `exists_slitSideFst_of_lt` and `slitHeightsFst_of_dense` on the new piece; the
  assembly `forceBoundaryData_eq_add_of_transport`).

The sided outer word at the later pair holds almost surely for every mean-identified word
(`ae_isRetainedWordFst_of_meanIdent`).

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Sec7 Sec7.Lemma76F Restart Restart.RetAux79 Supp7 MartChar.RealFlow

theorem add_notMem_jumps_of_notMem_shiftW {τ x : ℝ} {c : BoundaryWord}
    (hx : x ∉ (Exist.StagedLaw.BoundaryWord.shiftW τ c).jumps) : x + τ ∉ c.jumps := by
  intro h
  rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW] at hx
  exact hx (Finset.mem_image.2 ⟨x + τ, h, by ring⟩)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The later-line facts of the first continuation** (see the module docstring). -/
theorem ae_retLine_facts_fst (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) {t : ℝ≥0} (hu : d'.u = d.u + t) (hr : d'.r = d.r)
    {O₀ O₁ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' O₁ β₁) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → ω ∈ O₁ → (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.E → ω ∈ d'.E →
      (β₀ ω).IsSorted → (β₁ ω).IsSorted → InjOn (d.η₁ ω) (Icc 0 (d.u + t)) →
      d.η₁ ω (d.u + t) ∉ d.η₂ ω '' Icc 0 d.r →
      ∀ τ₀ τ₁ : ℝ, d'.inv ω τ₁ = d.η₁ ω (d.u + t) →
      IsRetainedWordFst κ θ₁ (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r (d'.inv ω) τ₁ (β₁ ω) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t) →
        d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t) →
        (∀ w ∈ H, ((d'.chart ω).recenter τ₁).2.1 w =
          ((d.chart ω).recenter τ₀).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, ((d'.chart ω).recenter τ₁).2.2 (((d'.chart ω).recenter τ₁).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter τ₀).2.2
              (((d.chart ω).recenter τ₀).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                  (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                  (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 j) Q - W Q) y =
            (Exist.StagedLaw.BoundaryWord.shiftW τ₁ (β₁ ω)).fn y + θ₁ * QuantumZipper.chiC κ := by
  have huu : d.u ≤ d'.u := by rw [hu]; exact le_self_add
  have hrr : d.r ≤ d'.r := hr.ge
  have htr := ae_fn_eq_of_trans_shift hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd hd' hag hag' huu hrr hm₀ hm₁
  filter_upwards [htr] with ω htrω
  intro hO₀ hO₁ hu₁ hr₁ hE hE' hs₀ hs₁ hi₁ hq₁ τ₀ τ₁ hτ₁ hfst W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hinv, hlift⟩ := retChart_trans_fst hd hd' h₁ h₂ hu hr hE hE' hg hWc hW0 hinj hQ hQ0 himg htip hτ₁ hi₁ hq₁
  refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
  · show (d'.chart ω).2.1 (w + τ₁) = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w + τ₀)
    rw [chart_inv_eq hE', chart_inv_eq hE]
    exact hinv w hw
  · show (d'.chart ω).2.2 ((d'.chart ω).2.1 (w + τ₁)) = _ +
      (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w + τ₀))
    rw [chart_inv_eq hE', chart_inv_eq hE, chart_lift_eq hE', chart_lift_eq hE]
    exact hlift w hw
  · have hw'c : Continuous fun s : ℝ => W s.toNNReal := hWc.comp continuous_real_toNNReal
    have hw'0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simp [hW0]
    have htr' : ∀ (x : ℝ) (v : ℝ → ℂ), QuantumZipper.IsForwardSol (fun s : ℝ => W s.toNNReal) (x : ℂ) Q v →
        x ∉ (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps →
        (v Q).re ∉ (Exist.StagedLaw.BoundaryWord.shiftW τ₁ (β₁ ω)).jumps →
        (Exist.StagedLaw.BoundaryWord.shiftW τ₁ (β₁ ω)).fn (v Q).re =
          (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn x := by
      intro x v hv hx hy
      rw [Exist.StagedLaw.BoundaryWord.fn_shiftW, Exist.StagedLaw.BoundaryWord.fn_shiftW]
      exact htrω hO₀ hO₁ hu₁ hr₁ hE hE' hs₀ hs₁ τ₀ τ₁ _ Q hw'c hw'0 Q.coe_nonneg hinv hlift x v hv
        (add_notMem_jumps_of_notMem_shiftW hx) (add_notMem_jumps_of_notMem_shiftW hy)
    obtain ⟨hL, hR⟩ := slitHeightsFst_of_dense hfst (ℓ := -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q)
      (ϱ := rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q) fun a' b' hab' hsub =>
        exists_slitSideFst_of_lt hd hd' hE hE' hg hWc hW0 hinj hQ himg htip hinv hab' hsub
    exact forceBoundaryData_eq_add_of_transport hκ θ₁ hWc htr'
      (Exist.StagedLaw.BoundaryWord.shiftW τ₁ (β₁ ω)).jumps.finite_toSet hL hR

end OrdDet

end RLC

end InteractingSLE
