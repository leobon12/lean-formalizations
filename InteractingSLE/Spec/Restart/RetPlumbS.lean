/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Restart.RetAux79Line

/-!
# K2's (S) for the retained continuation with the boundary stop: assembly

Packet PROVE-RETAUX79C (ruling R55). `RetAux79.hasSafeLaw_of_retLines` (K2's input (S), from the line kernels and the
per-line facts) for the second continuation of Lemma 7.6 with the source's lifetime, on a typed live event `F` (fixed
force-word type of the stop-line word; `F` inside the disjoint-pair event at `(u, r)` and the good event):

* the processes are those of `RetPlumbFam`/`RetPlumbLine`: the clock `retClock`, the lifetime `retLife`, the driver
  `retDrv` with the geometric force coordinates `geomLW`, `geomRW` of the typed marks `xL`, `xR`, the stop-line chart
  `(retFam … r).chart`, the line charts `(retFam … (r + t)).chart`, the line words `retWordAt … (r + t)` and the line
  means `g t + 𝔥₀`;
* **proved here**: `ae_retLine` (`hline` at every line), `hreach` (`ae_retReach`), `hreg` (`isForceReg_ret`), the
  continuity and normalization of the clock and the driver;
* **`hasSafeLaw_ret_of_plumbing`**: `HasSafeLaw` for the chart field `chartTransport (stop-line chart) 1 (θ₂χ) χ h`,
  with the time-changed filtration `Aux79.timeChange 𝓖 retClock`, from the remaining **probabilistic plumbing**, kept as
  hypotheses: the physical filtration `𝓖` with the clock adapted (`hQa`), the live event and the stop-line chart
  `𝓖 0`-measurable (`hF`, `hdom`, `hfwd`, `hliftm`), the line-safe events `𝓖 t`-measurable (`hS`), and the line kernels
  (`hker`, Aux. 77 at the lines `(u, r + t)` for σ-algebras `𝒢L t ≥ 𝓖 t` with means `g t + 𝔥₀`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv logDerivFwd fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Sec7 Sec7.Lemma76G MartChar.RealFlow DomainMarkov DomainMarkov.Aux79 K2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0}
  {c₀ : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ}
  {xR : Ω → Fin nR → ℝ} {F : Set Ω}

/-- **`hline` at every line** (the trivial line `t = 0` and the positive lines). -/
theorem ae_retLine (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂ (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (Lemma76F.capR u (r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (Lemma76F.capR u (r + t)) (ζ₂ ω) s))
    (hg : ∀ t, LocalSets.IsLocalSetMean (Lemma76F.cstUnion (ηc₁ t) (ηc₂ t) u (r + t))
      (WholeField.centredField h u₀) P (g t)) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hd (r + t)).isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
          (g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G η₁' η₂' u (r + t)).chart ω).2.1 w = ((retFam G η₁' η₂' u r).chart ω).2.1
        (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω) w)) ∧
      (∀ w ∈ H, ((retFam G η₁' η₂' u (r + t)).chart ω).2.2 (((retFam G η₁' η₂' u (r + t)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω)
          (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
            (retClock G η₁' η₂' ζ₂ u r t ω) w)).im +
          ((retFam G η₁' η₂' u r).chart ω).2.2 (((retFam G η₁' η₂' u r).chart ω).2.1
            (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
              (retClock G η₁' η₂' ζ₂ u r t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL i
              (retClock G η₁' η₂' ζ₂ u r t ω) ω -
            retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (retClock G η₁' η₂' ζ₂ u r t ω) ω)
          (fun j => PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR j
              (retClock G η₁' η₂' ζ₂ u r t ω) ω -
            retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (retClock G η₁' η₂' ζ₂ u r t ω) ω) y =
          (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  intro t
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
  · subst h0
    exact ae_retLine_zero hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG hu₀ hc₀ hc₀J hc₀b hF htype (ηc₁ 0) (ηc₂ 0)
      (g 0) (hc₁ 0) (hc₂ 0) (hm₁ 0) (hm₂ 0) (hag₁ 0) (hag₂ 0) (hg 0)
  · exact ae_retLine_pos hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG hu₀ hc₀ hc₀J hc₀b hF htype hpos (ηc₁ t)
      (ηc₂ t) (g t) (hc₁ t) (hc₂ t) (hm₁ t) (hm₂ t) (hag₁ t) (hag₂ t) (hg t)

/-- **`hreach`**: almost surely on the live event, every capacity before the lifetime is reached by the clock. -/
theorem ae_retReach (hκ : 0 < κ) (hκ4 : κ < 4) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω → ∃ t, q ≤ retClock G η₁' η₂' ζ₂ u r t ω := by
  filter_upwards [ha₂, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω e₂ hp₂ hωF hq
  obtain ⟨hpair, hGr⟩ := hF ω hωF
  exact exists_retClock_ge hd hGr (Supp7.IsPathGood.congr hp₂ e₂) hpair hq

/-- **`hreg`**: the geometric force coordinates of the driver are regular, for every `ω`. -/
theorem isForceReg_ret (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0)
    (κ θ₁ θ₂ : ℝ) (c₀ : BoundaryWord) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    IsForceReg (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL)
      (PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR) (retLife G η₁' η₂' ζ₂ u r) ω :=
  FCDet.isForceReg_thr (retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL xR _ ω

/-- **K2's (S) for the retained continuation with the boundary stop**, on a typed live event, from the probabilistic
plumbing (the physical filtration `𝓖` with the clock adapted, `𝓖 0`-measurability of the live event and of the
stop-line chart, `𝓖 t`-measurability of the line-safe events, and the line kernels with means `g t + 𝔥₀`). The
per-line facts, the reach of the clock, the regularity of the force coordinates and the normalizations are proved. -/
theorem hasSafeLaw_ret_of_plumbing (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂ (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (Lemma76F.capR u (r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (Lemma76F.capR u (r + t)) (ζ₂ ω) s))
    (hg : ∀ t, LocalSets.IsLocalSetMean (Lemma76F.cstUnion (ηc₁ t) (ηc₂ t) u (r + t))
      (WholeField.centredField h u₀) P (g t))
    {𝓖 : Filtration ℝ≥0 mΩ} (hFm : MeasurableSet[𝓖 0] F)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z))
    (hQa : ∀ t, Measurable[𝓖 t] (retClock G η₁' η₂' ζ₂ u r t))
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (lineSafe (retClock G η₁' η₂' ζ₂ u r)
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (retLife G η₁' η₂' ζ₂ u r) (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      tsupport φ ⊆ ((retFam G η₁' η₂' u r).chart ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * ((g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
            φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (((retFam G η₁' η₂' u r).chart ω).2.1 ''
            (H \ fwdHull (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
              (retClock G η₁' η₂' ζ₂ u r t ω))) φ φ : ℝ) : ℂ))) :
    HasSafeLaw κ ρL ρR P (timeChange 𝓖 (retClock G η₁' η₂' ζ₂ u r) hQa) F (retLife G η₁' η₂' ζ₂ u r)
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL)
      (PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1 (θ₂ * QuantumZipper.chiC κ)
        (QuantumZipper.chiC κ) (h ω) :=
  hasSafeLaw_of_retLines hFm (fun ω => (hd r).isConformal_chart ω) hdom hfwd hliftm
    (fun ω => (hd r).continuousOn_lift_chart ω) hh.1 (θ₂ * QuantumZipper.chiC κ)
    (continuous_retClock G η₁' η₂' ζ₂ u r) (monotone_retClock G η₁' η₂' ζ₂ u r) (retClock_zero G η₁' η₂' ζ₂ u r)
    hQa (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) (ae_retReach hκ hκ4 hη₂ ha₂ (hd r) hF)
    (Eventually.of_forall fun ω _ => isForceReg_ret G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ xL xR ω) hS 𝒢L h𝒢L h𝒢Lm
    (fun t ω => g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) hker
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
    (fun t ω => (hd (r + t)).isConformal_chart ω) (fun t ω => retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω)
    (ae_retLine hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG hu₀ hc₀ hc₀J hc₀b hF htype ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂
      hag₁ hag₂ hg)

end Restart.RetAux79

end InteractingSLE
