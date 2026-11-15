/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbS

/-!
# K2's (L) for the retained continuation with the boundary stop: assembly

Packet PROVE-RETAUX79C (ruling R55). `Aux79.hasSafeMembers_of_lineLocal` (K2's input (L)) for the second continuation
of Lemma 7.6 with the source's lifetime, on a typed live event, with the line sets `B t = ℍ \ D_t` (`D_t` the joint
unbounded domain at the line `(u, r + t)`):

* `harmonicOnNhd_lift_chart`: the lift of a retained chart is harmonic on its domain (imaginary part of the canonical
  logarithmic derivative);
* `ae_retLine_inv`: (III-a) for the chart inverses at every line (from the driver's later-line facts);
* `retLineSet`, `retLineSet_spec`, **`ae_retLineSet_eq`** (`hBK`): `ℍ \ B t = c.inv(ℍ \ K̃_{C(t)})` almost surely on
  the live event before the lifetime;
* **`hasSafeMembers_ret_of_plumbing`**: `HasSafeMembers` for the chart field from the remaining probabilistic
  plumbing (the filtration and measurability inputs shared with (S), the line σ-algebras `ℋ t ≥ 𝓖 t`, the hitting
  measurability of the line sets and their history-avoidance locality).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv logDerivFwd fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Sec7 Sec7.Lemma76G MartChar.RealFlow DomainMarkov DomainMarkov.Aux79 K2

/-- **The lift of a retained chart is harmonic on the chart domain.** -/
theorem harmonicOnNhd_lift_chart {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (d.chart ω).2.2 (d.chart ω).dom := by
  rw [hd.coe_dom_chart ω]
  by_cases hω : ω ∈ d.E
  · rw [RetData.chart_of_mem hω]
    have hdiff := (isCanonicalDerivLog_canonDerivLog (hd.isHPHull ω)).1.1
    intro z hz
    have hn : H \ fillH (d.K ω) ∈ 𝓝 z := (hd.isOpen_D ω).mem_nhds hz
    exact (hdiff.analyticAt hn).harmonicAt_im
  · rw [RetData.chart_of_notMem hω]
    exact InnerProductSpace.harmonicOnNhd_const (0 : ℝ)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0}
  {c₀ : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ}
  {xR : Ω → Fin nR → ℝ} {F : Set Ω}

/-- **(III-a) for the chart inverses at every line**, almost surely on the live event before the lifetime. -/
theorem ae_retLine_inv (hκ : 0 < κ) (hκ4 : κ < 4) (hx : x₂ < x₁)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      ∀ w ∈ H, ((retFam G η₁' η₂' u (r + t)).chart ω).2.1 w = ((retFam G η₁' η₂' u r).chart ω).2.1
        (fwdMapInv (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω) w) := by
  filter_upwards [hG (r + t), ha₁, ha₂, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hGt e₁ e₂ hp₁ hp₂ hωF hlt
  obtain ⟨hpair, hGr⟩ := hF ω hωF
  have hp₁' : IsPathGood (η₁' ω) (ζ₁ ω) x₁ := Supp7.IsPathGood.congr hp₁ e₁
  have hp₂' : IsPathGood (η₂' ω) (ζ₂ ω) x₂ := Supp7.IsPathGood.congr hp₂ e₂
  have hWc : Continuous fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω :=
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ ω).comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω) 0 = 0 := by
    show retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero]; exact retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ ω
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
  · subst h0
    intro w hw
    rw [retClock_zero, NNReal.coe_zero, fwdMapInv_zero_time hWc hW0 hw, add_zero]
  · have hdrv := isRetDriver_retDriver (exists_isRetDriver hd hGr hp₁' hp₂' hx hpair hc₀ hκ θ₂
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ))
    obtain ⟨-, -, -, hfacts⟩ := hdrv
    have htL := lt_retLifeP_of_retClock_lt (hd r) hGr hp₂' hpair hlt
    have hrt : ((r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := (coe_add_lt_iff.1 htL).trans_le contStop_le
    obtain ⟨-, -, hinv, -⟩ := hfacts t hpos htL (hGt hpair.1 hrt)
    rw [retClock_eq (hd r) hGr hp₂' hpair t]
    exact hinv

/-- **The line set**: the complement in `ℍ` of the joint unbounded domain at the line `(u, r + t)`. -/
def retLineSet (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (u r : ℝ≥0) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  H \ (retFam G η₁' η₂' u (r + t)).D ω

theorem retLineSet_spec (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood) (t : ℝ≥0) (ω : Ω) :
    retLineSet G η₁' η₂' u r t ω ⊆ H ∧ IsOpen (H \ retLineSet G η₁' η₂' u r t ω) := by
  have hDH : (retFam G η₁' η₂' u (r + t)).D ω ⊆ H := fun z hz => hz.1
  refine ⟨sdiff_subset, ?_⟩
  unfold retLineSet
  rw [sdiff_sdiff_cancel_left hDH]
  exact (hd (r + t)).isOpen_D ω

/-- **`hBK`**: almost surely on the live event before the lifetime, the line domain `ℍ \ B t` is the stop-line image of
`ℍ \ K̃_{C(t)}`. -/
theorem ae_retLineSet_eq (hκ : 0 < κ) (hκ4 : κ < 4) (hx : x₂ < x₁)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      H \ retLineSet G η₁' η₂' u r t ω = ((retFam G η₁' η₂' u r).chart ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω)) := by
  filter_upwards [ae_retLine_inv (θ₁ := θ₁) hκ hκ4 hx hη₁ hη₂ ha₁ ha₂ hd hG hc₀ hF t] with ω hinv hωF hlt
  have hWc : Continuous fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω :=
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ ω).comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω) 0 = 0 := by
    show retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero]; exact retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ ω
  have hDH : (retFam G η₁' η₂' u (r + t)).D ω ⊆ H := fun z hz => hz.1
  unfold retLineSet
  rw [sdiff_sdiff_cancel_left hDH, ← (hd (r + t)).coe_dom_chart ω, ((hd (r + t)).isConformal_chart ω).coe_dom,
    image_congr (hinv hωF hlt), ← image_image,
    QuantumZipper.RS.image_fwdMapInv_H hWc hW0 (retClock G η₁' η₂' ζ₂ u r t ω).coe_nonneg]

/-- **K2's (L) for the retained continuation with the boundary stop**, on a typed live event, from the probabilistic
plumbing: the physical filtration `𝓖` with the clock adapted, `𝓖 0`-measurability of the stop-line chart, `𝓖 t`-
measurability of the line-safe events of rational balls, line σ-algebras `ℋ t ≥ 𝓖 t`, the hitting measurability of the
line sets and their history-avoidance locality. The line-set identity `hBK`, the harmonic lift, the reach of the clock,
the regularity and the normalizations are proved. -/
theorem hasSafeMembers_ret_of_plumbing (hκ : 0 < κ) (hκ4 : κ < 4) (hx : x₂ < x₁)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    {𝓖 : Filtration ℝ≥0 mΩ}
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z))
    (hQa : ∀ t, Measurable[𝓖 t] (retClock G η₁' η₂' ζ₂ u r t))
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t] (lineSafe (retClock G η₁' η₂' ζ₂ u r)
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (retLife G η₁' η₂' ζ₂ u r) (Coupling.ballsK Fb) t))
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (retLineSet G η₁' η₂' u r t))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (retLineSet G η₁' η₂' u r t)
      (WholeField.centredField h u₀) P) :
    HasSafeMembers P (timeChange 𝓖 (retClock G η₁' η₂' ζ₂ u r) hQa) F (retLife G η₁' η₂' ζ₂ u r)
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1 (θ₂ * QuantumZipper.chiC κ)
        (QuantumZipper.chiC κ) (h ω) :=
  hasSafeMembers_of_lineLocal
    (VL := PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) fun _ => (Fin.elim0 : Fin 0 → ℝ))
    (VR := PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) fun _ => (Fin.elim0 : Fin 0 → ℝ)) hh.1 hu₀.1
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) (fun ω => (hd r).isConformal_chart ω) hdom
    hfwd hliftm (fun ω => (hd r).continuousOn_lift_chart ω) (fun ω => harmonicOnNhd_lift_chart (hd r) ω)
    (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ)
    (continuous_retClock G η₁' η₂' ζ₂ u r) (monotone_retClock G η₁' η₂' ζ₂ u r) (retClock_zero G η₁' η₂' ζ₂ u r)
    hQa (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) (ae_retReach hκ hκ4 hη₂ ha₂ (hd r) hF)
    (Eventually.of_forall fun ω _ => isForceReg_ret G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (fun _ => Fin.elim0)
      (fun _ => Fin.elim0) ω) hS ℋ h𝓖ℋ hℋ
    (retLineSet G η₁' η₂' u r) hBm (fun t ω => retLineSet_spec hd t ω) hloc
    (ae_retLineSet_eq hκ hκ4 hx hη₁ hη₂ ha₁ ha₂ hd hG hc₀ hF)

end Restart.RetAux79

end InteractingSLE
