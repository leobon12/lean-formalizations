/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS2
import InteractingSLE.Spec.Supplement.RelSafeGB6Read
import InteractingSLE.Spec.Supplement.BW1LinesSafe

/-!
# GB6's relative safe law, part 3: assembly from the line data

Packet PROVE-GB6-RELSAFE2. For one R-form version `(R, V)` of GB6's relative exploration and one word type `w`, this
file proves `Q3Stop.HasRelSafe` for the joint law of (record, relative variable) from the data of K2's lines step at
deterministic PHYSICAL times, in exactly the form of `BW1Lines.hasSafeLaw_life_of_lineKernel` /
`hasSafeMembers_life_of_lineLocal`:

* the physical filtration `𝓖 = RelSafe.physFilt` (record ∨ counterflow up to `t` ∨ null sets);
* the counterflow-frame field `h′ = R_*h`, read in the relative chart of the record `relChart (gb6Rec ω)` with the
  coefficients `1, 2πχ(16/κ), χ(16/κ)` (`RelSafeS2`: this is GB6's chart field `Hc` on the record event);
* the relative clock `a(t) = min(physClock t, V)` (`RelSafe`: continuous, monotone, adapted, reaches every level
  below `V`; the relative filtration traced on `{q ≤ a(t)}` is physical);
* the lifetime `V`, the relative driver `R`, the typed geometric marks;
* the threshold clause (`RelSafeS1.ae_canonStp_le_thr_gb6`) and the field congruence on the live event.

The remaining inputs of **`hasRelSafe_of_lines`** are the line data proper: the line kernels and means (`hker`,
`hmean`: Aux. 77/79 at the physical lines), the marked locality of the physical union (`hloc`, `hBK`, …), the
measurability of the safe events (`hSψ`, `hSb`) and the integrability of the chart field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.RelSafeS

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Restart Restart.DomainMarkov.K2
  Restart.FCDet Sec7.PocketTraversal

section Assembly

variable {κ θ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [hP : IsProbabilityMeasure P]
  {h h' Hc : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {s : ℝ≥0} {c : BoundaryWord} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {GT : Set Ω}

/-- The live event of the type `w`: the record lies in the record event and has type `w`. -/
def liveEv (κ θ : ℝ) (c : BoundaryWord) (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (w : WordType) : Set Ω :=
  gb6Rec s Wα ζα ⁻¹' (gb6TS s ∩ {r | wordType (16 / κ) (gb6WordOfRec κ θ c r) = w})

omit mΩ in
theorem liveEv_subset (w : WordType) :
    liveEv (Ω := Ω) κ θ c s Wα ζα w ⊆ gb6Rec s Wα ζα ⁻¹' gb6TS s := fun _ hω => hω.1

/-- The typed left marks read from the record. -/
abbrev typedL (κ θ : ℝ) (c : BoundaryWord) (w : WordType) (y : Q3Stop.CanonSpace) : Fin w.1 → ℝ :=
  typedXL (16 / κ) w (gb6WordOfRec κ θ c y.1)

/-- The typed right marks read from the record. -/
abbrev typedR (κ θ : ℝ) (c : BoundaryWord) (w : WordType) (y : Q3Stop.CanonSpace) : Fin w.2.1 → ℝ :=
  typedXR (16 / κ) w (gb6WordOfRec κ θ c y.1)

/-- **`HasRelSafe` for one R-form version and one word type from the line data at the physical lines.** -/
theorem hasRelSafe_of_lines (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hh'm : Measurable h') (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω))
    (E : Finset ℝ) (hcL : ∀ u, u < 0 → u ∉ E → u ∉ c.jumps → -bigLambda κ < -c.fn u + Real.pi * chiC κ)
    (hcR : ∀ u, 0 < u → u ∉ E → u ∉ c.jumps → -c.fn u - Real.pi * chiC κ < bigLambda κ)
    (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (hWm : ∀ r, Measurable (W r))
    (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) (w : WordType)
    -- the line data
    (𝒢L : ℝ≥0 → MeasurableSpace Ω)
    (h𝒢L : ∀ t, physFilt (measurable_recOf_cfE hfl s).2 hWm P t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
      min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      tsupport φ ⊆ (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h' ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((relChart (gb6Rec s Wα ζα ω)).2.1 '' (H \ fwdHull
            (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
      min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
        (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) →
      Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
          (chiC (16 / κ)) (M t ω) ψ =
        ∫ z, couplingMean (16 / κ) (fun r : ℝ => R r.toNNReal ω)
          (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal
          (DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (gb6Rec s Wα ζα ω, relVar Hc R V ω))
            (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (gb6Rec s Wα ζα ω, relVar Hc R V ω)) ω
            (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) z * ψ z)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, physFilt (measurable_recOf_cfE hfl s).2 hWm P t ≤ ℋ t)
    (hℋ : ∀ t, ℋ t ≤ mΩ) (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h' u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w → min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      H \ B t ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal))
    (hSψ : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[physFilt (measurable_recOf_cfE hfl s).2 hWm P t]
        {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω ∧ Disjoint (tsupport ψ)
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)})
    (hSb : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[physFilt (measurable_recOf_cfE hfl s).2 hWm P t]
        {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω ∧ Disjoint (Coupling.ballsK Fb)
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)})
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => Hc ω φ) P) :
    HasRelSafe (16 / κ) w (gb6WordOfRec κ θ c) (gb6TS s)
      (P.map fun ω => (gb6Rec s Wα ζα ω, relVar Hc R V ω)) := by
  have hrec : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hβ := measurable_gb6WordOfRec κ θ c
  have hE := measurableSet_gb6TS s
  have hRm := hver.1.1
  have hVm := hver.1.2.2.2.2.1
  have hRc := hver.1.2.1
  have hR0 := hver.1.2.2.1
  have hGTm' : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT := fun t =>
    measurableSet_goodSet_physFilt hrec hWm hGTm hGTae t
  set Φ : Ω → Q3Stop.CanonSpace := fun ω => (gb6Rec s Wα ζα ω, relVar Hc R V ω) with hΦdef
  have hΦ : Measurable Φ := hrec.prodMk (measurable_relVar hHcm hRm hVm)
  have hF : Φ ⁻¹' typeEvent (16 / κ) w (gb6WordOfRec κ θ c) (gb6TS s) = liveEv κ θ c s Wα ζα w := rfl
  have hF0 : MeasurableSet[physFilt hrec hWm P 0] (liveEv κ θ c s Wα ζα w) :=
    measurable_rec_physFilt hrec hWm 0 (hE.inter ((measurable_wordType (16 / κ)).comp hβ
      (measurableSet_singleton w)))
  have hWd : (fun t ω => canonDrv t (Φ ω)) = R := by
    funext t ω
    exact relDrv_relVar (hRc ω) (hR0 ω) t
  have hVd : (fun ω => canonStp (Φ ω)) = V := rfl
  -- the chart field is `Hc` on the live event
  have hX : ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
      Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h' ω) = canonFld (Φ ω) := by
    filter_upwards [ae_eq_chartTransport_relChart hκ hT hfl hα s hHc, ae_gb6RecGood hfl hα s] with ω hω hg hωF
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hωF.1
    exact (hω hs hsH).symm
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w → (q : ℝ≥0∞) < V ω →
      ∃ t, (q : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT t ω) (V ω) := fun q =>
    reach_min_physClock hGT hver.1 hGTae (Eventually.of_forall fun ω hω => hω.1) q
  have hreg : ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w → DomainMarkov.Aux79.IsForceReg R
      (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (Φ ω)) V ω := by
    refine Eventually.of_forall fun ω _ => ?_
    have h1 := isForceReg_thr (fun y => canonDrv_zero y) (fun y => continuous_canonDrv y) (typedL κ θ c w)
      (typedR κ θ c w) canonStp (Φ ω)
    rw [← hWd]
    exact h1
  have hdom : ∀ z, MeasurableSet[physFilt hrec hWm P 0]
      {ω | z ∈ (relChart (gb6Rec s Wα ζα ω)).dom} := fun z =>
    measurable_rec_physFilt hrec hWm 0 (measurableSet_mem_dom_relChart z)
  have hfwd : ∀ z, Measurable[physFilt hrec hWm P 0]
      ({ω | z ∈ (relChart (gb6Rec s Wα ζα ω)).dom}.indicator fun ω => (relChart (gb6Rec s Wα ζα ω)).1 z) :=
    fun z => (measurable_indicator_fwd_relChart z).comp (measurable_rec_physFilt hrec hWm 0)
  have hliftm : ∀ z, Measurable[physFilt hrec hWm P 0]
      ({ω | z ∈ (relChart (gb6Rec s Wα ζα ω)).dom}.indicator fun ω => (relChart (gb6Rec s Wα ζα ω)).2.2 z) :=
    fun z => (measurable_indicator_lift_relChart z).comp (measurable_rec_physFilt hrec hWm 0)
  have h𝓗' := fun q D (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) t =>
    measurableSet_inter_le_min_of_canonFilt hGT hrec hWm hGTm' hver hHcm q hD t
  -- (S)
  have hlaw : HasSafeLaw (16 / κ) (typedRhoL w) (typedRhoR w) P (Coupling.filtrationComap canonFilt hΦ)
      (liveEv κ θ c s Wα ζα w) V R (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (Φ ω))
      (fun ω => Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h' ω)) :=
    Theorem14.BW1Lines.hasSafeLaw_life_of_lineKernel hF0 (fun ω => isConformal_relChart (gb6Rec s Wα ζα ω))
      hdom hfwd hliftm (fun ω => continuousOn_lift_relChart (gb6Rec s Wα ζα ω)) hh'm
      (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ)) (continuous_min_physClock hGT) (monotone_min_physClock hGT)
      (min_physClock_zero hGT) (measurable_min_physClock hGT hrec hWm hGTm' hver) h𝓗' V hreach hreg hSψ 𝒢L h𝒢L
      h𝒢Lm M hker hmean
  -- (L)
  have hmem : HasSafeMembers P (Coupling.filtrationComap canonFilt hΦ) (liveEv κ θ c s Wα ζα w) V R
      (fun ω => Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h' ω)) :=
    Theorem14.BW1Lines.hasSafeMembers_life_of_lineLocal (VL := fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (Φ ω))
      (VR := fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (Φ ω)) hh'm hu₀ hh0
      (fun ω => isConformal_relChart (gb6Rec s Wα ζα ω)) hdom hfwd hliftm
      (fun ω => continuousOn_lift_relChart (gb6Rec s Wα ζα ω))
      (fun ω => harmonicOnNhd_lift_relChart (gb6Rec s Wα ζα ω)) (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ))
      (continuous_min_physClock hGT) (monotone_min_physClock hGT) (min_physClock_zero hGT)
      (measurable_min_physClock hGT hrec hWm hGTm' hver) h𝓗' V hreach hreg hSb ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK
  refine hasRelSafe_of_space hβ hE hrec hHcm hRm hVm ?_ ?_ hint
    (ae_canonStp_le_thr_gb6 hκ hκ4 hθ₁ hθ₂ c s E hcL hcR _ w)
  · rw [hF, hWd]
    exact hasSafeLaw_congr_fld hX hlaw
  · rw [hF, hWd]
    exact hasSafeMembers_congr_fld hX hmem

end Assembly

end InteractingSLE.Supp8.RelSafeS
