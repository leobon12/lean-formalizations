/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeLines

/-!
# GW2's stage identity: K2's relative safe law from line data, for an arbitrary record and chart

Packet PROVE-GW2-RELDET, ruling R106 (the stage identity for all stages, GB6's engine rerun stage by stage). At a
later stage the relative variable is read in a STAGE chart (the joint chart followed by the relative maps of the
earlier stages) and conditioned on a STAGE record (the counterflow record together with the earlier stages). Neither
is GB6's `relChart (gb6Rec s W ζ)`, so `GW2Rd.hasRelSafe_of_lines_gw2` (stage `0`) does not apply verbatim.

**`hasRelSafe_of_lines_rec`**: `HasRelSafe k w β E` for the joint law of an ARBITRARY measurable record `rec` and the
relative variable `(Hr, R, V)`, from

* an arbitrary chart family `c` (conformal, with dom/forward/lift readable at time `0` of the physical filtration `𝓖`),
  whose transport of the field `h` is the relative field `Hr` on the live event;
* an arbitrary clock `a` (continuous, monotone, `a 0 = 0`, adapted to `𝓖`, compatible with the canonical
  filtration, reaching every level below `V`);
* line data at the physical times (the kernels `hker`, the chart mean `hmean`, the marked locality `hloc` of the
  physical sets `B t` and their shape `hBK`, the safe events `hS`, `hSb`), the threshold clause and integrability.

This is GB6's `hasRelSafe_of_lines` (and stage `0`'s `hasRelSafe_of_lines_gw2`) with GB6's clock layer and the
counterflow record abstracted: the generic engines `BW1Lines.hasSafeLaw_life_of_lineKernel` and
`BW1Lines.hasSafeMembers_life_of_lineLocal`, then `hasRelSafe_of_space_cond`. Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k : ℝ} {w : WordType}
  {β : RecData → BoundaryWord} {E : Set RecData} {rec : Ω → RecData} {h Hr : Ω → DistOn upperHalfPlaneOpens}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {a : ℝ≥0 → Ω → ℝ≥0∞} {c : Ω → Chart}

/-- The live event of a word type for a record: the record lies in `E` and its word has type `w`. -/
abbrev liveEvRec (k : ℝ) (w : WordType) (β : RecData → BoundaryWord) (E : Set RecData) (rec : Ω → RecData) :
    Set Ω :=
  rec ⁻¹' (E ∩ {r | wordType k (β r) = w})

/-- **`HasRelSafe` from line data, for an arbitrary measurable record and chart family** (GB6's `hasRelSafe_of_lines`
with the record, the chart and the clock abstracted; conditional helper: the line data, the clock properties, the
threshold clause and the integrability are hypotheses). -/
theorem hasRelSafe_of_lines_rec (hβ : Measurable β) (hE : MeasurableSet E) (hrecm : Measurable rec)
    (hhm : Measurable h) (hHrm : Measurable Hr) (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) (hVm : Measurable V) (𝓖 : Filtration ℝ≥0 mΩ) (hrec : Measurable[𝓖 0] rec)
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (σa kc : ℝ)
    (hX : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → Chart.chartTransport (hc ω) 1 σa kc (h ω) = Hr ω)
    -- the clock
    (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω) (ha0 : ∀ ω, a 0 ω = 0)
    (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[Coupling.filtrationComap canonFilt (hrecm.prodMk (measurable_relVar hHrm hRm hVm)) q]
      D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    -- the line data
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → a t ω < V ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull
            (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → a t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa kc (M t ω) ψ =
        ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal
          (DomainMarkov.bheProc k (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (rec ω, relVar Hr R V ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (rec ω, relVar Hr R V ω)) ω
            (a t ω).toNNReal) z * ψ z)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ) (B : ℝ≥0 → Ω → Set ℂ)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t)) (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → a t ω < V ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal))
    (hSψ : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal)})
    (hSb : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint (Coupling.ballsK Fb) (fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal)})
    -- the threshold and integrability clauses
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
      ((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent k w β E]))
    (hthr : ∀ᵐ y ∂((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent k w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL k w (β y.1))
        (fun y => typedXR k w (β y.1)) y) :
    HasRelSafe k w β E (P.map fun ω => (rec ω, relVar Hr R V ω)) := by
  set Φ : Ω → Supp8.Q3Stop.CanonSpace := fun ω => (rec ω, relVar Hr R V ω) with hΦdef
  have hΦ : Measurable Φ := hrecm.prodMk (measurable_relVar hHrm hRm hVm)
  have hF : Φ ⁻¹' typeEvent k w β E = liveEvRec k w β E rec := rfl
  have hF0 : MeasurableSet[𝓖 0] (liveEvRec k w β E rec) :=
    hrec (hE.inter ((measurable_wordType k).comp hβ (measurableSet_singleton w)))
  have hWd : (fun t ω => canonDrv t (Φ ω)) = R := by
    funext t ω
    exact relDrv_relVar (hRc ω) (hR0 ω) t
  have hreg : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → DomainMarkov.Aux79.IsForceReg R
      (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (Φ ω)) V ω := by
    refine Eventually.of_forall fun ω _ => ?_
    have h1 := isForceReg_thr (fun y => canonDrv_zero y) (fun y => continuous_canonDrv y)
      (fun y => typedXL k w (β y.1)) (fun y => typedXR k w (β y.1)) canonStp (Φ ω)
    rw [← hWd]
    exact h1
  -- (S)
  have hlaw : HasSafeLaw k (typedRhoL w) (typedRhoR w) P (Coupling.filtrationComap canonFilt hΦ)
      (liveEvRec k w β E rec) V R (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (Φ ω))
      (fun ω => Chart.chartTransport (hc ω) 1 σa kc (h ω)) :=
    Theorem14.BW1Lines.hasSafeLaw_life_of_lineKernel hF0 hc hdom hfwd hliftm hliftc hhm σa kc hac ham ha0 haa
      h𝓗' V hreach hreg hSψ 𝒢L h𝒢L h𝒢Lm M hker hmean
  -- (L)
  have hmem : HasSafeMembers P (Coupling.filtrationComap canonFilt hΦ) (liveEvRec k w β E rec) V R
      (fun ω => Chart.chartTransport (hc ω) 1 σa kc (h ω)) :=
    Theorem14.BW1Lines.hasSafeMembers_life_of_lineLocal
      (VL := fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (Φ ω))
      (VR := fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (Φ ω)) hhm hu₀ hh0 hc hdom hfwd
      hliftm hliftc hlift σa kc hac ham ha0 haa h𝓗' V hreach hreg hSb ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK
  refine hasRelSafe_of_space_cond hβ hE hrecm hHrm hRm hVm ?_ ?_ hint hthr
  · rw [hF, hWd]
    exact hasSafeLaw_congr_fld hX hlaw
  · rw [hF, hWd]
    exact hasSafeMembers_congr_fld hX hmem

end Assembly

end InteractingSLE.Theorem14.GW2Rd
