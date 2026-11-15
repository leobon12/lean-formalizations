/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgLines
import InteractingSLE.Spec.Supplement.RelSafeS6

/-!
# GW2's stage identity: K2's relative safe law from marked locality and the union mean (any record, any chart)

Packet PROVE-GW2-RELDET, ruling R106. `GW2Rd.hasRelSafe_of_lines_rec` takes the line KERNELS `hker` (the conditional
characteristic functionals at the physical lines) and their means `hmean`. As in stage `0`
(`GW2Rd.hasGW2LineData_of_local`, GB6's `hasGB6LineData_of_local`), the kernels follow from the history-marked
locality of the physical union alone (`RelSafeS.ae_condExp_cexp_marked`). Then only the identification of the
local-set MEAN of the union in the chart remains.

**`hasRelSafe_of_local_rec`** is `hasRelSafe_of_lines_rec` with `hker`, `hmean` (and the auxiliary marks `𝒢L`, the
mean `M`) replaced by `hmeanL`: for every local-set mean `g` of the union `B t` of the centred field `h − u₀`, the
chart transport of `g + u₀` is the canonical coupling mean on the live event below the stop, off the stage hull.
This is the form PROVE-GW2-STAGEMEAN targets. Conditional helper with a distinct name.
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
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal LocalSets

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k : ℝ} {w : WordType}
  {β : RecData → BoundaryWord} {E : Set RecData} {rec : Ω → RecData} {h Hr : Ω → DistOn upperHalfPlaneOpens}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {a : ℝ≥0 → Ω → ℝ≥0∞} {c : Ω → Chart}

/-- **`HasRelSafe` from the marked union locality and the union mean, for an arbitrary record and chart family**
(conditional helper: the mean identification, the clock properties, the threshold clause and the integrability are
hypotheses). -/
theorem hasRelSafe_of_local_rec (hβ : Measurable β) (hE : MeasurableSet E) (hrecm : Measurable rec)
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
    -- the marked union locality and the union mean
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ) (B : ℝ≥0 → Ω → Set ℂ)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t)) (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → a t ω < V ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal))
    (hmeanL : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (B t) (WholeField.centredField h u₀) P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E rec → a t ω < V ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal) →
        Chart.chartTransport (hc ω) 1 σa kc
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω) (a t ω).toNNReal
            (DomainMarkov.bheProc k (typedRhoL w) (typedRhoR w) R
              (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (rec ω, relVar Hr R V ω))
              (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (rec ω, relVar Hr R V ω)) ω
              (a t ω).toNNReal) z * ψ z)
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
  set h₀ := WholeField.centredField h u₀ with hh₀def
  have hl : ∀ t, IsLocalSet (B t) h₀ P := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2 (hloc t).isAvoidanceLocal
  have hg : ∀ t, ∃ g, IsLocalSetMean (B t) h₀ P g := fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hl t)
  choose g hgm using hg
  have hu₀c : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu₀ z hz).1.continuousAt.continuousWithinAt
  refine hasRelSafe_of_lines_rec hβ hE hrecm hhm hHrm hRm hRc hR0 hVm 𝓖 hrec hc hdom hfwd hliftm hliftc hlift σa kc
    hX hac ham ha0 haa h𝓗' hreach (fun t => germSigma (B t) h₀ ⊔ ℋ t)
    (fun t => (h𝓖ℋ t).trans le_sup_right) (fun t => sup_le (germSigma_le (hBm t) hh0.measurable) (hℋ t))
    (fun t ω => g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ?_
    (fun t ψ => hmeanL t (g t) (hgm t) ψ) hu₀ hh0 ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK hSψ hSb hint hthr
  intro t φ
  have h1 := ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hgm t) φ
  have hsplit : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h₀ ω φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add, hh₀def, WholeField.centredField_apply h hu₀ ω φ]
    congr 1
    push_cast
    ring
  have hcs : (fun ω => Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (h₀ ω φ : ℂ))) =
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) • fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) :=
    rfl
  have h2 : P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma (B t) h₀ ⊔ ℋ t] =ᵐ[P]
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) •
        P[fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) | germSigma (B t) h₀ ⊔ ℋ t] := by
    rw [hsplit, hcs]
    exact condExp_smul _ _ _
  filter_upwards [h2, h1, hBK t] with ω hω2 hω hBKω hωF hlt _
  rw [hω2, Pi.smul_apply, hω, ← hBKω hωF hlt, smul_eq_mul, add_apply,
    SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c φ, Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have e : (∫ x, φ x * u₀ x) = ∫ z, u₀ z * φ z := by
    congr 1
    funext z
    ring
  rw [e]
  push_cast
  ring

end Assembly

end InteractingSLE.Theorem14.GW2Rd
