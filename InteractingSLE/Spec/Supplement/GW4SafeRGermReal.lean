/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRGermRefs
import InteractingSLE.Spec.Sec7.PocketSideInRealLanding

/-!
# GW4: exact heights at surviving real connectors

A surviving real characteristic supplies its own trace-free half-disc.
Local-set boundary decay and the canonical hydrodynamic lift preserve the
initial boundary height there. No reference increment law, incoming height
limit, inverse landing or lift-discrepancy premise is added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMapInv logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw LocalSets WholeField MartChar
  Sec7.PocketStopSide Sec7.Aux119Heights

/-- A surviving real characteristic has an incident half-disc avoiding any
set whose active complement is the actual finite Loewner domain. -/
theorem exists_free_halfDisc_of_surviving_real {W : ℝ → ℝ} (hW : Continuous W)
    {T x : ℝ} (hT : 0 ≤ T) {a : ℝ → ℂ}
    (ha : QuantumZipper.IsForwardSol W x T a) {B : Set ℂ}
    (hB : H \ B = H \ fwdHull W T) :
    ∃ r > 0, Disjoint (H ∩ ball (x : ℂ) r) B := by
  have hAlive := ZhanGT4.eventually_not_mem_fwdHull hW hT ha
  rw [← hB] at hAlive
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.1 hAlive
  exact ⟨r, hr, disjoint_left.2 fun z hz hzB => (hball ⟨hz.2, hz.1⟩).2 hzB⟩

/-- Every surviving original-real access has its exact initial height in
the actual random component line chart. This holds simultaneously in all
real characteristics for each mean version; no finite-access assumption is
used. Selecting which accesses are connectors remains a geometric task. -/
theorem ae_component_real_germs {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (B t) (centredField X u₀) ν g) :
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      let q := (lineClock F Wd GT V t ω).toNNReal
      ∀ x : ℝ, x ∉ c₀.jumps → ∀ a : ℝ → ℂ,
        QuantumZipper.IsForwardSol (wpath R ω) x q a →
        Tendsto (fun y => harmRep (g ω) (H \ B t ω) (fwdMapInv (wpath R ω) q y) +
            u₀ (fwdMapInv (wpath R ω) q y) +
            chiC k * (logDerivFwd (wpath R ω) q (fwdMapInv (wpath R ω) q y)).im)
          (𝓝[H] ((a q).re : ℂ)) (𝓝 (c₀.fn x)) := by
  obtain ⟨hu₀, -, -, hBm, hBc, hBloc, hShape⟩ := hloc
  have hZero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hu₀
  have hLocal : IsLocalSet (B t) (centredField X u₀) ν :=
    ((isLocalSet_tfae hZero (hBm t) (Eventually.of_forall (hBc t))).out 1 4).1
      (hBloc t).isAvoidanceLocal
  filter_upwards [ae_incident_zero_germ_of_local_increment hZero (hBm t) hLocal hg,
    hg.2.1, hShape t] with ω hGerm hH hS hlt
  dsimp only
  intro x hx a ha
  let q := (lineClock F Wd GT V t ω).toNNReal
  have hW : Continuous (wpath R ω) := (hRc ω).comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by
    simpa only [wpath, Real.toNNReal_zero] using hR0 ω
  obtain ⟨hv, hrep⟩ := harmRep_spec hH
  have hInv := tendsto_inverse_of_surviving_real hW hW0 q.coe_nonneg ha
  have hFree := exists_free_halfDisc_of_surviving_real hW q.coe_nonneg ha (hS hlt)
  have hPhysical := hGerm _ hv hrep (a q).re x _ hInv hFree
  have hInitial : Tendsto (sideMean k Chart.id u₀ (fun _ => 0))
      (𝓝[H] (x : ℂ)) (𝓝 (c₀.fn x)) := by
    change Tendsto (fun z => 0 + u₀ z + chiC k * 0) _ _
    simpa only [zero_add, mul_zero, add_zero] using hu₀.2.2 x hx
  have hTransport := tendsto_exact_height_at_surviving_real Chart.isConformal_id
    hW hW0 q.coe_nonneg ha hInitial
    (by simpa only [Chart.loewner, Chart.id, sub_zero] using hPhysical)
  change Tendsto (fun y => harmRep (g ω) (H \ B t ω) (fwdMapInv (wpath R ω) q y) +
    u₀ (fwdMapInv (wpath R ω) q y) + chiC k *
      ((logDerivFwd (wpath R ω) q (fwdMapInv (wpath R ω) q y)).im + 0)) _ _ at hTransport
  simpa only [add_zero] using hTransport

end InteractingSLE.Theorem14.GW4Fix
