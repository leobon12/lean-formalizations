/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FinGeom
import InteractingSLE.Spec.Sec7.SideLCGerm

/-!
# R.6's current-face geometry: the generic conjuncts, and the core inputs

PROVE-R6-CERT2. Several conjuncts of `R6Geom` hold for every pair of live current charts of driven traversals in
conformal pocket charts, with no geometry: the current domains are the complements of the active complements, the
charts are conformal, a physical landing of the outer chart at a real point lies off the outer domain (hence in the
outer set or on `ℝ`, and off the inner domain), and the outer set is inside the inner one once the inner domain is
inside the outer one. This file proves them and reduces the three named geometry inputs to their **core**:

* `landing_notMem_dom`, `localLanding_of_core`, def `R6GeomCore`, **`r6Geom_of_core`** (deterministic);
* `relChart_pocket_facts` (the live current chart of a driven traversal in a pocket chart);
* the named, unproved core inputs `R6GeomCoreMixedRemaining`, `R6GeomCoreMixedInfRemaining`,
  `R6GeomCoreMixedInfInfRemaining`, and **`r6GeomMixedRemaining_of_core`**, `…Inf…`, `…InfInf…`.

`R6GeomCore` keeps exactly the geometric content: inclusion of the two current domains, the transition reflecting
across `J` with its logarithm, the collars, the side and jump conditions, equal canonical heights, the outer landings,
and the one-sided local agreement `EU ∩ B(p, ε) ⊆ EC` at the two landing points.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Fin

open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketCoupling PocketStopField Lemma71C Lemma71I PocketTraversal PocketStop PocketSeedOpen PocketStopSide R7StopIn
  PocketUnionPt PocketStopWalls PocketStopWallsFin

/-! ### Deterministic -/

section Det

/-- **A physical landing of a conformal chart at a real point** lies in `ℍ̄` and off the chart's domain. -/
theorem landing_notMem_dom {c : Chart} (hc : c.IsConformal) {y : ℝ} {p : ℂ}
    (hl : Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 p)) : p ∈ Hbar ∧ p ∉ (c.dom : Set ℂ) := by
  have hne : (𝓝[H] (y : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  have hbar : p ∈ Hbar := QuantumZipper.isClosed_Hbar.mem_of_tendsto hl
    (eventually_nhdsWithin_of_forall fun z hz => QuantumZipper.H_subset_Hbar (hc.2.1 hz))
  refine ⟨hbar, fun hp => ?_⟩
  have hopen : IsOpen (c.dom : Set ℂ) := c.dom.isOpen
  have hcont : ContinuousAt c.1 p :=
    (hc.differentiableOn_fwd p hp).differentiableAt (hopen.mem_nhds hp) |>.continuousAt
  have h1 : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] (y : ℂ)) (𝓝 (c.1 p)) := hcont.tendsto.comp hl
  have h2 : Tendsto (fun z => c.1 (c.2.1 z)) (𝓝[H] (y : ℂ)) (𝓝 (y : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hc.2.2 z hz).symm)
  have he := tendsto_nhds_unique h1 h2
  have hH := hc.fwd_mem hp
  rw [he] at hH
  exact absurd hH (by simp [QuantumZipper.H])

/-- **The local landing from its one geometric half** (the outer landing and `EU ∩ B(p, ε) ⊆ EC`). -/
theorem localLanding_of_core {outer inner : Chart} {EC EU : Set ℂ} (hO : outer.IsConformal)
    (hincl : (inner.dom : Set ℂ) ⊆ outer.dom) (hOd : (outer.dom : Set ℂ) = H \ EC)
    (hId : (inner.dom : Set ℂ) = H \ EU) (hECH : EC ⊆ H) {y : ℝ} {p : ℂ}
    (hl : Tendsto outer.2.1 (𝓝[H] (y : ℂ)) (𝓝 p)) (hag : ∃ ε > 0, EU ∩ ball p ε ⊆ EC) :
    LocalLanding outer EC EU y p := by
  obtain ⟨hbar, hnot⟩ := landing_notMem_dom hO hl
  have hECU : EC ⊆ EU := fun z hz => by
    by_contra hzU
    have hzI : z ∈ (inner.dom : Set ℂ) := by rw [hId]; exact ⟨hECH hz, hzU⟩
    have hzO := hincl hzI
    rw [hOd] at hzO
    exact hzO.2 hz
  have hpC : p ∈ EC ∪ {z : ℂ | z.im = 0} := by
    rcases (show 0 ≤ p.im from hbar).lt_or_eq with hpos | h0
    · left
      by_contra hpE
      exact hnot (by rw [hOd]; exact ⟨hpos, hpE⟩)
    · exact Or.inr h0.symm
  have hpU : p ∈ EU ∪ {z : ℂ | z.im = 0} := by
    rcases hpC with h | h
    · exact Or.inl (hECU h)
    · exact Or.inr h
  exact ⟨hl, hpC, hpU, hag, ⟨1, one_pos, fun z hz => hECU hz.1⟩⟩

/-- **The core of R.6's current-face geometry**: `R6Geom` without its generic conjuncts (the domain identities and
the landing memberships and the inclusion `EC ⊆ EU` near the landings, which `r6Geom_of_core` derives). -/
def R6GeomCore (κ : ℝ) {nL nR mL mR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (σL : Fin (mL + 1) → ℝ)
    (σR : Fin (mR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ) (wL : Fin (mL + 1) → ℝ)
    (wR : Fin (mR + 1) → ℝ) (outer inner : Chart) (EC EU : Set ℂ) : Prop :=
  ∃ (J : Set ℝ) (G Lg : ℂ → ℂ) (y₀ η₀ ξ η : ℝ) (p₀ p : ℂ), R6Transition outer inner J G Lg ∧
    (R6Collar outer inner J G Lg y₀ η₀ ∧ y₀ ∉ forceJumpSet vL vR ∧ y₀ ∉ Ioo (vL 0) (vR 0) ∧
      η₀ ∉ forceJumpSet wL wR ∧ η₀ ∉ Ioo (wL 0) (wR 0) ∧
      forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀ ∧
      Tendsto outer.2.1 (𝓝[H] (y₀ : ℂ)) (𝓝 p₀) ∧ ∃ ε > 0, EU ∩ ball p₀ ε ⊆ EC) ∧
    (R6Collar outer inner J G Lg ξ η ∧ ξ ∉ forceJumpSet vL vR ∧ ξ ∈ Ioo (vL 0) (vR 0) ∧
      η ∉ forceJumpSet wL wR ∧ η ∈ Ioo (wL 0) (wR 0) ∧
      forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η ∧
      Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) ∧ ∃ ε > 0, EU ∩ ball p ε ⊆ EC)

/-- **`R6Geom` from its core and the generic conjuncts.** -/
theorem r6Geom_of_core {κ : ℝ} {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    {wL : Fin (mL + 1) → ℝ} {wR : Fin (mR + 1) → ℝ} {outer inner : Chart} {EC EU : Set ℂ}
    (hOd : (outer.dom : Set ℂ) = H \ EC) (hId : (inner.dom : Set ℂ) = H \ EU) (hECH : EC ⊆ H)
    (hcore : R6GeomCore κ ρL ρR σL σR vL vR wL wR outer inner EC EU) :
    R6Geom κ ρL ρR σL σR vL vR wL wR outer inner EC EU := by
  obtain ⟨J, G, Lg, y₀, η₀, ξ, η, p₀, p, htr, ⟨h1, h2, h3, h4, h5, h6, hl₀, hag₀⟩,
    ⟨k1, k2, k3, k4, k5, k6, hl, hag⟩⟩ := hcore
  have hO := htr.1
  have hincl := htr.2.2.1
  exact ⟨hOd, hId, J, G, Lg, y₀, η₀, ξ, η, p₀, p, htr,
    ⟨h1, h2, h3, h4, h5, h6, localLanding_of_core hO hincl hOd hId hECH hl₀ hag₀⟩,
    ⟨k1, k2, k3, k4, k5, k6, localLanding_of_core hO hincl hOd hId hECH hl hag⟩⟩

end Det

/-! ### The live current chart of a driven traversal in a pocket chart -/

section Chart

variable {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {γ : Ω → ℝ → ℂ} {q : ℝ≥0}

/-- **The live current chart of a driven traversal in a shifted pocket chart** is conformal, and its domain is the
complement of the active complement (which lies in `ℍ`). -/
theorem relChart_pocket_facts (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) {ω : Ω} (hω : ω ∈ A) (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) :
    (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).IsConformal ∧
      ((relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).dom : Set ℂ) =
        H \ activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω ∧
      activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω ⊆ H := by
  have hc : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal := (pChart_props hCo hCH hψ ω).2.2.1
  exact ⟨isConformal_relChart_of_driven (c := fun ω => shiftChart (pChart A C ψ ω) (n ω)) hγ hq hc,
    (H_diff_activeCompl_eq_relChart_dom hω hq hγ hc).symm, sdiff_subset⟩

end Chart

/-! ### The core inputs -/

/-- **Named, unproved: the core of `R6GeomMixedRemaining`** (`R6GeomCore` in place of `R6Geom`). -/
def R6GeomCoreMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6GeomCore k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: the core of `R6GeomMixedInfRemaining`**. -/
def R6GeomCoreMixedInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6GeomCore k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **Named, unproved: the core of `R6GeomMixedInfInfRemaining`**. -/
def R6GeomCoreMixedInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          R6GeomCore k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-! ### The reductions -/

/-- **`R6GeomMixedRemaining` from its core** (`r6Geom_of_core` with `relChart_pocket_facts` for the two live current
charts). -/
theorem r6GeomMixedRemaining_of_core {k rL rR c c' : ℝ} (hcore : R6GeomCoreMixedRemaining.{u} k rL rR c c') :
    R6GeomMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hcore hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hgc⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨-, hOd, hECH⟩ := relChart_pocket_facts (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
  obtain ⟨-, hId, -⟩ := relChart_pocket_facts (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1 hq'
  exact ⟨q', hq', r6Geom_of_core hOd hId hECH hgc⟩

/-- **`R6GeomMixedInfRemaining` from its core** (`r6Geom_of_core` with `relChart_pocket_facts` for the two live current
charts). -/
theorem r6GeomMixedInfRemaining_of_core {k rL rR c c' : ℝ}
    (hcore : R6GeomCoreMixedInfRemaining.{u} k rL rR c c') :
    R6GeomMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hcore hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hgc⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨-, hOd, hECH⟩ := relChart_pocket_facts (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
  obtain ⟨-, hId, -⟩ := relChart_pocket_facts (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1 hq'
  exact ⟨q', hq', r6Geom_of_core hOd hId hECH hgc⟩

/-- **`R6GeomMixedInfInfRemaining` from its core** (`r6Geom_of_core` with `relChart_pocket_facts` for the two live
current charts). -/
theorem r6GeomMixedInfInfRemaining_of_core {k rL rR c c' : ℝ}
    (hcore : R6GeomCoreMixedInfInfRemaining.{u} k rL rR c c') :
    R6GeomMixedInfInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA hA'
  filter_upwards [hcore hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hgc⟩ := hω hωA hωA' hωN
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨-, hOd, hECH⟩ := relChart_pocket_facts (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) hωA ((hA ω hωA).1.props (hA ω hωA).2).1 hωN.2.1
  obtain ⟨-, hId, -⟩ := relChart_pocket_facts (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) hωA' ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1 hq'
  exact ⟨q', hq', r6Geom_of_core hOd hId hECH hgc⟩

end InteractingSLE.Sec7.R6Fin
