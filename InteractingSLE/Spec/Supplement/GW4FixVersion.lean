/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixGauge
import InteractingSLE.Spec.Supplement.GW4RelLaw

/-!
# Theorem GW4's announced relative versions from measurable relative coordinates

Packet PROVE-T14-GW4FIX. PROVE-Q3-REL4 found that GW4's `GW4Rel.GW4RelStopKernelStatement` asks the stopped coupling
for EVERY version stop, which the stopped K2 reaches only along announcing sequences (as for GB6). GB6's corrected
route uses announced versions whose stops are path rules. This file gives GW4's announced versions:

* `IsPathRule₀` (a path rule of the path alone) and the bridges to the record form `HullId.IsPathRule`;
* **`IsGW4RelVersionA`**: a version of the relative traversal through a stopping time (`GW4Rel.IsGW4RelStopVersion`)
  whose stop is positive, a measurable path rule of the relative path, and announced by measurable finite path rules;
  **`GW4RelVersionAStatement`**: exhausting announced versions exist;
* **`IsGW4RelCoord`**, **`GW4RelCoordStatement`** (named input; the GW4 instance of the generic measurability of the
  relative driver, PROVE-GB6-RELSAFE's territory): under the conditional law given the walks, the relative traversal of
  a between-component has measurable coordinates — a measurable driver `D`, continuous before a measurable positive
  life `Λ`, whose hulls before `Λ` are relative hulls `A(t) = Φ(K'_t ∩ R⁻¹(C))` and which reaches every bounded `A(t)`
  before `Λ` (pathwise, Lemma GB11's relative parametrization `GB11GateFinal.gb11RelParamStatement`);
* `exists_lt_abs_of_far`: the relative endpoint at infinity (`GW4Rel.exists_far_relHullFam`) forces `|D|` to be
  unbounded before a finite `Λ` (a driver bounded by `M` up to `s` has its hull in the ball of radius `M + 3√s`);
* **`gw4RelVersionAStatement_of_coord`**: the coordinate versions stopped by the running-maximum gauge
  (`GW4Fix.maxRead`, `exists_aeSeparationReadout_maxRead`) are exhausting announced versions.

The record of the relative chain is constant (`gw4Rec`): under the conditional law given the walks the walks are fixed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId
  Supp8.Q3Stop

/-! ### Path rules of the path alone -/

/-- The constant record of GW4's relative chain (under the conditional law given the walks the walks are fixed). -/
def gw4Rec : RecData := (0, 0, false)

/-- **A path rule of the path alone**: its value does not change when the path changes after it. -/
def IsPathRule₀ (ρ : (ℝ≥0 → ℝ) → ℝ≥0∞) : Prop :=
  ∀ w w' : ℝ≥0 → ℝ, (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ w → w u = w' u) → ρ w' = ρ w

theorem isPathRule_comp_snd {ρ : (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule₀ ρ) : IsPathRule fun x => ρ x.2 :=
  fun _ w w' h => hρ w w' h

theorem isPathRule₀_of_isPathRule {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (r : RecData) :
    IsPathRule₀ fun w => ρ (r, w) :=
  fun w w' h => hρ r w w' h

/-! ### Announced versions and measurable coordinates -/

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **An announced version of GW4's relative traversal**: a version through a stopping time of the relative path
(`GW4Rel.IsGW4RelStopVersion`) whose stop is almost surely positive, almost surely a measurable path rule of the
relative path, and announced by measurable finite path rules (nondecreasing, below the stop, with supremum the stop). -/
def IsGW4RelVersionA (ν : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (c : Chart) (C : Set ℂ) (R : ℝ≥0 → Ω → ℝ)
    (V : Ω → ℝ≥0∞) : Prop :=
  IsGW4RelStopVersion ν W' c C R V ∧ (∀ᵐ ω ∂ν, 0 < V ω) ∧
    (∃ ρ : (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable ρ ∧ IsPathRule₀ ρ ∧ ∀ᵐ ω ∂ν, V ω = ρ fun u => R u ω) ∧
    ∃ ρs : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞, (∀ n, Measurable (ρs n)) ∧ (∀ n, IsPathRule₀ (ρs n)) ∧
      (∀ n w, ρs n w ≠ ⊤) ∧ (∀ w, Monotone fun n => ρs n w) ∧
      ∀ᵐ ω ∂ν, (∀ n, ρs n (fun u => R u ω) < V ω) ∧ ⨆ n, ρs n (fun u => R u ω) = V ω

/-- **Measurable coordinates of the relative traversal** (under a measure `ν`): a measurable driver `D`, `0` at `0`
and continuous before a measurable positive life `Λ`, such that `ν`-almost surely every hull of `D` before `Λ` is a
relative hull `A(t) = Φ(K'_t ∩ R⁻¹(C))` of the ambient counterflow `W'`, and every bounded relative hull is a hull of
`D` before `Λ`. -/
structure IsGW4RelCoord (ν : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (c : Chart) (C : Set ℂ) (D : ℝ≥0 → Ω → ℝ)
    (Λ : Ω → ℝ≥0∞) : Prop where
  measurable : ∀ t, Measurable (D t)
  life_measurable : Measurable Λ
  life_pos : ∀ ω, 0 < Λ ω
  continuous : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < Λ ω}
  zero : ∀ ω, D 0 ω = 0
  hull : ∀ᵐ ω ∂ν, ∀ s : ℝ≥0, (s : ℝ≥0∞) < Λ ω → ∃ t : ℝ≥0,
    fwdHull (fun r : ℝ => D r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t
  exhaust : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, Bornology.IsBounded (relHullFam c C (fun u => W' u ω) t) →
    ∃ s : ℝ≥0, (s : ℝ≥0∞) < Λ ω ∧ fwdHull (fun r : ℝ => D r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t

end Defs

/-- **Named input (measurability): measurable coordinates of GW4's relative traversals.** In the setting of
`GW4Reg.GW4RelativeLawRegStatement`, for almost every conditioning sample `ω₀`, every between-component `C` of the two
walks and every component chart `c`, the relative traversal has measurable coordinates under the conditional law `ν`
given the walks (`IsGW4RelCoord`). Pathwise the relative driver is Lemma GB11's relative parametrization
(`GB11GateFinal.gb11RelParamStatement`, proved); the content is its measurable choice (the generic measurability of a
relative driver, as for GB6's `SourceC.exists_relative_driver`). -/
def GW4RelCoordStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ c : Chart, IsComponentChart R L C c →
          ∃ (D : ℝ≥0 → Ω → ℝ) (Λ : Ω → ℝ≥0∞), IsGW4RelCoord ν W' c C D Λ

/-- **Exhausting announced versions of GW4's relative traversals** (the announced form of
`GW4Rel.GW4RelVersionStatement`): in the setting of `GW4RelCoordStatement`, there are announced versions
`(R m, V m)` (`IsGW4RelVersionA`) such that `ν`-almost surely every bounded relative hull is the hull of some `R m`
at a relative time before `V m`. -/
def GW4RelVersionAStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ c : Chart, IsComponentChart R L C c →
          ∃ (Rv : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
            (∀ m, IsGW4RelVersionA ν W' c C (Rv m) (V m)) ∧
            ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, Bornology.IsBounded (relHullFam c C (fun u => W' u ω) t) →
              ∃ m, ∃ s : ℝ≥0, (s : ℝ≥0∞) < V m ω ∧
                fwdHull (fun r : ℝ => Rv m r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t

/-! ### The relative driver blows up at a finite life -/

/-- **A bounded driver has bounded hulls before a finite life**: if `|D| ≤ M` before `Λ` and the far relative hulls are
hulls of `D` before `Λ`, the hull family stays in the ball of radius `M + 3√Λ`; hence (relative endpoint at infinity)
`|D|` exceeds every bound before a finite life. -/
theorem exists_lt_abs_of_far {D : ℝ≥0 → ℝ} {Λ : ℝ≥0∞} (hDc : ContinuousOn D {u | (u : ℝ≥0∞) < Λ})
    {A : ℝ≥0 → Set ℂ}
    (hex : ∀ t, Bornology.IsBounded (A t) → ∃ s : ℝ≥0, (s : ℝ≥0∞) < Λ ∧ fwdHull (fun r : ℝ => D r.toNNReal) s = A t)
    (hfar : ∀ M : ℝ, ∃ t, Bornology.IsBounded (A t) ∧ ¬ A t ⊆ closedBall 0 M) (hΛ : Λ ≠ ⊤) (M : ℝ) :
    ∃ s : ℝ≥0, (s : ℝ≥0∞) < Λ ∧ M < |D s| := by
  by_contra hn
  have hle : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Λ → |D s| ≤ M := fun s hs => by
    by_contra hlt
    exact hn ⟨s, hs, lt_of_not_ge hlt⟩
  obtain ⟨t, htb, htf⟩ := hfar (M + 3 * Real.sqrt Λ.toReal)
  obtain ⟨s, hsΛ, hst⟩ := hex t htb
  apply htf
  rw [← hst]
  have hfz : Continuous fun r : ℝ => D (min r.toNNReal s) :=
    hDc.comp_continuous (continuous_real_toNNReal.min continuous_const)
      fun r => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt hsΛ
  rw [← fwdHull_freeze_eq hDc hsΛ s.coe_nonneg le_rfl]
  rcases (zero_le : (0 : ℝ≥0) ≤ s).lt_or_eq with hs0 | hs0
  · have hsub := QuantumZipper.CaraR.fwdHull_subset_closedBall hfz (NNReal.coe_pos.2 hs0) (M := M) fun r _ =>
      hle _ ((ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt hsΛ)
    refine hsub.trans (closedBall_subset_closedBall ?_)
    have hsl : (s : ℝ) ≤ Λ.toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hΛ).2 hsΛ.le
      rwa [ENNReal.coe_toReal] at this
    have := Real.sqrt_le_sqrt hsl
    linarith
  · subst hs0
    rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hfz]
    exact empty_subset _

/-! ### The announced coordinate versions -/

/-- **GW4's exhausting announced versions from measurable relative coordinates** (conditional helper with a distinct
name): the coordinate driver frozen at the gauge stops of the running-maximum gauge (`maxRead`, levels
`gaugeLevel 1 m`, caps `m + 1`) gives announced versions; the relative endpoint at infinity (from Theorem 1.3, GB10
and the walks' barrier with its pocket shape) makes the gauge vanish at a finite life. -/
theorem gw4RelVersionAStatement_of_coord (h13 : Exist.Theorem13Statement.{u})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u}) (hC : GW4RelCoordStatement.{u}) :
    GW4RelVersionAStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_transient_noSimpleArc h13 hκ hκ4 hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hBω hCω
  intro R L ν C hCm c hch
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨D, Λ, hco⟩ := hCω C hCm c hch
  obtain ⟨αR, αL, hαR, hαL, hP, hbar⟩ := hBω
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  have hblow : ∀ᵐ ω ∂ν, Λ ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < Λ ω ∧ M < |D s ω| := by
    filter_upwards [hambω, hbar, hco.exhaust] with ω hambω' hbarω hexω hΛ M
    obtain ⟨hW'c, hW'0, γ, hγ, hγt, hno⟩ := hambω'
    exact exists_lt_abs_of_far (hco.continuous ω) hexω
      (exists_far_relHullFam hW'c hW'0 hγ hγt hno (hbarω γ hγ) hP hCm' hch') hΛ M
  obtain ⟨g, hread⟩ := exists_aeSeparationReadout_maxRead (P := ν) (rec := fun _ => gw4Rec) measurable_const
    hco.measurable hco.life_measurable hco.life_pos hco.continuous hco.zero hblow
  have hv := coordStop_lt_life hread
  have hvm := measurable_coordStop_of_readout hread
  have hadapt : AdaptedBefore (Filtration.const ℝ≥0 ‹MeasurableSpace Ω› le_rfl) Λ D := fun t A hA =>
    (measurableSet_lt measurable_const hco.life_measurable).inter (hco.measurable t hA)
  have hε := measurable_recLevel measurable_maxRead
  have hpm : Measurable fun w : ℝ≥0 → ℝ => (gw4Rec, w) := measurable_const.prodMk measurable_id
  refine ⟨coordDriver (D := D) (g := g), fun m ω => (coordStop (g := g) m ω : ℝ≥0∞), fun m => ?_, ?_⟩
  · refine ⟨⟨⟨fun t => measurable_freeze hadapt hco.continuous (hvm m) (hv m) t,
      continuous_freeze hco.continuous (hv m), fun ω => ?_, measurable_coe_nnreal_ennreal.comp (hvm m), ?_⟩,
      fun ω t ht => freeze_after (ENNReal.coe_le_coe.1 ht), fun t => ?_⟩,
      ae_of_all _ fun ω => ENNReal.coe_pos.2 (localStop_pos (hread.continuous ω) (hread.zero_pos ω) m),
      ⟨fun w => hitRule maxRead (recLevel maxRead m) (m + 1) (gw4Rec, w),
        (measurable_hitRule measurable_maxRead (hε m)).comp hpm,
        isPathRule₀_of_isPathRule (isPathRule_hitRule isCausal_maxRead) gw4Rec, ae_coordStop_eq_hitRule hread m⟩,
      fun n w => annRules maxRead m n (gw4Rec, w), fun n => (measurable_annRules measurable_maxRead m n).comp hpm,
      fun n => isPathRule₀_of_isPathRule (isPathRule_annRules isCausal_maxRead m n) gw4Rec,
      fun n w => annRules_ne_top maxRead m n _, fun w => monotone_annRules maxRead m _,
      ae_annRules_coord_rec hread m⟩
    · simpa only [coordDriver, freeze, zero_min] using hco.zero ω
    · filter_upwards [hco.hull] with ω hω s hs
      obtain ⟨t, ht⟩ := hω s (hs.trans (hv m ω))
      exact ⟨t, (fwdHull_freeze_eq (hco.continuous ω) (hv m ω) s.coe_nonneg
        (NNReal.coe_le_coe.2 (ENNReal.coe_le_coe.1 hs.le))).trans ht⟩
    · refine ⟨(fun w => (gw4Rec, w)) ⁻¹' prefixHitSet maxRead (recLevel maxRead m) (m + 1) t,
        hpm (measurableSet_prefixHitSet measurable_maxRead (hε m) _ _),
        fun w w' hw => isDetUpTo_prefixHitSet isCausal_maxRead _ _ t gw4Rec w w' hw, ?_⟩
      exact ae_coordStop_le_iff hread m t
  · filter_upwards [hco.exhaust] with ω hω t ht
    obtain ⟨s, hs, hst⟩ := hω t ht
    obtain ⟨m, hm⟩ := exists_lt_localStop (hread.continuous ω) (t := s) fun u hu =>
      hread.positive ω u ((ENNReal.coe_le_coe.2 hu).trans_lt hs)
    exact ⟨m, s, ENNReal.coe_lt_coe.2 hm,
      (fwdHull_freeze_eq (hco.continuous ω) (hv m ω) s.coe_nonneg (NNReal.coe_le_coe.2 hm.le)).trans hst⟩

/-- **The measurability leaf of PROVE-GW4-RELLAW's split (`GW4Rel.GW4RelVersionStatement`) from announced versions**:
announced versions are versions through a stopping time. -/
theorem gw4RelVersionStatement_of_versionA (hV : GW4RelVersionAStatement.{u}) : GW4RelVersionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hV κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hVω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨Rv, V, hver, hexh⟩ := hVω C hCm c hch
  exact ⟨Rv, V, fun m => (hver m).1, hexh⟩

/-- `GW4Rel.GW4RelVersionStatement` from measurable relative coordinates (conditional helper). -/
theorem gw4RelVersionStatement_of_coord (h13 : Exist.Theorem13Statement.{u})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u}) (hC : GW4RelCoordStatement.{u}) : GW4RelVersionStatement.{u} :=
  gw4RelVersionStatement_of_versionA (gw4RelVersionAStatement_of_coord h13 hB hC)

end InteractingSLE.Theorem14.GW4Fix
