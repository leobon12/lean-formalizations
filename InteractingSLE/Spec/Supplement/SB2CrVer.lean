/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NaStmt

/-!
# The root's relative versions in B's own time (D44)

Packet PROVE-SB2-CONDFIN (round 8, D44). At the root `ℓ = relOff` the line family is LCMEAN's tail family in B's own
time (`𝓖 t` = capped pasts at the deterministic B-time `t`, `A₁`, `A₂ t` of `Ml.exists_sb2LineFamily_cf`). The
relative piece starts only at B's entrance at `R`. The structures below are NOJUMP's version structures
`Na.StageVersionG`/`Na.StageVersionS` with the changes forced by that, and nothing else:

* the live event is the ROOT event `Fr` (B enters the relative domain at `R` before dying). It is an event of the
  relative filtration at time `0` (the entrance, `root_meas`), not of `lineFiltC 𝓖 0`: the clock `a` is `0` until the
  entrance, positive only on the root (`clock_root`);
* the time change is STRICT (`timeChange`: `D ∈ 𝓗_q ⇒ D ∩ {q < a t} ∈ lineFiltC 𝓖 t`). The usual form fails at
  `q = 0`, since `𝓗 0` holds the root event. The strict form follows from the usual one for `q > 0` and, at `q = 0`,
  from `𝓗 0` being the past stopped at the entrance;
* the safe events are asked where the clock is positive (`safeS`, `safeL`): `{a t < Λ}` reads the stops, which see
  the root event;
* the stops' record is measurable for `𝓗 0` (`RootVersionS.record_meas`), for the same reason.

Why the D44 text ("live event `stageEvent ∩ {relOff ≥ ℓ} ∩ {0 < ζ_ℓ}`, clauses only on the root") needs this: the stops
are path rules of the relative driver (`IsPathRule`), so `{V m = 0}` is decided by the record and `W 0 = 0`. With the
record measurable for `lineFiltC 𝓖 0` (B-time `0`) the stops could not be positive exactly on the root, which is not a
B-time-`0` event. The consumer (K2: `Cr.hasSafeLaw_life_of_lineKernelS`, `Cr.hasSafeMembers_life_of_lineLocalS`,
then LCMEAN's core with `𝒢 = 𝓗 0`) conditions on `𝓗 0` and uses the line facts only where `0 < a t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cr

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **One relative version at the root, in B's own time.** `Na.StageVersionG` with the root event `Fr` as live event
(an event of `𝓗 0`), the clock positive only on `Fr`, the strict time change and the safe events where the clock is
positive. -/
structure RootVersionG (κ ψ : ℝ) (P : Measure Ω) (Fr : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ)
    (A₂ : ℝ≥0 → Ω → Set ℂ) (Φ : Ω → Chart) (β₁ : Ω → BoundaryWord) (types : Set WordType)
    (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (L : Ω → ℝ≥0∞) where
  𝓗 : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → ℝ
  a : ℝ≥0 → Ω → ℝ≥0∞
  Λ : WordType → Ω → ℝ≥0∞
  marks_le : lineFiltC P 𝓖 0 ≤ 𝓗 0
  root_meas : MeasurableSet[𝓗 0] Fr
  W_zero : ∀ ω, W 0 ω = 0
  W_cont : ∀ ω, Continuous fun t => W t ω
  W_adapted : StronglyAdapted 𝓗 W
  clock_cont : ∀ ω, Continuous fun t => a t ω
  clock_mono : ∀ ω, Monotone fun t => a t ω
  clock_zero : ∀ ω, a 0 ω = 0
  clock_meas : ∀ t, Measurable[lineFiltC P 𝓖 t] (a t)
  clock_root : ∀ t, ∀ᵐ ω ∂P, 0 < a t ω → ω ∈ Fr
  timeChange : ∀ (q : ℝ≥0) (D' : Set Ω), MeasurableSet[𝓗 q] D' → ∀ t,
    MeasurableSet[lineFiltC P 𝓖 t] (D' ∩ {ω | (q : ℝ≥0∞) < a t ω})
  reach : ∀ w ∈ types, ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → (q : ℝ≥0∞) < Λ w ω →
    ∃ t, (q : ℝ≥0∞) ≤ a t ω
  reg : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
    Aux79.IsForceReg W (geomLW W (cellXL κ ψ β₁ w)) (geomRW W (cellXR κ ψ β₁ w)) (Λ w) ω
  safeS : ∀ w ∈ types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[lineFiltC P 𝓖 t]
    {ω | 0 < a t ω ∧ a t ω < Λ w ω ∧ Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  safeL : ∀ w ∈ types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[lineFiltC P 𝓖 t]
    {ω | 0 < a t ω ∧ a t ω < Λ w ω ∧
      Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  hull : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → a t ω < Λ w ω →
    H \ (A₁ t ω ∪ A₂ t ω) = (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)
  trace : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → a t ω < Λ w ω →
    ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun s : ℝ => W s.toNNReal ω) ηr ∧
      ∀ s : ℝ≥0, s ≤ t → tL ω ≤ s → pc ω s ∈ ((Φ ω).dom : Set ℂ) → ηr (a s ω).toReal = (Φ ω).1 (pc ω s)
  alive : ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → a t ω < Λ w ω → (t : ℝ≥0∞) < L ω
  Λ_le : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
    Λ w ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ β₁ w) (cellXR κ ψ β₁ w) ω

/-- **The root's relative versions at announced stops, in B's own time** (`Na.StageVersionS` over `RootVersionG`,
with the record measurable for every version's `𝓗 0` and every clause on the root event). -/
structure RootVersionS (κ ψ : ℝ) (P : Measure Ω) (Fr : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ)
    (A₂ : ℝ≥0 → Ω → Set ℂ) (Φ : Ω → Chart) (β₁ : Ω → BoundaryWord) (types : Set WordType)
    (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (L : Ω → ℝ≥0∞) (relLife : Ω → ℝ≥0∞) where
  ver : ℕ → RootVersionG κ ψ P Fr 𝓖 A₁ A₂ Φ β₁ types pc tL L
  V : ℕ → Ω → ℝ≥0∞
  record : Ω → RecData
  record_meas : ∀ m, Measurable[(ver m).𝓗 0] record
  ρ : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρs : ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρ_meas : ∀ m, Measurable (ρ m)
  ρ_rule : ∀ m, Supp8.GB6.HullId.IsPathRule (ρ m)
  ρs_meas : ∀ m n, Measurable (ρs m n)
  ρs_rule : ∀ m n, Supp8.GB6.HullId.IsPathRule (ρs m n)
  ρs_fin : ∀ m n x, ρs m n x ≠ ⊤
  ρs_mono : ∀ m x, Monotone fun n => ρs m n x
  Λ_eq : ∀ m w, (ver m).Λ w = V m
  V_eq : ∀ m ω, V m ω = ρ m (record ω, fun s => (ver m).W s ω)
  ann : ∀ m, ∀ᵐ ω ∂P, ω ∈ Fr → (∀ n, ρs m n (record ω, fun s => (ver m).W s ω) < V m ω) ∧
    ⨆ n, ρs m n (record ω, fun s => (ver m).W s ω) = V m ω
  V_lt : ∀ m, ∀ᵐ ω ∂P, ω ∈ Fr → V m ω < relLife ω
  V_mono : ∀ ω, Monotone fun m => V m ω
  V_sup : ∀ᵐ ω ∂P, ω ∈ Fr → ⨆ m, V m ω = relLife ω
  W_eq : ∀ m m', m ≤ m' → ∀ᵐ ω ∂P, ω ∈ Fr → ∀ t : ℝ≥0, (t : ℝ≥0∞) < V m ω →
    (ver m).W t ω = (ver m').W t ω

end InteractingSLE.Theorem14.SB.Cr
