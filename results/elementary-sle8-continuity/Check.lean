import InteractingSLE.Frozen.SLE8.ContinuousTrace
import Mathlib.Util.AssertNoSorry

/-! Release audit of the advertised theorems: the frozen Theorem 1.1 of the note, then the proved inputs of its
proof (not frozen). Every `#print axioms` report must list only axioms among `propext`, `Classical.choice` and
`Quot.sound` (any subset). -/
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

-- The frozen theorem: Theorem 1.1 of the note (existence and continuity of the SLE₈ trace).
assert_no_sorry InteractingSLE.SLE8.ae_exists_continuous_trace
#print axioms InteractingSLE.SLE8.ae_exists_continuous_trace

-- Alvisio–Lawler [AL14]: Theorem 2 (with exponent `p` on `Δ`, and as printed), Theorem 4 (upper bound) and the
-- convergent half of Corollary 1.
assert_no_sorry InteractingSLE.SLE8.AL14.exists_ae_eventually_derivGridMaxStar_le
#print axioms InteractingSLE.SLE8.AL14.exists_ae_eventually_derivGridMaxStar_le
assert_no_sorry InteractingSLE.SLE8.AL14.exists_ae_eventually_derivGridMaxStar_four_le
#print axioms InteractingSLE.SLE8.AL14.exists_ae_eventually_derivGridMaxStar_four_le
assert_no_sorry InteractingSLE.SLE8.AL14.al14_theorem4_upper
#print axioms InteractingSLE.SLE8.AL14.al14_theorem4_upper
assert_no_sorry InteractingSLE.SLE8.AL14.al14_corollary1_summable
#print axioms InteractingSLE.SLE8.AL14.al14_corollary1_summable

-- The note's Lemmas 2.2, 2.3, 3.1, 3.2, 3.3.
assert_no_sorry InteractingSLE.SLE8.revFlow_revDriver_bounds
#print axioms InteractingSLE.SLE8.revFlow_revDriver_bounds
assert_no_sorry InteractingSLE.SLE8.exists_normalizedDeriv_le_gridTime
#print axioms InteractingSLE.SLE8.exists_normalizedDeriv_le_gridTime
assert_no_sorry InteractingSLE.SLE8.exists_criticalChangeOfMeasure
#print axioms InteractingSLE.SLE8.exists_criticalChangeOfMeasure
assert_no_sorry InteractingSLE.SLE8.exists_measure_twoPoint_deriv_le
#print axioms InteractingSLE.SLE8.exists_measure_twoPoint_deriv_le
assert_no_sorry InteractingSLE.SLE8.exists_measure_occupation_le
#print axioms InteractingSLE.SLE8.exists_measure_occupation_le

-- The forms consumed by the assembly: [AL14] Corollary 1 and Lemma 3.1, unconditionally.
assert_no_sorry InteractingSLE.SLE8.al14CorollaryOneStatement_holds
#print axioms InteractingSLE.SLE8.al14CorollaryOneStatement_holds
assert_no_sorry InteractingSLE.SLE8.lemma31Statement_holds
#print axioms InteractingSLE.SLE8.lemma31Statement_holds

/-- **Lemma 2.1 of the note, unconditionally**: for every `β ∈ (0, 1/4)`, almost surely there is `C_β` with
`y_k |F_t'(i y_k)| ≤ C_β k^{-β}` for all `k ≥ 1` and `t ∈ [0, 1]`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (β : ℝ) (hβ : 0 < β) (hβ4 : β < 1 / 4) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ∀ t ∈ Icc (0 : ℝ) 1,
        InteractingSLE.SLE8.normalizedDeriv (QuantumZipper.drive 8 B ω) k t ≤ C * (k : ℝ) ^ (-β) :=
  InteractingSLE.SLE8.lemma21_of_al14CorollaryOne
    (InteractingSLE.SLE8.al14CorollaryOneStatement_holds P) B hB β hβ hβ4

/-- **Proposition 4.1 of the note, unconditionally** (number of large scales): for every `δ ∈ (0, 1/10)`, almost
surely, for all large `n`, with `N = 2^n` and `r = N^δ`, at most `r⁷` of the scales `N < k ≤ 2N` have
`A_k(t_k) ≥ exp(-r/n²)`, uniformly in `t ∈ [0, 1]`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
      (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
          Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
            InteractingSLE.SLE8.normalizedDeriv (QuantumZipper.drive 8 B ω) k
              (((4 : ℝ) ^ k)⁻¹ * ⌊(4 : ℝ) ^ k * t⌋)).card : ℝ) ≤
        (((2 : ℝ) ^ n) ^ δ) ^ 7 :=
  InteractingSLE.SLE8.prop41_of_lemma31 hB (InteractingSLE.SLE8.lemma31Statement_holds P) hδ0 hδ1

-- The assembly: Theorem 1.1 from Lemma 2.1 and Proposition 4.1, and its unconditional form.
assert_no_sorry InteractingSLE.SLE8.ae_exists_continuous_trace_of_scale_count
#print axioms InteractingSLE.SLE8.ae_exists_continuous_trace_of_scale_count
assert_no_sorry InteractingSLE.SLE8.ae_exists_continuous_trace_final
#print axioms InteractingSLE.SLE8.ae_exists_continuous_trace_final

/-- The frozen theorem is the provider's theorem, which is the unconditional assembly. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    type_of% (InteractingSLE.SLE8.ae_exists_continuous_trace hB) :=
  InteractingSLE.SLE8.ae_exists_continuous_trace_final hB

/-! Every declaration of the included project modules (the new `InteractingSLE`, `MathFin` and `BrownianMotion`
modules and the released `QuantumZipper` and `LQGDimension` modules they import) reaches only the three standard axioms. -/
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := moduleNames[idx.toNat]!
    if (`InteractingSLE).isPrefixOf m || (`MathFin).isPrefixOf m || (`BrownianMotion).isPrefixOf m ||
        (`QuantumZipper).isPrefixOf m || (`LQGDimension).isPrefixOf m then
      roots := roots.push n
  if roots.isEmpty then throwError "No included declarations found"
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing declaration {n}"
    match ci with
    | .axiomInfo _ =>
      axioms := axioms.insert n
      unless allowed.contains n do
        throwError "Disallowed axiom reachable from included declarations: {n}"
    | _ => pure ()
    pending := pending ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      pending := pending ++ v.getUsedConstants
  logInfo m!"ELEMENTARY_SLE8_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
