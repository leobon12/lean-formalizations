import GaussianLQG.Frozen.MainTheorem
import Mathlib.Util.AssertNoSorry

/-! First-order fluctuations of small-γ LQG distance: the exact statement of the frozen main theorem
`GaussianLQG.main_theorem` (Theorem 1.1 of the source note), its seven frozen definitions, the inputs
(S1) and (S6) (the note's Lemma 2.1) as theorems, the uniform-in-ξ DDDF20 results behind (S6), absence
of `sorry` and axioms, then an axiom audit of every declaration in the included `GaussianLQG`,
`LQGMetric`, `LQGDimension` and `QuantumZipper` modules. The result guide documents the correspondence
with the paper. -/

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ## The main theorem: its type, restated verbatim from `GaussianLQG/Frozen/MainTheorem.lean` -/

#check GaussianLQG.main_theorem

namespace GaussianLQG

example :
    ∀ (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (_hh : LQGMetric.IsNormalizedWPGFF h P),
    -- `q` is the unique median of `M`, and `q < 0`
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    -- (1.7): convergence in probability
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    -- the limit has law `N(-q/2, 3/8)`
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    -- (1.8): convergence in law to `N(-q/2, 3/8)` (indexed by `γ ∈ (0,2)`)
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    -- (1.9) for every choice of medians `m_γ` of `D^γ(0,1)`
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
  main_theorem

end GaussianLQG

assert_no_sorry GaussianLQG.main_theorem
#print axioms GaussianLQG.main_theorem

/-! ## The seven frozen definitions -/

#print GaussianLQG.segMeasure
#print GaussianLQG.measPairing
#print GaussianLQG.segPairing
#print GaussianLQG.dyadicUnit
#print GaussianLQG.diagMin
#print GaussianLQG.qConst
#print GaussianLQG.IsCanonicalLQGMetric

/-! ## (S1): `d_γ = 2 + O(γ)`, from results already in this repository -/

#check GaussianLQG.dimensionInput_holds
assert_no_sorry GaussianLQG.dimensionInput_holds
#print axioms GaussianLQG.dimensionInput_holds

/-! ## (S6), the note's Lemma 2.1, for every family of canonical metrics -/

#print GaussianLQG.UniformMomentInput

example (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → GaussianLQG.IsCanonicalLQGMetric γ (D γ)) :
    GaussianLQG.UniformMomentInput D := by
  obtain ⟨c, hc, hstar⟩ :=
    GaussianLQG.StarBound.exists_lfppUniformMoments GaussianLQG.Uniform.ifaceHolderMomentU_holds
  exact GaussianLQG.uniformMomentInput_of_lfppUniformMoments c hc hstar D hD

assert_no_sorry GaussianLQG.Uniform.ifaceHolderMomentU_holds
assert_no_sorry GaussianLQG.StarBound.exists_lfppUniformMoments
assert_no_sorry GaussianLQG.uniformMomentInput_of_lfppUniformMoments
#print axioms GaussianLQG.Uniform.ifaceHolderMomentU_holds
#print axioms GaussianLQG.StarBound.exists_lfppUniformMoments
#print axioms GaussianLQG.uniformMomentInput_of_lfppUniformMoments

/-! ## DDDF20 uniformly in ξ: Corollary 17, Proposition 18 and its Step 4, Condition (T), Theorem 20 -/

#check GaussianLQG.Uniform.cor17_unif
#check GaussianLQG.Uniform.prop18_unif
#check GaussianLQG.Uniform.p18_step4_unif
#check GaussianLQG.Uniform.conditionTU_small_all
#check GaussianLQG.Uniform.thm20_unif_holds

assert_no_sorry GaussianLQG.Uniform.cor17_unif
assert_no_sorry GaussianLQG.Uniform.prop18_unif
assert_no_sorry GaussianLQG.Uniform.p18_step4_unif
assert_no_sorry GaussianLQG.Uniform.conditionTU_small_all
assert_no_sorry GaussianLQG.Uniform.thm20_unif_holds
#print axioms GaussianLQG.Uniform.cor17_unif
#print axioms GaussianLQG.Uniform.prop18_unif
#print axioms GaussianLQG.Uniform.p18_step4_unif
#print axioms GaussianLQG.Uniform.conditionTU_small_all
#print axioms GaussianLQG.Uniform.thm20_unif_holds

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
    if (`GaussianLQG).isPrefixOf m || (`LQGMetric).isPrefixOf m || (`LQGDimension).isPrefixOf m ||
        (`QuantumZipper).isPrefixOf m then
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
  logInfo m!"GAUSSIAN_LQG_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
