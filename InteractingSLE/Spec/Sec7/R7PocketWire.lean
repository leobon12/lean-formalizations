/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7PocketCore
import InteractingSLE.Spec.Sec7.Lemma725RefSafeWire

/-!
# Theorem R.7's reference (`hR7`) from one named input on the whole range: the phase selection lives in the pocket mean

Packet PROVE-R7POCKET. Theorem R.7 (`source/spec/p433-480.md` L1051–L1070, pp. 477–478): "Lemma R.6 selects the zero
phase for arbitrarily large weights … Theorem 2.4 identifies the integrated force-point SDE before the relative capacity
lifetime `L` … This contradiction excludes every finite `L`".

`Lemma725RefSafe.r7ReferenceStatement_of_pocketChartTwoSeed` split `hR7` at the seed weight `κ − 6`: below it from the
two-seed pocket's field-level data (`PocketChartTwoSeedStatement`), above it from the `P`-side pocket itself
(`PocketTwoSeedPSideStatement`), because the landed (E) chain re-ran Aux. lemma 122's phase selection, which needs seed
weights `< 2A − 2 = κ − 6`. But `PocketChartTwoSeedStatement`'s mean identification `PocketMeanIdent` already fixes the
canonical (zero-phase) heights; for Theorem R.7's mixed and outer pockets that is exactly Lemma R.6's conclusion, where
the zero phase is selected for arbitrarily large weights by the shared-side comparison with an inner pocket. With the
zero-phase chain (`R7PocketPhase`, `R7PocketCore`) the pocket's field-level data give the `P`-side pocket for **every**
pair of seed weights `> −2`:

* **`pocketTwoSeedPSideStatement_of_charFun_zeroPhase`**, **`pocketTwoSeedPSideStatement_of_chart_zeroPhase`**,
  **`pocketTwoSeedPSideStatement_of_pocketChartTwoSeed_zeroPhase`**: no upper seed-weight bound;
* **`r7ReferenceStatement_of_pocketChartTwoSeed_all`**: `hR7` from `PocketChartTwoSeedStatement` on the whole range of
  Theorem R.7 (`r_L, r_R > −2`, `max(r_L, r_R) ≥ κ/2 − 4`), with no separate `P`-side input above `κ − 6`.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefSafe

open Restart.DomainMarkov Restart.DomainMarkov.K2 Aux122Disint PhaseSel PocketMartLife PocketCoupling LocalSets
  Coupling MartChar PocketTraversal Lemma71C PocketAdapt PocketWordLife LawUnique PocketStop WholeField

universe u

section Word


/-- **The `P`-side pocket of a two-seed word with its field** (`Lemma725RefK2.PocketTwoSeedPSideStatement`, the
named input of `hR7`) from the zero-phase core, for the constant two-seed word `SLE_κ(r_L; r_R)` with **any** seed
weights `> −2` (`pocketTwoSeedPSideStatement_of_charFun` without the bound `< κ − 6`): the pathwise property `Good` of
the relative driver with infinite lifetime, almost surely,
and the determination of the killed relative history by `(E, X)` for an `𝓔`-measurable record `E`. -/
theorem pocketTwoSeedPSideStatement_of_charFun_zeroPhase {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL)
    (hR : -2 < rR) {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    {Ω : Type u} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u)
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) {X : Ω → DistOn upperHalfPlaneOpens}
    (hXm : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P
      (usualAugmentation (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k) P)
      (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) X)
    (hmem : HasSafeMembers P (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k)
      univ (fun ω => capLife (γ ω)) (fun t ω => segDriver (γ ω) t) X)
    (hGood : ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε : Type u} [MeasurableSpace ε] {E : Ω → ε} (hEm : Measurable[𝓔] E)
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1} (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, killedHistory (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) ω = g (E ω, X ω)) :
    Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR Good := by
  have hsL : ∀ m : Fin 1, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), (fun _ : Fin 1 => rL) i := by
    intro m
    rw [Subsingleton.elim m 0, Finset.filter_true_of_mem fun i _ => (Subsingleton.elim i 0).le]
    simpa using hL
  have hsR : ∀ m : Fin 1, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), (fun _ : Fin 1 => rR) i := by
    intro m
    rw [Subsingleton.elim m 0, Finset.filter_true_of_mem fun i _ => (Subsingleton.elim i 0).le]
    simpa using hR
  obtain ⟨Ω₃, m₃, hSB, P₃, hP₃, π, B, 𝓗, 𝓗', hπ, hae, hlife, hE, h𝓔', hWa, hVLa, hVRa, hS, hL⟩ :=
    exists_pocketField_core_zeroPhase (nL := 0) (nR := 0) hκ hsL hsR h𝓔 hγ hγm hunb
      (measurable_const (a := LP.twoSeedXL)) (measurable_const (a := LP.twoSeedXR)) (fun _ => rfl) (fun _ => rfl)
      (fun _ => fun i j _ => le_rfl) (fun _ => fun i j _ => le_rfl) hXm
      hint hcf hmem
  refine ⟨Ω₃, MeasurableSpace.comap π 𝓔, m₃, hSB, P₃, hP₃, univ, ε, inferInstance, fun ω => E (π ω),
    fun ω => X (π ω), fun t ω => segDriver (γ (π ω)) t,
    fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) i t (π ω),
    fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXR) j t (π ω), B, fun _ => ⊤, 𝓗, 𝓗',
    hE, by rw [measure_univ]; exact one_ne_zero, fun s hs => ⟨_, hEm hs, rfl⟩, hXm.comp hπ, h𝓔', hWa, hVLa, hVRa,
    hS, hL, ?_, g, hg, ?_⟩
  · filter_upwards [hae _ hGood] with ω hω _
    exact hω (hlife ω)
  · filter_upwards [hae _ hdet] with ω hω _
    have e : killedHistory (fun t ω => segDriver (γ (π ω)) t)
        (fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) i t (π ω))
        (fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXR) j t (π ω)) (fun _ => ⊤) ω =
        killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
          (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) (π ω) := by
      simp only [killedHistory, hlife ω]
    rw [e]
    exact hω

end Word

section Chart

/-- **The `P`-side pocket of a two-seed word with its field, from the field on the ambient space**
(`pocketChart_levelOne` and `pocketTwoSeedPSideStatement_of_charFun_zeroPhase`), for **any** seed weights `> −2`:
besides the inputs of `pocketChart_levelOne` for the constant two-seed word, the traversal unbounded in
`ℍ`, the pathwise property `Good` of the relative driver with infinite lifetime, and the determination `hdet`. -/
theorem pocketTwoSeedPSideStatement_of_chart_zeroPhase {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL)
    (hR : -2 < rR) {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hker : PocketKernel 𝓦 P A γ c h 𝓜 M)
    (hmean : PocketMeanIdent κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ (fun _ => LP.twoSeedXL)
      (fun _ => LP.twoSeedXR) c a k M)
    (hKm : ∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ c s))
    (hKloc : ∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s) (activeCompl A γ c s) (centredField h u₀) P)
    (hGood : ∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε : Type u} [MeasurableSpace ε] {E : Ω → ε} (hEm : Measurable[𝓦] E)
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1} (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, ω ∈ A → killedHistory (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR)
      (fun ω => capLife (γ ω)) ω = g (E ω, Chart.chartTransport (hc ω) 1 a k (h ω))) :
    Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR Good := by
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : StandardBorelSpace A := hAm.standardBorel
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  obtain ⟨hX, hint, hcf, hmem⟩ := pocketChart_levelOne h𝓦 hA hPA hγ hγm (measurable_const (a := LP.twoSeedXL))
    (measurable_const (a := LP.twoSeedXR)) hc hdom hfwd hliftm hliftc hlift a k hhm hu₀ hh0 hker hmean hKm hKloc
  refine pocketTwoSeedPSideStatement_of_charFun_zeroPhase hκ hL hR (MeasurableSpace.comap_mono h𝓦)
    (fun ω : A => hγ ω ω.2) hγm (fun ω => hunb ω ω.2) hX hint hcf hmem ?_ (fun s hs => ⟨_, hEm hs, rfl⟩) hg ?_
  · filter_upwards [ae_condSub_of_ae hAm hGood] with ω hω
    exact hω ω.2
  · filter_upwards [ae_condSub_of_ae hAm hdet] with ω hω
    exact hω ω.2

end Chart

/-- **`PocketTwoSeedPSideStatement` from the two-seed pocket's field-level data, for every pair of seed weights
`> −2`** (`pocketTwoSeedPSideStatement_of_pocketChartTwoSeed` without the bound `< κ − 6`: the zero phase is part of
`PocketMeanIdent`). -/
theorem pocketTwoSeedPSideStatement_of_pocketChartTwoSeed_zeroPhase {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL)
    (hR : -2 < rR) {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (h : PocketChartTwoSeedStatement.{u} κ rL rR Good) :
    Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR Good := by
  obtain ⟨Ω, 𝓦, mΩ, hSB, P, hP, A, γ, c, hc, a, k, hf, u₀, 𝓜, M, ε, mε, E, g, h𝓦, hA, hPA, hγ, hγm, hunb, hdom,
    hfwd, hliftm, hliftc, hlift, hhm, hu₀, hh0, hker, hmean, hKm, hKloc, hGood, hEm, hg, hdet⟩ := h
  exact pocketTwoSeedPSideStatement_of_chart_zeroPhase hκ hL hR h𝓦 hA hPA hγ hγm hunb hc hdom hfwd hliftm hliftc
    hlift a k hhm hu₀ hh0 hker hmean hKm hKloc hGood hEm hg hdet

/-- **Theorem R.7's reference (`hR7`) from the two-seed pockets' field-level data on the whole range** (Theorem R.7:
`r_L, r_R > −2`, `max(r_L, r_R) ≥ κ/2 − 4`), with transient traces. Compared with
`r7ReferenceStatement_of_pocketChartTwoSeed`, the pairs with a seed weight `≥ κ − 6` need no separate `P`-side input:
their phase selection is Lemma R.6's, inside the pocket mean identification of `PocketChartTwoSeedStatement`. -/
theorem r7ReferenceStatement_of_pocketChartTwoSeed_all
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      PocketChartTwoSeedStatement.{u} κ rL rR fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧
        (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) :
    R7.R7ReferenceStatement.{u} :=
  Lemma725RefK2.r7ReferenceStatement_of_pSide fun κ hκ rL rR hL hR hmax =>
    pocketTwoSeedPSideStatement_of_pocketChartTwoSeed_zeroPhase hκ hL hR (h κ hκ rL rR hL hR hmax)

end InteractingSLE.Sec7.Lemma725RefSafe
