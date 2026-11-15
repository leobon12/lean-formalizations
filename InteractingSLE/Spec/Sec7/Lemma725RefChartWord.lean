/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefChartGen
import InteractingSLE.Spec.Sec7.PocketStopFieldAssembly

/-!
# Lemma 7.25's pocket field data for the strip system's change pockets

Packet PROVE-LEMMA725REF4, item 1 (a). Specification §7.4.1, Aux. lemmas 119–122, 124–125 and 130, Lemma 7.25's proof
(`source/spec/p385-432.md` L171–L250, L401–L515, pp. 393–398, 408–414).

The strip-level glue of PROVE-STRIPSYS20/26/35 (`PocketWordAssembly.pocketWordEvolution_of_cfPocketConfig`,
`PocketSeedOpen.pocketWordEvolution_of_cfPocketConfigInf`, `…_of_changeConfig`,
`PocketStopField.pocketStopField_cfPocket`)
derives `Lemma725Ref.PocketWordEvolution` from the remaining field-level inputs `PocketStopWallsInput`/`…Inf`. Here the
same construction — the walls-measurable Jordan coordinate `ψ` with its marks (`exists_measurable_pocketMarks_pts`,
`…Inf_pts`), the word-shape event (`R(1)` on the selected right arc or not), and the shifted canonical pocket chart of
`PocketStopWallsField` — is carried out with the chart explicit
(`Lemma725RefChartGen.pocketChartFieldStatement_of_stop`), so that it produces
`Lemma725RefSafe.PocketChartFieldStatement` (the named input of `href725` left by PROVE-LEMMA725REF3).

The determination `hdet` is the one additional named input, `PocketHistDet` (per word-shape event: the killed relative
history is a Borel function of a walls' record and the pocket field read in the shifted canonical chart, for every
walls-measurable branch integer and constant); `PocketDetInput`/`…Inf` quantify it over the word-shape events and
Jordan coordinates as `PocketStopWallsInput` does. It is Aux. lemma 125's "Recovering the local curve from its local
field" (p. 398): the ambient recovery, Proposition 5.13 and the measurable pocket erasure (`Lemma725RefDet*`).

## Main results

* `PocketHistDet`, `PocketDetInput`, `PocketDetInputInf` (the named determination input);
* `pocketChartField_cfPocket`, `pocketChartField_cfPocketInf`: one word-shape event;
* `pocketChartField_of_cfPocketConfig`, `pocketChartField_of_cfPocketConfigInf`: the word-shape selection;
* **`pocketChartField_of_changeConfig'`**: `PocketChartFieldStatement κ′ r_L r_R` from a random change pocket of either
  kind with `PocketStopWallsInput`/`…Inf` and `PocketDetInput`/`…Inf`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma725RefChart

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe

universe u

/-! ### The named determination input -/

section Defs

variable {Ω : Type u}

/-- **Named input: the determination of the killed relative pocket history** (Aux. lemma 125's "Recovering the local
curve from its local field", p. 398; Astra's shortcut note, Proposition 2.1 step 3: the ambient recovery,
Proposition 5.13 and the measurable pocket erasure). For every walls-measurable branch integer `n` and every constant
`a`, almost surely on the word-shape event `A` the killed relative history of the traversal `γ` with marks `xL`, `xR`
is a Borel function of a record `E` measurable for the walls' σ-algebra `𝓦` (standard Borel) and of the pocket field
`chartTransport c 1 a χ(κ) h` read in the shifted canonical pocket chart `c = shiftChart (pChart A C ψ) n`. -/
def PocketHistDet (κ : ℝ) {nL nR : ℕ} (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (C : Ω → Set ℂ)
    (ψ : Ω → ℂ → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ a : ℝ, ∃ (ε : Type u) (_ : MeasurableSpace ε) (_ : StandardBorelSpace ε)
    (E : Ω → ε) (g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1)),
    Measurable[𝓦] E ∧ Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ A → ∀ hc : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal,
        killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
          (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) ω =
            g (E ω, Chart.chartTransport hc 1 a (chiC κ) (h ω))

/-- **The determination input on every word-shape event** (bounded change pocket; the companion of
`PocketStopWallsInput`). -/
def PocketDetInput (κ : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketHistDet (16 / κ) 𝓦 P A (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
        (fun ω => cfPocket (R ω) (L ω) r) ψ h) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketHistDet (16 / κ) 𝓦 P A (travAll R L r η ψ) marksL1All (marksRAll L r ψ)
        (fun ω => cfPocket (R ω) (L ω) r) ψ h)

/-- **The determination input on every word-shape event** (change pocket opening at the flow seed). -/
def PocketDetInputInf (κ : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketHistDet (16 / κ) 𝓦 P A (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
        (fun ω => cfPocket (R ω) (L ω) r) ψ h) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketHistDet (16 / κ) 𝓦 P A (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ)
        (fun ω => cfPocket (R ω) (L ω) r) ψ h)

end Defs

/-! ### One word-shape event -/

section Word

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketChartFieldStatement` on one word-shape event of a bounded change pocket**: as
`PocketStopField.pocketStopField_cfPocket` and `PocketStop.pocketStopChartLaw_cfPocket`, with the chart of
`PocketStopWallsField` kept explicit (every geometric hypothesis of `pocketChartFieldStatement_of_stop` comes from the
counterflow pocket configuration) and the determination `PocketHistDet`. -/
theorem pocketChartField_cfPocket [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketStopWallsField κ ρL ρR 𝓦 P A (travAll R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull R L r W η ψ) h₀ u)
    (hdet : PocketHistDet κ 𝓦 P A (travAll R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨n, a, hn, hq⟩ := hin
  obtain ⟨ε, mε, hSBε, E, g, hEm, hg, hdetω⟩ := hdet n hn a
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAll R L r η ψ ω u ∈ H ∧ M < ‖travAll R L r η ψ ω u‖ := fun ω hω =>
    (hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ hψm
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hP : ∀ ω ∈ A, Sec6.IsReversePocket (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r)
      (cfArcL (R ω) (L ω) r) (cfBeta (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG hω)).conf (hcfg ω (hAG hω)).bounded)
      (hcfg ω (hAG hω)).trace (hcfg ω (hAG hω)).continuous_W (hcfg ω (hAG hω)).W_zero (hcfg ω (hAG hω)).revR
      (hcfg ω (hAG hω)).revL (hcfg ω (hAG hω)).visR
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (ψ ω) := fun ω hω => by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ ω hω
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  exact pocketChartFieldStatement_of_stop hρL hρR hsL hsR h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2) hxLm hxRm hseedL hseedR hxLd hxRd hxLi hxRi
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1)
    hCm hψm' (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTime (hP ω hω) (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1) (fun q => (hq q).2) hEm hg
    hdetω

/-- **`PocketChartFieldStatement` on one word-shape event of a change pocket opening at the flow seed** (as
`pocketChartField_cfPocket`, for `IsCfPocketConfigInf`, the traversal `travAllInf` and the hulls `stopHullInf`). -/
theorem pocketChartField_cfPocketInf [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketStopWallsField κ ρL ρR 𝓦 P A (travAllInf R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHullInf R L r W η ψ) h₀ u)
    (hdet : PocketHistDet κ 𝓦 P A (travAllInf R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨n, a, hn, hq⟩ := hin
  obtain ⟨ε, mε, hSBε, E, g, hEm, hg, hdetω⟩ := hdet n hn a
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAllInf R L r η ψ ω u ∈ H ∧ M < ‖travAllInf R L r η ψ ω u‖ := fun ω hω =>
    (hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hP : ∀ ω ∈ A, Sec6.IsReversePocketInf (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r)
      (cfArcLInf (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).isReversePocketInf
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) :=
    fun ω hω => by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  exact pocketChartFieldStatement_of_stop hρL hρR hsL hsR h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2) hxLm hxRm hseedL hseedR hxLd hxRd hxLi hxRi
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1)
    hCm hψm' (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1) (fun q => (hq q).2) hEm hg
    hdetω

end Word

end InteractingSLE.Sec7.Lemma725RefChart
