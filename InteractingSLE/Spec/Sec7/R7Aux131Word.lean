/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7Aux131Stop
import InteractingSLE.Spec.Sec7.R7Aux131Good
import InteractingSLE.Spec.Sec7.Lemma725RefMarksWord
import InteractingSLE.Spec.Sec7.PocketStopMarkedWire

/-!
# Aux. lemma 131's pocket: the two-seed word on the change pocket of two constant-angle walls

Packet PROVE-R7-AUX131. Specification §7.4.1, proof of Aux. lemma 131 (`source/spec/p385-432.md` L527–L548,
pp. 414–416): "Select the first rationally labelled noncontact interval in a fixed enumeration. Its two endpoint
contacts and their corresponding left-path parameters determine a Jordan pocket by Aux. lemma 33. The choice is
measurable from the two incoming paths. An endpoint may be the original seed or target; the compactified Jordan
argument includes both cases. There are no angle-change marks in this pocket. […] The inversion in Aux. lemma 120
therefore gives exactly the seed weights `(r_L, r_R)` in (CS13.3), with no distant force marks. […] The resulting
erased traversal is continuous from the entry endpoint to the terminal endpoint. […] Aux. lemma 125 now supplies its
full canonical field–path kernel, field determination, and infinite relative capacity lifetime. […] The Jordan
boundary homeomorphism sends the actual terminal endpoint of this complete traversal to infinity."

For two walls `R` (right) and `L` (left) and a parameter `r` of `L` off `R`, `PocketCoord.changePocket R L r` is the
Jordan pocket of the noncontact interval of `L` containing `r` (Aux. lemma 33; `IsChangeConfigInc` asks nothing about
angle changes). For constant-angle walls the pocket carries the constant two-seed word `SLE_κ(r_L; r_R)` with no
other marks. This file proves `R7PocketStopStatement κ r_L r_R GoodR7` from such a pocket:

* **`r7PocketStop_cfPocket`** (bounded pocket) and **`r7PocketStop_cfPocketInf`** (pocket opening at the flow seed):
  from the counterflow configuration on a walls' event, a measurable Jordan coordinate, the walls union law at the
  left end `T⁰(q)` and the two-seed side limits (`PocketStopWallsField` for the two-seed word), a standard Borel
  record of the walls, Proposition 5.13 and the counterflow's continuity. The union law at `T(q)` (R67), the pocket
  chart, the driven traversal with large points, the pocket-inclusion events, the exterior decomposition with its
  record, the measurable erasure and **the transience `GoodR7` (CS13.2)** are proved;
* `TwoSeedWallsInput`, `TwoSeedWallsInputInf`: the remaining field-level inputs on every walls' sub-event;
* **`r7PocketStop_of_changeConfig`**: the bounded pocket where it has positive probability, the pocket opening at the
  flow seed otherwise (the flow-chart orientation gives the Jordan coordinates);
* **`twoSeedWallsInput_of_sideLimit`**, **`twoSeedWallsInputInf_of_sideLimit`**: the walls law at `T⁰(q)` discharged
  by STRIPSYS43's `pocketStopWallsLaw_stopHull0_marked` (the walls are field-determined and entrance-local flow
  lines of the counterflow's coupling); only the two-seed side limits remain.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7Aux131

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket

universe u

/-! ### One pocket shape -/

section Word

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from a bounded change pocket of two walls with the two-seed word**:
the counterflow configuration on the walls' event `G`, a walls' sub-event `A` of positive probability with a
point-measurable Jordan coordinate, the two-seed walls data at the left end `T⁰(q)` (`PocketStopWallsField`: the walls
union law and the two-seed side limits), a standard Borel record `E₀` of the walls, Proposition 5.13 and the
counterflow's continuity. -/
theorem r7PocketStop_cfPocket [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketStopWallsField κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 𝓦 P A (travAll R L r η ψ)
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r W η ψ) h₀ u)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAll R L r η ψ ω u ∈ H ∧ M < ‖travAll R L r η ψ ω u‖ := fun ω hω =>
    (hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
    PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ hψm
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
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
  have hers := pocketErasure_cfPocket (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) h𝓦 hRm hLm hGm
    hcfg hηc hηm hA hAG hψ hψm measurable_const measurable_const hE₀ hgen
  exact r7PocketStopStatement_of_stop_marks h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun U hUo hUH => measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH)
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTime (hP ω hω) (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1))
    (fun q => (hq q).2)
    (Eventually.of_forall fun ω hω hL => goodR7_cfTraversal (hcfg ω (hAG hω)) (hψ ω hω) hL) hE₀ hgen h513 hers

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from a change pocket of two walls opening at the flow seed with the
two-seed word** (as `r7PocketStop_cfPocket`, for `IsCfPocketConfigInf`, `travAllInf`, `stopHull0Inf`). -/
theorem r7PocketStop_cfPocketInf [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hPA : 0 < P A) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketStopWallsField κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 𝓦 P A (travAllInf R L r η ψ)
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0Inf R L r W η ψ) h₀ u)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hdrive : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travAllInf R L r η ψ ω u ∈ H ∧ M < ‖travAllInf R L r η ψ ω u‖ := fun ω hω =>
    (hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
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
  have hers := pocketErasure_cfPocketInf (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) h𝓦 hRm hLm
    hGm hcfg hηc hηm hA hAG hψ hψm measurable_const measurable_const hE₀ hgen
  exact r7PocketStopStatement_of_stop_marks h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun U hUo hUH => measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH)
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_stopHullInf_of_stopHull0Inf hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1))
    (fun q => (hq q).2)
    (Eventually.of_forall fun ω hω hL => goodR7_cfTraversalInf (hcfg ω (hAG hω)) (hψ ω hω) hL) hE₀ hgen h513 hers

end Word

/-! ### The remaining inputs on every walls' sub-event, and the shape selection -/

section Defs

variable {Ω : Type*}

/-- **The remaining two-seed field-level inputs of a bounded change pocket** on every walls' sub-event `A ⊆ G` of
positive probability and for every point-measurable Jordan coordinate: the walls union law at the left end `T⁰(q)` and
the two-seed side limits (`PocketStopWallsField` for the word `(r_L; r_R)` with the seed marks). -/
def TwoSeedWallsInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    PocketStopWallsField κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 𝓦 P A (travAll R L r η ψ)
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r W η ψ) h₀ u

/-- **The remaining two-seed field-level inputs of a change pocket opening at the flow seed.** -/
def TwoSeedWallsInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    PocketStopWallsField κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 𝓦 P A (travAllInf R L r η ψ)
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0Inf R L r W η ψ) h₀ u

end Defs

section Select

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from a random change pocket of two walls of either kind** (Aux. lemma
131: "An endpoint may be the original seed or target; the compactified Jordan argument includes both cases"): on the
walls' event `G` of positive probability the change configuration, the bounded counterflow configuration where
`0 < rightLo` and the one opening at the flow seed where `rightLo = 0`; the measurable Jordan coordinates are built from
the flow-chart orientation (`exists_measurable_pocketMarks_pts`, `…Inf_pts`), and the bounded pocket is used where it
has positive probability, the pocket opening at the flow seed otherwise. -/
theorem r7PocketStop_of_changeConfig [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G)
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : TwoSeedWallsInput κ rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ u)
    (hinI : TwoSeedWallsInputInf κ rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀ u)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  set Gp := {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} with hGpdef
  have hGpm : MeasurableSet[𝓦] Gp := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).1
  have hG0 : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} = G \ Gp := by
    ext ω
    simp only [hGpdef, mem_ofPred_eq, Set.mem_sdiff, not_and]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  have hseed : ∀ ω ∈ G \ Gp, rightLo (R ω) (L ω) r = 0 := fun ω hω =>
    le_antisymm (not_lt.1 fun h => hω.2 ⟨hω.1, h⟩) ((hconf ω hω.1).changeCorner_props.1.1)
  by_cases hp : 0 < P Gp
  · have hcfg' : ∀ ω ∈ Gp, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω) := fun ω hω => hcfg ω hω.1 hω.2
    obtain ⟨ψ, hψ, hψm, -⟩ := exists_measurable_pocketMarks_pts (mΩ := 𝓦) hRm hLm hGpm
      (fun ω hω => (hcfg' ω hω).conf)
      (fun ω hω => zero_notMem_closure_of_rightLo_pos (hcfg' ω hω).conf (hcfg' ω hω).bounded)
      (fun ω hω => (hcfg' ω hω).oriented) (discTime 1)
    exact r7PocketStop_cfPocket h𝓦 hRm hLm hGpm hcfg' hηc hηm hGpm subset_rfl hp hψ hψm hh₀ hu hub
      (hin Gp hGpm subset_rfl hp ψ hψ hψm) hE₀ hgen h513
  · have hPA : 0 < P (G \ Gp) := by
      have h1 : P G ≤ P (G ∩ Gp) + P (G \ Gp) := measure_le_inter_add_sdiff P G Gp
      have h2 : P (G ∩ Gp) = 0 := measure_mono_null inter_subset_right (le_antisymm (not_lt.1 hp) zero_le)
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    rw [hG0] at hinI
    have hGm' : MeasurableSet[𝓦] (G \ Gp) := hGm.diff hGpm
    have hcfg' : ∀ ω ∈ G \ Gp, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω) := fun ω hω =>
      hcfgI ω hω.1 (hseed ω hω)
    obtain ⟨ψ, hψ, hψm, -⟩ := exists_measurable_pocketMarksInf_pts (mΩ := 𝓦) hRm hLm hGm'
      (fun ω hω => (hcfg' ω hω).conf) (fun ω hω => (hcfg' ω hω).seed) (fun ω hω => (hcfg' ω hω).oriented)
      (discTime 1)
    exact r7PocketStop_cfPocketInf h𝓦 hRm hLm hGm' hcfg' hηc hηm hGm' subset_rfl hPA hψ hψm hh₀ hu hub
      (hinI (G \ Gp) hGm' subset_rfl hPA ψ hψ hψm) hE₀ hgen h513

end Select

/-! ### The walls law discharged: only the two-seed side limits remain -/

section Wire

variable {Ω : Type*}

open PocketStopMarked PocketStopWalls

/-- **`TwoSeedWallsInput` from the two-seed side limits** (bounded pocket): the walls law at `T⁰(q)` is
`PocketStopMarked.pocketStopWallsLaw_stopHull0_marked` (STRIPSYS43), for the counterflow a frozen coupling with almost
surely infinite lifetime, `ζ′ = ∞` on `G`, field-determined and entrance-local walls, and the marks' σ-algebra
`𝓦 ≤ σ(fullHist ![R, L]) ∨ 𝓕_0` (one pair of walls: STRIPSYS43's per-`q` obstruction does not arise). -/
theorem twoSeedWallsInput_of_sideLimit {κ rL rR : ℝ}
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) (u : ℂ → ℝ)
    (hside : ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a (centredField h'' u₀') u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q) :
    TwoSeedWallsInput κ rL rR 𝓦 P R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η G (centredField h'' u₀') u := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  obtain ⟨n, a', hn, hS⟩ := hside A hA hAG hPA ψ hψ hψm
  exact ⟨n, a', hn, fun q => ⟨pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0
    hRm hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω))
    (fun ω hω => hζG ω (hAG hω)) hψ hψm q, hS q⟩⟩

/-- **`TwoSeedWallsInputInf` from the two-seed side limits** (pocket opening at the flow seed). -/
theorem twoSeedWallsInputInf_of_sideLimit {κ rL rR : ℝ}
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) (u : ℂ → ℝ)
    (hside : ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a (centredField h'' u₀') u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q) :
    TwoSeedWallsInputInf κ rL rR 𝓦 P R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η G (centredField h'' u₀') u := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  obtain ⟨n, a', hn, hS⟩ := hside A hA hAG hPA ψ hψ hψm
  exact ⟨n, a', hn, fun q => ⟨pocketStopWallsLaw_stopHull0Inf_marked hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0
    hL0 hRm hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω))
    (fun ω hω => hζG ω (hAG hω)) hψ hψm q, hS q⟩⟩

end Wire

end InteractingSLE.Sec7.R7Aux131
