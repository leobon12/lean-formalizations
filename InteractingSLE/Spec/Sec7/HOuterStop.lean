/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterUnion

/-!
# Theorem R.7's outer pockets: the stop-level statement from one mixed or outer pocket

Packet PROVE-HOUTER. Proof of Theorem R.7 (`source/spec/p433-480.md` L1058–L1068, pp. 477–478): "The traversal
argument above gives a complete continuous relative trace, and Lemma R.5 and its corollary give every stopped Gaussian
kernel. […] Aux. 124–125 give its full field–path joint kernel and determining graph."

The landed Aux. 131 template (`R7Aux131.r7PocketStop_cfPocket(Inf)`, `R7Aux131.r7PocketStop_of_changeConfig`) derives
`R7Pocket.R7PocketStopStatement` from a contained (reverse-visited) change pocket. Here the same is done for a mixed or
outer change pocket (`IsOuterCfg`, `IsOuterCfgInf`: the erasure facts and the relative Loewner conclusion in place of
the reverse pocket), with the SAME field-level inputs as the contained case (`R7Aux131.TwoSeedWallsInput(Inf)`: the
walls' marked union law at the ambient stop `T⁰(q)` and the two-seed side limits), and with the hull sets chosen as the
relative hull sets `relHull` (the relative active domain of a mixed or outer pocket is not `C ∩ D_{T(q)}`):

* `pocketStopUnionLaw_outer`, `pocketStopUnionLaw_outerInf`: the union law of the relative complement from the walls'
  law at `T⁰(q)` (`pocketStopUnionLaw_relHull_of_wallsLaw` with `relDomain_subset_domain_ambTime0(Inf)` and
  `mem_hull_of_mem_image(Inf)`);
* **`r7PocketStop_outerPocket`**, **`r7PocketStop_outerPocketInf`**: `R7PocketStopStatement κ r_L r_R GoodR7` from one
  random outer pocket on a walls' event with the walls data `PocketStopWallsField`, a standard Borel walls record and
  Proposition 5.13 (as `R7Aux131.r7PocketStop_cfPocket(Inf)`);
* **`r7PocketStop_of_outerConfig`**: the shape selection (bounded where it has positive probability, opening at the
  flow seed otherwise), with the measurable Jordan coordinates from the flow-chart orientation.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Bornology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.HOuter

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin Lemma725RefMarks R7Pocket R7Aux131 R7StopIn

universe u

/-! ### The union law of the relative complement for the change pocket -/

section Union

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ}
  {r : ℝ≥0} {G A : Set Ω} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- **The union law of the relative complement of a bounded outer pocket** from the walls' marked union law at the
ambient stop `T⁰(q)` (`stopHull0`). -/
theorem pocketStopUnionLaw_outer (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0 R L r W η ψ q) h₀ q) :
    PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (fun ω => relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAll R L r η ψ ω) q) h₀ q := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (ψ ω) := fun ω hω => by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]
    exact hψ ω hω
  refine pocketStopUnionLaw_relHull_of_wallsLaw h𝓦 hpre hCm hψm'
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (cfPocket_walls_props (hG ω (hAG hω))).1) (fun ω hω => (cfPocket_walls_props (hG ω (hAG hω))).2)
    (fun ω hω => (hψ ω hω).2.2.2.1.1.continuousOn) (fun ω hω => (hψ ω hω).2.2.2.1.2.mapsTo)
    (fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1) (fun ω hω hq => ?_) (fun ω hω hq y hy hyZ => ?_) hW
  · have hc := hcfg ω (hAG hω)
    have hCb : IsBounded (cfPocket (R ω) (L ω) r) :=
      isBounded_image_negInv (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
    exact relDomain_subset_domain_ambTime0 hc.erase hc.trace hc.continuous_W hc.W_zero (hCH ω hω) hCb (hψ' ω hω)
      (hc.props (hψ ω hω)).1 q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)
  · have hc := hcfg ω (hAG hω)
    have hL := hc.erase.clock_σ_pos
    have h0 := capInv_nonneg (travAll R L r η ψ ω) q
    have hZ : ψ ω y ∈ (fun v => ψ ω (Sec6.erasedPath (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) v)) ''
        Icc 0 (clockOf (Sec6.pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
          (capInv (travAll R L r η ψ ω) q)) := by
      rw [← image_relCurve_Icc _ hL h0]; exact hyZ
    exact mem_hull_of_mem_image hc.erase hc.trace (hCH ω hω) (hψ' ω hω) (clockOf_mem_Ico hL h0) hy hZ

/-- **The union law of the relative complement of an outer pocket opening at the flow seed** from the walls' marked
union law at the ambient stop `T⁰(q)` (`stopHull0Inf`). -/
theorem pocketStopUnionLaw_outerInf (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0Inf R L r W η ψ q) h₀ q) :
    PocketStopUnionLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (fun ω => relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAllInf R L r η ψ ω) q) h₀ q := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) :=
    fun ω hω => by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
  refine pocketStopUnionLaw_relHull_of_wallsLaw h𝓦 hpre hCm hψm'
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (cfPocket_walls_props (hG ω (hAG hω))).1) (fun ω hω => (cfPocket_walls_props (hG ω (hAG hω))).2)
    (fun ω hω => (hψ ω hω).2.2.2.1.1.continuousOn) (fun ω hω => (hψ ω hω).2.2.2.1.2.mapsTo)
    (fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1) (fun ω hω hq => ?_) (fun ω hω hq y hy hyZ => ?_) hW
  · have hc := hcfg ω (hAG hω)
    exact relDomain_subset_domain_ambTime0Inf hc.erase hc.trace (hCH ω hω) (hψ' ω hω)
      (hc.props (hψ ω hω)).1 q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)
  · have hc := hcfg ω (hAG hω)
    have hL := hc.erase.clockEnd_pos
    have h0 := capInv_nonneg (travAllInf R L r η ψ ω) q
    have hZ : ψ ω y ∈ (fun v => ψ ω (Sec6.erasedPathInf (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v)) ''
        Icc 0 (clockOf (Sec6.clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
          (capInv (travAllInf R L r η ψ ω) q)) := by
      rw [← image_relCurve_Icc _ hL h0]; exact hyZ
    exact mem_hull_of_mem_imageInf hc.erase hc.trace (hCH ω hω) (hψ' ω hω) (clockOf_mem_Ico hL h0) hy hZ

end Union

/-! ### One outer pocket shape -/

section Word

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from a bounded mixed or outer change pocket with the two-seed word**
(`R7Aux131.r7PocketStop_cfPocket` for `IsOuterCfg`): the outer configuration on the walls' event `G`, a walls'
sub-event `A` of positive probability with a point-measurable Jordan coordinate, the two-seed walls data at the left
fibre end `T⁰(q)` (`PocketStopWallsField`: the walls union law and the two-seed side limits), a standard Borel record
`E₀` of the walls, Proposition 5.13 and the counterflow's continuity. The hull sets of the conclusion are the
relative hull sets `relHull`. -/
theorem r7PocketStop_outerPocket [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
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
  have hdrive := fun ω (hω : ω ∈ A) => (hcfg ω (hAG hω)).props (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u := fun u hu =>
    measurable_travAll_outer h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hers := pocketErasure_outer (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) h𝓦 hRm hLm hGm
    hcfg hηc hηm hA hAG hψ hψm measurable_const measurable_const hE₀ hgen
  exact r7PocketStopStatement_of_stop_marks (F := fun q ω => relHull (cfPocket (R ω) (L ω) r) (ψ ω)
      (travAll R L r η ψ ω) q) h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2.1) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun U hUo hUH => measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH)
    (fun q ω hω hq => isOpen_H_diff_relHull (hCo ω hω) (hCH ω hω) (hψ ω hω).2.2.2.1.1.continuousOn
      (hdrive ω hω).1 hq)
    (fun q ω hω _ => image_inter_H_diff_relHull (hCH ω hω) (hψ ω hω).2.2.2.1 _ q) hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_outer h𝓦 hRm hLm hGm hcfg hA hAG hψ hψm (hpre q) (hq q).1)
    (fun q => (hq q).2)
    (Eventually.of_forall fun ω hω hL => (hdrive ω hω).2.2.2 hL) hE₀ hgen h513 hers

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from a mixed or outer change pocket opening at the flow seed with the
two-seed word** (`R7Aux131.r7PocketStop_cfPocketInf` for `IsOuterCfgInf`). -/
theorem r7PocketStop_outerPocketInf [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
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
  have hdrive := fun ω (hω : ω ∈ A) => (hcfg ω (hAG hω)).props (hψ ω hω)
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travAllInf_outer h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => (hdrive ω hω).1) hγm
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hers := pocketErasure_outerInf (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) h𝓦 hRm hLm
    hGm hcfg hηc hηm hA hAG hψ hψm measurable_const measurable_const hE₀ hgen
  exact r7PocketStopStatement_of_stop_marks (F := fun q ω => relHull (cfPocket (R ω) (L ω) r) (ψ ω)
      (travAllInf R L r η ψ ω) q) h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2.1) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun U hUo hUH => measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH)
    (fun q ω hω hq => isOpen_H_diff_relHull (hCo ω hω) (hCH ω hω) (hψ ω hω).2.2.2.1.1.continuousOn
      (hdrive ω hω).1 hq)
    (fun q ω hω _ => image_inter_H_diff_relHull (hCH ω hω) (hψ ω hω).2.2.2.1 _ q) hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_outerInf h𝓦 hRm hLm hGm hcfg hA hAG hψ hψm (hpre q) (hq q).1)
    (fun q => (hq q).2)
    (Eventually.of_forall fun ω hω hL => (hdrive ω hω).2.2.2 hL) hE₀ hgen h513 hers

end Word

/-! ### The shape selection -/

section Select

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`R7PocketStopStatement κ r_L r_R GoodR7` from a random mixed or outer change pocket of two walls of either
kind** (`R7Aux131.r7PocketStop_of_changeConfig` for `IsOuterCfg`, `IsOuterCfgInf`): on the walls' event `G` of
positive probability the change configuration, the bounded outer configuration where `0 < rightLo` and the one opening
at the flow seed where `rightLo = 0`; the field-level inputs are exactly the contained case's
`R7Aux131.TwoSeedWallsInput(Inf)`. -/
theorem r7PocketStop_of_outerConfig [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G)
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
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
  · have hcfg' : ∀ ω ∈ Gp, IsOuterCfg (R ω) (L ω) r (W ω) (η ω) := fun ω hω => hcfg ω hω.1 hω.2
    obtain ⟨ψ, hψ, hψm, -⟩ := exists_measurable_pocketMarks_pts (mΩ := 𝓦) hRm hLm hGpm
      (fun ω hω => (hcfg' ω hω).conf)
      (fun ω hω => zero_notMem_closure_of_rightLo_pos (hcfg' ω hω).conf (hcfg' ω hω).bounded)
      (fun ω hω => (hcfg' ω hω).oriented) (discTime 1)
    exact r7PocketStop_outerPocket h𝓦 hRm hLm hGpm hcfg' hηc hηm hGpm subset_rfl hp hψ hψm hh₀ hu hub
      (hin Gp hGpm subset_rfl hp ψ hψ hψm) hE₀ hgen h513
  · have hPA : 0 < P (G \ Gp) := by
      have h1 : P G ≤ P (G ∩ Gp) + P (G \ Gp) := measure_le_inter_add_sdiff P G Gp
      have h2 : P (G ∩ Gp) = 0 := measure_mono_null inter_subset_right (le_antisymm (not_lt.1 hp) zero_le)
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    rw [hG0] at hinI
    have hGm' : MeasurableSet[𝓦] (G \ Gp) := hGm.diff hGpm
    have hcfg' : ∀ ω ∈ G \ Gp, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω) := fun ω hω =>
      hcfgI ω hω.1 (hseed ω hω)
    obtain ⟨ψ, hψ, hψm, -⟩ := exists_measurable_pocketMarksInf_pts (mΩ := 𝓦) hRm hLm hGm'
      (fun ω hω => (hcfg' ω hω).conf) (fun ω hω => (hcfg' ω hω).seed) (fun ω hω => (hcfg' ω hω).oriented)
      (discTime 1)
    exact r7PocketStop_outerPocketInf h𝓦 hRm hLm hGm' hcfg' hηc hηm hGm' subset_rfl hPA hψ hψm hh₀ hu hub
      (hinI (G \ Gp) hGm' subset_rfl hPA ψ hψ hψm) hE₀ hgen h513

end Select

end InteractingSLE.Sec7.HOuter
