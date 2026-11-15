/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OLawPocket
import InteractingSLE.Spec.Sec7.R5OutCut
import InteractingSLE.Spec.Sec7.R5OutDomain
import InteractingSLE.Spec.Sec7.R5EnlR7Walls

/-!
# R.5's enlarged-stop increment law on an outer R.7 test (bounded outer pocket)

Packet PROVE-R5-OUTERLAW (ruling R88). The outer twin of `PocketStopMarked.r7HasOldChartIncrementLawOn`
(PROVE-R5-ENLARGED). On an outer test (`HOuter.IsOuterCfg`) the current domain is the relative domain
`C ∩ (ℍ ∖ relHull_q)` (the component incident to the pocket target), not `C ∩ (ℍ ∖ K_{T⁰(q)})`, so the three
union laws of Lemma R.5's proof are

* the reference law at the original time `s` (`R5Phase.pocketStopUnionLaw_ref`, for every change pocket), set
  `B = (ℍ ∖ C) ∪ K̃_s`;
* the current law at `T⁰(q)` for the **relative hull** `relHull C ψ γ q` (`pocketStopUnionLaw_outer_fix`: the proof of
  `HOuter.pocketStopUnionLaw_outer` with the coordinate's measurability at fixed points only, so that the marks may be
  the stopped information `markedStopSigma T⁰(q)`), from PROVE-R5-OUTER's walls law
  `R5Out.pocketStopWallsLaw_stopHull0_markedStop`;
* the enlarged law at `T⁰(q) ∨ s` for the relative hull of the **cut pocket** `C ∩ (ℍ ∖ K̃_s)`
  (`R5Out.pocketStopUnionLaw_relativeCut` with the walls law `R5Out.pocketStopWallsLaw_regHull_max_markedStop`:
  `pocketStopUnionLaw_outer_cut`).

On `{s ≤ T⁰(q)}` the two relative hulls agree and contain `K̃_s` (`outer_relHull_cut_eq`, `regHull_subset_relHull`).
**`r7HasOldChartIncrementLawOn_outer`** assembles the conditioned increment law for every reference chart `old` of one
component of `ℍ ∖ B`, through `R5OLaw.hasOldChartIncrementLawOn_of_pocketLaws_stop_comp`.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Bornology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5OLaw

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopWallsFin R5Enl PocketTraversal
  PocketAdapt Lemma725RefMarks Sec6 R7StopIn PocketStopMarked PocketWordPerQ LocalSets

/-! ### Pathwise facts of an outer pocket at a live capacity -/

section Path

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}

/-- **The relative active domain of an outer pocket misses the ambient hull at `T⁰(q)`.** -/
theorem outer_relDom_subset (hc : HOuter.IsOuterCfg R L r W η) (hψ : IsCfJordan R L r ψ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (cfTraversal R L r η ψ)) :
    cfPocket R L r ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (cfTraversal R L r η ψ) s.toNNReal) q) ⊆
      H \ fwdHull W (ambTime0 η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) ψ q) := by
  have hCH : cfPocket R L r ⊆ H := PocketJordan.image_negInv_subset_H hc.conf.changePocket_subset_H
  have hCb : IsBounded (cfPocket R L r) :=
    isBounded_image_negInv (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
  have hψ' : Sec6.IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]
    exact hψ
  exact HOuter.relDomain_subset_domain_ambTime0 hc.erase hc.trace hc.continuous_W hc.W_zero hCH hCb hψ'
    (hc.props hψ).1 q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)

/-- **A pocket point whose image is on the traversal's prefix up to `q` is in the ambient hull at `T⁰(q)`.** -/
theorem outer_mem_hull_of_prefix (hc : HOuter.IsOuterCfg R L r W η) (hψ : IsCfJordan R L r ψ) (q : ℝ≥0)
    {y : ℂ} (hy : y ∈ cfPocket R L r)
    (hyZ : ψ y ∈ cfTraversal R L r η ψ '' Icc 0 (capInv (cfTraversal R L r η ψ) q)) :
    y ∈ fwdHull W (ambTime0 η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) ψ q) := by
  have hCH : cfPocket R L r ⊆ H := PocketJordan.image_negInv_subset_H hc.conf.changePocket_subset_H
  have hψ' : Sec6.IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]
    exact hψ
  have hL := hc.erase.clock_σ_pos
  have h0 := capInv_nonneg (cfTraversal R L r η ψ) q
  have hZ : ψ y ∈ (fun v => ψ (Sec6.erasedPath η (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v)) ''
      Icc 0 (clockOf (Sec6.pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
        (firstHit η (cfArcR R L r 0)) (firstHit η (cfArcR R L r 0)))
        (capInv (cfTraversal R L r η ψ) q)) := by
    rw [← image_relCurve_Icc _ hL h0]; exact hyZ
  exact HOuter.mem_hull_of_mem_image hc.erase hc.trace hCH hψ' (clockOf_mem_Ico hL h0) hy hZ

end Path

/-! ### The relative hulls of the pocket and of the cut pocket -/

section Sets

variable {C K : Set ℂ} {ψ : ℂ → ℂ} {γ : ℝ → ℂ} {q : ℝ≥0}

/-- A set of `ℍ` lies in the relative hull of the pocket cut by it. -/
theorem subset_relHull_inter (hKH : K ⊆ H) : K ⊆ HOuter.relHull (C ∩ (H \ K)) ψ γ q := fun _ hz =>
  ⟨hKH hz, fun h => h.1.2.2 hz⟩

/-- A set of `ℍ` missing the relative active domain lies in the relative hull. -/
theorem subset_relHull_of_disjoint (hKH : K ⊆ H)
    (hdis : ∀ z ∈ C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q), z ∉ K) :
    K ⊆ HOuter.relHull C ψ γ q := fun z hz => ⟨hKH hz, fun h => hdis z h hz⟩

/-- If `K` misses the relative active domain, cutting the pocket by `K` does not change the relative hull. -/
theorem relHull_inter_eq_of_disjoint
    (hdis : ∀ z ∈ C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q), z ∉ K) :
    HOuter.relHull C ψ γ q = HOuter.relHull (C ∩ (H \ K)) ψ γ q := by
  ext z
  simp only [HOuter.relHull, Set.mem_sdiff, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h => hn ⟨h.1.1, h.2⟩⟩
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h => hn ⟨⟨h.1, hz, hdis z ⟨h.1, h.2⟩⟩, h.2⟩⟩

end Sets

/-! ### The current and enlarged union laws of an outer pocket -/

section Union

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ}
  {r : ℝ≥0} {A : Set Ω} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- **The union law of the relative complement of a bounded outer pocket, with the coordinate measurable at fixed
points** (`HOuter.pocketStopUnionLaw_outer`'s proof, whose only use of `IsPointMeasurable` is at fixed points; this
allows marks larger than the walls' σ-algebra). -/
theorem pocketStopUnionLaw_outer_fix {W : Ω → ℝ → ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z)) {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0 R L r W η ψ q) h₀ q) :
    PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (fun ω => HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAll R L r η ψ ω) q) h₀ q := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  exact HOuter.pocketStopUnionLaw_relHull_of_wallsLaw h𝓦 hpre hCm hψm
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => (cfPocket_walls_props (hG ω hω)).1) (fun ω hω => (cfPocket_walls_props (hG ω hω)).2)
    (fun ω hω => (hψ ω hω).2.2.2.1.1.continuousOn) (fun ω hω => (hψ ω hω).2.2.2.1.2.mapsTo)
    (fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1) (fun ω hω hq => outer_relDom_subset (hcfg ω hω) (hψ ω hω) hq)
    (fun ω hω _ y hy hyZ => outer_mem_hull_of_prefix (hcfg ω hω) (hψ ω hω) q hy hyZ) hW

variable {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

omit mΩ in
/-- On the live event the marked stop is the finite `stopTime0`. -/
theorem stopTimeM_eq_of_live {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hl : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    stopTimeM A R L r η ψ q ω = stopTime0 R L r η ψ q ω := by
  unfold stopTimeM
  exact ite_eq_left ⟨hω, hl⟩

omit mΩ in
/-- On the live event the ambient hull at `T⁰(q)` is the regularized hull at the marked stop (outer pocket). -/
theorem stopHull0_eq_regHull_stopTimeM
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hl : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω =
      regHull W' ζ' (stopTimeM A R L r η ψ q ω).toNNReal ω := by
  rw [stopTimeM_eq_of_live hω hl]
  exact PocketStopMarked.Outer.stopHull0_eq_regHull' (hcfg ω hω) (hζA ω hω) q

omit mΩ in
/-- **The relative active domain misses the regularized hull at every original time before `T⁰(q)`** (outer
pocket, `q` live). -/
theorem notMem_regHull_of_relDom
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {q s : ℝ≥0} {ω : Ω}
    (hω : ω ∈ A) (hl : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsT : (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω) :
    ∀ z ∈ cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull (fun t : ℝ =>
      segDriver (travAll R L r η ψ ω) t.toNNReal) q), z ∉ regHull W' ζ' s ω := by
  intro z hz hzs
  have hzT := (outer_relDom_subset (hcfg ω hω) (hψ ω hω) hl hz).2
  have hTlt : stopTimeM A R L r η ψ q ω < ⊤ := by
    rw [stopTimeM_eq_of_live hω hl]; exact ENNReal.ofReal_lt_top
  refine hzT ?_
  change z ∈ stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω
  rw [stopHull0_eq_regHull_stopTimeM hcfg hζA hω hl]
  refine regHull_mono W' ζ' ω ?_ hzs
  simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono hTlt.ne hsT

/-- **The enlarged union law of a bounded outer pocket at `T⁰(q) ∨ s`**: the relative hull of the pocket cut by
`K̃_s` (`R5Out.pocketStopUnionLaw_relativeCut` with the ambient hull `K̃_{T⁰(q) ∨ s}` and the walls' law there). -/
theorem pocketStopUnionLaw_outer_cut (h𝓦 : 𝓦 ≤ mΩ)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (q s : ℝ≥0)
    (hpre : locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r ∩ (H \ regHull W' ζ' s ω)})
    (hψm : ∀ z, Measurable[𝓦]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r ∩ (H \ regHull W' ζ' s ω)}.indicator fun ω => ψ ω z))
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (fun ω => regHull W' ζ' (max (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞)).toNNReal ω) h₀ q) :
    PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (fun ω => HOuter.relHull (cfPocket (R ω) (L ω) r ∩ (H \ regHull W' ζ' s ω)) (ψ ω)
        (travAll R L r η ψ ω) q) h₀ q := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hTlt : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → stopTimeM A R L r η ψ q ω < ⊤ :=
    fun ω hω hl => by rw [stopTimeM_eq_of_live hω hl]; exact ENNReal.ofReal_lt_top
  have hmono : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      regHull W' ζ' (stopTimeM A R L r η ψ q ω).toNNReal ω ⊆
        regHull W' ζ' (max (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞)).toNNReal ω ∧
      regHull W' ζ' s ω ⊆ regHull W' ζ' (max (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞)).toNNReal ω := by
    intro ω hω hl
    have hne : max (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞) ≠ ⊤ := (max_lt (hTlt ω hω hl) ENNReal.coe_lt_top).ne
    exact ⟨regHull_mono W' ζ' ω (ENNReal.toNNReal_mono hne (le_max_left _ _)),
      regHull_mono W' ζ' ω (by simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono hne (le_max_right _ _))⟩
  refine R5Out.pocketStopUnionLaw_relativeCut h𝓦 hpre
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω _ => R5Phase.isOpen_H_diff_regHull W' ζ' s ω) hCm hψm
    (fun ω hω => (cfPocket_walls_props (hG ω hω)).1) (fun ω hω => (cfPocket_walls_props (hG ω hω)).2)
    (fun ω hω => (hψ ω hω).2.2.2.1.1.continuousOn) (fun ω hω => (hψ ω hω).2.2.2.1.2.mapsTo)
    (fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1) (fun ω hω hl => (hmono ω hω hl).2)
    (fun ω hω hl z hz => ?_) (fun ω hω hl y hy hyZ => ?_) hW
  · obtain ⟨⟨hzC, hzs⟩, hzψ⟩ := hz
    have hzT := outer_relDom_subset (hcfg ω hω) (hψ ω hω) hl ⟨hzC, hzψ⟩
    change z ∈ H \ stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω at hzT
    rw [stopHull0_eq_regHull_stopTimeM hcfg hζA hω hl] at hzT
    rcases le_total (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞) with hle | hle
    · rw [max_eq_right hle, ENNReal.toNNReal_coe]; exact hzs
    · rw [max_eq_left hle]; exact hzT
  · have hyT := outer_mem_hull_of_prefix (hcfg ω hω) (hψ ω hω) q hy.1 hyZ
    change y ∈ stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q ω at hyT
    rw [stopHull0_eq_regHull_stopTimeM hcfg hζA hω hl] at hyT
    exact (hmono ω hω hl).1 hyT

end Union

/-! ### A point off the regularized hull at a fixed time -/

section RegHull

variable {Ω : Type*} {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A fixed point off the regularized hull at a fixed time `t` is an `𝓕_t`-event** (`ℍ ∖ K̃_t` is open; balls
around the point avoiding the hull are `𝓕_t`-events, `PocketStopWallsFin.measurableSet_disjoint_regHull`). -/
theorem measurableSet_mem_H_diff_regHull [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (t : ℝ≥0) (z : ℂ) :
    MeasurableSet[drivingFiltration P hX t] {ω | z ∈ H \ regHull W ζ t ω} := by
  by_cases hz : z ∈ H
  · obtain ⟨ρ, hρ, hρH⟩ := Metric.isOpen_iff.1 QuantumZipper.isOpen_H z hz
    have e : {ω | z ∈ H \ regHull W ζ t ω} =
        ⋃ n : ℕ, {ω | Disjoint (regHull W ζ t ω) (Metric.ball z (ρ / ((n : ℝ) + 1)))} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hzd
        obtain ⟨e, he, heB⟩ := Metric.isOpen_iff.1 (R5Phase.isOpen_H_diff_regHull W ζ t ω) z hzd
        obtain ⟨n, hn⟩ := exists_nat_gt (ρ / e)
        refine ⟨n, Set.disjoint_left.2 fun w hwB hw => (heB (Metric.ball_subset_ball ?_ hw)).2 hwB⟩
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ he] at hn
        nlinarith
      · rintro ⟨n, hn⟩
        exact ⟨hz, fun hzB => Set.disjoint_left.1 hn hzB (Metric.mem_ball_self (by positivity))⟩
    rw [e]
    refine MeasurableSet.iUnion fun n => measurableSet_disjoint_regHull hC hκ hX hζ t _ Metric.isOpen_ball ?_
    exact (Metric.ball_subset_ball (div_le_self hρ.le
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))).trans hρH
  · have e : {ω | z ∈ H \ regHull W ζ t ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h' => hz h'.1
    rw [e]
    exact @MeasurableSet.empty _ (drivingFiltration P hX t)

end RegHull

/-! ### The R.7 assembly for a bounded outer pocket -/

section R7Inst

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c₀ : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **R.5's enlarged-stop increment law on an outer R.7 test** (bounded outer pocket; clause 4 of
`R5Out.R5ClausesCompOn` for the reference at the original time `s`): from the walls' data, the base chart's facts,
and a reference chart `old` of one component of `ℍ ∖ B` (`B = (ℍ ∖ C) ∪ K̃_s`) on an event `G'` of the reference
record — its domain events `hdom`, forward map `hfwd`, `dom ⊆ ℍ ∖ B` with an open complementary piece, and the current
domain inside its domain when `s ≤ T⁰(q)` and `q` is live — for every pair event `M ⊆ G'` with `s ≤ T⁰(q)` and `q`
live on `M`. The current law is for the relative hull at `T⁰(q)`, the enlarged law for the relative hull of the pocket
cut by `K̃_s` at `T⁰(q) ∨ s`; all three marked laws and every record relation are derived here. -/
theorem r7HasOldChartIncrementLawOn_outer
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (q s : ℝ≥0) {G' : Set Ω}
    (hG' : MeasurableSet[germSigma (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (R5Phase.refInfo P hX R L s) A
        (travAll R L r η ψ) 0] G')
    {old : Ω → Chart} (hOld : ∀ ω ∈ G', (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[germSigma (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (R5Phase.refInfo P hX R L s) A
        (travAll R L r η ψ) 0] (G' ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[germSigma (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (R5Phase.refInfo P hX R L s) A
        (travAll R L r η ψ) 0] ((G' ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldSub : ∀ ω ∈ G', ((old ω).dom : Set ℂ) ⊆
      H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω)
    (hCut : ∀ ω ∈ G', IsOpen ((H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0 ω) \ (old ω).dom))
    (hNest : ∀ ω ∈ G', (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω → ω ∈ A →
      (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ (old ω).dom)
    {M : Set Ω} (hMG : M ⊆ G') (hME : ∀ ω ∈ M, (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω)
    (hMlive : ∀ ω ∈ M, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A (travAll R L r η ψ)
        (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0) (centredField h'' u₀') P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        HasOldChartIncrementLawOn P M old (relChart c (travAll R L r η ψ) q) gOld g := by
  classical
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hh₀ := WholeField.isZeroBoundaryGFF_centredField hC hu₀'
  have h𝓦 := wallsSigma_le_drivingFiltration (P := P) hX R L
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hGpre := PocketStopMarked.Outer.isMarkedStop_stopTimeM h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q
  have hS0pre : locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q ≤
      MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ ⨆ t, drivingFiltration P hX t :=
    fun M hM => PocketStopMarked.Outer.measurableSet_sup_iSup_of_locPrefixSigma h𝓦 hWad hRm' hLm' hGm hG hA hAG
      hcfg hζA hψ hψm q M hM
  have hT := isMarkedStop_bot_of hGpre
  have hmle : ∀ T : Ω → ℝ≥0∞, markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T ≤ mΩ := fun T =>
    (markedStopSigma_le T).trans (sup_le (measurable_fullHist hm2).comap_le
      (iSup_le fun t => (drivingFiltration P hX).le t))
  -- the pocket and its coordinate at fixed points
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  -- the current law at `T⁰(q)` (relative hull)
  have hCurW := R5Out.pocketStopWallsLaw_stopHull0_markedStop hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm
    hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q
  have hpreC := (locPrefixSigma_markedStopSigma_le hGpre hS0pre).trans (hmle _)
  have hleT := wallsSigma_le_markedStopSigma hX hT
  have hCur := pocketStopUnionLaw_outer_fix (hmle _) hcfg hψ (fun z => hleT _ (hCm z))
    (fun z => (hψm' z).mono hleT le_rfl) hpreC hCurW
  -- the enlarged law at `T⁰(q) ∨ s` (relative hull of the cut pocket)
  have hEnlW := R5Out.pocketStopWallsLaw_regHull_max_markedStop hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0
    hRm hLm hdetR hdetL hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q s
  obtain ⟨hGmax, hS0max⟩ := isMarkedStop_locPrefixSigma_max hGpre hS0pre s
  have hpreE := (locPrefixSigma_markedStopSigma_le hGmax hS0max).trans (hmle _)
  have hTs := isMarkedStop_bot_of hGmax
  have hleTs := wallsSigma_le_markedStopSigma hX hTs
  have hsle : drivingFiltration P hX s ≤ markedStopSigma (drivingFiltration P hX) (fullHist ![R, L])
      (fun ω => max (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞)) := le_markedStopSigma_max hT s
  have hKs : ∀ z, MeasurableSet[markedStopSigma (drivingFiltration P hX) (fullHist ![R, L])
      (fun ω => max (stopTimeM A R L r η ψ q ω) (s : ℝ≥0∞))] {ω | z ∈ H \ regHull W' ζ' s ω} := fun z =>
    hsle _ (measurableSet_mem_H_diff_regHull hC hκ' hX hζ s z)
  have eCut : ∀ z, {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r ∩ (H \ regHull W' ζ' s ω)} =
      {ω | z ∈ H \ regHull W' ζ' s ω} ∩ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z => by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    tauto
  have hEnl := pocketStopUnionLaw_outer_cut (hmle _) hcfg hζA hψ q s hpreE
    (fun z => by rw [eCut z]; exact (hKs z).inter (hleTs _ (hCm z)))
    (fun z => by
      rw [eCut z, ← Set.indicator_indicator]
      exact ((hψm' z).mono hleTs le_rfl).indicator (hKs z)) hEnlW
  -- the reference law at the original time `s`
  have hRef := R5Phase.pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ s
  have hA' : MeasurableSet[R5Phase.refInfo P hX R L s] A := R5Phase.wallsSigma_le_refInfo (P := P) hX R L s _ hA
  have hpreB : locPrefixSigma (R5Phase.refInfo P hX R L s) A (travAll R L r η ψ) 0 ≤ mΩ := by
    rw [PocketStopSide.locPrefixSigma_zero_of_driven hA' hγ]
    exact R5Phase.refInfo_le hX hRm hLm s
  have hBs := measurable_refSet_refInfo hC hκ' hX hζ hRc hLc hGm hG hA hAG hγ s
  -- the hulls
  have hKH : ∀ ω, regHull W' ζ' s ω ⊆ H := fun _ _ hz => hz.1
  have hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      activeDom A (travAll R L r η ψ) c q ω = cfPocket (R ω) (L ω) r ∩
        (H \ HOuter.relHull (cfPocket (R ω) (L ω) r) (ψ ω) (travAll R L r η ψ ω) q) := by
    intro ω hω hl
    rw [PocketStopSide.activeDom_eq_relChart_dom hω hl (hγ ω hω) (hc ω hω),
      R5Out.current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hω hl (hγ ω hω) (hc ω hω)
        (hcdom ω hω) (hceq ω hω) (hCH ω hω) (hψ ω hω).2.2.2.1,
      HOuter.H_diff_relHull (hCH ω hω), ← inter_assoc, inter_self]
  refine hasOldChartIncrementLawOn_of_pocketLaws_stop_comp hh₀ hT hγ hc hCo
    (fun ω _ => R5Phase.isOpen_H_diff_regHull W' ζ' s ω)
    (fun ω hω hl => HOuter.isOpen_H_diff_relHull ((hCo ω hω).inter (R5Phase.isOpen_H_diff_regHull W' ζ' s ω))
      (inter_subset_left.trans (hCH ω hω)) ((hψ ω hω).2.2.2.1.1.continuousOn.mono inter_subset_left) (hγ ω hω) hl)
    (fun ω hω hl => HOuter.isOpen_H_diff_relHull (hCo ω hω) (hCH ω hω) (hψ ω hω).2.2.2.1.1.continuousOn
      (hγ ω hω) hl) hact hpreB hRef hpreC hCur hpreE hEnl hBs
    (fun ω _ _ => subset_relHull_inter (hKH ω))
    (fun ω hsT hω hl => subset_relHull_of_disjoint (hKH ω) (notMem_regHull_of_relDom hcfg hζA hψ hω hl hsT))
    (fun ω hsT hω hl => relHull_inter_eq_of_disjoint (notMem_regHull_of_relDom hcfg hζA hψ hω hl hsT))
    hG' hOld hdom hfwd hOldSub hCut ?_ hMG hME hMlive
  intro ω hωG hsT hω hl z hz
  refine hNest ω hωG hsT hω hl ?_
  rw [R5Out.current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hω hl (hγ ω hω) (hc ω hω)
    (hcdom ω hω) (hceq ω hω) (hCH ω hω) (hψ ω hω).2.2.2.1, HOuter.H_diff_relHull (hCH ω hω)]
  have hz' := hz.2
  rw [HOuter.H_diff_relHull (inter_subset_left.trans (hCH ω hω))] at hz'
  exact ⟨hz'.1.1, hz'.2⟩

end R7Inst

end InteractingSLE.Sec7.R5OLaw
