/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefMarksPocket
import InteractingSLE.Spec.Sec7.PocketStopWallsFinField

/-!
# Lemma 7.25's pocket field data for one word-shape event, with the enlarged record

Packet PROVE-LEMMA725REF6 (the strip-level re-glue, first layer). Specification §7.4, Aux. lemmas 119–125 and 130,
Lemma 7.25's proof (`source/spec/p385-432.md` L171–L250, L401–L515); rulings R67–R69.

REF4's `Lemma725RefChart.pocketChartField_cfPocket` (and `…Inf`) feeds STRIPSYS35's walls data and the named
determination `PocketHistDet` **at the same σ-algebra `𝓦`** to the stop-level theorem. With R68 (as amended) the walls
law stays at the walls' `𝓦`, while the union law and the determination need the record `𝓦 ∨ σ(h₁)`; the two
theorems here call `pocketChartFieldStatement_of_stop_marks` instead, which builds that record. `PocketHistDet` is
replaced by its proved ingredients: the measurable pocket erasure (`pocketErasure_cfPocket`, REF4, at `𝓦`), a
standard Borel record `E₀` generating `𝓦` up to null sets, Proposition 5.13 (`h513`) and the continuity of the
counterflow.

The pocket-inclusion events `{U ⊆ C}` of the change pocket `C = cfPocket R L r` are walls' events
(`measurableSet_subset_cfPocket`): `U ⊆ C` iff the inverted walls avoid `U` and the points of a dense sequence lying
in `U` lie in `C` (`disjoint_extHullSet_iff` with the empty hull), and the walls are hitting-measurable (continuous
versions of the walls off the configuration event).

## Main results

* `subset_iff_walls`, `measurable_walls_piecewise`, `measurableSet_subset_cfPocket`;
* **`pocketChartField_cfPocket_marks`**, **`pocketChartField_cfPocketInf_marks`**.

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

namespace InteractingSLE.Sec7.Lemma725RefMarks

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField LawUnique Lemma725RefSafe
  Lemma725RefChart Lemma725RefRecovery PocketStopWallsFin

universe u

/-! ### The pocket-inclusion events are walls' events -/

section Walls

/-- **Inclusion in the pocket through the walls** (deterministic): for an open pocket `C ⊆ ℍ` bounded by the walls
`Γ` and an open `U ⊆ ℍ`, `U ⊆ C` iff `Γ` avoids `U` and the points of a dense sequence lying in `U` lie in `C`. -/
theorem subset_iff_walls {C Γ U : Set ℂ} (hCo : IsOpen C) (hΓC : Disjoint (H ∩ Γ) C) (hfr : frontier C ∩ H ⊆ Γ)
    (hUo : IsOpen U) (hUH : U ⊆ H) {e : ℕ → ℂ} (he : DenseRange e) :
    U ⊆ C ↔ Disjoint Γ U ∧ ∀ n, e n ∈ U → e n ∈ C := by
  have h1 : Disjoint (extHullSet C ∅) U ↔ U ⊆ C := by
    constructor
    · intro hd z hzU
      by_contra hzC
      exact Set.disjoint_left.1 hd ⟨hUH hzU, Or.inl hzC⟩ hzU
    · intro hsub
      refine Set.disjoint_left.2 fun z hz hzU => ?_
      rcases hz.2 with hzC | hz0
      · exact hzC (hsub hzU)
      · exact hz0
  have h2 : Disjoint (H ∩ (Γ ∪ ∅)) U ↔ Disjoint Γ U := by
    rw [union_empty]
    constructor
    · intro hd
      exact Set.disjoint_left.2 fun z hzΓ hzU => Set.disjoint_left.1 hd ⟨hUH hzU, hzΓ⟩ hzU
    · intro hd
      exact hd.mono_left inter_subset_right
  rw [← h1, disjoint_extHullSet_iff hCo hΓC hfr hUo hUH he, h2]

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω}

open Classical in
/-- **The inverted walls are hitting-measurable** after replacing the walls off the configuration event `G` by the
constant path `0`. -/
theorem measurable_walls_piecewise {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) :
    Measurable[𝓦, hittingSigma] fun ω => negInv '' (range (if ω ∈ G then R ω else fun _ => 0) ∪
      range (if ω ∈ G then L ω else fun _ => 0)) := by
  have hc : ∀ (S : Ω → ℝ≥0 → ℂ), (∀ ω ∈ G, Continuous (S ω)) →
      ∀ ω, Continuous (if ω ∈ G then S ω else fun _ => (0 : ℂ)) := fun S hS ω => by
    by_cases hω : ω ∈ G
    · rw [ite_eq_left hω]; exact hS ω hω
    · rw [ite_eq_right hω]; exact continuous_const
  have hm : ∀ (S : Ω → ℝ≥0 → ℂ), (∀ t, Measurable[𝓦] fun ω => S ω t) →
      ∀ t, Measurable[𝓦] fun ω => (if ω ∈ G then S ω else fun _ => (0 : ℂ)) t := fun S hS t => by
    have e : (fun ω => (if ω ∈ G then S ω else fun _ => (0 : ℂ)) t) = fun ω => if ω ∈ G then S ω t else 0 := by
      funext ω
      by_cases hω : ω ∈ G <;> simp [hω]
    rw [e]
    exact Measurable.ite hGm (hS t) measurable_const
  exact WangWu.measurable_image_negInv.comp (Lemma71Pin.measurable_union_hitting
    (Lemma71Pin.measurable_range_hitting (hc R fun ω hω => (hG ω hω).right.1) (hm R hRm))
    (Lemma71Pin.measurable_range_hitting (hc L fun ω hω => (hG ω hω).left.1) (hm L hLm)))

/-- **The pocket-inclusion events of the change pocket are walls' events.** -/
theorem measurableSet_subset_cfPocket {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set Γ' : Ω → Set ℂ := fun ω => negInv '' (range (if ω ∈ G then R ω else fun _ => 0) ∪
    range (if ω ∈ G then L ω else fun _ => 0)) with hΓ'
  have hΓm : Measurable[𝓦, hittingSigma] Γ' := measurable_walls_piecewise hRm hLm hGm hG
  have hkey : {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} =
      (A ∩ Γ' ⁻¹' {S : Set ℂ | Disjoint S U}) ∩ ptEvent A (fun ω => cfPocket (R ω) (L ω) r) e U := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, ptEvent]
    constructor
    · rintro ⟨hωA, hsub⟩
      have hωG := hAG hωA
      have hcf := hG ω hωG
      obtain ⟨hd, hpt⟩ := (subset_iff_walls (isOpen_image_negInv' hcf.isOpen_changePocket
        hcf.changePocket_subset_H) (cfPocket_walls_props hcf).1 (cfPocket_walls_props hcf).2 hUo hUH he).1 hsub
      refine ⟨⟨hωA, ?_⟩, fun n hn => ⟨hωA, hpt n hn⟩⟩
      simp only [hΓ', ite_eq_left hωG]
      exact hd
    · rintro ⟨⟨hωA, hd⟩, hpt⟩
      have hωG := hAG hωA
      have hcf := hG ω hωG
      refine ⟨hωA, (subset_iff_walls (isOpen_image_negInv' hcf.isOpen_changePocket hcf.changePocket_subset_H)
        (cfPocket_walls_props hcf).1 (cfPocket_walls_props hcf).2 hUo hUH he).2 ⟨?_, fun n hn => (hpt n hn).2⟩⟩
      simpa only [hΓ', ite_eq_left hωG] using hd
  rw [hkey]
  exact (hA.inter (hΓm (measurableSet_avoid hUo hUH))).inter
    (measurableSet_ptEvent (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) e U)

end Walls

/-! ### One word-shape event -/

section Word

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketChartFieldStatement` on one word-shape event of a bounded change pocket, with the enlarged record**:
REF4's `pocketChartField_cfPocket` with `PocketHistDet` replaced by the counterflow's continuity, a standard Borel
record `E₀` generating the walls' `𝓦` up to null sets, and Proposition 5.13 (`h513`); the union law with the
enlarged marks, the exterior decomposition and the erasure are proved (`pocketChartFieldStatement_of_stop_marks`). -/
theorem pocketChartField_cfPocket_core [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
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
    {n : Ω → ℤ} (hn : Measurable[𝓦] n) {a : ℝ}
    (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHull R L r W η ψ q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A (travAll R L r η ψ) xL xR
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
      (activeCompl A (travAll R L r η ψ) (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        q) q)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    PocketChartFieldStatement.{u} κ rL rR := by
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
  have hers := pocketErasure_cfPocket h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hψ hψm hxLm hxRm hE₀ hgen
  exact pocketChartFieldStatement_of_stop_marks hρL hρR hsL hsR h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2) hxLm hxRm hseedL hseedR hxLd hxRd hxLi hxRi
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun U hUo hUH => measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH)
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTime (hP ω hω) (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub hn hU hside hE₀ hgen h513 hers

/-- **`PocketChartFieldStatement` on one word-shape event of a change pocket opening at the flow seed, with the
enlarged record** (as `pocketChartField_cfPocket_marks`, for `IsCfPocketConfigInf`, `travAllInf`, `stopHullInf`). -/
theorem pocketChartField_cfPocketInf_core [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
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
    {n : Ω → ℤ} (hn : Measurable[𝓦] n) {a : ℝ}
    (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHullInf R L r W η ψ q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A (travAllInf R L r η ψ) xL xR
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
      (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    PocketChartFieldStatement.{u} κ rL rR := by
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
  have hers := pocketErasure_cfPocketInf h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hψ hψm hxLm hxRm hE₀ hgen
  exact pocketChartFieldStatement_of_stop_marks hρL hρR hsL hsR h𝓦 hA hPA (fun ω hω => (hdrive ω hω).1) hγm
    (fun ω hω => (hdrive ω hω).2) hxLm hxRm hseedL hseedR hxLd hxRd hxLi hxRi
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun U hUo hUH => measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH)
    (fun q ω hω _ => isOpen_H_diff_fwdHull_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (ψ ω) q)
    (fun q ω hω hq => image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)) hh₀ hu hub hn hU hside hE₀ hgen h513 hers

/-- **`PocketChartFieldStatement` on one word-shape event of a bounded change pocket, with the enlarged record**:
REF4's `pocketChartField_cfPocket` with `PocketHistDet` replaced by the counterflow's continuity, a standard Borel
record `E₀` generating the walls' `𝓦` up to null sets, and Proposition 5.13 (`h513`); STRIPSYS35's walls data at the
right end `T(q)` (`stopHull`). -/
theorem pocketChartField_cfPocket_marks [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
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
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) 
      (PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
        hψm)
  exact pocketChartField_cfPocket_core hρL hρR hsL hsR h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hPA hψ hψm hxLm hxRm
    hseedL hseedR hxLd hxRd hxLi hxRi hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1)
    (fun q => (hq q).2) hE₀ hgen h513

/-- **The same with the walls union law at the left end `T⁰(q)`** (ruling R67; STRIPSYS41's `stopHull0`, transferred
to `T(q)` by `pocketStopUnionLaw_stopHull_of_stopHull0`). -/
theorem pocketChartField_cfPocket_marks0 [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
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
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r W η ψ) h₀ u)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) 
      (PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
        hψm)
  exact pocketChartField_cfPocket_core hρL hρR hsL hsR h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hPA hψ hψm hxLm hxRm
    hseedL hseedR hxLd hxRd hxLi hxRi hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1))
    (fun q => (hq q).2) hE₀ hgen h513

/-- **`PocketChartFieldStatement` on one word-shape event of a change pocket opening at the flow seed, with the
enlarged record** (STRIPSYS35's walls data at `T(q)`, `stopHullInf`). -/
theorem pocketChartField_cfPocketInf_marks [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
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
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) 
      fun u hu => measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  exact pocketChartField_cfPocketInf_core hρL hρR hsL hsR h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hPA hψ hψm hxLm hxRm
    hseedL hseedR hxLd hxRd hxLi hxRi hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1)
    (fun q => (hq q).2) hE₀ hgen h513

/-- **The same with the walls union law at the left end `T⁰(q)`** (ruling R67, `stopHull0Inf`). -/
theorem pocketChartField_cfPocketInf_marks0 [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
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
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0Inf R L r W η ψ) h₀ u)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) 
      fun u hu => measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  exact pocketChartField_cfPocketInf_core hρL hρR hsL hsR h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hPA hψ hψm hxLm hxRm
    hseedL hseedR hxLd hxRd hxLi hxRi hh₀ hu hub hn
    (fun q => pocketStopUnionLaw_stopHullInf_of_stopHull0Inf hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1))
    (fun q => (hq q).2) hE₀ hgen h513

end Word

end InteractingSLE.Sec7.Lemma725RefMarks
