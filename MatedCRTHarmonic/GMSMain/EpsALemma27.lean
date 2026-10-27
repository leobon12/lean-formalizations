import MatedCRTHarmonic.GMSMain.EpsAProp210

/-!
# [18] Lemma 2.7 at every real mesh `ε ∈ (0, 1)`, in the consumer shapes of `GMSLemma27/Consumers.lean`

Source: [18] Lemma 2.7 : for `q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)`,
"for each `ε ∈ (0, 1)`", with probability `1 − O_ε(ε^α)` every cell `H^ε_x` meeting `B_ρ(0)` has diameter `≤ ε^q`.

L27's `GMSLemma27.lemma27_segments` already holds at every real `ε ∈ (0, 1)` on any `CellModel`; only its consumers
(`GMSLemma27.lemma27_cells_transfer`, `lemma27CellDiam_of_cellModel`, `cellDiamBound_of_cellModel`,
`ae_eventually_cellDiamBound_of_cellModel`) are written for the dyadic meshes `2^{-k}` of a `RandomCellFamily`. The
first three use dyadic-ness only as notation (and `mesh 0 = 1` to absorb `k = 0`); the last one uses it for a
Borel–Cantelli sum `Σ_k 2^{-kα} < ∞`, which has no real-`ε` analogue. Here:

* `epsA_lemma27_cells_transfer` — Lemma 2.7 at every real mesh for cell maps `J ε ω x` identified a.s. with the
  model's cells along a measure-preserving map (the real-mesh `lemma27_cells_transfer`);
* `epsA_lemma27_closedBall_transfer` — the closed-disk form (the `Lemma27CellDiam` shape, at `ρ' = (1+ρ)/2`);
* **`epsA_lemma27_segments_coupling`**, **`epsA_lemma27_coupling`** — for the γ-cone curve `η` of every frozen coupling:
  all segments `η([a, b])`, `b − a ≤ ε` (resp. all cells `η([ε(x−1), εx])`) meeting `B_ρ(0)` have diameter `≤ ε^q`,
  outer failure probability `≤ C ε^α` for every `α < α(q, γ)`; `epsA_lemma27_closedBall_coupling` (closed disk);
* **`EpsALemma27Bad`**, **`epsA_lemma27Bad_coupling`** — G3's `GMS3.CellDiamBound H ρ ε^q` for EVERY cellular
  embedding `H` of `MatedCRT.graph ε (bm ω) h` with the curve cells (and existence of one);
* **`epsA_ae_eventually_lemma27_coupling`** — the real-`ε` replacement of the Borel–Cantelli consumer, by the dyadic
  comparison: almost surely, for all small real `ε > 0`, every segment of length `≤ ε` meeting `B_ρ(0)` (in
  particular every cell `H^ε_x`) has diameter `≤ ε^q` (dyadic mesh `2^{-k} ≥ ε` with a slightly larger `q′`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic MatedCRTHarmonic.GMSLemma27

variable {γ : ℝ}

/-! ### Transfer along a cell-model identification (real-mesh `lemma27_cells_transfer`) -/

/-- **[18] Lemma 2.7 at every real mesh, transferred to cell maps identified with the model's cells.** -/
theorem epsA_lemma27_cells_transfer (M : CellModel γ) (hSLE : SegmentsContainBalls M)
    (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (e : Ω' → M.Ω) (he : MeasurePreserving e P' M.P) (J : ℝ → Ω' → ℤ → Set ℂ)
    (hJ : ∀ ε : ℝ, ∀ᵐ ω ∂P', ∀ x, J ε ω x = M.cell ε (e ω) x)
    {q ρ α : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P' {ω | ∀ x, (J ε ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (J ε ω x) ≤ ε ^ q}ᶜ ≤
        ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC⟩ := lemma27_segments M hSLE hGMC hdom hγ hq hq' hρ.1 hρ.2 hα
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  have hsub : {ω | ∀ x, (J ε ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (J ε ω x) ≤ ε ^ q}ᶜ ≤ᵐ[P']
      e ⁻¹' (segmentDiamGood M ε q ρ)ᶜ := by
    filter_upwards [hJ ε] with ω hω
    intro hbad hgood
    apply hbad
    intro x hx
    rw [hω x] at hx ⊢
    exact segmentDiamGood_subset_cellDiamGood M ε q ρ hgood x hx
  calc P' {ω | ∀ x, (J ε ω x ∩ ball (0 : ℂ) ρ).Nonempty → diam (J ε ω x) ≤ ε ^ q}ᶜ
      ≤ P' (e ⁻¹' (segmentDiamGood M ε q ρ)ᶜ) := measure_mono_ae hsub
    _ ≤ M.P (segmentDiamGood M ε q ρ)ᶜ := he.measure_preimage_le _
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε
    _ ≤ ENNReal.ofReal (max C 0 * ε ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hε.1.le _))

/-- An event "cells meeting `B_{(1+ρ)/2}(0)` are small" is contained in "cells meeting `B̄_ρ(0)` are small". -/
theorem epsA_closedBall_good_of_ball_good {ι : Type*} {J : ι → Set ℂ} {ρ δ : ℝ} (hρ1 : ρ < 1)
    (h : ∀ x, (J x ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty → diam (J x) ≤ δ) :
    ∀ x, (J x ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (J x) ≤ δ := by
  intro x hx
  refine h x ?_
  obtain ⟨w, hw1, hw2⟩ := hx
  refine ⟨w, hw1, ?_⟩
  rw [mem_closedBall, dist_zero_right] at hw2
  rw [mem_ball, dist_zero_right]
  linarith

/-- **The closed-disk form at every real mesh** (the `Lemma27CellDiam` shape, [18] Lemma 2.7 applied at
`ρ' = (1+ρ)/2 ∈ (ρ, 1)`; IA1 note N1), for every `ρ ∈ [0, 1)` and every `α < α(q, γ)` (independent of `ρ`). -/
theorem epsA_lemma27_closedBall_transfer (M : CellModel γ) (hSLE : SegmentsContainBalls M)
    (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M) (hγ : 0 < γ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (e : Ω' → M.Ω) (he : MeasurePreserving e P' M.P) (J : ℝ → Ω' → ℤ → Set ℂ)
    (hJ : ∀ ε : ℝ, ∀ᵐ ω ∂P', ∀ x, J ε ω x = M.cell ε (e ω) x)
    {q ρ α : ℝ} (hq : 0 < q) (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P' {ω | ∀ x, (J ε ω x ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (J ε ω x) ≤ ε ^ q}ᶜ ≤
        ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_cells_transfer M hSLE hGMC hdom hγ e he J hJ hq hq'
    (ρ := (1 + ρ) / 2) ⟨by linarith, by linarith⟩ hα
  refine ⟨C, hC0, fun ε hε => (measure_mono (compl_subset_compl.mpr ?_)).trans (hC ε hε)⟩
  intro ω hω
  exact epsA_closedBall_good_of_ball_good hρ1 hω

/-! ### The γ-cone curve of a frozen coupling -/

section Coupling

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Lemma 2.7 for all segments of the γ-cone curve, at every real mesh**: for `q ∈ (0, 2/(2+γ)²)`,
`ρ ∈ (0, 1)` and `α < α(q, γ)`, there is `C` with: for every `ε ∈ (0, 1)`, the outer probability that some segment
`η([a, b])` with `b − a ≤ ε` meets `B_ρ(0)` and has diameter `> ε^q` is at most `C ε^α`. -/
theorem epsA_lemma27_segments_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P {ω | ∀ a b : ℝ, b - a ≤ ε → (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc a b) ≤ ε ^ q}ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  have hpar := MesoModel.final_areaParametrization_of_coupling D hstd hγ
  set M := (MoTInput.coneRealizationOfCoupling D hstd hγ).toCellModel hpar with hM
  obtain ⟨C, hC⟩ := lemma27_segments M (MesoModel.final_segmentsContainBalls_of_coupling D hstd hγ hpar)
    (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2)
    (GMCFacts.areaDominates_toCellModel (MoTInput.coneRealizationOfCoupling D hstd hγ) hpar hγ.1 hγ.2)
    hγ.1 hq hq' hρ.1 hρ.2 hα
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  have hsub : {ω | ∀ a b : ℝ, b - a ≤ ε → (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (η ω '' Icc a b) ≤ ε ^ q}ᶜ ≤ᵐ[P] (segmentDiamGood M ε q ρ)ᶜ := by
    filter_upwards [MoTInput.ae_bundleCurve_eq D] with ω hω
    intro hbad hgood
    apply hbad
    have hc : MoTInput.bundleCurve (D := D) ω = η ω := hω
    have hg : ∀ a b : ℝ, b - a ≤ ε → ((MoTInput.bundleCurve (D := D) ω : ℝ → ℂ) '' Icc a b ∩
        ball (0 : ℂ) ρ).Nonempty → diam ((MoTInput.bundleCurve (D := D) ω : ℝ → ℂ) '' Icc a b) ≤ ε ^ q :=
      hgood
    rw [hc] at hg
    exact hg
  calc P {ω | ∀ a b : ℝ, b - a ≤ ε → (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc a b) ≤ ε ^ q}ᶜ
      ≤ P (segmentDiamGood M ε q ρ)ᶜ := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε
    _ ≤ ENNReal.ofReal (max C 0 * ε ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hε.1.le _))

/-- **[18] Lemma 2.7 for the cells of the γ-cone curve, at every real mesh** ([18] (2.9)): every cell
`H^ε_x = η([ε(x−1), εx])` meeting `B_ρ(0)` has diameter `≤ ε^q`, outer failure probability `≤ C ε^α`. -/
theorem epsA_lemma27_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_segments_coupling D hstd hγ hq hq' hρ hα
  refine ⟨C, hC0, fun ε hε => (measure_mono (compl_subset_compl.mpr ?_)).trans (hC ε hε)⟩
  intro ω hω x hx
  exact hω _ _ (le_of_eq (by ring)) hx

/-- **The closed-disk form for the γ-cone curve** (the `Lemma27CellDiam` shape) at every real mesh, every
`ρ ∈ [0, 1)`, every `α < α(q, γ)`. -/
theorem epsA_lemma27_closedBall_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ closedBall (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_coupling D hstd hγ hq hq' (ρ := (1 + ρ) / 2)
    ⟨by linarith, by linarith⟩ hα
  refine ⟨C, hC0, fun ε hε => (measure_mono (compl_subset_compl.mpr ?_)).trans (hC ε hε)⟩
  intro ω hω
  exact epsA_closedBall_good_of_ball_good (J := fun x : ℤ => η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    hρ1 hω

end Coupling

/-- **The failure event of [18] Lemma 2.7 at mesh `ε` in G3's form** for the mated-CRT map `MatedCRT.graph ε (bm ω) h`
with the cells of `η`: the complement of "the map is locally finite and the curve cells form a cellular embedding of
it, and EVERY such embedding `H` satisfies `GMS3.CellDiamBound H ρ ε^q`" (cells meeting `B_ρ(0)` have diameter
`≤ ε^q`). -/
def EpsALemma27Bad {Ω : Type*} (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε q ρ : ℝ) : Set Ω :=
  {ω | ¬ ((∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (hlf : MatedCRT.IsLocallyFinite ε (bm ω)) (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        (∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) → GMS3.CellDiamBound H ρ (ε ^ q))}

section Coupling

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Lemma 2.7 in G3's `CellDiamBound` form at every real mesh, for every frozen coupling** (the real-mesh
`cellDiamBound_of_cellModel`): for `q ∈ (0, 2/(2+γ)²)`, `ρ ∈ (0, 1)`, `α < α(q, γ)`, there is `C ≥ 0` with
`P (EpsALemma27Bad bm η ε q ρ) ≤ C ε^α` for every `ε ∈ (0, 1)`. -/
theorem epsA_lemma27Bad_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      P (EpsALemma27Bad bm η ε q ρ) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_coupling D hstd hγ hq hq' hρ hα
  refine ⟨C, hC0, fun ε hε => ?_⟩
  set N : Set Ω := {ω | ¬ ∃ (hlf : MatedCRT.IsLocallyFinite ε (bm ω))
      (H : CellularEmbedding (MatedCRT.graph ε (bm ω) hlf) 0),
        ∀ x : ℤ, H.cell x = η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)} with hN
  have hN0 : P N = 0 := ae_iff.mp (epsA_ae_exists_cellularEmbedding D hε.1)
  have hsub : EpsALemma27Bad bm η ε q ρ ⊆
      {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
        diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ ∪ N := by
    intro ω hbad
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hgood, hex⟩ := hcon
    apply hbad
    refine ⟨not_not.mp hex, fun hlf H hcell x hx => ?_⟩
    rw [hcell x] at hx
    have h := hgood x hx
    unfold GMS3.cellDiam
    rw [hcell x]
    exact h
  calc P (EpsALemma27Bad bm η ε q ρ)
      ≤ P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
          diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ + P N :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = P {ω | ∀ x : ℤ, (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩ ball (0 : ℂ) ρ).Nonempty →
          diam (η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ≤ ε ^ q}ᶜ := by rw [hN0, add_zero]
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε

/-- **Almost surely, for all small real meshes, the curve segments of length `≤ ε` meeting `B_ρ(0)` have diameter
`≤ ε^q`** (the real-`ε` replacement of L27's Borel–Cantelli consumer `ae_eventually_cellDiamBound_of_cellModel`).
Comparison with the dyadic meshes: for `q < q′ < 2/(2+γ)²`, Borel–Cantelli at `ε_k = 2^{-k}` with exponent `q′`; for
`ε ∈ (ε_{k+1}, ε_k]` a segment of length `≤ ε ≤ ε_k` has diameter `≤ ε_k^{q′} ≤ (2ε)^{q′} ≤ ε^q` once
`2^{q′} ε^{q′ − q} ≤ 1`. In particular every cell `H^ε_x` meeting `B_ρ(0)` has diameter `≤ ε^q`. -/
theorem epsA_ae_eventually_lemma27_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ρ : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a b : ℝ, b - a ≤ ε →
      (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty → diam (η ω '' Icc a b) ≤ ε ^ q := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  -- a slightly larger exponent `q₁`
  set q₁ : ℝ := (q + 2 / (2 + γ) ^ 2) / 2 with hq₁
  have hqq₁ : q < q₁ := by rw [hq₁]; linarith
  have hq₁' : q₁ < 2 / (2 + γ) ^ 2 := by rw [hq₁]; linarith
  have hq₁0 : 0 < q₁ := hq.trans hqq₁
  have hexp := lemma27Exponent_pos hγ.1 hq₁0 hq₁'
  set α : ℝ := lemma27Exponent q₁ γ / 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  obtain ⟨C, hC0, hC⟩ := epsA_lemma27_segments_coupling D hstd hγ hq₁0 hq₁' hρ
    (α := α) (by rw [hα]; linarith)
  -- Borel–Cantelli at the dyadic meshes `k ≥ 1`
  set G : ℕ → Set Ω := fun k => {ω | ∀ a b : ℝ, b - a ≤ CellFamily.mesh (k + 1) →
    (η ω '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty → diam (η ω '' Icc a b) ≤ CellFamily.mesh (k + 1) ^ q₁} with hG
  have hbound : ∀ k : ℕ, P (G k)ᶜ ≤ ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ (-α)) ^ (k + 1) := by
    intro k
    have hε : CellFamily.mesh (k + 1) ∈ Ioo (0 : ℝ) 1 :=
      ⟨BundleSec4.bundle_mesh_pos _, GMSLemma27.mesh_lt_one (by omega)⟩
    refine (hC _ hε).trans (le_of_eq ?_)
    rw [GMSLemma27.mesh_rpow_eq, ENNReal.ofReal_mul hC0,
      ENNReal.ofReal_pow (Real.rpow_nonneg zero_le_two _)]
  have hx1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hsum : ∑' k, P (G k)ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have hgeom := (tsum_geometric_lt_top.mpr ((ENNReal.ofReal_lt_one).mpr hx1)).ne
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    rw [pow_succ]
    exact mul_le_of_le_one_right' (ENNReal.ofReal_le_one.mpr hx1.le)
  -- the threshold where `2^{q₁} ε^{q₁ − q} ≤ 1`
  have hthr : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (2 : ℝ) ^ q₁ * ε ^ (q₁ - q) ≤ 1 := by
    obtain ⟨ε₀, hε₀, -, hε₀'⟩ := epsA_exists_rpow_le (show 0 < q₁ - q by linarith)
      (inv_pos.2 (Real.rpow_pos_of_pos two_pos q₁))
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    have h := hε₀' ε hε.1 hε.2
    have h2 : 0 < (2 : ℝ) ^ q₁ := Real.rpow_pos_of_pos two_pos q₁
    calc (2 : ℝ) ^ q₁ * ε ^ (q₁ - q) ≤ (2 : ℝ) ^ q₁ * ((2 : ℝ) ^ q₁)⁻¹ :=
          mul_le_mul_of_nonneg_left h h2.le
      _ = 1 := mul_inv_cancel₀ h2.ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  have hK' : ∀ k ≥ K, ω ∈ G k := fun k hk => by simpa using hK k hk
  -- for `ε < 2^{-(K+1)}`, use the dyadic mesh `2^{-(k+1)}` with `2^{-(k+2)} < ε ≤ 2^{-(k+1)}`, `k ≥ K`
  filter_upwards [hthr, Ioo_mem_nhdsGT (BundleSec4.bundle_mesh_pos (K + 1))] with ε hthrε hε a b hab hmeet
  have hε0 : 0 < ε := hε.1
  -- the dyadic index: `n = ⌊log₂ (1/ε)⌋`, so `2^{-(n+1)} < ε ≤ 2^{-n}`
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, CellFamily.mesh (n + 1) < ε ∧ ε ≤ CellFamily.mesh n := by
    have hex : ∃ n : ℕ, CellFamily.mesh (n + 1) < ε := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε0 (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨n, lt_of_le_of_lt ?_ hn⟩
      rw [CellFamily.mesh, zpow_neg, zpow_natCast, one_div, inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    classical
    let n := Nat.find hex
    have hn : CellFamily.mesh (n + 1) < ε := Nat.find_spec hex
    refine ⟨n, hn, ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, GMSLemma27.mesh_zero]
      exact (hε.2.trans_le (le_of_lt (GMSLemma27.mesh_lt_one (by omega)))).le
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      rw [not_lt, show n - 1 + 1 = n by omega] at hmin
      exact hmin
  have hnK : K ≤ n := by
    by_contra hlt
    push Not at hlt
    have : CellFamily.mesh (K + 1) ≤ CellFamily.mesh (n + 1) := GMS4FO.mesh_anti (by omega)
    exact lt_asymm hn1 (hε.2.trans_le this)
  -- the dyadic mesh `2^{-n} = 2^{-((n-1)+1)}` is `≥ ε`; `n ≥ 1` since `ε < 2^{-(K+1)} ≤ 1/2`
  have hn0 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    rw [this] at hn1
    have h1 : CellFamily.mesh (K + 1) ≤ CellFamily.mesh (0 + 1) := GMS4FO.mesh_anti (by omega)
    exact absurd (hn1.trans hε.2) (not_lt.mpr h1)
  have hgood : ω ∈ G (n - 1) := hK' (n - 1) (by
    by_contra hlt
    push Not at hlt
    -- `n − 1 < K ≤ n` forces `n = K`, then `ε < mesh (K+1) = mesh (n+1)`, contradicting `hn1`
    have hnK' : n = K := by omega
    rw [hnK'] at hn1
    exact absurd hn1 (not_lt.mpr hε.2.le))
  have hn' : n - 1 + 1 = n := by omega
  have hseg := hgood a b (by rw [hn']; exact hab.trans hn2) hmeet
  rw [hn'] at hseg
  -- `ε_n ≤ 2ε`, so `ε_n^{q₁} ≤ (2ε)^{q₁} = 2^{q₁} ε^{q₁−q} ε^q ≤ ε^q`
  have hmesh2 : CellFamily.mesh n ≤ 2 * ε := by
    have h := hn1.le
    have hsucc : CellFamily.mesh (n + 1) = CellFamily.mesh n / 2 := by
      rw [CellFamily.mesh, CellFamily.mesh, Nat.cast_succ, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num [div_eq_mul_inv]
    rw [hsucc] at h
    linarith
  calc diam (η ω '' Icc a b) ≤ CellFamily.mesh n ^ q₁ := hseg
    _ ≤ (2 * ε) ^ q₁ := Real.rpow_le_rpow (BundleSec4.bundle_mesh_pos n).le hmesh2 hq₁0.le
    _ = (2 : ℝ) ^ q₁ * ε ^ (q₁ - q) * ε ^ q := by
        rw [Real.mul_rpow zero_le_two hε0.le, mul_assoc, ← Real.rpow_add hε0, sub_add_cancel]
    _ ≤ 1 * ε ^ q := mul_le_mul_of_nonneg_right hthrε (Real.rpow_nonneg hε0.le _)
    _ = ε ^ q := one_mul _

end Coupling

end MatedCRTHarmonic.GMSMain
