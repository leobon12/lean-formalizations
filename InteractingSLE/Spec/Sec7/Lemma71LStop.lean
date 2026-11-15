/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71LRule
import InteractingSLE.Spec.Sec7.Lemma71ICap
import InteractingSLE.Spec.Sec7.Lemma71GLaw
import InteractingSLE.Spec.Sec7.Lemma71KData

/-!
# Lemma 7.1: the capacity stopping time of the mapped segment and the prefix filtration (R3/G7)

Packet PROVE-LEMMA71L, item R3/G7. Specification §7.1 (`source/spec/p193-240.md` L576–L606, p. 224): "For each
bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the revealed outer
curves and the middle prefix."

On a three-curve space with the pocket construction of PROVE-LEMMA71K (`Lemma71K.IsPocketConstruction`):

* `PocketGood` (the pathwise good event; almost sure, `ae_pocketGood`) and `PocketGood.visit` (the visit clock of the
  middle curve through the pocket and the closing-point facts, from `visitClock_of_isMarkedPocket`);
* `exists_capData`: the chart and its domain as measurable functions `G`, `M` of the outer histories, and the closing
  point as a measurable function `Y` of them (Doob–Dynkin);
* `capStop G M Y t`: the stopping rule `capRule` at the level `2t` on the outer histories (jointly measurable and
  Galmarino: the hypotheses `hSm`, `hSg` of the three-curve law, `measurable_capStop`, `capStop_galmarino`);
* **`prefixFiltrationOf_le_aeSigma`** (R3/G7): the prefix filtration of the mapped segment at capacity time `t` is
  contained, up to null sets, in the σ-algebra of the outer curves and the middle curve stopped at `capStop … t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71L

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71I Lemma71C Lemma71K Sec6 LocalSets

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- The complete outer histories. -/
def outerHist (β α : Ω → ℝ≥0 → ℂ) (ω : Ω) : Hist × Hist :=
  (histOf (pathCoord (β ω)) ⊤, histOf (pathCoord (α ω)) ⊤)

/-- The closing point of the pocket in the disc picture: the right wall at its last rational time in the closed
pocket. -/
def closePt (α : Ω → ℝ≥0 → ℂ) (C : Ω → Set ℂ) (ω : Ω) : ℂ :=
  wallPt (α ω) (closeTime (α ω) (closure (cayley '' C ω)))

/-- **The pathwise good event** of a pocket construction on a three-curve space: the order and contact clauses of the
three-curve space and the almost-sure clauses of `Lemma71K.IsPocketConstruction`. -/
def PocketGood (β α γ : Ω → ℝ≥0 → ℂ) (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ) (ω : Ω) : Prop :=
  WangWu.IsOrderedArcs (realPath (α ω)) (realPath (γ ω)) (realPath (β ω)) ∧
    NoCommonArc (γ ω) (α ω) ∧ NoCommonArc (γ ω) (β ω) ∧
    C ω ∈ betweenComponents (range (α ω)) (range (β ω)) ∧
    frontier (C ω) ∩ H ⊆ range (β ω) ∪ range (α ω) ∧
    ∃ (a' b' : ℝ) (Ψ : ℂ → ℂ), IsMarkedPocket (α ω) (C ω) a' b' ∧
      ContinuousOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) ∧
      InjOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) ∧
      MapsTo Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}) Hbar ∧ Ψ (wallPt (α ω) a') = 0 ∧
      Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C ω) \ {wallPt (α ω) b'}] (wallPt (α ω) b')) atTop ∧
      (∀ x ∈ C ω, (c ω).1 x = Ψ (cayley x)) ∧
      (∀ u, 0 ≤ u → segPt (γ ω) (closure (cayley '' C ω)) u ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'} ∧
        γ' ω u = Ψ (segPt (γ ω) (closure (cayley '' C ω)) u))

/-- The good event is almost sure. -/
theorem ae_pocketGood (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') : ∀ᵐ ω ∂P, PocketGood β α γ C c γ' ω := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hae⟩ := hS
  obtain ⟨-, -, -, -, -, -, -, -, hbetw, hfr, -, -, hmark⟩ := hpc
  filter_upwards [hae, hbetw, hfr, hmark] with ω hω hb hf hm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hord, hγα, hγβ⟩ := hω
  obtain ⟨a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hseg, -⟩ := hm
  exact ⟨hord, hγα, hγβ, hb, hf, a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hseg⟩

/-- A visit clock does not see the mapped segment off `[0, ∞)`. -/
theorem IsVisitClock.congr {C₀ : Set ℂ} {F : ℂ → ℂ} {η : ℝ≥0 → ℂ} {Γ Γ' : ℝ → ℂ} {k : ℝ → ℝ}
    (hv : IsVisitClock C₀ F η Γ k) (he : ∀ u, 0 ≤ u → Γ u = Γ' u) : IsVisitClock C₀ F η Γ' k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  exact ⟨h1, h2, h3, fun u hu => he u hu ▸ h4 u hu, h5, h6⟩

omit mΩ in
/-- **On the good event: the visit clock and the closing point.** -/
theorem PocketGood.visit {ω : Ω} (hg : PocketGood β α γ C c γ' ω) (hCo : IsOpen (C ω)) (hCH : C ω ⊆ H)
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω) (hγH : ∀ t, γ ω t ∈ Hbar) :
    IsVisitClock (C ω) (c ω).1 (γ ω) (γ' ω) (visitClock (γ ω) (closure (cayley '' C ω))) ∧
      (∀ u, 0 ≤ u → cayley (γ ω (visitClock (γ ω) (closure (cayley '' C ω)) u).toNNReal) =
        segPt (γ ω) (closure (cayley '' C ω)) u) ∧
      (∀ u, 0 ≤ u → 0 < (γ' ω u).im → γ ω (visitClock (γ ω) (closure (cayley '' C ω)) u).toNNReal ∈ C ω) ∧
      (∀ u, 0 ≤ u → EndOK (closePt α C ω) (ENNReal.ofReal (visitClock (γ ω) (closure (cayley '' C ω)) u))
        (pathCoord (γ ω))) ∧
      (∀ T : ℝ≥0, EndOK (closePt α C ω) T (pathCoord (γ ω)) →
        ∃ U, ∀ u, 0 ≤ u → visitClock (γ ω) (closure (cayley '' C ω)) u ≤ T → u ≤ U) := by
  obtain ⟨hord, hγα, hγβ, hb, -, a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hseg⟩ := hg
  have hclose : closePt α C ω = wallPt (α ω) b' := by
    obtain ⟨ha0, hab, hb1, hI, -⟩ := hM
    rw [closePt, (openTime_closeTime_eq ha0 hab hb1 hI).2]
  have hFm : ∀ z ∈ C ω, (c ω).1 z ∈ H := fun z hz => hc.fwd_mem (by rw [← SetLike.mem_coe, hdom]; exact hz)
  have hFs : ∀ w ∈ H, ∃ z ∈ C ω, (c ω).1 z = w := fun w hw =>
    ⟨(c ω).2.1 w, by rw [← hdom]; exact hc.inv_mem_dom hw, hc.2.2 w hw⟩
  obtain ⟨hvc, hcay, hin, hD1, hD2⟩ := visitClock_of_isMarkedPocket hord (interior_contact_eq_empty hγα)
    (interior_contact_eq_empty hγβ) hb hM hΨc hΨi hΨH hΨ0 hΨinf hCo hCH hγH hΨeq hFm hFs
  rw [hclose]
  refine ⟨hvc.congr fun u hu => ((hseg u hu).2).symm, hcay, fun u hu hpos => hin u hu ?_, hD1, hD2⟩
  rw [← (hseg u hu).2]
  exact hpos

/-! ### The chart and the closing point as functions of the outer histories -/

omit mΩ in
/-- Continuous paths with `m`-measurable rational coordinates have `m`-measurable coordinates. -/
theorem measurable_coord_of_rat {m : MeasurableSpace Ω} {η : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (η ω))
    (hq : ∀ q : ℚ≥0, Measurable[m] fun ω => η ω q) (t : ℝ≥0) : Measurable[m] fun ω => η ω t := by
  obtain ⟨q, hqt⟩ := exists_seq_nnrat_tendsto t
  let _ : MeasurableSpace Ω := m
  exact measurable_of_tendsto_metrizable (fun n => hq (q n))
    (tendsto_pi_nhds.2 fun ω => ((hc ω).tendsto t).comp hqt)

omit mΩ in
/-- `σ(β, α)` is contained in the σ-algebra of the complete outer histories. -/
theorem comap_pair_le_comap_outerHist (hβc : ∀ ω, Continuous (β ω)) (hαc : ∀ ω, Continuous (α ω)) :
    MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤
      MeasurableSpace.comap (outerHist β α) inferInstance := by
  have hA := comap_measurable (m := (inferInstance : MeasurableSpace (Hist × Hist))) (outerHist β α)
  have hβq : ∀ q : ℚ≥0, Measurable[MeasurableSpace.comap (outerHist β α) inferInstance] fun ω => β ω q :=
    fun q => by
      have e : (fun ω => β ω q) = (fun z : Hist × Hist => z.1.2 q) ∘ outerHist β α := by
        funext ω
        simp only [Function.comp_apply, outerHist, histOf]
        rw [stopCoord_of_le le_top]
        rfl
      rw [e]
      exact ((measurable_pi_apply q).comp (measurable_snd.comp measurable_fst)).comp hA
  have hαq : ∀ q : ℚ≥0, Measurable[MeasurableSpace.comap (outerHist β α) inferInstance] fun ω => α ω q :=
    fun q => by
      have e : (fun ω => α ω q) = (fun z : Hist × Hist => z.2.2 q) ∘ outerHist β α := by
        funext ω
        simp only [Function.comp_apply, outerHist, histOf]
        rw [stopCoord_of_le le_top]
        rfl
      rw [e]
      exact ((measurable_pi_apply q).comp (measurable_snd.comp measurable_snd)).comp hA
  let _ : MeasurableSpace Ω := MeasurableSpace.comap (outerHist β α) inferInstance
  have hpair : Measurable fun ω => (β ω, α ω) :=
    (measurable_pi_iff.2 fun t => measurable_coord_of_rat hβc hβq t).prodMk
      (measurable_pi_iff.2 fun t => measurable_coord_of_rat hαc hαq t)
  exact measurable_iff_comap_le.1 hpair

/-- **The pocket chart, its domain and the closing point as measurable functions of the outer histories**
(PROVE-LEMMA71I's `exists_capacityRule` for the chart of the pocket construction; Doob–Dynkin for the closing point). -/
theorem exists_capData (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    ∃ (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ),
      Measurable G ∧ MeasurableSet M ∧ Measurable Y ∧ (∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) ∧
      (∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) ∧ (∀ ω, Y (outerHist β α ω) = closePt α C ω) := by
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, -, -⟩ := hS
  obtain ⟨hC, hCm, hconf, hdom, hfm, -, -, -, -, -, -, -, -⟩ := hpc
  have hle := comap_pair_le_comap_outerHist hβ62.1 hα62.1
  set m : MeasurableSpace Ω := MeasurableSpace.comap (outerHist β α) inferInstance with hm
  have hCm' : ∀ (z : ℂ) (r : ℝ), MeasurableSet[m] {ω | closedBall z r ⊆ C ω} := fun z r => hle _ (hCm z r)
  have hFc : ∀ ω, ContinuousOn (c ω).1 (C ω) := fun ω => by
    rw [← hdom ω]
    exact (hconf ω).differentiableOn_fwd.continuousOn
  have hset : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := fun z => by
    ext ω
    show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
    rw [hdom]
  have hFm : ∀ z, Measurable[m] ({ω | z ∈ C ω}.indicator fun ω => (c ω).1 z) := fun z => by
    rw [← hset z]
    exact (hfm z).mono hle le_rfl
  obtain ⟨G, M, hG, hM, hMiff, hGeq, -⟩ :=
    Lemma71I.exists_capacityRule (A := outerHist β α) (fun ω => (hC ω).1) hCm' hFc hFm
  -- the closing point is `σ(outer histories)`-measurable
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hCH : ∀ ω, C ω ⊆ H := fun ω => (hC ω).2.2.2
  have hmem : ∀ z, MeasurableSet[m] {ω | z ∈ C ω} := fun z =>
    @Lemma71E.measurableSet_mem_of_closedBall Ω m C hCo hCm' z
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hαm : ∀ t, Measurable[m] fun ω => α ω t := fun t =>
    (((measurable_pi_apply t).comp measurable_snd).comp (comap_measurable _)).mono hle le_rfl
  have hY : Measurable[m] (closePt α C) := by
    have hU : ∀ q : ℚ, MeasurableSet[m] {ω | wallPt (α ω) q ∈ closure (cayley '' C ω)} := fun q =>
      @measurableSet_mem_closure_cayley_image Ω m C hCo hCH hmem e he _
        (@measurable_wallPt_const Ω m α hαm q)
    have hct := @measurable_closeTime Ω m α (fun ω => closure (cayley '' C ω)) hU
    exact @measurable_wallPt Ω m α hα62.1 hαm _ hct
  obtain ⟨Y, hYm, hYeq⟩ := hY.exists_eq_measurable_comp
  exact ⟨G, M, Y, hG, hM, hYm, hMiff, hGeq, fun ω => (congrFun hYeq ω).symm⟩

/-! ### The capacity stopping time -/

/-- **The capacity stopping rule at capacity time `t`** on the outer histories `(x, y)` and the middle coordinates. -/
def capStop (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ) (t : ℝ≥0)
    (x y : Hist) (cc : ℚ≥0 → ℂ) : ℝ≥0∞ :=
  capRule G M Y (ENNReal.ofReal (2 * (t : ℝ))) (x, y) cc

/-- The capacity stopping time `τ_t` of the middle curve. -/
def capTime (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ)
    (β α γ : Ω → ℝ≥0 → ℂ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  capStop G M Y t (outerHist β α ω).1 (outerHist β α ω).2 (pathCoord (γ ω))

section Rule

variable {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

theorem measurable_capStop (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y) (t : ℝ≥0) :
    Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => capStop G M Y t z.1.1 z.1.2 z.2 :=
  measurable_capRule hG hM hY _

theorem capStop_galmarino (t : ℝ≥0) (x y : Hist) (cc cc' : ℚ≥0 → ℂ)
    (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ capStop G M Y t x y cc → cc q = cc' q) :
    capStop G M Y t x y cc' = capStop G M Y t x y cc :=
  capRule_galmarino (x, y) cc cc' h

end Rule

end Space

end InteractingSLE.Sec7.Lemma71L
