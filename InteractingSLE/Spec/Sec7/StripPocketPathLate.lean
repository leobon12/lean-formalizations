/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketPathWalls
import InteractingSLE.Spec.Sec7.RS133Prob
import InteractingSLE.Spec.Sec7.StripPocketConfigEvent
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Theorem 1.3's pocket word: late points of `β = η_{π/2}` off `α` ((RS13.3)) for the strip system

Packet PROVE-STRIPSYS31. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440–L456,
p. 411): "The path `β` has points outside the complete range of `α` at arbitrarily late finite times. […] Retain the
two full marked local sets. Nested local-set boundary comparison identifies the union mean with each single-path mean
on this collar. […] Expressing both germs in one chart therefore forces `θ₁ − π/2 = 2πn` (RS13.3). This is impossible
because `−π < θ₁ − π/2 < 0`."

PROVE-STRIPSYS19's `RS133.ae_late_of_sideHeights` proves (RS13.3) almost surely from Lemma 6.2's inputs of both paths,
their side heights at countably many stops, the countably many boundary comparisons, and the first-visit order. Here
its inputs are supplied for the strip system's `α = η^{1,∞}_{−π/2,θ₁}` and `β = η_{π/2}`:

* `cfT`, **`strictAntiOn_cfT`**: the counterflow's first visit `T(z)` of `m(z)` decreases strictly along a wall in
  reverse visit order with every point visited ("Distinct points of an incoming path have strictly decreasing `T` in
  its incoming order");
* `ae_late_of_sideHeights_frozen`: `RS133.ae_late_of_sideHeights` with the locality of `β` asked only for its frozen
  paths `t ↦ β(t ∧ q)` (the stopped ranges are the same sets; for the one-piece flow line `β` the landed locality is
  the frozen one, `Restart.StagedEntrance.isEntranceHistoryLocal_frozenPath_of_isFlowLine`, Aux. lemma 56);
* `ae_hdet_leftExtremal`, `ae_sideHeights_leftExtremal`: field determination of `β` (R48-safe: `AdmCode.admDrv`) and
  its single-path side heights at every stop (`Aux119Heights.ae_hasSideHeights_of_isFlowLine`);
* **`ae_late_strip`**: (RS13.3) almost surely for the strip system, from the walls' reverse visit order (Lemma 5.7, a
  named input of the pocket word) — the input `hlate` of `StripPocketConfig.pocketWordEvolution_of_stripPocket`.

No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology Metric
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec7

namespace StripPocketPath

open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open StripSideHeightProb StripGeom LocalSets
open Exist.Staged (IsRegularDriver)
open Restart.StagedEntrance (frozenPath continuous_frozenPath)
open PocketJordan PocketMeas

/-! ### First visits of the counterflow along a wall -/

/-- **The counterflow's first visit of a wall point** `T(z) = inf {t : η(t) = m(z)}` (in the counterflow chart
`m(z) = −1/z`; `⊤` if never visited). -/
def cfT (η : ℝ → ℂ) (z : ℂ) : ℝ≥0∞ := Aux130.firstVisit (nnPath η) (WangWu.negInv z)

/-- **Strict decrease of `T` along a wall** (p. 410): along an injective wall in reverse visit order whose points
after the seed are all visited, `T` decreases strictly on `(0, ∞)`. -/
theorem strictAntiOn_cfT {R : ℝ≥0 → ℂ} {η : ℝ → ℂ} (hRi : Injective R) (hη : ContinuousOn η (Ici 0))
    (hrev : IsWallReverseVisit R η) (hvis : IsWallVisited R η) :
    StrictAntiOn (fun t => cfT η (R t)) (Ioi 0) := by
  intro a ha c _ hac
  obtain ⟨t, ht⟩ := hvis a ha
  have hlt := StripPocketConfig.firstVisit_lt_top_of_mem ht
  have hmem := StripPocketConfig.mem_image_firstVisit hη hlt
  have hmem' := hrev _ a c ha hac.le hmem
  have hle : cfT η (R c) ≤ cfT η (R a) := by
    have h1 := StripPocketConfig.firstVisit_le_of_mem hmem'
    rwa [ENNReal.coe_toNNReal hlt.ne] at h1
  refine lt_of_le_of_ne hle fun heq' => ?_
  have heq : cfT η (R c) = cfT η (R a) := heq'
  have hc := StripPocketConfig.continuous_nnPath_of hη
  have h1 := Aux130.apply_firstVisit hc hlt
  have h2 := Aux130.apply_firstVisit hc (show cfT η (R c) < ⊤ from heq ▸ hlt)
  change nnPath η (cfT η (R c)).toNNReal = WangWu.negInv (R c) at h2
  change nnPath η (cfT η (R a)).toNNReal = WangWu.negInv (R a) at h1
  rw [heq] at h2
  have he : WangWu.negInv (R a) = WangWu.negInv (R c) := h1.symm.trans h2
  simp only [WangWu.negInv, neg_inj, inv_inj] at he
  exact hac.ne (hRi he)

/-! ### (RS13.3) with frozen locality for the second path -/

theorem image_frozenPath_Icc (γ : ℝ≥0 → ℂ) (q : ℝ≥0) : frozenPath γ q '' Icc 0 q = γ '' Icc 0 q := by
  refine image_congr fun t ht => ?_
  simp only [frozenPath, min_eq_left ht.2]

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **`RS133.ae_late_of_sideHeights` with frozen locality for `β`**: the same conclusion when the locality of `β` is
known only for its frozen paths `t ↦ β(t ∧ q)` (whose stopped ranges at `q` are those of `β`). -/
theorem ae_late_of_sideHeights_frozen (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {α β : Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (X ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α X P) (hαim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im)
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (X ω))
    (hβloc : ∀ q : ℝ≥0, Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (β ω) q) X P)
    (hβim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (β ω t).im)
    {W₁ W₂ : Ω → ℝ≥0 → ℝ} (T : Ω → ℂ → ℝ≥0∞)
    (hpath : ∀ᵐ ω ∂P, IsGeneratingTrace (W₁ ω) ⊤ (α ω) ∧ Continuous (W₁ ω) ∧ W₁ ω 0 = 0 ∧
      IsGeneratingTrace (W₂ ω) ⊤ (β ω) ∧ Continuous (W₂ ω) ∧ W₂ ω 0 = 0 ∧ Injective (α ω) ∧ Injective (β ω) ∧
      (∀ t, 0 < t → α ω t ∈ H) ∧ Tendsto (fun t => ‖α ω t‖) atTop atTop ∧
      Tendsto (fun t => ‖β ω t‖) atTop atTop ∧ StrictAntiOn (fun t => T ω (α ω t)) (Ioi 0) ∧
      StrictAntiOn (fun t => T ω (β ω t)) (Ioi 0))
    {κ θ₁ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) ≤ θ₁) (hθ₁' : θ₁ < π / 2) {u₀ : ℂ → ℝ}
    {t₀ : ℝ≥0} {Q₁ Q₂ : Set ℝ≥0} (hQ₁c : Q₁.Countable) (hQ₂c : Q₂.Countable) (hQ₁ : ∀ a, ∃ q ∈ Q₁, a ≤ q)
    (hQ₂ : ∀ a, ∃ q ∈ Q₂, a < q) {gα gβ : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgα : ∀ q ∈ Q₁, IsLocalSetMean (fun ω => α ω '' Icc 0 q ∩ H) X P (gα q))
    (hgβ : ∀ q ∈ Q₂, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) X P (gβ q))
    (hside₁ : ∀ q ∈ Q₁, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (α ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 q ∩ H) → gα q ω φ = ∫ z, v z * φ z) →
      ∀ s, t₀ < s → s < q → HasSideHeights κ θ₁ (α ω) 0 (W₁ ω) q (α ω s) v u₀)
    (hside₂ : ∀ q ∈ Q₂, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (β ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q ∩ H) → gβ q ω φ = ∫ z, v z * φ z) →
      ∀ s, 0 < s → s < q → HasSideHeights κ (π / 2) (β ω) 0 (W₂ ω) q (β ω s) v u₀) :
    ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ closure (range (α ω)) := by
  classical
  set vα : ℝ≥0 → Ω → ℂ → ℝ := fun q ω =>
    if hq : IsHarmonicDistOn (gα q ω) (H \ (α ω '' Icc 0 q ∩ H)) then hq.choose else 0 with hvαdef
  set vβ : ℝ≥0 → Ω → ℂ → ℝ := fun q ω =>
    if hq : IsHarmonicDistOn (gβ q ω) (H \ (β ω '' Icc 0 q ∩ H)) then hq.choose else 0 with hvβdef
  have hvα : ∀ q ∈ Q₁, ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (vα q ω) (H \ (α ω '' Icc 0 q ∩ H)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 q ∩ H) →
        gα q ω φ = ∫ z, vα q ω z * φ z := by
    intro q hq
    filter_upwards [(hgα q hq).2.1] with ω hω
    simp only [hvαdef, hω, ↓reduceDIte]
    exact hω.choose_spec
  have hvβ : ∀ q ∈ Q₂, ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (vβ q ω) (H \ (β ω '' Icc 0 q ∩ H)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q ∩ H) →
        gβ q ω φ = ∫ z, vβ q ω z * φ z := by
    intro q hq
    filter_upwards [(hgβ q hq).2.1] with ω hω
    simp only [hvβdef, hω, ↓reduceDIte]
    exact hω.choose_spec
  -- the boundary comparison for the frozen second path, read back on the ranges of `β`
  have hcmp : ∀ q₁ ∈ Q₁, ∀ q₂ ∈ Q₂, ∀ᵐ ω ∂P, ∀ vA vB : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vA (H \ (α ω '' Icc 0 q₁ ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (α ω '' Icc 0 q₁ ∩ H) → gα q₁ ω φ = ∫ z, vA z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ (β ω '' Icc 0 q₂ ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q₂ ∩ H) → gβ q₂ ω φ = ∫ z, vB z * φ z) →
      ∀ z₀ ∈ α ω '' Icc 0 q₁ ∩ H, z₀ ∈ β ω '' Icc 0 q₂ ∩ H →
      (∃ r > 0, β ω '' Icc 0 q₂ ∩ H ∩ ball z₀ r ⊆ α ω '' Icc 0 q₁ ∩ H) →
      (∃ r > 0, α ω '' Icc 0 q₁ ∩ H ∩ ball z₀ r ⊆ β ω '' Icc 0 q₂ ∩ H) →
      Tendsto (fun z => vA z - vB z) (𝓝[H \ (α ω '' Icc 0 q₁ ∩ H ∪ β ω '' Icc 0 q₂ ∩ H)] z₀) (𝓝 0) := by
    intro q₁ hq₁ q₂ hq₂
    have hgB : IsLocalSetMean (fun ω => frozenPath (β ω) q₂ '' Icc 0 q₂ ∩ H) X P (gβ q₂) := by
      simpa only [image_frozenPath_Icc] using hgβ q₂ hq₂
    have h := RS133.ae_tendsto_sub_ranges hX hαc hα0 hαm hαdet hαloc hαim
      (β := fun ω => frozenPath (β ω) q₂) (fun ω => continuous_frozenPath (hβc ω))
      (fun ω => by simp only [frozenPath, min_eq_left (zero_le : (0 : ℝ≥0) ≤ q₂), hβ0])
      (fun t => hβm _) (Restart.StagedEntrance.frozenPath_ae_eq_comp hβdet q₂) (hβloc q₂)
      (hβim.mono fun ω hω t => hω _) q₁ q₂ (hgα q₁ hq₁) hgB
    simpa only [image_frozenPath_Icc] using h
  have h1 := (ae_ball_iff hQ₁c).2 fun q hq => (hvα q hq).and (hside₁ q hq)
  have h2 := (ae_ball_iff hQ₂c).2 fun q hq => (hvβ q hq).and (hside₂ q hq)
  have h3 := (ae_ball_iff hQ₁c).2 fun q₁ hq₁ => (ae_ball_iff hQ₂c).2 fun q₂ hq₂ => hcmp q₁ hq₁ q₂ hq₂
  filter_upwards [hpath, h1, h2, h3] with ω hp hω1 hω2 hω3
  obtain ⟨hg₁, hW₁c, hW₁0, hg₂, hW₂c, hW₂0, hαi, hβi, hαH, hαu, hβu, hTα, hTβ⟩ := hp
  exact RS133.late_of_sideHeights (T ω) hg₁ hW₁c hW₁0 hg₂ hW₂c hW₂0 hαi hβi hαH hαu hβu hTα hTβ hκ hκ4 hθ₁ hθ₁'
    hQ₁ hQ₂ (v₁ := fun q => vα q ω) (v₂ := fun q => vβ q ω)
    (fun q hq s hs1 hs2 => (hω1 q hq).2 _ (hω1 q hq).1.1 (hω1 q hq).1.2 s hs1 hs2)
    (fun q hq s hs1 hs2 => (hω2 q hq).2 _ (hω2 q hq).1.1 (hω2 q hq).1.2 s hs1 hs2)
    (fun q₁ hq₁ q₂ hq₂ z₀ hz₁ hz₂ hl₁ hl₂ => hω3 q₁ hq₁ q₂ hq₂ _ _ (hω1 q₁ hq₁).1.1 (hω1 q₁ hq₁).1.2
      (hω2 q₂ hq₂).1.1 (hω2 q₂ hq₂).1.2 z₀ hz₁ hz₂ hl₁ hl₂)

end Prob

/-! ### The strip system -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The driver of `β = η_{π/2}` is field-determined** (R48-safe): almost surely its lifetime is infinite and it is
`AdmCode.admDrv (π/2) (c₀, h)` for a sorted word `c₀` of the data `b`. -/
theorem exists_ae_leftExtremal_eq_admDrv (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∃ c₀ : Restart.BoundaryWord, ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧
      (Es StripSys.leftExtremalSpec 0 ω).1 =
        (AdmCode.admDrv h44 hS.kappa_pos hS.kappa_lt_four (π / 2) (c₀, h ω)).1 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  obtain ⟨hL0, hR0⟩ := heights_pi_div_two hκ hκ4 hcumL hcumR
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have h44c : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 (π / 2))
      (flowLineRhoR κ c₀.fn c₀.jumps 0 (π / 2)) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData (π / 2)
      (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL0 y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR0 y hy hyJ
  have hEd := (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
    (fun y hy => hc₀ y hy)).2 (isFlowLineDriver_leftExtremal hκ hb hS.gff hS.isStagedHistory_leftExtremal)
  refine ⟨c₀, ?_⟩
  filter_upwards [AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 (π / 2) c₀ h44c hEd] with ω h2
  refine ⟨h2.1, funext fun t => ?_⟩
  exact (h2.2.2 t (by rw [h2.1]; exact ENNReal.coe_lt_top)).symm

/-- **Lemma 6.2's determination input for `β = η_{π/2}`**: every version of `β` is, at every time, almost surely a
Borel function of the centred field `h − 𝔥₀` (LP11's reconstruction of the field-determined driver). -/
theorem hdet_leftExtremal (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω)) (u₀ : ℂ → ℝ) {β : Ω → ℝ≥0 → ℂ}
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω)) :
    ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  obtain ⟨c₀, hD⟩ := exists_ae_leftExtremal_eq_admDrv h44 hS hcumL hcumR
  intro t
  set c : DistOn upperHalfPlaneOpens :=
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hc
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens => g + c := Coupling.measurable_add_distOnConst c
  refine ⟨fun g => LP.traceAt t (AdmCode.admDrv h44 hS.kappa_pos hS.kappa_lt_four (π / 2) (c₀, g + c)).1, ?_, ?_⟩
  · exact (LP.measurable_traceAt t).comp (measurable_fst.comp
      ((AdmCode.measurable_admDrv h44 hS.kappa_pos hS.kappa_lt_four (π / 2)).comp (measurable_const.prodMk hadd)))
  · filter_upwards [hD, hβtr] with ω hω hη
    have hcent : WholeField.centredField h u₀ ω + c = h ω := by
      simp only [WholeField.centredField, hc, sub_add_cancel]
    simp only [hcent, ← hω.2]
    have hcc := StripWall.continuous_of_isRegularDriver (hregE ω) hω.1
    exact (LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn (hregE ω).2.1 ENNReal.coe_lt_top).symm

/-- The countable unbounded set of stops `{n + 2 : n ∈ ℕ}` (all after the change time `1` of `α`). -/
def stops : Set ℝ≥0 := range fun n : ℕ => (((n : ℚ≥0) + 2 : ℚ≥0) : ℝ≥0)

theorem stops_countable : stops.Countable := countable_range _

theorem coe_stop (n : ℕ) : ((((n : ℚ≥0) + 2 : ℚ≥0) : ℝ≥0)) = (n : ℝ≥0) + 2 := by
  push_cast
  rfl

theorem exists_stop_lt (a : ℝ≥0) : ∃ q ∈ stops, a < q := by
  obtain ⟨n, hn⟩ := exists_nat_ge a
  refine ⟨_, ⟨n, rfl⟩, ?_⟩
  dsimp only
  rw [coe_stop]
  calc a ≤ n := hn
    _ < (n : ℝ≥0) + 2 := by simp

theorem one_lt_of_mem_stops {q : ℝ≥0} (hq : q ∈ stops) : 1 < q := by
  obtain ⟨n, rfl⟩ := hq
  dsimp only
  rw [coe_stop]
  calc (1 : ℝ≥0) < 2 := one_lt_two
    _ ≤ (n : ℝ≥0) + 2 := le_add_of_nonneg_left zero_le

/-- **(RS13.3) for the strip system** (p. 411): almost surely `β = η_{π/2}` has points off the complete range of
`α = η^{1,∞}_{−π/2,θ₁}` at arbitrarily late times, for `θ₁ ∈ (−π/2, π/2)`, given the walls' reverse first-visit order
with every point after the seed visited (Lemma 5.7). -/
theorem ae_late_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω))
    {α β : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    {η : Ω → ℝ → ℂ} (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hrev : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω)) :
    ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (α ω) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  set X := WholeField.centredField h u₀ with hXdef
  have hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hm := StripSys.neg_pi_div_two_mem_Icc
  -- the first path `α`
  have hDα : StripWall.IsDetTwoPiece P h (Es (StripSys.alphaSpec θ₁)) :=
    StripWall.isDetTwoPiece_of_heights h44 hκ hκ4 hb hh (hS.isStagedHistory_alpha hθ₁c) hregα (hL44 _ hm)
      (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c) hθ₁c.1 (by linarith [hθ₁c.2])
  have hαdet := hDα.hdet hregα u₀ hαtr
  have hαloc := StripWall.isEntranceHistoryLocal_alpha h44 hS hcumL hcumR hθ₁c hregα hu₀ hαc hα0 hαm hαtr
  have hαs := StripWall.ae_simple_trace_alpha hS hcumL hcumR hθ₁c hregα
  have hαsp := StripWall.ae_isSimpleProper_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαtr
  have hαim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (α ω t).im := by
    filter_upwards [hαsp] with ω hω t
    rcases eq_zero_or_pos t with rfl | ht
    · rw [hα0]; simp
    · exact (hω.2.2.2.1 t ht).le
  obtain ⟨gα, hgα⟩ := StripWall.exists_isLocalSetMean_prefix hX hαc hα0 hαm hαdet hαloc
  have hside₁ := StripWall.ae_sideHeights_second hκ hb hh (hS.isStagedHistory_alpha hθ₁c) hregα
    (hαs.mono fun ω hω => hω.1) hu₀ hαc hα0 hαm hαdet hαloc
    (by filter_upwards [hαtr, hαsp] with ω h1 h2 using ⟨h1, h2.2.1, h2.2.2.2.1⟩) hgα
  -- the second path `β = η_{π/2}`
  have hβs := ae_simple_trace_leftExtremal_strip hS hcumL hcumR
  have hβsp := ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr
  have hβim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (β ω t).im := by
    filter_upwards [hβsp] with ω hω t
    rcases eq_zero_or_pos t with rfl | ht
    · rw [hβ0]; simp
    · exact (hω.2.2.2.1 t ht).le
  have hβdet := hdet_leftExtremal h44 hS hcumL hcumR hregE u₀ hβtr
  have hβtr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (Es StripSys.leftExtremalSpec 0 ω).1 t)
      ((Es StripSys.leftExtremalSpec 0 ω).2) (fun t => β ω t - ((0 : ℝ) : ℂ)) := by
    filter_upwards [hβs, hβtr] with ω h1 h2
    rw [h1.1]
    simpa only [Complex.ofReal_zero, sub_zero] using h2
  have hfl : IsFlowLine κ b jumps 0 (π / 2) P h β (fun ω => (Es StripSys.leftExtremalSpec 0 ω).2) := by
    refine StripWall.isFlowLine_of_isFlowLineDriver
      (isFlowLineDriver_leftExtremal hκ hb hh hS.isStagedHistory_leftExtremal) ?_
    filter_upwards [hβs, hβtr] with ω h1 h2
    rw [h1.1]
    exact h2
  have hζβ : ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ := hβs.mono fun ω hω => hω.1
  have hβloc : ∀ q : ℝ≥0, Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (β ω) q) X P := fun q =>
    Restart.StagedEntrance.isEntranceHistoryLocal_frozenPath_of_isFlowLine hκ hκ4 hb hh hfl hζβ hu₀ hβc hβm q
      (Eventually.of_forall fun ω t _ => rfl)
  have hfz0 : ∀ q : ℝ≥0, ∀ ω, frozenPath (β ω) q 0 = 0 := fun q ω => by
    simp only [frozenPath, min_eq_left (zero_le : (0 : ℝ≥0) ≤ q), hβ0]
  have hβmean : ∀ q : ℝ≥0, ∃ g, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) X P g := fun q => by
    have hloc := StripMark.isLocalSet_range hX (fun ω => continuous_frozenPath (hβc ω)) (hfz0 q)
      (fun t => hβm _) (Restart.StagedEntrance.frozenPath_ae_eq_comp hβdet q) (hβloc q) q
    simp only [image_frozenPath_Icc] at hloc
    exact IsLocalSet.exists_isLocalSetMean hX (StripMark.measurable_range hβc hβm q) hloc
  choose gβ hgβ using hβmean
  have hside₂ : ∀ q ∈ stops, ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (β ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (β ω '' Icc 0 q ∩ H) → gβ q ω φ = ∫ z, v z * φ z) →
      ∀ s, 0 < s → s < q →
        HasSideHeights κ (π / 2) (β ω) 0 (Es StripSys.leftExtremalSpec 0 ω).1 q (β ω s) v u₀ := by
    intro q _
    have hg' : IsLocalSetMean (fun ω => frozenPath (β ω) q '' Icc 0 q ∩ H) X P (gβ q) := by
      simpa only [image_frozenPath_Icc] using hgβ q
    have key := Aux119Heights.ae_hasSideHeights_of_isFlowLine hκ hb hh hfl hβtr' hu₀
      (ηc := fun ω => frozenPath (β ω) q) (fun ω => continuous_frozenPath (hβc ω)) (hfz0 q) (fun t => hβm _)
      (Restart.StagedEntrance.frozenPath_ae_eq_comp hβdet q) (hβloc q) q
      (Eventually.of_forall fun ω t ht _ => by simp only [frozenPath, min_eq_left ht]) hg'
    simp only [image_frozenPath_Icc] at key
    filter_upwards [key, hζβ, hβsp] with ω hk hζ hsp v hv hrep s hs1 hs2
    exact hk (by rw [hζ]; exact ENNReal.coe_lt_top) v hv hrep s hs2 (hsp.2.2.2.1 s hs1)
  -- the first visits and the paths
  have hpath : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω) ∧
      Continuous (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1) ∧
      catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1 0 = 0 ∧
      IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω) ∧
      Continuous (Es StripSys.leftExtremalSpec 0 ω).1 ∧ (Es StripSys.leftExtremalSpec 0 ω).1 0 = 0 ∧
      Injective (α ω) ∧ Injective (β ω) ∧ (∀ t, 0 < t → α ω t ∈ H) ∧
      Tendsto (fun t => ‖α ω t‖) atTop atTop ∧ Tendsto (fun t => ‖β ω t‖) atTop atTop ∧
      StrictAntiOn (fun t => cfT (η ω) (α ω t)) (Ioi 0) ∧ StrictAntiOn (fun t => cfT (η ω) (β ω t)) (Ioi 0) := by
    filter_upwards [hαtr, hαs, hαsp, hβtr, hβs, hβsp, hrev] with ω hα1 hα2 hα3 hβ1 hβ2 hβ3 hr
    obtain ⟨hcc, hc0⟩ := StripWall.continuous_catPath_of_isRegularDriver (hregα 0 ω) (hregα 1 ω) hα2.1.1
      hα2.1.2 1
    exact ⟨hα1, hcc, hc0, hβ1, StripWall.continuous_of_isRegularDriver (hregE ω) hβ2.1, (hregE ω).2.1, hα3.2.1,
      hβ3.2.1, hα3.2.2.2.1, hα3.2.2.2.2, hβ3.2.2.2.2, strictAntiOn_cfT hα3.2.1 (hηc ω) hr.1 hr.2.1,
      strictAntiOn_cfT hβ3.2.1 (hηc ω) hr.2.2.1 hr.2.2.2⟩
  have hlate := ae_late_of_sideHeights_frozen hX hαc hα0 hαm hαdet hαloc hαim hβc hβ0 hβm hβdet hβloc hβim
    (W₁ := fun ω => catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1)
    (W₂ := fun ω => (Es StripSys.leftExtremalSpec 0 ω).1) (fun ω => cfT (η ω)) hpath hκ hκ4 hθ₁c.1 hθ₁.2
    (t₀ := 1) stops_countable stops_countable (fun a => (exists_stop_lt a).imp fun q hq => ⟨hq.1, hq.2.le⟩)
    exists_stop_lt (gα := gα) (gβ := gβ) (fun q _ => hgα q) (fun q _ => hgβ q)
    (fun q hq => by
      obtain ⟨n, rfl⟩ := hq
      have key := hside₁ ((n : ℚ≥0) + 2) (one_lt_of_mem_stops ⟨n, rfl⟩)
      filter_upwards [key, hαsp] with ω hk hsp v hv hrep s hs1 hs2
      exact hk v hv hrep s hs1 hs2 (hsp.2.2.2.1 s (lt_of_le_of_lt zero_le hs1)))
    hside₂
  filter_upwards [hlate] with ω hω N
  obtain ⟨t, hNt, ht⟩ := hω N
  exact ⟨t, hNt, fun hmem => ht (subset_closure hmem)⟩

end Strip

end StripPocketPath

end Sec7

end InteractingSLE
