/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentG
import InteractingSLE.Spec.Restart.ConverseBeforeK2
import InteractingSLE.Spec.Restart.FlowStopIdentLift

/-!
# Flow locality for Cameron–Martin shift pairs from (L1) on the enlargement

Packet PROVE-L1-CM (`planning/handoffs/PROVE-L1G.md` §4.2). The only consumer of `RLC.FlowLocalityStatement` is
Lemma G3 (`RLC.g3ChartComparisonStatement_of_locality`), and G3 uses it only for a **Cameron–Martin shift pair**: a
GFF `H₀` (data `b`) under `Q₀`, a deterministic distribution `T` vanishing on test functions supported in `N`, and
`Ĥ = H₀ + T`, a GFF with data `bR` under an equivalent law `Q` (`RLC.exists_shift_isGFFWithBoundaryData`). The class
is symmetric: `H₀ = Ĥ + (−T)`.

PROVE-L1G's (L1) (`FlowStopIdentG.FlowLineStopIdentLStatement`) asks for a Brownian motion of the stopped coupling on
the given space at all times; after the stop it has no source. Here (L1) is stated **on the enlargement**
`S × (ℕ → ℝ)` (the noise space of `ConverseBefore.exists_noiseBM`), where independent noise is available, and only
for shift pairs:

* `FlowPathFacts`, `ae_flowPathFacts`: the pathwise facts of a flow line (an integrated path of its word whose driver
  has the path as generating trace);
* `isStoppedFlowLineG_of_L`: PROVE-L1G's Galmarino conversion (`flowLineStopIdentGStatement_of_L`) for a stopped
  flow line on any space, given the pathwise facts of the original flow line there;
* `FlowLineStopIdentCMStatement` (**named input**): (L1) with the lifetime clause, for shift pairs, on the enlargement;
  `flowLineStopIdentCMStatement_of_L`: it follows from PROVE-L1G's input `FlowStopIdentG.FlowLineStopIdentLStatement`
  (shift pairs agree near `N`; the stopped coupling lifts along `fst`, `FlowStopIdentLift.isStoppedFlowLineL_fst`), so
  it is no stronger;
* `ae_stopMatch_of_CM`: the flow line of `H₀`, stopped at its exit time from `V`, matches on that interval the
  field-determined flow line of `Ĥ` (Aux. lemma 54 for Galmarino stops and Theorems 1.2–1.3, run on the enlargement,
  the conclusion brought back to `S` by `ConverseBefore.ae_of_ae_fst`);
* `FlowLocalityShiftStatement`: `RLC.FlowLocalityStatement` for shift pairs;
* **`flowLocalityShiftStatement_of_CM`**, `flowLocalityShiftStatement_of_CM_through`: flow locality for shift pairs
  from the named input, Aux. lemma 54 for Galmarino stops (or the WFS kernel target `WFS.ThroughKernelStatement`) and
  Theorems 1.2–1.3.

R43/R48: Theorems 1.2–1.3 are hypotheses; these results serve Theorem 1.5 (Lemma G3) only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCM

open LawUnique StoppedExtend StoppedExtendWF FlowStopIdentG Exist.Staged ConverseBefore

/-! ### The pathwise facts of a flow line -/

/-- **The pathwise facts of a flow line**: an integrated path of the flow-line word of `(b, J)` from `y` at the angle
`θ` with lifetime `U`, whose driver has `Γ − y` as generating trace through `U`. -/
def FlowPathFacts (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (y θ : ℝ) (Γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) : Prop :=
  ∃ (w : ℝ≥0 → ℝ) (vL : Fin (flowLineNL b J y) → ℝ≥0 → ℝ) (vR : Fin (flowLineNR b J y) → ℝ≥0 → ℝ)
    (β : ℝ≥0 → ℝ), IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
      (flowLineRhoR κ b J y θ) w vL vR β U ∧ IsGeneratingTrace w U fun t => Γ t - y

/-- A flow line has its pathwise facts almost surely. -/
theorem ae_flowPathFacts {κ θ y : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {S : Type*} [MeasurableSpace S] {P : Measure S}
    {h : S → DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} (hΓ : IsFlowLine κ b J y θ P h Γ U) :
    ∀ᵐ x ∂P, FlowPathFacts κ b J y θ (Γ x) (U x) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hC, hgen⟩ := hΓ
  filter_upwards [hC.1.2.2.2.2, hgen] with x hp hg
  exact ⟨fun t => W t x, fun i t => VL i t x, fun j t => VR j t x, fun t => B t x, hp, hg⟩

/-! ### The Galmarino rule on any space -/

/-- **(L1G) from (L1) with the lifetime clause, on any space** (PROVE-L1G's `flowLineStopIdentGStatement_of_L`, with
the pathwise facts of the original flow line as the only input about it): a stopped flow line of the data
`(bR, Ĵ)` through the exit time of `Γ` from `V`, with the lifetime clause, is a stopped flow line through a Galmarino
stop, the rule being `flowRule` with the seed condition of `(b, J)`. -/
theorem isStoppedFlowLineG_of_L {κ θ y : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {V : Set ℂ} (hV : IsOpen V)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {Γ : Ω → ℝ≥0 → ℂ}
    {U : Ω → ℝ≥0∞} (hb : ∀ᵐ ω ∂P, FlowPathFacts κ b J y θ (Γ ω) (U ω))
    (hL : IsStoppedFlowLineL κ bR Ĵ y θ V P h Γ fun ω => RLC.exitTime V (Γ ω) (U ω)) :
    IsStoppedFlowLineG κ bR Ĵ y θ P h Γ fun ω => RLC.exitTime V (Γ ω) (U ω) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen, hlife⟩ := hL
  set e : Ω → ℝ≥0∞ := fun ω => RLC.exitTime V (Γ ω) (U ω) with he
  set R := flowRule (SeedStop κ b J y θ V) y V (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ) with hRdef
  have hR : ∀ᵐ ω ∂P, e ω = R (killedHistory W VL VR e ω) := by
    filter_upwards [hSC.1.ae_path, hSC.2.1, hgen, hlife, hb] with ω hp hc hg hl hf
    obtain ⟨w, vL, vR, β, hp₀, hg₀⟩ := hf
    have hs := exitTime_seed (θ := θ) hV hp₀ hg₀
    exact flowRule_killedHistory (e := e) (ω := ω) hV hp hc hg hl rfl hs.1 hs.2
  exact ⟨h', 𝓕, W, VL, VR, B, R, htr, hSC, measurable_flowRule _ _ _ _ _, isHistGalmarino_flowRule _ _ _ _ _, hR,
    hgen⟩

/-! ### (L1) for shift pairs, on the enlargement -/

/-- **Named input: (L1) with the lifetime clause, for Cameron–Martin shift pairs, on the enlargement** (Aux. lemma 97's
proof, pp. 326–327, and Lemma G3's proof, pp. 492–493, in the shift-pair form of `planning/handoffs/PROVE-L1G.md`
§4.2). Fix `0 < κ < 4`, data `b` (jumps `J`) and `bR` (jumps `Ĵ`) agreeing on an open `O ⊆ ℝ`, an open `N` with real
points only over `O` and a bounded open `V` with `closure V ⊆ N`. Let `Q₀`, `Q` be equivalent probability measures on
`S`, `H₀` a GFF with data `b` under `Q₀`, `T` a deterministic distribution vanishing on the test functions supported
in `N`, and `Ĥ = H₀ + T` a GFF with data `bR` under `Q`. Then for every angle-`θ` flow line `Γ` of `H₀` from `y`
(lifetime `U`), there is a noise law `ν` on `ℕ → ℝ` such that on `S × (ℕ → ℝ)` under `Q ⊗ ν`, the path `Γ` (read
through the first factor), stopped at its exit time from `V`, is a stopped flow line of `Ĥ` (read through the first
factor) with the data `(bR, Ĵ)`, with the lifetime clause (`FlowStopIdentG.IsStoppedFlowLineL`). -/
def FlowLineStopIdentCMStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N → ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ → (∀ x, Ĥ x = H₀ x + T) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLineL κ bR Ĵ y θ V (Q.prod ν) (fun p => Ĥ p.1) (fun p => Γ p.1)
          fun p => RLC.exitTime V (Γ p.1) (U p.1)

/-- **PROVE-L1G's named input gives this one**: for a shift pair the fields agree on test functions supported in `N`,
so `FlowStopIdentG.FlowLineStopIdentLStatement` gives the stopped flow line with the lifetime clause on `S` under `Q`;
read through the first factor of `Q ⊗ δ₀` it is one on the enlargement (`FlowStopIdentLift.isStoppedFlowLineL_fst`).
So the enlarged shift-pair input is no stronger than PROVE-L1G's. -/
theorem flowLineStopIdentCMStatement_of_L (hL : FlowLineStopIdentLStatement.{u}) :
    FlowLineStopIdentCMStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ T hH₀ hĤ hsh hT0
    Γ U hΓ
  have hagr : ∀ (x : S) (φ : TestOn upperHalfPlaneOpens), tsupport φ ⊆ N → Ĥ x φ = H₀ x φ := fun x φ hφ => by
    rw [hsh x]
    show H₀ x φ + T φ = H₀ x φ
    rw [hT0 φ hφ, add_zero]
  have hL1 := hL κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U hΓ
  have hμ : (Q.prod (Measure.dirac (0 : ℕ → ℝ))).map Prod.fst = Q := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact ⟨Measure.dirac 0, inferInstance, FlowStopIdentLift.isStoppedFlowLineL_fst hμ hL1⟩

/-- **The stopped match for a shift pair** (from the named input, Aux. lemma 54 for Galmarino stops and Theorems
1.2–1.3): `Q`-almost surely, the flow line `Γ` of `H₀`, stopped at its exit time from `V`, is on `[0, e]` the
field-determined flow line of the data `(bR, Ĵ)` of `Ĥ` (`flowDetCode`), whose lifetime is at least `e`. -/
theorem ae_stopMatch_of_CM (hCM : FlowLineStopIdentCMStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) {O : Set ℝ}
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {N : Set ℂ} (hN : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O)
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVN : closure V ⊆ N) (y θ : ℝ) {S : Type u}
    [MeasurableSpace S] {Q₀ Q : Measure S} [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q] (hQ₀Q : Q₀ ≪ Q)
    (hQQ₀ : Q ≪ Q₀) {H₀ Ĥ : S → DistOn upperHalfPlaneOpens} {T : DistOn upperHalfPlaneOpens}
    (hH₀ : IsGFFWithBoundaryData Q₀ H₀ b J) (hĤ : IsGFFWithBoundaryData Q Ĥ bR Ĵ) (hsh : ∀ x, Ĥ x = H₀ x + T)
    (hT0 : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0) {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hΓ : IsFlowLine κ b J y θ Q₀ H₀ Γ U) :
    ∀ᵐ x ∂Q, IsStopMatch (flowDetCode h12p hκ bR Ĵ y θ (Ĥ x)) (Γ x) (RLC.exitTime V (Γ x) (U x)) := by
  obtain ⟨ν, hν, hL⟩ :=
    hCM κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ T hH₀ hĤ hsh hT0 Γ U hΓ
  have hfacts : ∀ᵐ p ∂(Q.prod ν), FlowPathFacts κ b J y θ (Γ p.1) (U p.1) :=
    ae_fst_of_ae (P₀ := ν) (q := fun x => FlowPathFacts κ b J y θ (Γ x) (U x)) (hQQ₀.ae_le (ae_flowPathFacts hΓ))
  have hG := isStoppedFlowLineG_of_L hV hfacts hL
  have m := hG.ae_stopMatch_of_extendGK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ bR Ĵ y θ)
  exact ae_of_ae_fst (P₀ := ν)
    (q := fun x => IsStopMatch (flowDetCode h12p hκ bR Ĵ y θ (Ĥ x)) (Γ x) (RLC.exitTime V (Γ x) (U x))) m

/-! ### Flow locality for shift pairs -/

/-- **Flow-line locality for Cameron–Martin shift pairs** (`RLC.FlowLocalityStatement` with the hypothesis "`Ĥ = H₀`
on test functions supported in `N`" strengthened to "`Ĥ = H₀ + T` for a deterministic `T` vanishing there", the only
form Lemma G3 uses): the angle-`θ` flow line `Γ` of `H₀` from `y` (under `Q₀`) and the angle-`θ` flow line `α` of `Ĥ`
from `y` (under `Q`) agree, `Q₀`-almost surely, up to and including their common exit time from `V`. -/
def FlowLocalityShiftStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N → ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ → (∀ x, Ĥ x = H₀ x + T) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0) →
    ∀ (Γ α : S → ℝ≥0 → ℂ) (U ζ : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      IsFlowLine κ bR Ĵ y θ Q Ĥ α ζ → ∀ᵐ x ∂Q₀, RLC.StoppedAgree V (Γ x) (U x) (α x) (ζ x)

/-- **Flow locality for shift pairs from (L1) on the enlargement**, Aux. lemma 54 for Galmarino stops and Theorems
1.2–1.3. The named input is applied twice, the second time to the reversed shift pair `(Ĥ, Q, bR) → (H₀, Q₀, b)`
with the shift `−T`; `StoppedExtend.stoppedAgree_of_matches` concludes. -/
theorem flowLocalityShiftStatement_of_CM (hCM : FlowLineStopIdentCMStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : FlowLocalityShiftStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ T hH₀ hĤ hsh hT0
    Γ α U ζ hΓ hα
  have m1 := ae_stopMatch_of_CM hCM hext h12p h13 hκ hκ4 hb hbR hO hbO hN hNO hV hVb hVN y θ hQ₀Q hQQ₀ hH₀ hĤ hsh
    hT0 hΓ
  have hsh' : ∀ x, H₀ x = Ĥ x + -T := fun x => by rw [hsh x, add_neg_cancel_right]
  have hT0' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → (-T) φ = 0 := fun φ hφ => by
    show -(T φ) = 0
    rw [hT0 φ hφ, neg_zero]
  have m2 := ae_stopMatch_of_CM hCM hext h12p h13 hκ hκ4 hbR hb hO (fun z hz => (hbO z hz).symm) hN hNO hV hVb hVN
    y θ hQQ₀ hQ₀Q hĤ hH₀ hsh' hT0' hα
  have c1 := isFlowDet_flowDetCode h12p hκ bR Ĵ y θ Q Ĥ α ζ hα
  have c2 := isFlowDet_flowDetCode h12p hκ b J y θ Q₀ H₀ Γ U hΓ
  filter_upwards [hQ₀Q.ae_le m1, hQ₀Q.ae_le c1, m2, c2] with z e1 e2 e3 e4
  exact stoppedAgree_of_matches e1 e2 e3 e4

/-- **Flow locality for shift pairs from (L1) on the enlargement, the WFS kernel target and Theorems 1.2–1.3**
(Aux. lemma 54 for Galmarino stops from `WFS.ThroughKernelStatement`, `WFS.stoppedHullExtendGKStatement_of_through`). -/
theorem flowLocalityShiftStatement_of_CM_through (hCM : FlowLineStopIdentCMStatement.{u})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{u, u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : FlowLocalityShiftStatement.{u} :=
  flowLocalityShiftStatement_of_CM hCM (fun _ hκ hκ4 => WFS.stoppedHullExtendGKStatement_of_through hκ
    (hT _ hκ hκ4)) h12p h13

end FlowStopIdentCM

end Restart

end InteractingSLE
