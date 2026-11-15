/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LawProofReg
import InteractingSLE.Spec.Supplement.S9BSide

/-!
# The filled pocket of Theorem GW4 from the exit shape of the walks

Packet PROVE-T14-GW4T2. PROVE-T14-GW4S reduced the filled-pocket clause of Theorem GW4 (`GW4Ident.GW4FillStatement`:
"if the counterflow reaches the exit `x_C` at a finite time `σ`, then `R⁻¹(C) ⊆ K'_σ`"; GB11's proof, p. 556: "its
two whole boundary arcs have been visited […] Its interior is then separated from the original target and is already
filled") to the barrier input and a deterministic named input `GW4Ident.GW4FillDetStatement`. That deterministic
statement asks for the pocket shape from GB11's barrier input alone, which does not contain it (GB11's source barrier
input takes the `C_j` to be "the Jordan interiors bounded by their two arcs between successive common contacts").

Here the shape is made explicit as a property of the two walks (`WalkExitShape`): for every between-component `C` and
every component chart of `C`, with exit `x_C` (the chart's boundary value at `0`), the frontier of `C` lies on the two
walks beyond `x_C` (`frontier C ⊆ α_R([s, ∞)) ∪ α_L([t, ∞))`, `α_R(s) = α_L(t) = x_C`). With it the filled pocket is
**proved** (`relDom_subset_fwdHull_of_visited`, `fill_of_exitShape`):

* `0 ∉ C̄` (the walks are injective from `0` and `x_C ≠ 0` since `x_C` is visited), and every point of `∂C ∩ ℍ` is
  visited by the physical counterflow at or before `σ` (reverse first visits along each walk);
* hence (deterministic Loewner topology) the unbounded component `U` of `ℍ \ γ([0, σ])` read physically,
  `V = −1/U`, is a preconnected set that meets `C` and misses `∂C`, so `V ⊆ C`; as `U` is unbounded, `0 ∈ C̄`, a
  contradiction. So `R⁻¹(C) ⊆ K'_σ`.

The barrier input of the chain is strengthened accordingly (`GW4BarrierShapeRegStatement`: the R51 barrier input plus
`WalkExitShape` of the walks of `ω₀`, a property of `ω₀` alone), and the R51 filled pocket follows from it with no
further input (`gw4FillRegStatement_of_barrierShape`), so `GW4Ident.GW4FillDetStatement` is no longer needed.

## Main results

* `WalkExitShape`, `GW4BarrierShapeRegStatement`, `gw4BarrierRegStatement_of_shape`;
* **`relDom_subset_fwdHull_of_visited`** (deterministic core), **`fill_of_exitShape`**;
* **`gw4FillRegStatement_of_barrierShape`**, `gw4RelativeHullRegStatement_of_barrierShape`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Reg

open GW4Traverse GW4Ident

/-! ### The exit shape of the walks -/

/-- **The exit shape of the walks** (GB11's barrier input, p. 555: "Let `C_j` be the Jordan interiors bounded by
their two arcs between successive common contacts"; Lemma GB11: "write its flow-oriented endpoints as `x_C, y_C`"):
for every between-component `C` of the ranges of `α_R`, `α_L` and every component chart `c` of `C`, the boundary
value `x_C` of `c` at `0` is a common point `α_R(s) = α_L(t)` beyond which (in the flow order from `0`) the whole
frontier of `C` lies. -/
def WalkExitShape (αR αL : ℝ≥0 → ℂ) : Prop :=
  ∀ C ∈ betweenComponents (range αR) (range αL), ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
    ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) →
      ∃ s t : ℝ≥0, αR s = xC ∧ αL t = xC ∧ frontier C ⊆ αR '' Ici s ∪ αL '' Ici t

/-! ### Elementary facts -/

theorem isClosed_range_of_isCompleteSimpleFlow {α : ℝ≥0 → ℂ} (h : GB11.IsCompleteSimpleFlow α) :
    IsClosed (range α) := by
  rw [← image_univ]
  exact Supp9B.isClosed_image ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩ isClosed_univ

/-- A between-component of two closed sets is open. -/
theorem isOpen_of_mem_betweenComponents {R L C : Set ℂ} (hR : IsClosed R) (hL : IsClosed L)
    (hC : C ∈ betweenComponents R L) : IsOpen C := by
  obtain ⟨z, -, -, -, rfl⟩ := hC
  exact (QuantumZipper.isOpen_H.sdiff (hR.union hL)).connectedComponentIn

/-- For `p ≠ 0`, the first physical visit of `p` is the first visit of `−1/p` by the trace. -/
theorem firstVisit_eq_aux130 (γ : ℝ≥0 → ℂ) {p : ℂ} (hp : p ≠ 0) :
    GB11.firstVisit γ p = Sec7.Aux130.firstVisit γ (-p⁻¹) := by
  unfold GB11.firstVisit Sec7.Aux130.firstVisit
  refine iInf_congr fun t => iInf_congr_Prop ⟨fun h => ?_, fun h => ?_⟩ fun _ => rfl
  · rw [← h.2, inv_neg, inv_inv, neg_neg]
  · refine ⟨by rw [h]; exact neg_ne_zero.2 (inv_ne_zero hp), ?_⟩
    rw [h, inv_neg, inv_inv, neg_neg]

/-- **A finite first physical visit is attained** (for a continuous trace). -/
theorem exists_eq_firstVisit {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {p : ℂ} (hT : GB11.firstVisit γ p < ⊤) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) = GB11.firstVisit γ p ∧ γ t ≠ 0 ∧ -(γ t)⁻¹ = p := by
  have hp : p ≠ 0 := by
    rintro rfl
    refine (lt_top_iff_ne_top.1 hT) (top_le_iff.1 (le_iInf₂ fun t ht => ?_))
    exact absurd (neg_eq_zero.1 ht.2) (inv_ne_zero ht.1)
  rw [firstVisit_eq_aux130 γ hp] at hT ⊢
  have h := Sec7.Aux130.apply_firstVisit hγ hT
  refine ⟨_, ENNReal.coe_toNNReal hT.ne, ?_, ?_⟩
  · rw [h]; exact neg_ne_zero.2 (inv_ne_zero hp)
  · rw [h, inv_neg, inv_inv, neg_neg]

/-- A finite first physical visit is not the original target `0`. -/
theorem ne_zero_of_firstVisit_lt_top {γ : ℝ≥0 → ℂ} {p : ℂ} (hT : GB11.firstVisit γ p < ⊤) : p ≠ 0 := by
  rintro rfl
  refine (lt_top_iff_ne_top.1 hT) (top_le_iff.1 (le_iInf₂ fun t ht => ?_))
  exact absurd (neg_eq_zero.1 ht.2) (inv_ne_zero ht.1)

/-! ### The deterministic core -/

/-- **A pocket whose boundary in `ℍ` has been visited is filled** (deterministic). Let `γ` be a generating trace of
`W'` on `[0, ∞]` (the counterflow in the chart `R(z) = −1/z`), `C ⊆ ℍ` open with `0 ∉ C̄`, and suppose every point
of `∂C ∩ ℍ` is visited by the physical counterflow `−1/γ` by time `σ`. Then `R⁻¹(C) ⊆ K'_σ`.

Proof: if `w ∈ R⁻¹(C)` were outside `K'_σ`, it would lie in the unbounded component `U` of `ℍ \ γ([0, σ])`; the
physical image `V = −1/U` is preconnected, meets `C` at `−1/w` and misses `∂C` (a point of `∂C ∩ ℍ` is `−1/γ(t)`,
`t ≤ σ`, and `γ(t) ∉ U`), so `V ⊆ C`; since `U` is unbounded, `V` has points arbitrarily close to `0`, so `0 ∈ C̄`. -/
theorem relDom_subset_fwdHull_of_visited {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W' ⊤ γ)
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) (h0 : (0 : ℂ) ∉ closure C) {σ : ℝ≥0}
    (hvis : ∀ p ∈ frontier C, p ∈ H → ∃ t : ℝ≥0, t ≤ σ ∧ γ t ≠ 0 ∧ -(γ t)⁻¹ = p) :
    relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal) σ := by
  intro w hw
  by_contra hK
  obtain ⟨⟨z₀, -, hcc⟩, hunb⟩ := hγ.2.2 σ ENNReal.coe_lt_top
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) (σ : ℝ) with hKdef
  set Γ := γ '' Icc 0 σ with hΓ
  have hwH : w ∈ H := relDom_subset_H hCH hw
  have hUpc : IsPreconnected (H \ K) := hcc ▸ isPreconnected_connectedComponentIn
  have hUΓ : ∀ u ∈ H \ K, u ∉ Γ := by
    rw [← hcc]
    intro u hu
    exact (connectedComponentIn_subset _ _ hu).2
  set V := (fun u : ℂ => -u⁻¹) '' (H \ K) with hV
  have hcont : ContinuousOn (fun u : ℂ => -u⁻¹) (H \ K) := fun u hu =>
    (continuousAt_negInv (ne_zero_of_mem_H' hu.1)).continuousWithinAt
  have hVpc : IsPreconnected V := hUpc.image _ hcont
  have hVC : V ⊆ C := by
    refine hVpc.subset_of_closure_inter_subset hCo ⟨-w⁻¹, ⟨w, ⟨hwH, hK⟩, rfl⟩, hw⟩ ?_
    rintro q ⟨hqc, hqV⟩
    by_contra hqC
    obtain ⟨u, hu, rfl⟩ := hqV
    have hfr : -u⁻¹ ∈ frontier C := ⟨hqc, by rwa [hCo.interior_eq]⟩
    obtain ⟨t, htσ, hγt, heq⟩ := hvis _ hfr (negInv_mem_H' hu.1)
    have : γ t = u := by
      have h2 := congrArg (fun z : ℂ => -z⁻¹) heq
      simpa only [negInv_negInv'] using h2
    exact hUΓ u hu ⟨t, ⟨zero_le, htσ⟩, this⟩
  apply h0
  rw [Metric.mem_closure_iff]
  intro ε hε
  rw [isBounded_iff_forall_norm_le] at hunb
  push Not at hunb
  obtain ⟨u, hu, hlt⟩ := hunb (1 / ε)
  have hu0 : u ≠ 0 := ne_zero_of_mem_H' hu.1
  refine ⟨-u⁻¹, hVC ⟨u, hu, rfl⟩, ?_⟩
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu0
  rw [dist_zero_left, norm_neg, norm_inv]
  calc ‖u‖⁻¹ < (1 / ε)⁻¹ := inv_strictAnti₀ (by positivity) hlt
    _ = ε := by rw [one_div, inv_inv]

/-- **A pocket bounded by the two walks beyond a visited common point is filled** (deterministic). Let the walks
`α_R`, `α_L` be complete simple flows visited in strict reverse first-visit order by the physical counterflow `−1/γ`,
`C ⊆ ℍ` open with frontier on the walks beyond a common point `x = α_R(s) = α_L(t)`. If `x` is visited at a finite
time `σ`, then `R⁻¹(C) ⊆ K'_σ`. -/
theorem fill_of_frontier_subset {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W' ⊤ γ)
    {αR αL : ℝ≥0 → ℂ} (hfR : GB11.IsCompleteSimpleFlow αR) (hfL : GB11.IsCompleteSimpleFlow αL)
    (hrevR : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (αR a') < GB11.firstVisit γ (αR a))
    (hrevL : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (αL a') < GB11.firstVisit γ (αL a))
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {s t : ℝ≥0} {xC : ℂ} (hs : αR s = xC) (ht : αL t = xC)
    (hfr : frontier C ⊆ αR '' Ici s ∪ αL '' Ici t) (hσ : GB11.firstVisit γ xC < ⊤) :
    relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal) (GB11.firstVisit γ xC).toNNReal := by
  have hγc : Continuous γ := by
    have h := hγ.2.1
    have hU : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun x => show (x : ℝ≥0∞) ≤ ⊤ from le_top
    rw [hU] at h
    exact continuousOn_univ.1 h
  have hx0 : xC ≠ 0 := ne_zero_of_firstVisit_lt_top hσ
  obtain ⟨tσ, htσ, -, -⟩ := exists_eq_firstVisit hγc hσ
  have hσeq : (GB11.firstVisit γ xC).toNNReal = tσ := by rw [← htσ, ENNReal.toNNReal_coe]
  rw [hσeq]
  have hs0 : 0 < s := by
    refine pos_iff_ne_zero.2 fun h0 => hx0 ?_
    rw [← hs, h0, hfR.2.2.1]
  have ht0 : 0 < t := by
    refine pos_iff_ne_zero.2 fun h0 => hx0 ?_
    rw [← ht, h0, hfL.2.2.1]
  -- the origin is not adherent to `C`
  have h0 : (0 : ℂ) ∉ closure C := by
    rw [closure_eq_self_union_frontier]
    rintro (h0C | h0fr)
    · exact ne_zero_of_mem_H' (hCH h0C) rfl
    · rcases hfr h0fr with ⟨r, hr, hr0⟩ | ⟨r, hr, hr0⟩
      · have : r = 0 := hfR.2.1 (hr0.trans hfR.2.2.1.symm)
        exact (lt_irrefl (0 : ℝ≥0)) (lt_of_lt_of_le hs0 (this ▸ (hr : s ≤ r)))
      · have : r = 0 := hfL.2.1 (hr0.trans hfL.2.2.1.symm)
        exact (lt_irrefl (0 : ℝ≥0)) (lt_of_lt_of_le ht0 (this ▸ (hr : t ≤ r)))
  -- every boundary point in `ℍ` is visited by `σ`
  have hvis : ∀ p ∈ frontier C, p ∈ H → ∃ r : ℝ≥0, r ≤ tσ ∧ γ r ≠ 0 ∧ -(γ r)⁻¹ = p := by
    intro p hp _
    have key : ∀ (α : ℝ≥0 → ℂ) (a : ℝ≥0), α a = xC → 0 < a →
        (∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a)) →
        ∀ r ∈ Ici a, α r = p → ∃ r' : ℝ≥0, r' ≤ tσ ∧ γ r' ≠ 0 ∧ -(γ r')⁻¹ = p := by
      intro α a ha ha0 hrev r hr hrp
      have hle : GB11.firstVisit γ p ≤ GB11.firstVisit γ xC := by
        rcases eq_or_lt_of_le (show a ≤ r from hr) with rfl | hlt
        · rw [← hrp, ha]
        · rw [← hrp, ← ha]; exact (hrev a r ha0 hlt).le
      obtain ⟨r', hr', hγr', hr'p⟩ := exists_eq_firstVisit hγc (lt_of_le_of_lt hle hσ)
      refine ⟨r', ?_, hγr', hr'p⟩
      have : (r' : ℝ≥0∞) ≤ tσ := by rw [hr', htσ]; exact hle
      exact_mod_cast this
    rcases hfr hp with ⟨r, hr, hrp⟩ | ⟨r, hr, hrp⟩
    · exact key αR s hs hs0 hrevR r hr hrp
    · exact key αL t ht ht0 hrevL r hr hrp
  exact relDom_subset_fwdHull_of_visited hγ hCo hCH h0 hvis

/-- **The filled pocket from the exit shape** (deterministic; replaces `GW4Ident.GW4FillDetStatement`). Under GB11's
barrier input and the exit shape of the walks, if the physical counterflow visits the exit `x_C` of a between-component
`C` at a finite time `σ`, then `R⁻¹(C) ⊆ K'_σ`. -/
theorem fill_of_exitShape {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W' ⊤ γ) {αR αL : ℝ≥0 → ℂ}
    (hB : GB11.IsGB11Barrier αR αL γ) (hS : WalkExitShape αR αL) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range αR) (range αL)) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) {xC : ℂ} (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC))
    (hσ : GB11.firstVisit γ xC < ⊤) :
    relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal) (GB11.firstVisit γ xC).toNNReal := by
  obtain ⟨hfR, hfL, -, -, -, hrevR, hrevL⟩ := hB
  obtain ⟨s, t, hs, ht, hfr⟩ := hS C hC c hc xC hxC
  exact fill_of_frontier_subset hγ hfR hfL hrevR hrevL
    (isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hfR)
      (isClosed_range_of_isCompleteSimpleFlow hfL) hC) (subset_H_of_mem_betweenComponents hC) hs ht hfr hσ

/-! ### The barrier input with the exit shape -/

/-- **Named input: the barrier input of GB11 for the actual sewn walks with their exit shape, R51 form**:
`GW4BarrierRegStatement` together with `WalkExitShape` of the two walks of `ω₀` (a deterministic property of the
walks of `ω₀`: GB11's source barrier input takes the between-components to be the two-arc Jordan pockets between
successive common contacts, with the flow-oriented exit `x_C`). -/
def GW4BarrierShapeRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∃ αR αL : ℝ≥0 → ℂ, range αR = R ∧ range αL = L ∧ WalkExitShape αR αL ∧
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → GB11.IsGB11Barrier αR αL γ

/-- The barrier input with the exit shape gives the R51 barrier input. -/
theorem gw4BarrierRegStatement_of_shape (hB : GW4BarrierShapeRegStatement.{u}) : GW4BarrierRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  obtain ⟨αR, αL, hR, hL, -, hbar⟩ := hω
  exact ⟨αR, αL, hR, hL, hbar⟩

/-- **The filled pocket in GW4's setting, R51 form, from the barrier input with the exit shape** (no further input:
`fill_of_exitShape`; the generating trace is given, so Theorem 1.3 is not used). -/
theorem gw4FillRegStatement_of_barrierShape (hB : GW4BarrierShapeRegStatement.{u}) :
    GW4FillRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hBω
  intro R L ν C hCm c hch
  obtain ⟨αR, αL, hαR, hαL, hshape, hbar⟩ := hBω
  filter_upwards [hbar] with ω hbarω
  intro γ hγ xC hxC hσ
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  exact fill_of_exitShape hγ (hbarω γ hγ) hshape hCm' hch' hxC hσ

/-- **Theorem GW4's relative hulls, R51 form, without the deterministic fill input** (conditional helper): Lemma
GB11, the barrier input with the exit shape, the R51 component law input, no return and Theorems 1.2–1.3. -/
theorem gw4RelativeHullRegStatement_of_barrierShape (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hGB11 : GB11.GB11Statement) (hB : GW4BarrierShapeRegStatement.{u})
    (hL : GW4RelativeLawRegStatement.{u}) (hNR : CounterflowNoReturnStatement.{u}) :
    GW4RelativeHullRegStatement.{u} :=
  gw4RelativeHullRegStatement_of_chain_ident
    (gw4RelativeChainRegStatement_of_gb11 h13 hGB11 (gw4BarrierRegStatement_of_shape hB)
      (gw4CompletionRegStatement_of_law h13 hL (gw4FillRegStatement_of_barrierShape hB) hNR))
    (gw4RelativeIdentRegStatement_of_law h12 h13 hL)

end GW4Reg

end Theorem14

end InteractingSLE
