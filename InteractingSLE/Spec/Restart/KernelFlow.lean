/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Kernel
import InteractingSLE.Spec.Restart.Integrate
import InteractingSLE.Spec.Restart.ChartSpace

/-!
# The general restart kernel: continuations that are canonical flows of the conditional field

Packet PROVE-RESTARTKERNEL. Theorem W8's proof (p. 541) finishes the restart in two steps: the nested Gaussian kernels
and Theorem 2.4 make every actual conditional future a flow of the conditional chart field, and then "Universal
finite-force determination now identifies each actual conditional future, with its reconstructed own stopping rule, as
the canonical flow of the same conditional field. Equality of the two individual field–history graph laws identifies
their joint pair law". This file isolates the second step in a form usable by every restart kernel of the project.

* **`IsFlowCode κ θ F`**: `F` is a Borel *canonical flow code*: from a word `c`, a seed `x` and a field `f` it returns
  a path code with a lifetime (`RestartSpace`'s coding, decoded continuously on the closed lifetime interval) such
  that, on every probability space, for every GFF `h` with the data of `c`, every path that agrees almost surely with
  the decoded code of `F ((c, x), h)` on its lifetime, with that lifetime, is the angle-`θ` flow line of `h` from `x`
  (determination by the field, Theorem 1.2, realized on any space as in `Exist.exists_isFlowLine_of_thm12_thm13`).
  `FlowCodeStatement` asserts that such codes exist for `0 < κ < 4`; it is the one global named input of the restart
  kernels proved here (it involves no conditioning).
* `IsCodeMatch p γ U`: the path `γ` with lifetime `U` is the decoded code `p` on `[0, U]`.
* `measurableSet_codeMatchSet`, `codeMatch_of_mem_codeMatchSet`: for continuous paths the match is a countable
  (dyadic) condition, hence a measurable event of `(datum, restart point)`.
* **`ae_isFlowLine_of_codeMatch`**: for every kernel `K` disintegrating `(β, X)` on `M`, if (R1) holds under `K` and
  almost surely on `M` the continuation coordinate of `X` matches the canonical flow code of the chart field
  (the pathwise determination identity "(Det)"), then for almost every datum `c` the continuation is, under `K c`, the
  flow line of the chart field with the word and seed of `c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open LQGMetric Sec2.Assembly

instance : Nonempty RestartSpace := ⟨(0, ((0, 0), 0), ((0, 0), 0))⟩

/-! ### Matching a decoded path code -/

/-- The path `γ` with lifetime `U` is the decoded path code `p`: the lifetimes agree and `γ = decPath p` on `[0, U]`. -/
def IsCodeMatch (p : (PCode × PCode) × ℝ≥0∞) (γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) : Prop :=
  U = p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U → γ t = decPath p t

/-- The dyadic form of the match, as a set of pairs (datum, restart point). -/
def codeMatchSet {C S : Type*} (G : C × S → (PCode × PCode) × ℝ≥0∞) (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) :
    Set (C × S) :=
  {p | U p.2 = (G p).2 ∧ ∀ n k : ℕ, (dyad n k : ℝ≥0∞) ≤ U p.2 → Γ p.2 (dyad n k) = decPath (G p) (dyad n k)}

theorem measurableSet_codeMatchSet {C S : Type*} [MeasurableSpace C] [MeasurableSpace S]
    {G : C × S → (PCode × PCode) × ℝ≥0∞} (hG : Measurable G) {Γ : S → ℝ≥0 → ℂ}
    (hΓ : ∀ t, Measurable fun s => Γ s t) {U : S → ℝ≥0∞} (hU : Measurable U) :
    MeasurableSet (codeMatchSet G Γ U) := by
  have hU' : Measurable fun p : C × S => U p.2 := hU.comp measurable_snd
  have hl : MeasurableSet {p : C × S | U p.2 = (G p).2} :=
    measurableSet_eq_fun hU' (measurable_snd.comp hG)
  have hd : ∀ n k : ℕ, MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) ≤ U p.2 →
      Γ p.2 (dyad n k) = decPath (G p) (dyad n k)} := fun n k => by
    have h1 : MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) ≤ U p.2} := measurableSet_le measurable_const hU'
    have h2 : MeasurableSet {p : C × S | Γ p.2 (dyad n k) = decPath (G p) (dyad n k)} :=
      measurableSet_eq_fun ((hΓ _).comp measurable_snd) ((measurable_decPath _).comp hG)
    have e : {p : C × S | (dyad n k : ℝ≥0∞) ≤ U p.2 → Γ p.2 (dyad n k) = decPath (G p) (dyad n k)} =
        {p : C × S | (dyad n k : ℝ≥0∞) ≤ U p.2}ᶜ ∪
          {p : C × S | Γ p.2 (dyad n k) = decPath (G p) (dyad n k)} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    exact h1.compl.union h2
  have e : codeMatchSet G Γ U = {p : C × S | U p.2 = (G p).2} ∩ ⋂ n : ℕ, ⋂ k : ℕ,
      {p : C × S | (dyad n k : ℝ≥0∞) ≤ U p.2 → Γ p.2 (dyad n k) = decPath (G p) (dyad n k)} := by
    ext p
    simp only [codeMatchSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  exact hl.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => hd n k)

/-- On the dyadic match set, a path continuous on its lifetime matches the code. -/
theorem codeMatch_of_mem_codeMatchSet {C S : Type*} {G : C × S → (PCode × PCode) × ℝ≥0∞}
    {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} {p : C × S}
    (hc : ContinuousOn (Γ p.2) {t | (t : ℝ≥0∞) ≤ U p.2}) (hp : p ∈ codeMatchSet G Γ U) :
    IsCodeMatch (G p) (Γ p.2) (U p.2) := by
  obtain ⟨hU, hd⟩ := hp
  refine ⟨hU, eqOn_of_dyad hc ?_ hd⟩
  rw [hU]
  exact continuousOn_decPath (G p)

/-- A match gives the dyadic match. -/
theorem mem_codeMatchSet_of_codeMatch {C S : Type*} {G : C × S → (PCode × PCode) × ℝ≥0∞}
    {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞} {p : C × S} (h : IsCodeMatch (G p) (Γ p.2) (U p.2)) :
    p ∈ codeMatchSet G Γ U :=
  ⟨h.1, fun _ _ hle => h.2 _ hle⟩

/-! ### Canonical flow codes -/

/-- **A Borel canonical flow code for the angle `θ`** (determination of flow lines by the field, Theorem 1.2,
realized on every space). `F` is jointly measurable in the word `c`, the seed `x` and the field, and for every sorted
word `c` and seed `x`, on every probability space, every GFF `h` with the data of `c` and every path `η` with lifetime
`ζ` that almost surely agree with the decoded code `F ((c, x), h)` on the lifetime: `η` is the angle-`θ` flow line of
`h` from `x` with available lifetime `ζ`. -/
def IsFlowCode (κ θ : ℝ)
    (F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞) : Prop :=
  Measurable F ∧ ∀ (c : BoundaryWord) (x : ℝ), c.IsSorted →
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData Q h c.fn c.jumps → (∀ᵐ ω ∂Q, IsCodeMatch (F ((c, x), h ω)) (η ω) (ζ ω)) →
      IsFlowLine κ c.fn c.jumps x θ Q h η ζ

/-- **Named input: canonical flow codes exist** for every angle, `0 < κ < 4`. Source: Theorem 1.2 (field
determination, jointly measurable in the word: `Exist.Staged.Theorem12ParamStatement`), Theorem 1.3 (the trace), and
the realization of the determined flow line on any space carrying a GFF with the same data (as in
`Exist.exists_isFlowLine_of_thm12_thm13`); the almost sure freedom in the lifetime uses a filtration containing the
null sets (`IsOptionalHullCoupling.congr_ae`). **Not proved in Lean.** -/
def FlowCodeStatement : Prop :=
  ∀ κ θ : ℝ, 0 < κ → κ < 4 → ∃ F, IsFlowCode κ θ F

/-! ### The continuations under a disintegrating kernel -/

/-- **The continuation is the flow line of the chart field under almost every kernel measure.** Let `K` disintegrate
the restart variable `X` over the datum `β` on `M`. Suppose that for almost every datum `c` the word `w c` is sorted and
under `K c` the chart field `H` is a GFF with that word ((R1), `ae_isGFFWithBoundaryData_of_condExp_word`), and that
almost surely on `M` the continuation coordinate `(Γ, U)` of `X` matches the canonical flow code of the chart field
with the word and seed of `β` ((Det)). Then for almost every datum `c`, under `K c`, `Γ` with lifetime `U` is the
angle-`θ` flow line of `H` from the seed `x c`. -/
theorem ae_isFlowLine_of_codeMatch {Ω : Type*} {C S : Type} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {w : C → BoundaryWord} (hw : Measurable w) {x : C → ℝ} (hx : Measurable x)
    {H : S → DistOn upperHalfPlaneOpens} (hH : Measurable H) {Γ : S → ℝ≥0 → ℂ}
    (hΓ : ∀ t, Measurable fun s => Γ s t) {U : S → ℝ≥0∞} (hU : Measurable U)
    (hΓc : ∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hF : IsFlowCode κ θ F)
    (hgff : ∀ᵐ c ∂(P.restrict M).map β,
      (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps)
    (hdet : ∀ᵐ ω ∂P, ω ∈ M → IsCodeMatch (F ((w (β ω), x (β ω)), H (X ω))) (Γ (X ω)) (U (X ω))) :
    ∀ᵐ c ∂(P.restrict M).map β, IsFlowLine κ (w c).fn (w c).jumps (x c) θ (K c) H Γ U := by
  set G : C × S → (PCode × PCode) × ℝ≥0∞ := fun p => F ((w p.1, x p.1), H p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (((hw.comp measurable_fst).prodMk (hx.comp measurable_fst)).prodMk
    (hH.comp measurable_snd))
  have hE := measurableSet_codeMatchSet hGm hΓ hU
  have hK := ae_ae_of_map_eq_compProd hM hβ hX hlaw hE (by
    filter_upwards [hdet] with ω hω hωM
    exact mem_codeMatchSet_of_codeMatch (G := G) (p := (β ω, X ω)) (hω hωM))
  filter_upwards [hK, hgff] with c hc ⟨hcs, hcg⟩
  refine hF.2 (w c) (x c) hcs (K c) H Γ U hcg ?_
  filter_upwards [hc] with s hs
  exact codeMatch_of_mem_codeMatchSet (G := G) (p := (c, s)) (hΓc s) hs

end Restart

end InteractingSLE
