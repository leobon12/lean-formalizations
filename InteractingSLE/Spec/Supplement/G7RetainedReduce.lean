/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RetainedPath

/-!
# Lemma G7 and the joint retained-pair carrier from one retained-pair restart input

Packet PROVE-G7. Sources: Lemma G7 (`source/spec/p481-528.md` L403–L422, pp. 497–498), the proof of Theorem 7.12D
(`source/spec/p529-576.md`, p. 543: "the outer-word argument of Aux. 85–86 gives the full canonical initial finite
word"), Lemma W2's proof (p. 531: "G7 identifies both actual fresh stopped paths with the canonical flows of the same
conditional finite-word field, in their actual joint field–path law").

`Supp7.G7RetainedPairStatement` (one tip, with the outer word) and `Supp9D.JointRetainedPairStatement` (both tips)
are two readings of one fact: at a retained pair `(u, r)` the conditional law of the field in the inherited
hydrodynamic chart at the second tip, together with the two fresh continuations read in relative capacity, is the
canonical finite-word coupling. This file states that fact once, **in terms of the measurable canonical chart field
of `G7RetainedMeas.lean`** (`RetData.IsMeasGood.chartField`), as the named input `RetainedPairRestartStatement`, and
proves both carriers from it:

* the chart itself (active chart at the second tip, inverse, lift, `IsChartTransport`) is the proved retained chart
  (`exists_retChart`), at every ordinary retained pair (`RetData.IsMeasGood.mem_E_of_ordinary`);
* the separation of fresh common points in the joint carrier is proved (`eq_of_inv_eq_of_notMem`);
* G7's **outer-word weights** are proved from the word's heights on the exposed sides
  (`outerWord_of_isRetainedWord`): `0` on both sides of the second path (`κ < 4`), `D − 2` and `D` on the two sides of
  the first path, with (7.12D.1) `κ/2 − 2 ≤ D − 2`; the first path's sides lie right of the second tip;
* G7's one-word datum is the joint datum `(c, w)` with `w` stored in a free slot of the word (`wordEnc`), so the
  conditional law given the word is the joint kernel (`map_prodMap_compProd`); `θ₁ < θ₂` follows from (7.12D.1).

## The named input

`RetainedPairRestartStatement`: for two flow lines (`x₂ ≤ x₁`, `θ₁ < θ₂`), any measurable retained data `d` agreeing
almost surely with them on `[0, u]`, `[0, r]` when `u < ζ₁`, `r < ζ₂`, there are a canonical space and a kernel as in
`JointRetainedPairStatement` (datum `(c, w)`, `w > 0`, GFF with datum `c`, angle-`θ₁` flow line from `w`, angle-`θ₂`
flow line from `0`) such that almost surely at an ordinary retained pair: `ω ∈ M`, the chart field coordinate is the
canonical retained chart field `hd.chartField κ h ω`, both continuations are read in the canonical chart inverse
`d.inv ω` up to and including their first new contact with the retained union (`IsRetainedClock`), and the word `c`
has the canonical heights on the exposed sides (`IsRetainedWord`: `−λ − θ₂χ` / `λ − θ₂χ` left / right of `0` on the
second path, `−λ − θ₁χ` or `λ − θ₁χ` at positive positions on the first path, no jump and no position `0` there). This
is Lemma G7's conditional law (the relative mean identification of Aux. 78/80 with Aux. 85–86's outer word, and the
continuation assertion through Theorem 2.4 and integrated driving uniqueness) together with W8.1's relative capacity
clocks; it is **not proved in Lean**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### The pathwise predicates of the named input -/

/-- **A continuation read in a chart, up to and including its first new contact with `A`**: a clock `c`, strictly
increasing on the chart times `[0, σ]`, `σ ≤ U`, maps them onto the physical times `t ≥ a`, `t ≤ ζ`, with no point of
`A` strictly between `a` and `t`; there `η ∘ c = ψ ∘ Γ`, and the chart path lies in `ℍ̄`. -/
def IsRetainedClock (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (A : Set ℂ) (ψ : ℂ → ℂ) (Γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) :
    Prop :=
  ∃ (c : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞), σ ≤ U ∧ StrictMonoOn c {s | (s : ℝ≥0∞) ≤ σ} ∧
    c '' {s | (s : ℝ≥0∞) ≤ σ} = {t | a ≤ t ∧ (t : ℝ≥0∞) ≤ ζ ∧ ∀ t' : ℝ≥0, a < t' → t' < t → η t' ∉ A} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η (c s) = ψ (Γ s)) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → Γ s ∈ Hbar

/-- **The canonical heights of the retained word on the exposed sides** (Aux. lemmas 78, 85–86; chart at the second
tip `β(b)`): every real `y` whose inverse-chart image is an interior point of the retained union other than the two
tips and the old common points is not `0`, not a jump of `c`, and: on the second path `c(y) = −λ − θ₂χ` for `y < 0`
and `λ − θ₂χ` for `y > 0` (its canonical new-side germs); on the first path `y > 0` and `c(y)` is one of its two
side heights `∓λ − θ₁χ`. -/
def IsRetainedWord (κ θ₁ θ₂ : ℝ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) (ψ : ℂ → ℂ)
    (c : BoundaryWord) : Prop :=
  ∀ y : ℝ, ψ y ∈ H → ψ y ≠ β b → ψ y ≠ α a → ψ y ∉ α '' Icc 0 a ∩ β '' Icc 0 b →
    y ≠ 0 ∧ y ∉ c.jumps ∧
      (ψ y ∈ β '' Icc 0 b → (y < 0 → c.fn y = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
        (0 < y → c.fn y = sleLambda κ - θ₂ * QuantumZipper.chiC κ)) ∧
      (ψ y ∈ α '' Icc 0 a → 0 < y ∧ (c.fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ ∨
        c.fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ))

/-- **Named input: the retained-pair restart in the canonical chart** (Lemma G7, pp. 497–498, for both current tips
at once, as in Lemma W2's proof, p. 531, with the outer-word heights of Aux. 85–86 and W8.1's clocks). See the module
docstring. **Not proved in Lean.** -/
def RetainedPairRestartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ H (X ω) = hd.chartField κ h ω ∧
        IsRetainedClock (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω)
          (Γ₁ (X ω)) (U₁ (X ω)) ∧
        IsRetainedClock (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω)
          (Γ₂ (X ω)) (U₂ (X ω)) ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1

/-! ### The outer word -/

/-- (7.12D.1) forces `θ₁ < θ₂`. -/
theorem lt_of_weight {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hwt : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ)) :
    θ₁ < θ₂ := by
  unfold Sec4.cumWeightRight at hwt
  have hlam := Sec4.sleLambda_pos hκ
  have hchi := Sec4.chiC_pos hκ hκ4
  have h1 : -1 < ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) / sleLambda κ := by
    linarith
  rw [lt_div_iff₀ hlam] at h1
  nlinarith

/-- **The outer-word weights** (proof of Theorem 7.12D, p. 543, with (7.12D.1)). -/
theorem outerWord_of_isRetainedWord {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hwt : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ))
    {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {c : BoundaryWord} (hW : IsRetainedWord κ θ₁ θ₂ α a β b ψ c)
    {y : ℝ} (hmem : ψ y ∈ prefixSet α a β b) (hyH : ψ y ∈ H) (h1 : ψ y ≠ β b) (h2 : ψ y ≠ α a)
    (h3 : ψ y ∉ α '' Icc 0 a ∩ β '' Icc 0 b) :
    y ≠ 0 ∧ y ∉ c.jumps ∧
      (0 < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn y + θ₂ * QuantumZipper.chiC κ)) ∧
      (y < 0 → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn y + θ₂ * QuantumZipper.chiC κ)) := by
  obtain ⟨hy0, hyJ, hβside, hαside⟩ := hW y hyH h1 h2 h3
  have hlam := Sec4.sleLambda_pos hκ
  have hzero : κ / 2 - 2 ≤ 0 := by linarith
  refine ⟨hy0, hyJ, fun hy => ?_, fun hy => ?_⟩
  · rcases hmem with hα | hβ
    · obtain ⟨-, hc | hc⟩ := hαside hα
      · rw [hc]; exact hwt
      · rw [hc]
        unfold Sec4.cumWeightRight at hwt ⊢
        have : (sleLambda κ - θ₁ * QuantumZipper.chiC κ + θ₂ * QuantumZipper.chiC κ) / sleLambda κ =
            ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) / sleLambda κ + 2 := by
          field_simp; ring
        linarith
    · rw [(hβside hβ).2 hy]
      unfold Sec4.cumWeightRight
      rw [sub_add_cancel, div_self hlam.ne']
      linarith
  · rcases hmem with hα | hβ
    · exact absurd (hαside hα).1 (not_lt.2 hy.le)
    · rw [(hβside hβ).1 hy]
      unfold Sec4.cumWeightLeft
      rw [sub_add_cancel, neg_neg, div_self hlam.ne']
      linarith

/-! ### Lemma G7 -/

/-- **Lemma G7 at the retained pair, with the outer word, from the retained-pair restart input.** -/
theorem g7RetainedPairStatement_of_restart (hR : RetainedPairRestartStatement.{u}) :
    G7RetainedPairStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  have hθ := lt_of_weight hκ hκ4 hwt
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  obtain ⟨mH, -, mU₂, -, mΓ₂, -, cΓ₂⟩ := hco
  have hK' := hK
  have hmapβ : (P.restrict M).map (fun ω => wordEnc (β ω)) = ((P.restrict M).map β).map wordEnc :=
    (Measure.map_map wordEnc.measurable hβ).symm
  refine ⟨S, mS, H, Γ₂, U₂, M, fun ω => wordEnc (β ω), X, K.comap wordEnc.symm wordEnc.symm.measurable,
    mH, mU₂, mΓ₂, cΓ₂, hM, wordEnc.measurable.comp hβ, hX, inferInstance, ?_, ?_, ?_⟩
  · -- the disintegration, re-indexed by the word recording the position
    have h1 : (P.restrict M).map (fun ω => (wordEnc (β ω), X ω)) =
        ((P.restrict M).map (fun ω => (β ω, X ω))).map (Prod.map wordEnc id) := by
      rw [Measure.map_map (wordEnc.measurable.prodMap measurable_id) (hβ.prodMk hX)]
      rfl
    rw [h1, hdis, hmapβ]
    exact map_prodMap_compProd wordEnc.measurable wordEnc.symm.measurable fun a => wordEnc.symm_apply_apply a
  · -- the conditional law
    rw [hmapβ, wordEnc.measurableEmbedding.ae_map_iff]
    filter_upwards [hlaw] with c hc
    rw [Kernel.comap_apply, wordEnc.symm_apply_apply, fn_wordEnc, jumps_wordEnc]
    exact ⟨hc.2.1, hc.2.2.2⟩
  · -- the pathwise relation
    filter_upwards [hpath, hag] with ω hω hagω hord
    obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
    have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
    obtain ⟨hMω, hHX, -, ⟨c₂, σ₂, hσ, hmono, himg, hpth, -⟩, hword⟩ := hω hord
    have hg := hd.good ω (RetData.E_subset_G hE)
    obtain ⟨-, hC⟩ := hd.isRetChart hE
    have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
    have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
    have hdom := activeDomain_congr_Icc e₁ e₂
    have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
    have htr := hd.isChartTransport_chartField κ h ω
    rw [RetData.chart_of_mem hE, ← hHX] at htr
    refine ⟨hMω, d.fwd ω, d.inv ω, d.lift ω, c₂, σ₂, ?_, ?_, hC.fwd_inv, ?_, ?_, ?_, htr, hσ, hmono, himg, hpth, ?_⟩
    · rw [← hdom, ← htip]; exact hC.isActiveChart hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.continuousOn_lift hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.deriv_eq hg.2.2.2.2.2.1
    · intro y hyH h1 h2 h3
      have hmem := inv_mem_prefixSet_of_real hC hg.2.2.2.2.2.1 hg.1 hg.2.1 hyH
      rw [prefixSet_congr_Icc e₁ e₂] at hmem
      have := outerWord_of_isRetainedWord hκ hκ4 hwt hword hmem hyH h1 h2 h3
      rwa [fn_wordEnc, jumps_wordEnc]

/-! ### The joint carrier -/

/-- **The joint retained-pair carrier from the retained-pair restart input.** -/
theorem jointRetainedPairStatement_of_restart (hR : RetainedPairRestartStatement.{u}) :
    Supp9D.JointRetainedPairStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  refine ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, ?_⟩
  filter_upwards [hpath, hag] with ω hω hagω hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, hHX, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩, -⟩ :=
    hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  have htr := hd.isChartTransport_chartField κ h ω
  rw [RetData.chart_of_mem hE, ← hHX] at htr
  refine ⟨hMω, d.fwd ω, d.inv ω, d.lift ω, c₁, c₂, σ₁, σ₂, ?_, ?_, hC.fwd_inv, ?_, ?_, ?_, htr, hσ₁, hmono₁,
    himg₁, hσ₂, hmono₂, himg₂, hpth₁, hpth₂, ?_⟩
  · rw [← hdom, ← htip]; exact hC.isActiveChart hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.continuousOn_lift hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.deriv_eq hg.2.2.2.2.2.1
  · intro s₁ s₂ hs₁ hs₂ he hA
    have hψ : d.inv ω (Γ₁ (X ω) s₁) = d.inv ω (Γ₂ (X ω) s₂) := by rw [← hpth₁ s₁ hs₁, ← hpth₂ s₂ hs₂, he]
    have hK : d.inv ω (Γ₁ (X ω) s₁) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
      rw [prefixSet_congr_Icc e₁ e₂, ← hpth₁ s₁ hs₁]; exact hA
    exact eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 (hH₁ s₁ hs₁) (hH₂ s₂ hs₂) hψ hK

end Supp7

end InteractingSLE
