/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Counterflow
import InteractingSLE.Spec.Sec4.SpecialOrder

/-!
# §4.2: Lemma 4.7 from the two inputs of Remark 4.8, and the outer steps of Proposition 4.9

Packet PROVE-SEC4-B2 (specification §4.2, `source/spec/p097-144.md` L486–L545, pp. 117–120).

Remark 4.8 records that "the proof of Lemma 4.7 has two inputs": (a) the continuity (and, before `T_top`, the
simplicity) of the flow line `η` up to its first upper-boundary contact `T_top`, and (b) for every `η`-stopping time
`τ < T_top`, `η′` almost surely first exits `𝒮 \ η([0, τ])` (through `∂_L𝒮 ∪ η([0, τ])`) at `η(τ)`; "the completed
first segment is then included by the limiting argument". This file proves that implication in full, with `η′`
parametrized on `[0, 1]` (`stripCounterflowPath`) and every object read in the chart `E` (`Strip.lean`): input (b) is
used at the deterministic times `q < T_top` (the stopping times `q ∧ T_n` on `{q < T_n}`), countably many of which
suffice; the conclusion then holds simultaneously for every `τ ∈ [0, T_top]` on one almost sure event, with the
containment of the completed first segment and the reverse chronological order (pathwise steps of PROVE-SEC4-B,
`SpecialOrder.lean`).

* `lemma47_pathwise`, `lemma47_of_remark48` (conditional helper: Lemma 4.7 from Remark 4.8 (a), (b)).
* `isStripLeftBoundary_of_dense`, `prop49_of_lemma47` (conditional helper: Proposition 4.9's last step, "taking a
  countable dense collection of stopping times `τ′` … and invoking the almost sure continuity of `η′`": the left
  boundary statement from Lemma 4.7's containment and the per-time statement "`η′(τ′)` is to the right of `η`").
* `IsRemark48Data`, `isRemark48Data_of_isProp411Data` (Proposition 4.11: "By combining Remark 4.8 and Remark 4.10"):
  the data class of Proposition 4.11 satisfies the sufficient conditions of Remark 4.8 for `h − π/2 χ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec4

/-- The positive rationals below `τ` are dense in `[0, τ]`. -/
theorem Icc_subset_closure_rat_Ioo {τ : ℝ} (hτ : 0 < τ) :
    Icc 0 τ ⊆ closure (Ioo 0 τ ∩ range ((↑) : ℚ → ℝ)) := by
  rw [← closure_Ioo hτ.ne]
  exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
    isClosed_closure

/-- **Lemma 4.7 from Remark 4.8, one realization.** Let `ξ` be the completed counterflow on `[0, 1]` and `η` the flow
path on `[0, T]` (`T = T_top > 0`), continuous there and simple before `T` (input (a)). If, at every rational time
`q ∈ [0, T)`, `ξ` first hits `∂_L𝒮 ∪ η([0, q])` at `η(q)` (input (b) at these times), then for every `τ ∈ [0, T]` it
first hits `∂_L𝒮 ∪ η([0, τ])` at `η(τ)`; it contains `η([0, T])`; and it visits `η(t)` strictly before its first
visit to `η(s)` whenever `0 ≤ s < t ≤ T` (reverse chronological order). -/
theorem lemma47_pathwise {ξ η : ℝ → ℂ} {T : ℝ} (hT : 0 < T) (hξ : ContinuousOn ξ (Icc 0 1))
    (hη : ContinuousOn η (Icc 0 T)) (hinj : InjOn η (Ico 0 T))
    (hb : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < T →
      IsFirstHitPoint ξ 1 (lowerLineH ∪ η '' Icc 0 q) (η q)) :
    (∀ τ ∈ Icc 0 T, IsFirstHitPoint ξ 1 (lowerLineH ∪ η '' Icc 0 τ) (η τ)) ∧
      η '' Icc 0 T ⊆ ξ '' Icc 0 1 ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
        ∃ v ∈ Icc (0 : ℝ) 1, ξ v = η t ∧ ∀ w ∈ Icc 0 v, ξ w ≠ η s := by
  -- the dense sets of rational times
  have key : ∀ τ, 0 < τ → τ ≤ T →
      IsFirstHitPoint ξ 1 (lowerLineH ∪ η '' Icc 0 τ) (η τ) ∧ η '' Icc 0 τ ⊆ ξ '' Icc 0 1 ∧
        ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ τ →
          ∃ v ∈ Icc (0 : ℝ) 1, ξ v = η t ∧ ∀ w ∈ Icc 0 v, ξ w ≠ η s := by
    intro τ hτ hτT
    refine isFirstHitPoint_and_image_subset_and_reverse hξ (hη.mono (Icc_subset_Icc_right hτT)) hτ
      (hinj.mono (Ico_subset_Ico_right hτT)) (D := Ioo 0 τ ∩ range ((↑) : ℚ → ℝ))
      (fun x hx => Ioo_subset_Ico_self hx.1) (Icc_subset_closure_rat_Ioo hτ) ?_
    rintro _ ⟨hx, r, rfl⟩
    exact hb r hx.1.le (hx.2.trans_le hτT)
  refine ⟨fun τ hτ => ?_, (key T hT le_rfl).2.1, (key T hT le_rfl).2.2⟩
  rcases eq_or_lt_of_le hτ.1 with h0 | hpos
  · subst h0
    simpa using hb 0 (by simp) (by simpa using hT)
  · exact (key τ hpos hτ.2).1

/-- **Lemma 4.7 from the two inputs of Remark 4.8** (conditional helper; Remark 4.8: "The proof of Lemma 4.7 has two
inputs"). On `(Ω, P)`, let `ξ ω` be the completed counterflow on `[0, 1]`, `η ω` the flow path and `T ω = T_top`.
Assume (a): almost surely `0 < T`, `η` is continuous on `[0, T]` and simple on `[0, T)`, and `ξ` is continuous on
`[0, 1]` (actual endpoint, Lemma 4.5); and (b) at deterministic times: for every `q ≥ 0`, almost surely on
`{q < T}`, `ξ` first hits `∂_L𝒮 ∪ η([0, q])` at `η(q)`. Then almost surely, simultaneously for all `τ ∈ [0, T]`, `ξ`
first hits `∂_L𝒮 ∪ η([0, τ])` at `η(τ)`; `ξ` contains `η([0, T])`; and `ξ` hits the points of `η` in reverse
chronological order. -/
theorem lemma47_of_remark48 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ η : Ω → ℝ → ℂ}
    {T : Ω → ℝ}
    (ha : ∀ᵐ ω ∂P, 0 < T ω ∧ ContinuousOn (η ω) (Icc 0 (T ω)) ∧ InjOn (η ω) (Ico 0 (T ω)) ∧
      ContinuousOn (ξ ω) (Icc 0 1))
    (hb : ∀ q : ℝ, 0 ≤ q → ∀ᵐ ω ∂P, q < T ω →
      IsFirstHitPoint (ξ ω) 1 (lowerLineH ∪ η ω '' Icc 0 q) (η ω q)) :
    ∀ᵐ ω ∂P, (∀ τ ∈ Icc 0 (T ω), IsFirstHitPoint (ξ ω) 1 (lowerLineH ∪ η ω '' Icc 0 τ) (η ω τ)) ∧
      η ω '' Icc 0 (T ω) ⊆ ξ ω '' Icc 0 1 ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T ω →
        ∃ v ∈ Icc (0 : ℝ) 1, ξ ω v = η ω t ∧ ∀ w ∈ Icc 0 v, ξ ω w ≠ η ω s := by
  have hb' : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < T ω →
      IsFirstHitPoint (ξ ω) 1 (lowerLineH ∪ η ω '' Icc 0 q) (η ω q) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ (q : ℝ)
    · filter_upwards [hb q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [ha, hb'] with ω ⟨hT, hη, hinj, hξ⟩ hω
  exact lemma47_pathwise hT hξ hη hinj hω

/-- **Lemma 4.7 from Remark 4.8, read in the strip carriers** (conditional helper). `η ω` is the flow path in the chart
`E` (the trace of `IsStripFlowLine`), `T_top = firstUpperContact (η ω)`, and `γ ω` is the reverse counterflow's trace
in the chart `M_q` (the trace of the driver of `IsStripCounterflowDriver κ (−π/2) q`), completed to
`stripCounterflowPath q (γ ω)`. Inputs: (a) almost surely `0 < T_top < ∞` and `η` is continuous on `[0, T_top]` and
simple on `[0, T_top)`; the counterflow trace is continuous, avoids `−1` and tends to `∞` (actual endpoint `0`);
(b) at deterministic times `q′ < T_top`, the first-exit statement. Conclusion: Lemma 4.7 for every `τ ∈ [0, T_top]`
simultaneously, with containment and reverse chronological order. -/
theorem lemma47_of_remark48_strip {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ℝ}
    {η γ : Ω → ℝ≥0 → ℂ}
    (ha : ∀ᵐ ω ∂P, 0 < (firstUpperContact (η ω)).toReal ∧
      ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (firstUpperContact (η ω)).toReal) ∧
      InjOn (fun s : ℝ => η ω s.toNNReal) (Ico 0 (firstUpperContact (η ω)).toReal))
    (hγ : ∀ᵐ ω ∂P, Continuous (γ ω) ∧ (∀ t, γ ω t ≠ -1) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hb : ∀ q' : ℝ, 0 ≤ q' → ∀ᵐ ω ∂P, q' < (firstUpperContact (η ω)).toReal →
      IsFirstHitPoint (stripCounterflowPath q (γ ω)) 1
        (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 q') (η ω q'.toNNReal)) :
    ∀ᵐ ω ∂P,
      (∀ τ ∈ Icc 0 (firstUpperContact (η ω)).toReal,
        IsFirstHitPoint (stripCounterflowPath q (γ ω)) 1
          (lowerLineH ∪ (fun s : ℝ => η ω s.toNNReal) '' Icc 0 τ) (η ω τ.toNNReal)) ∧
      (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (firstUpperContact (η ω)).toReal ⊆
        stripCounterflowPath q (γ ω) '' Icc 0 1 ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ (firstUpperContact (η ω)).toReal →
        ∃ v ∈ Icc (0 : ℝ) 1, stripCounterflowPath q (γ ω) v = η ω t.toNNReal ∧
          ∀ w ∈ Icc 0 v, stripCounterflowPath q (γ ω) w ≠ η ω s.toNNReal := by
  have ha' : ∀ᵐ ω ∂P, 0 < (firstUpperContact (η ω)).toReal ∧
      ContinuousOn (fun s : ℝ => η ω s.toNNReal) (Icc 0 (firstUpperContact (η ω)).toReal) ∧
      InjOn (fun s : ℝ => η ω s.toNNReal) (Ico 0 (firstUpperContact (η ω)).toReal) ∧
      ContinuousOn (stripCounterflowPath q (γ ω)) (Icc 0 1) := by
    filter_upwards [ha, hγ] with ω h1 h2
    exact ⟨h1.1, h1.2.1, h1.2.2, continuousOn_stripCounterflowPath h2.1 h2.2.1 h2.2.2⟩
  exact lemma47_of_remark48 (ξ := fun ω => stripCounterflowPath q (γ ω))
    (η := fun ω s => η ω s.toNNReal) ha' hb

/-! ### Proposition 4.9: the left boundary from a dense set of counterflow times -/

/-- If a continuous completed counterflow `ξ` on `[0, 1]` contains the closed set `A` and avoids the open left side
of `A` at a dense set of times, then `A` is its left boundary (Proposition 4.9 proof, last sentence). -/
theorem isStripLeftBoundary_of_dense {ξ : ℝ → ℂ} {A : Set ℂ} (hA : IsClosed A)
    (hξ : ContinuousOn ξ (Icc 0 1)) (hAK : A ⊆ ξ '' Icc 0 1) {D : Set ℝ} (hD : Icc 0 1 ⊆ closure D)
    (hDsub : D ⊆ Icc 0 1) (hright : ∀ s ∈ D, ξ s ∉ leftEndSide A) :
    IsStripLeftBoundary A (ξ '' Icc 0 1) := by
  refine ⟨hAK, eq_empty_iff_forall_notMem.2 ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsL⟩
  have hU := isOpen_leftEndSide hA
  have hpre : ξ ⁻¹' leftEndSide A ∈ 𝓝[Icc 0 1] s := (hξ s hs).preimage_mem_nhdsWithin
    (hU.mem_nhds hsL)
  obtain ⟨V, hVo, hsV, hVsub⟩ := mem_nhdsWithin.1 hpre
  obtain ⟨d, hdV, hdD⟩ := mem_closure_iff.1 (hD hs) V hVo hsV
  exact hright d hdD (hVsub ⟨hdV, hDsub hdD⟩)

/-- **Proposition 4.9, last step** (conditional helper). Assume almost surely that `ξ` is continuous on `[0, 1]`,
`η` is continuous on `[0, T]` and `ξ` contains `η([0, T])` (Lemma 4.7), and that for each deterministic time
`s ∈ [0, 1)` almost surely `ξ(s)` is not strictly on the left of `η([0, T])` (Proposition 4.9 proof: "`η′(τ′)` is to
the right of `η`"). Then almost surely `η([0, T])` is the left boundary of the completed counterflow range. -/
theorem prop49_of_lemma47 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ η : Ω → ℝ → ℂ}
    {T : Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (ξ ω) (Icc 0 1) ∧ ContinuousOn (η ω) (Icc 0 (T ω)))
    (hsub : ∀ᵐ ω ∂P, η ω '' Icc 0 (T ω) ⊆ ξ ω '' Icc 0 1)
    (hright : ∀ s ∈ Ico (0 : ℝ) 1, ∀ᵐ ω ∂P, ξ ω s ∉ leftEndSide (η ω '' Icc 0 (T ω))) :
    ∀ᵐ ω ∂P, IsStripLeftBoundary (η ω '' Icc 0 (T ω)) (ξ ω '' Icc 0 1) := by
  have hr : ∀ᵐ ω ∂P, ∀ r : ℚ, (r : ℝ) ∈ Ioo (0 : ℝ) 1 →
      ξ ω r ∉ leftEndSide (η ω '' Icc 0 (T ω)) := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : (r : ℝ) ∈ Ioo (0 : ℝ) 1
    · filter_upwards [hright r (Ioo_subset_Ico_self hr)] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hr
  filter_upwards [hcont, hsub, hr] with ω ⟨hξ, hη⟩ hω hrω
  refine isStripLeftBoundary_of_dense ((isCompact_Icc.image_of_continuousOn hη).isClosed) hξ hω
    (Icc_subset_closure_rat_Ioo one_pos) (fun x hx => Ioo_subset_Icc_self hx.1) ?_
  rintro _ ⟨hx, r, rfl⟩
  exact hrω r hx

/-! ### Proposition 4.11: Remarks 4.8 and 4.10 combined -/

/-- The sufficient conditions of Remark 4.8 on the data of the strip field `h`, written for `h − π/2 χ` (lower data
`bL`, upper data `bU` of `h`, `z₀ = x₀ + i`, `λ′ = λ(16/κ)`): for (a), `h` is at most `−λ + πχ` left of `0` and at
least `λ − πχ` right of `0` on `∂_L𝒮`; for (b), `h − π/2 χ` is at most `−λ′ − πχ` left of `z₀` and at least
`λ′ + πχ` right of `z₀` on `∂_U𝒮`, and at most `−λ′` left of `0` and at least `λ′` right of `0` on `∂_L𝒮`; all data
piecewise constant with finitely many changes. -/
def IsRemark48Data (κ x₀ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) : Prop :=
  IsPiecewiseConstantBoundaryData bL JL ∧ IsPiecewiseConstantBoundaryData bU JU ∧
    ((∀ x < 0, bL x ≤ -sleLambda κ + π * chiC κ) ∧ ∀ x, 0 < x → sleLambda κ - π * chiC κ ≤ bL x) ∧
    ((∀ x < x₀, bU x - π / 2 * chiC κ ≤ -sleLambda (16 / κ) - π * chiC κ) ∧
      ∀ x, x₀ < x → sleLambda (16 / κ) + π * chiC κ ≤ bU x - π / 2 * chiC κ) ∧
    (∀ x < 0, bL x - π / 2 * chiC κ ≤ -sleLambda (16 / κ)) ∧
      ∀ x, 0 < x → sleLambda (16 / κ) ≤ bL x - π / 2 * chiC κ

/-- The data class of Proposition 4.11 satisfies the conditions of Remark 4.8 (for `0 < κ < 4`): with
`λ′ = λ − π/2 χ` (4.2), `−λ − π/2 χ = −λ′ − πχ`, `λ + π/2 χ = λ′ + πχ`, `−λ + π/2 χ = −λ′`, `λ − π/2 χ = λ′` and
`λ − πχ ≤ λ`. -/
theorem isRemark48Data_of_isProp411Data {κ x₀ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (h : IsProp411Data κ x₀ bL bU JL JU) : IsRemark48Data κ x₀ bL bU JL JU := by
  obtain ⟨hL, hU, hLl, hLr, hUl, hUr⟩ := h
  have hlam := sleLambda_sixteen_div_eq_sub hκ
  have hχ := chiC_pos hκ hκ4
  have hπ := Real.pi_pos
  have hπχ : 0 < π * chiC κ := mul_pos hπ hχ
  refine ⟨hL, hU, ⟨hLl, fun x hx => by linarith [hLr x hx]⟩, ⟨fun x hx => ?_, fun x hx => ?_⟩,
    fun x hx => ?_, fun x hx => ?_⟩
  · have := hUl x hx; rw [hlam]; linarith
  · have := hUr x hx; rw [hlam]; linarith
  · have := hLl x hx; rw [hlam]; linarith
  · have := hLr x hx; rw [hlam]; linarith

end Sec4

end InteractingSLE
