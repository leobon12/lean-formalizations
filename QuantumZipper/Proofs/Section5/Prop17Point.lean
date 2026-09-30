import QuantumZipper.Statements.Prop17

/-!
# Proposition 1.7, clause 1: the length-`L` point of a γ-wedge (S5-PLAN node D5-a)

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Proposition 1.7 (§1.6):
"choose `y > 0` with `ν_h[0,y] = L`". STATEMENT_SPEC B5 defines
`y := inf {y > 0 : ν_h[0,y] ≥ L}` (`wedgeLengthPoint`) and adds to the conclusion that a.s.
`ν_h[0,y] = L` and `y` is the unique such point.

* `lenPoint_spec` (deterministic): for a measure `μ` on `ℝ` with no atoms, positive on nonempty
  open intervals, finite on `[0,y]` and with `μ[0,∞) = ∞`, the point
  `sInf {y | 0 < y ∧ L ≤ μ[0,y]}` is positive, has `μ[0,y] = L`, and is the only `y' > 0` with
  `μ[0,y'] = L`. Own elementary proof (AGENT_GUIDE cost rule): continuity of measure from above
  and below along `y ± 1/(n+1)`, and strict monotonicity of `y ↦ μ[0,y]`.
* `wedgeLengthPoint_spec`: the same for `qBoundaryMeasure γ x`; finiteness on `[0,y]` is not a
  hypothesis, because a non-junk `qBoundaryMeasure` is locally finite (`IsVagueLimitR`), and
  positivity excludes the junk value `0`.
* `theorem1_7_clause1_of`, `theorem1_7_of`: clause 1 of `theorem1_7` from the named prerequisite
  `WedgeBoundaryRegularStmt` (the boundary measure of every quantum wedge is a.s. atomless,
  positive on intervals and has infinite mass on `[0,∞)`), and `theorem1_7` from that plus
  `Prop17ShiftStmt` (clause 2, the D5 main node). Both prerequisites are hypotheses only.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuantumZipper
namespace S5

section CDF

variable {μ : Measure ℝ}

/-- The set of `y > 0` with `μ[0,y] ≥ L`. -/
def lenSet (μ : Measure ℝ) (L : ℝ) : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal L ≤ μ (Icc 0 y)}

/-- The first point `y > 0` with `μ[0,y] ≥ L` (`wedgeLengthPoint` for `μ = ν_x`). -/
def lenPoint (μ : Measure ℝ) (L : ℝ) : ℝ := sInf (lenSet μ L)

theorem measure_Icc_zero_eq_add {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    μ (Icc 0 b) = μ (Icc 0 a) + μ (Ioc a b) := by
  rw [← Icc_union_Ioc_eq_Icc ha hab]
  exact measure_union (Set.disjoint_left.2 fun x hx hy => (not_lt.2 hx.2) hy.1) measurableSet_Ioc

/-- Strict monotonicity of `y ↦ μ[0,y]` on `[0,∞)` when `μ` charges every open interval. -/
theorem measure_Icc_zero_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hpos : ∀ u v : ℝ, u < v → 0 < μ (Ioo u v)) (hfin : μ (Icc 0 a) ≠ ⊤) :
    μ (Icc 0 a) < μ (Icc 0 b) := by
  rw [measure_Icc_zero_eq_add (μ := μ) ha hab.le]
  exact ENNReal.lt_add_right hfin
    ((hpos a b hab).trans_le (measure_mono Ioo_subset_Ioc_self)).ne'

/-- **D5-a, deterministic core.** Existence, positivity and uniqueness of the length-`L` point. -/
theorem lenPoint_spec {L : ℝ} (hL : 0 < L) (hatom : ∀ t : ℝ, μ {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < μ (Ioo u v)) (hfin : ∀ y : ℝ, μ (Icc 0 y) ≠ ⊤)
    (hinf : μ (Ici 0) = ⊤) :
    0 < lenPoint μ L ∧ μ (Icc 0 (lenPoint μ L)) = ENNReal.ofReal L ∧
      ∀ y' : ℝ, 0 < y' → μ (Icc 0 y') = ENNReal.ofReal L → y' = lenPoint μ L := by
  unfold lenPoint
  set S := lenSet μ L with hS
  set y₀ := sInf S with hy₀
  have hbdd : BddBelow S := ⟨0, fun y hy => hy.1.le⟩
  have hup : ∀ {y y' : ℝ}, y ∈ S → y ≤ y' → y' ∈ S := fun hy h =>
    ⟨hy.1.trans_le h, hy.2.trans (measure_mono (Icc_subset_Icc_right h))⟩
  -- `S` is nonempty since `μ[0,n] ↑ μ[0,∞) = ∞`.
  have hne : S.Nonempty := by
    have hU : Ici (0 : ℝ) = ⋃ n : ℕ, Icc 0 (n : ℝ) := by
      ext x
      simp only [mem_Ici, mem_iUnion, mem_Icc]
      exact ⟨fun h => let ⟨n, hn⟩ := exists_nat_ge x; ⟨n, h, hn⟩, fun ⟨_, h, _⟩ => h⟩
    have hmono : Monotone fun n : ℕ => Icc (0 : ℝ) n := fun n m h =>
      Icc_subset_Icc_right (Nat.cast_le.2 h)
    rw [hU, hmono.measure_iUnion] at hinf
    by_contra hS0
    have hle : ∀ n : ℕ, μ (Icc 0 (n : ℝ)) ≤ ENNReal.ofReal L := by
      intro n
      by_contra hn
      push Not at hn
      exact hS0 ⟨max (n : ℝ) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
        hn.le.trans (measure_mono (Icc_subset_Icc_right (le_max_left _ _)))⟩
    have h := iSup_le hle
    rw [hinf] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  have hy0 : 0 ≤ y₀ := le_csInf hne fun y hy => hy.1.le
  -- Lower bound: `Icc 0 y₀ = ⋂ₙ Icc 0 (y₀ + 1/(n+1))`, each of measure `≥ L`.
  have hge : ENNReal.ofReal L ≤ μ (Icc 0 y₀) := by
    have hI : Icc 0 y₀ = ⋂ n : ℕ, Icc 0 (y₀ + 1 / ((n : ℝ) + 1)) := by
      ext x
      simp only [mem_Icc, mem_iInter]
      constructor
      · rintro ⟨h0, h1⟩ n
        exact ⟨h0, h1.trans (le_add_of_nonneg_right (by positivity))⟩
      · intro h
        refine ⟨(h 0).1, ?_⟩
        by_contra hx
        push Not at hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        have := (h n).2
        linarith
    have hanti : Antitone fun n : ℕ => Icc (0 : ℝ) (y₀ + 1 / ((n : ℝ) + 1)) := by
      intro n m h
      apply Icc_subset_Icc_right
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := Nat.one_div_le_one_div h
      linarith
    rw [hI, hanti.measure_iInter (fun n => measurableSet_Icc.nullMeasurableSet) ⟨0, hfin _⟩]
    refine le_iInf fun n => ?_
    have hlt : y₀ < y₀ + 1 / ((n : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne hlt
    exact (hup hs hslt.le).2
  -- Upper bound: `Icc 0 y₀ ⊆ ⋃ₙ Icc 0 (y₀ − 1/(n+1)) ∪ {y₀}`, each piece of measure `≤ L`.
  have hle : μ (Icc 0 y₀) ≤ ENNReal.ofReal L := by
    have hsub : Icc 0 y₀ ⊆ (⋃ n : ℕ, Icc 0 (y₀ - 1 / ((n : ℝ) + 1))) ∪ {y₀} := by
      rintro x ⟨h0, h1⟩
      rcases h1.lt_or_eq with h | h
      · left
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        exact mem_iUnion.2 ⟨n, h0, by linarith⟩
      · right
        exact h
    have hmono : Monotone fun n : ℕ => Icc (0 : ℝ) (y₀ - 1 / ((n : ℝ) + 1)) := by
      intro n m h
      apply Icc_subset_Icc_right
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := Nat.one_div_le_one_div h
      linarith
    have hpiece : ∀ n : ℕ, μ (Icc 0 (y₀ - 1 / ((n : ℝ) + 1))) ≤ ENNReal.ofReal L := by
      intro n
      by_cases hz : 0 < y₀ - 1 / ((n : ℝ) + 1)
      · have hzlt : y₀ - 1 / ((n : ℝ) + 1) < y₀ := sub_lt_self _ (by positivity)
        have hnot := notMem_of_lt_csInf hzlt hbdd
        simp only [hS, lenSet, mem_ofPred_eq, not_and, not_le] at hnot
        exact (hnot hz).le
      · push Not at hz
        calc μ (Icc 0 (y₀ - 1 / ((n : ℝ) + 1))) ≤ μ {0} :=
              measure_mono fun x hx => mem_singleton_iff.2 (le_antisymm (hx.2.trans hz) hx.1)
          _ = 0 := hatom 0
          _ ≤ _ := bot_le
    calc μ (Icc 0 y₀) ≤ μ (⋃ n : ℕ, Icc 0 (y₀ - 1 / ((n : ℝ) + 1))) + μ {y₀} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = ⨆ n : ℕ, μ (Icc 0 (y₀ - 1 / ((n : ℝ) + 1))) := by
          rw [hatom, add_zero, hmono.measure_iUnion]
      _ ≤ ENNReal.ofReal L := iSup_le hpiece
  have heq : μ (Icc 0 y₀) = ENNReal.ofReal L := le_antisymm hle hge
  have hpos0 : 0 < y₀ := by
    rcases hy0.lt_or_eq with h | h
    · exact h
    · exfalso
      have heq' := heq
      rw [← h, Icc_self, hatom] at heq'
      exact (ENNReal.ofReal_pos.2 hL).ne heq'
  refine ⟨hpos0, heq, fun y' hy' hy'L => ?_⟩
  rcases lt_trichotomy y' y₀ with h | h | h
  · exfalso
    have := measure_Icc_zero_lt hy'.le h hpos (hfin y')
    rw [hy'L, heq] at this
    exact lt_irrefl _ this
  · exact h
  · exfalso
    have := measure_Icc_zero_lt hy0 h hpos (hfin y₀)
    rw [hy'L, heq] at this
    exact lt_irrefl _ this

end CDF

/-- A `qBoundaryMeasure` that is not the junk value `0` is a vague limit, hence locally finite. -/
theorem isLocallyFiniteMeasure_qBoundaryMeasure {γ : ℝ} {x : FieldSample}
    (h : qBoundaryMeasure γ x ≠ 0) : IsLocallyFiniteMeasure (qBoundaryMeasure γ x) := by
  classical
  unfold qBoundaryMeasure at h ⊢
  split_ifs at h ⊢ with hex
  · exact hex.choose_spec.1
  · exact absurd rfl h

/-- **D5-a for `ν_x`.** If `ν_x = qBoundaryMeasure γ x` has no atoms, charges every nonempty open
interval and `ν_x[0,∞) = ∞`, then `wedgeLengthPoint γ L x` is positive, has `ν_x[0,y] = L`, and
is the unique `y' > 0` with `ν_x[0,y'] = L` (STATEMENT_SPEC B5). -/
theorem wedgeLengthPoint_spec {γ L : ℝ} {x : FieldSample} (hL : 0 < L)
    (hatom : ∀ t : ℝ, qBoundaryMeasure γ x {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ x (Ioo u v))
    (hinf : qBoundaryMeasure γ x (Ici 0) = ⊤) :
    0 < wedgeLengthPoint γ L x ∧
      qBoundaryMeasure γ x (Icc 0 (wedgeLengthPoint γ L x)) = ENNReal.ofReal L ∧
      ∀ y' : ℝ, 0 < y' → qBoundaryMeasure γ x (Icc 0 y') = ENNReal.ofReal L →
        y' = wedgeLengthPoint γ L x := by
  have hne : qBoundaryMeasure γ x ≠ 0 := by
    intro h0
    have h1 := hpos 0 1 one_pos
    rw [h0] at h1
    simp at h1
  have := isLocallyFiniteMeasure_qBoundaryMeasure hne
  exact lenPoint_spec hL hatom hpos (fun _ => measure_Icc_lt_top.ne) hinf

/-- **Prerequisite of D5-a (named, hypothesis only).** The boundary measure of an `α`-quantum
wedge is a.s. atomless, positive on every nonempty open interval, and has infinite mass on
`[0,∞)` (Sheffield §1.6: "an infinite amount in each neighborhood of ∞"). Owner: M4 (wedge
versions of `AtomlessUncond`, positivity, `InfiniteMass`, with the law transfer of R23 (c)). -/
def WedgeBoundaryRegularStmt (γ α : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), IsQuantumWedge γ α Y P →
    ∀ᵐ ω ∂P, (∀ t : ℝ, qBoundaryMeasure γ (Y ω) {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ (Y ω) (Ioo u v)) ∧
      qBoundaryMeasure γ (Y ω) (Ici 0) = ⊤

/-- **Clause 2 of Proposition 1.7 (the D5 main node), as a named statement.** -/
def Prop17ShiftStmt (γ L : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), IsQuantumWedge γ γ Y P →
    IsQuantumWedge γ γ
      (fun ω => canonical γ (translate (Y ω) (wedgeLengthPoint γ L (Y ω) : ℂ))) P

/-- **D5-a.** Clause 1 of Proposition 1.7 from the wedge boundary-measure prerequisite. -/
theorem theorem1_7_clause1_of {γ L : ℝ} (hL : 0 < L) (hreg : WedgeBoundaryRegularStmt γ γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample) (hY : IsQuantumWedge γ γ Y P) :
    ∀ᵐ ω ∂P,
      qBoundaryMeasure γ (Y ω) (Icc 0 (wedgeLengthPoint γ L (Y ω))) = ENNReal.ofReal L ∧
      ∀ y' : ℝ, 0 < y' → qBoundaryMeasure γ (Y ω) (Icc 0 y') = ENNReal.ofReal L →
        y' = wedgeLengthPoint γ L (Y ω) := by
  filter_upwards [hreg P Y hY] with ω ⟨h1, h2, h3⟩
  obtain ⟨-, he, hu⟩ := wedgeLengthPoint_spec hL h1 h2 h3
  exact ⟨he, hu⟩

/-- **Proposition 1.7 from its two prerequisites** (`WedgeBoundaryRegularStmt` for clause 1,
`Prop17ShiftStmt` for clause 2). -/
theorem theorem1_7_of (hreg : ∀ γ : ℝ, 0 < γ → γ < 2 → WedgeBoundaryRegularStmt γ γ)
    (hshift : ∀ γ L : ℝ, 0 < γ → γ < 2 → 0 < L → Prop17ShiftStmt γ L) : theorem1_7 := by
  intro γ L hγ hγ2 hL Ω _ P _ Y hY
  exact ⟨theorem1_7_clause1_of hL (hreg γ hγ hγ2) P Y hY, hshift γ L hγ hγ2 hL P Y hY⟩

end S5
end QuantumZipper
