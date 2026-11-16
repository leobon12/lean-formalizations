/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermWord

/-!
# The terminal retained pair: the named input reduced to the path identity

Packet PROVE-RC-TERM (ruling R124). `TermAssemble.lean` reduced the named input `TerminalRetainedCondDetStatement` to
`TerminalRetainedClockStatement` (positive seed position, the word just left of the terminal point, and the clock of
the first path). The first two clauses are deterministic consequences of the freshly reached real tip
(`TermWord.lean`). What remains is the path identity alone:

**`TerminalRetainedPathStatement`** (named input, **not proved in Lean**): almost surely on the trigger event there
are a clock `c₁` and `σ` at most the lifetime of the decoded canonical flow code `Γ` of the chart field
`Term.termField` for the datum `(Term.termWord, Term.termSeed)`, with `c₁` strictly increasing on `[0, σ]`, mapping it
onto the physical times of the first path up to and including its first new contact with the completed second path,
and `η₁ (c₁ s) = Term.termInv x₂ r (Γ s)` for `s ≤ σ`.

* **`terminalRetainedClock_of_path`**, **`terminalRetainedCondDet_of_path`**: the clock statement and the named input
  `TerminalRetainedCondDetStatement` from the path identity;
* **`pocketCorner_of_path`**, `g7GB7aFirstHitReal_of_path`: the pocket-corner exclusion and the real first-hit
  exclusion from the path identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

universe u

namespace InteractingSLE.RealContact

open Restart LQGMetric Sec2.Assembly Exist.Staged Exist.StagedLaw Term

open PiecewiseConstantBoundaryData (leftLim)

namespace Term

variable {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {η : ℝ≥0 → ℂ} {x q : ℝ} {T : ℝ≥0}

/-- The recentred completed path lies in the closed half-plane. -/
theorem mapsTo_trace_Hbar (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (termRec e)))
    (hT : (T : ℝ≥0∞) = e.2) (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x)) :
    MapsTo (fun s : ℝ => η s.toNNReal - x) (Icc 0 (rtime (termRec e))) Hbar := by
  have hη' := isGeneratingTrace_retOf hT hη
  have hwc : Continuous (retOf ⊤ e).1 := continuous_retOf he hg
  have hw0 : (retOf ⊤ e).1 0 = 0 := by
    change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min ⊤ e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min _ _)), ENNReal.toNNReal_zero]
    exact he.2.1
  intro s hs
  rw [rtime_termRec hT] at hs
  exact Sec7.IsGeneratingTrace.mem_Hbar hη' hwc.continuousOn hw0
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2))

/-- The recentred completed path does not visit its terminal point before the lifetime. -/
theorem trace_ne_tip (hT : (T : ℝ≥0∞) = e.2) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ e.2}) (htip : η T = q) :
    ∀ s : ℝ, 0 ≤ s → s < rtime (termRec e) → η s.toNNReal - x ≠ ((q - x : ℝ) : ℂ) := by
  intro s hs hsT hEq
  rw [rtime_termRec hT] at hsT
  have hlt : s.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe hs).2 hsT
  have h1 : η s.toNNReal = η T := by
    rw [htip]
    rw [Complex.ofReal_sub] at hEq
    exact sub_left_injective hEq
  have h2 : s.toNNReal = T := hinj (show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e.2 from hT ▸ ENNReal.coe_le_coe.2 hlt.le)
    (show (T : ℝ≥0∞) ≤ e.2 from hT.le) h1
  exact absurd hlt (h2 ▸ lt_irrefl _)

end Term

/-- **Named input: the path identity of the first path in the chart of the completed second path** (Lemma G7's
conclusion at the retained pair `(0, ζ₂)`, supplement pp. 497–498: "it is the canonical stopped flow of the
conditional field, with its original stopping rule recovered in relative capacity"). Binders of
`TerminalRetainedDetStatement`. Almost surely on the trigger event (`η₂` ends at a real point `e < x₂`, and `η₁`
visits a real point `y ≤ e` before its lifetime), with `r` the record of the second path through its lifetime, `Γ`
the decoded canonical flow code of the chart field `Term.termField κ x₂ r (h ω)` for the datum
`(Term.termWord κ θ₂ c r, Term.termSeed x₁ x₂ r)` and `U` its lifetime: there are a clock `c₁` and `σ ≤ U` with `c₁`
strictly increasing on `[0, σ]`, mapping it onto the physical times `t ≤ ζ₁` with no contact with `η₂([0, T])`
strictly between `0` and `t`, and `η₁ (c₁ s) = Term.termInv x₂ r (Γ s)` for `s ≤ σ`. **Not proved in Lean.** -/
def TerminalRetainedPathStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F →
    ∀ (c : BoundaryWord) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), c.IsSorted → c.jumps = jumps.image (· - x₂) →
      (∀ y ∉ jumps.image (· - x₂), c.fn y = b (y + x₂)) → Measurable E → (∀ ω, IsRegularDriver (E ω)) →
      (∀ ω, (E ω).2 = ζ₂ ω) →
      IsFlowLineDriver κ c.fn c.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω)) (fun s ω => (E ω).1 s)
        (fun ω => (E ω).2) →
      (∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun t => η₂ ω t - x₂)) →
      ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (e : ℝ), (T : ℝ≥0∞) = ζ₂ ω → η₂ ω T = e → e < x₂ →
        (∃ (s : ℝ≥0) (y : ℝ), (s : ℝ≥0∞) < ζ₁ ω ∧ η₁ ω s = y ∧ y ≤ e) →
        ∃ (c₁ : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞),
          σ ≤ (F ((termWord κ θ₂ c (termRec (E ω)), termSeed x₁ x₂ (termRec (E ω))),
            termField κ x₂ (termRec (E ω)) (h ω))).2 ∧
          StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ} ∧
          c₁ '' {s | (s : ℝ≥0∞) ≤ σ} =
            {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ω ∧ ∀ t' : ℝ≥0, 0 < t' → t' < t → η₁ ω t' ∉ η₂ ω '' Icc 0 T} ∧
          ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ ω (c₁ s) = termInv x₂ (termRec (E ω))
            (decPath (F ((termWord κ θ₂ c (termRec (E ω)), termSeed x₁ x₂ (termRec (E ω))),
              termField κ x₂ (termRec (E ω)) (h ω))) s)

/-- **The clock statement from the path identity**: the seed position is positive (`IsFreshRealTip.markPos_pos`) and
the word has the original datum just left of the terminal point (`IsFreshRealTip.leftLim_stopWord`). -/
theorem terminalRetainedClock_of_path (hP : TerminalRetainedPathStatement.{u}) :
    TerminalRetainedClockStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ F hF c E hcs hcJ hcb hEm hreg
    hE2 hfl htrace
  have hpath := hP κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ F hF c E hcs hcJ hcb hEm
    hreg hE2 hfl htrace
  have hgood : ∀ᵐ ω ∂P, min ⊤ (E ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ω))) :=
    ae_isDrvGood_of_isFlowLineDriver hκ ⊤ hreg hfl
  filter_upwards [hpath, hgood, htrace, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂]
    with ω hω hgω htω hinjω T e hT he hex hvis
  have hTe : (T : ℝ≥0∞) = (E ω).2 := by rw [hE2]; exact hT
  have hg : LocalExt.IsDrvGood (recHist (termRec (E ω))) :=
    hgω (by rw [min_eq_right le_top, ← hTe]; exact ENNReal.coe_ne_top)
  have hη : IsGeneratingTrace (E ω).1 (E ω).2 (fun t => η₂ ω t - x₂) := by rw [hE2]; exact htω
  have hinj : InjOn (η₂ ω) {t | (t : ℝ≥0∞) ≤ (E ω).2} := by rw [hE2]; exact hinjω
  have hfresh := isFreshRealTip_of_trace (hreg ω) hg hTe hη hinj he (ne_of_lt hex)
  have hq : e - x₂ < 0 := sub_neg.2 hex
  have hγH := mapsTo_trace_Hbar (hreg ω) hg hTe hη
  have hne := trace_ne_tip (x := x₂) hTe hinj he
  refine ⟨hfresh.markPos_pos hq (sub_nonneg.2 hx), ?_, hω T e hT he hex hvis⟩
  have h1 : leftLim (termWord κ θ₂ c (termRec (E ω))).fn 0 = leftLim c.fn (e - x₂) :=
    hfresh.leftLim_stopWord hκ c θ₂ hq hγH hne
  have h2 : leftLim c.fn = leftLim fun y => b (y + x₂) := Restart.leftLim_congr hcb
  rw [h1, h2, Exist.leftLim_comp_add, sub_add_cancel]

/-- **The named input `TerminalRetainedCondDetStatement` from the path identity.** -/
theorem terminalRetainedCondDet_of_path (hP : TerminalRetainedPathStatement.{u}) :
    TerminalRetainedCondDetStatement.{u} :=
  terminalRetainedCondDet_of_clock (terminalRetainedClock_of_path hP)

/-- **The pocket-corner exclusion from the path identity.** -/
theorem pocketCorner_of_path (hP : TerminalRetainedPathStatement.{u}) : PocketCornerStatement.{u} :=
  pocketCorner_of_terminalCondDet (terminalRetainedCondDet_of_path hP)

/-- **The real first-hit exclusion from the path identity.** -/
theorem g7GB7aFirstHitReal_of_path (hP : TerminalRetainedPathStatement.{u}) :
    G7GB7aFirstHitRealStatement.{u} :=
  g7GB7aFirstHitReal_of_pocketCorner (pocketCorner_of_path hP)

end InteractingSLE.RealContact
