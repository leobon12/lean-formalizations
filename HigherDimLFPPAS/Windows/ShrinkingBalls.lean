import HigherDimLQGMetric.Frozen.TendstoInProbLU
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Shrinking balls under local-uniform convergence in probability

The limit is assumed to have measurable evaluations and continuous sample paths. These
hypotheses make the shrinking-ball modulus measurable, while local-uniform convergence controls
the approximating functions on a fixed compact neighborhood.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal

namespace HigherDimLFPPAS.Windows

open HigherDimLFPP (Rd)

/-- The product of two closed balls, represented as a subtype of the product space. -/
abbrev winShrinkPair {d : ℕ} (x y : Rd d) (ρ : ℝ) :=
  {p : Rd d × Rd d // p ∈ Metric.closedBall x ρ ×ˢ Metric.closedBall y ρ}

theorem winShrinkPair_mem {d : ℕ} {x y : Rd d} {ρ : ℝ}
    (p : winShrinkPair x y ρ) :
    p.1.1 ∈ Metric.closedBall x ρ ∧ p.1.2 ∈ Metric.closedBall y ρ := by
  have hp := p.2
  change p.1.1 ∈ Metric.closedBall x ρ ∧ p.1.2 ∈ Metric.closedBall y ρ at hp
  exact hp

/-- A product of two closed balls is compact in the finite-dimensional Euclidean spaces used here. -/
theorem winShrinkPair_compact {d : ℕ} (x y : Rd d) (ρ : ℝ) :
    IsCompact (Set.univ : Set (winShrinkPair x y ρ)) := by
  have hs : IsCompact (Metric.closedBall x ρ ×ˢ Metric.closedBall y ρ) :=
    (isCompact_closedBall x ρ).prod (isCompact_closedBall y ρ)
  have hcompactSpace : CompactSpace (winShrinkPair x y ρ) := isCompact_iff_compactSpace.mp hs
  exact isCompact_univ

/-- The infimum of a random function on a product of two closed balls. -/
def winShrinkInf {d : ℕ} {Ω : Type*} (X : Ω → Rd d × Rd d → ℝ)
    (x y : Rd d) (ρ : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨅ p : winShrinkPair x y (ρ n), X ω p.1

/-- The oscillation of the limit function on shrinking product balls, relative to the centre. -/
def winShrinkModulus {d : ℕ} {Ω : Type*} (X : Ω → Rd d × Rd d → ℝ)
    (x y : Rd d) (ρ : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ p : winShrinkPair x y (ρ n), |X ω p.1 - X ω (x, y)|

/-- Measurability of the shrinking-ball modulus follows from evaluations on a countable dense
sequence in the closed product balls. -/
theorem winShrinkModulus_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Rd d × Rd d → ℝ) (x y : Rd d) (ρ : ℝ)
    (hρ : 0 < ρ) (hEval : ∀ p, Measurable (fun ω => X ω p))
    (hCont : ∀ ω, Continuous (X ω)) :
    Measurable (fun ω =>
      ⨆ p : winShrinkPair x y ρ, |X ω p.1 - X ω (x, y)|) := by
  let K := winShrinkPair x y ρ
  have hK : Nonempty K := by
    refine ⟨⟨(x, y), ?_⟩⟩
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_self, hρ.le, and_self]
  let q := TopologicalSpace.denseSeq K
  have hq : Dense (Set.range q) := TopologicalSpace.denseRange_denseSeq K
  have hmeas : ∀ i : ℕ, Measurable (fun ω => |X ω (q i).1 - X ω (x, y)|) := by
    intro i
    exact continuous_abs.measurable.comp ((hEval (q i).1).sub (hEval (x, y)))
  have heq (ω : Ω) :
      (⨆ i : ℕ, |X ω (q i).1 - X ω (x, y)|) =
        ⨆ p : K, |X ω p.1 - X ω (x, y)| := by
    let f : K → ℝ := fun p => |X ω p.1 - X ω (x, y)|
    have hf : Continuous f := by
      exact continuous_abs.comp ((hCont ω).comp continuous_subtype_val |>.sub continuous_const)
    calc
      (⨆ i : ℕ, f (q i)) = ⨆ p : Set.range q, f p := by
        symm
        exact iSup_range' f q
      _ = ⨆ p : K, f p := hq.ciSup' hf
  rw [show (fun ω => ⨆ p : K, |X ω p.1 - X ω (x, y)|) =
      fun ω => ⨆ i : ℕ, |X ω (q i).1 - X ω (x, y)| from funext (fun ω => (heq ω).symm)]
  exact Measurable.iSup hmeas

/-- Continuity on the compact product of closed balls bounds the modulus's defining supremum. -/
theorem winShrinkModulus_range_bddAbove {d : ℕ} {Ω : Type*}
    (X : Ω → Rd d × Rd d → ℝ) (x y : Rd d) (ρ : ℝ) (ω : Ω)
    (hCont : Continuous (X ω)) :
    BddAbove (Set.range (fun p : winShrinkPair x y ρ =>
      |X ω p.1 - X ω (x, y)|)) := by
  let K := winShrinkPair x y ρ
  have hcompactSpace : CompactSpace K := by
    exact isCompact_iff_compactSpace.mp
      ((isCompact_closedBall x ρ).prod (isCompact_closedBall y ρ))
  have hK : IsCompact (Set.univ : Set K) := isCompact_univ
  have hf : Continuous (fun p : K => |X ω p.1 - X ω (x, y)|) := by
    exact continuous_abs.comp (hCont.comp continuous_subtype_val |>.sub continuous_const)
  simpa only [Set.image_univ] using hK.bddAbove_image hf.continuousOn

/-- For every continuous sample path, the oscillation on product balls tends to zero as their
radii tend to zero. -/
theorem winShrinkModulus_tendsto_zero {d : ℕ} {Ω : Type*}
    (X : Ω → Rd d × Rd d → ℝ) (x y : Rd d) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop (𝓝 0)) (hρpos : ∀ n, 0 < ρ n)
    (hCont : ∀ ω, Continuous (X ω)) (ω : Ω) :
    Tendsto (fun n => winShrinkModulus X x y ρ n ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : ContinuousAt (X ω) (x, y) :=
    (continuous_iff_continuousAt.mp (hCont ω)) (x, y)
  obtain ⟨r, hr, hclose⟩ := (Metric.continuousAt_iff.mp hcont) (ε / 2) (by linarith)
  have hrho : ∀ᶠ n in atTop, ρ n < r := by
    exact hρ.eventually (Iio_mem_nhds hr)
  filter_upwards [hrho] with n hnr
  have hpoint (p : winShrinkPair x y (ρ n)) :
      |X ω p.1 - X ω (x, y)| < ε / 2 := by
    have hp : dist p.1 (x, y) ≤ ρ n := by
      simp only [Prod.dist_eq, max_le_iff]
      have hpball := winShrinkPair_mem p
      exact ⟨Metric.mem_closedBall.mp hpball.1, Metric.mem_closedBall.mp hpball.2⟩
    have hdist : dist (X ω p.1) (X ω (x, y)) < ε / 2 :=
      hclose (lt_of_le_of_lt hp hnr)
    simpa only [Real.dist_eq] using hdist
  have hKn : Nonempty (winShrinkPair x y (ρ n)) := by
    refine ⟨⟨(x, y), ?_⟩⟩
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_self,
      (hρpos n).le, and_self]
  have hupper : winShrinkModulus X x y ρ n ω ≤ ε / 2 := by
    change (⨆ p : winShrinkPair x y (ρ n),
      |X ω p.1 - X ω (x, y)|) ≤ ε / 2
    apply ciSup_le
    intro p
    exact le_of_lt (hpoint p)
  have hnonneg : 0 ≤ winShrinkModulus X x y ρ n ω := by
    have hbdd : BddAbove (Set.range (fun p : winShrinkPair x y (ρ n) =>
        |X ω p.1 - X ω (x, y)|)) :=
      ⟨ε / 2, fun z hz => by rcases hz with ⟨p, rfl⟩; exact le_of_lt (hpoint p)⟩
    obtain ⟨p⟩ := hKn
    exact le_ciSup_of_le hbdd p (abs_nonneg _)
  have hdist : dist (winShrinkModulus X x y ρ n ω) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt hupper (by linarith)
  exact hdist

/-- The infimum of the approximating functions on two shrinking closed balls converges in outer
probability to the limit function at the pair of centres. The evaluation measurability assumption
is used only to turn the continuous limit's shrinking-ball modulus into a measurable random
variable. -/
theorem tendstoInProbLU_winShrinkInf {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → Rd d × Rd d → ℝ) (X : Ω → Rd d × Rd d → ℝ)
    (hConv : HigherDimLQGMetric.TendstoInProbLU P Xn atTop X)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) (hρpos : ∀ n, 0 < ρ n)
    (hEval : ∀ p, Measurable (fun ω => X ω p))
    (hCont : ∀ ω, Continuous (X ω)) (x y : Rd d) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => P {ω | ENNReal.ofReal δ ≤
        edist (winShrinkInf (Xn n) x y ρ n ω) (X ω (x, y))}) atTop (𝓝 0) := by
  intro δ hδ
  let α := δ / 3
  let β := δ / 3
  let R := max (‖x‖ + 1) (‖y‖ + 1)
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hsmall : α + β < δ := by
    dsimp [α, β]
    linarith
  have hρeventually : ∀ᶠ n in atTop, ρ n ≤ 1 := by
    filter_upwards [hρ.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn using hn.le
  let locSup (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ⨆ p ∈ Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R,
      edist (Xn n ω p) (X ω p)
  let locBad (n : ℕ) : Set Ω := {ω | ENNReal.ofReal α ≤ locSup n ω}
  let modBad (n : ℕ) : Set Ω := {ω | β ≤ winShrinkModulus X x y ρ n ω}
  let bad (n : ℕ) : Set Ω := {ω | ENNReal.ofReal δ ≤
    edist (winShrinkInf (Xn n) x y ρ n ω) (X ω (x, y))}
  have hLoc : Tendsto (fun n => P (locBad n)) atTop (𝓝 0) := by
    simpa [locBad, locSup] using hConv R hR α hα
  have hmodMeas (n : ℕ) :
      Measurable (fun ω => winShrinkModulus X x y ρ n ω) := by
    exact winShrinkModulus_measurable X x y (ρ n) (hρpos n) hEval hCont
  have hmodSet (n : ℕ) : MeasurableSet (modBad n) := by
    exact measurableSet_le measurable_const (hmodMeas n)
  have hMod : Tendsto (fun n => P (modBad n)) atTop (𝓝 0) := by
    have hmeasure := MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
      atTop P hmodSet (fun ω => by
        filter_upwards [
          (winShrinkModulus_tendsto_zero X x y ρ hρ hρpos hCont ω).eventually
            (Iio_mem_nhds hβ)] with n hn
        change (β ≤ winShrinkModulus X x y ρ n ω) ↔ False
        exact iff_false_intro (not_le_of_gt hn))
    have hzero : P (fun _ : Ω => False) = 0 := by
      change P (∅ : Set Ω) = 0
      exact MeasureTheory.measure_empty
    rw [hzero] at hmeasure
    simpa [modBad] using hmeasure
  have hcontain (n : ℕ) (hnρ : ρ n ≤ 1) : bad n ⊆ locBad n ∪ modBad n := by
    intro ω hω
    by_contra hnot
    have hLocNot : ω ∉ locBad n := by
      intro h
      exact hnot (Or.inl h)
    have hModNot : ω ∉ modBad n := by
      intro h
      exact hnot (Or.inr h)
    have hLocSup : locSup n ω < ENNReal.ofReal α := lt_of_not_ge hLocNot
    have hmod : winShrinkModulus X x y ρ n ω < β := lt_of_not_ge hModNot
    have hmodBdd := winShrinkModulus_range_bddAbove X x y (ρ n) ω (hCont ω)
    have hK : Nonempty (winShrinkPair x y (ρ n)) := by
      refine ⟨⟨(x, y), ?_⟩⟩
      simp only [Set.mem_prod, Metric.mem_closedBall, dist_self,
        (hρpos n).le, and_self]
    have hlocal (p : winShrinkPair x y (ρ n)) :
        |Xn n ω p.1 - X ω p.1| < α := by
      have hpball := winShrinkPair_mem p
      have ha : p.1.1 ∈ Metric.closedBall (0 : Rd d) R := by
        apply Metric.mem_closedBall.mpr
        calc
          dist p.1.1 0 ≤ dist p.1.1 x + dist x 0 := dist_triangle _ _ _
          _ ≤ ρ n + ‖x‖ := by
            exact add_le_add (Metric.mem_closedBall.mp hpball.1) (by simp)
          _ ≤ ‖x‖ + 1 := by linarith
          _ ≤ R := le_max_left _ _
      have hb : p.1.2 ∈ Metric.closedBall (0 : Rd d) R := by
        apply Metric.mem_closedBall.mpr
        calc
          dist p.1.2 0 ≤ dist p.1.2 y + dist y 0 := dist_triangle _ _ _
          _ ≤ ρ n + ‖y‖ := by
            exact add_le_add (Metric.mem_closedBall.mp hpball.2) (by simp)
          _ ≤ ‖y‖ + 1 := by linarith
          _ ≤ R := le_max_right _ _
      have hp : p.1 ∈ Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R :=
        ⟨ha, hb⟩
      have hle : edist (Xn n ω p.1) (X ω p.1) ≤ locSup n ω :=
        le_iSup_of_le p.1 (le_iSup_of_le hp le_rfl)
      have hlt : edist (Xn n ω p.1) (X ω p.1) < ENNReal.ofReal α :=
        lt_of_le_of_lt hle hLocSup
      apply (ENNReal.ofReal_lt_ofReal_iff hα).mp
      simpa only [edist_dist, Real.dist_eq] using hlt
    have hmodulus (p : winShrinkPair x y (ρ n)) :
        |X ω p.1 - X ω (x, y)| < β := by
      have hle : |X ω p.1 - X ω (x, y)| ≤ winShrinkModulus X x y ρ n ω :=
        le_ciSup hmodBdd p
      exact lt_of_le_of_lt hle hmod
    have htotal (p : winShrinkPair x y (ρ n)) :
        |Xn n ω p.1 - X ω (x, y)| < α + β := by
      have htriangle :
          |Xn n ω p.1 - X ω (x, y)| ≤
            |Xn n ω p.1 - X ω p.1| + |X ω p.1 - X ω (x, y)| := by
        calc
          |Xn n ω p.1 - X ω (x, y)| =
              |(Xn n ω p.1 - X ω p.1) + (X ω p.1 - X ω (x, y))| := by
                congr 1
                ring
          _ ≤ _ := abs_add_le _ _
      exact lt_of_le_of_lt htriangle (add_lt_add (hlocal p) (hmodulus p))
    have hlower (p : winShrinkPair x y (ρ n)) :
        X ω (x, y) - (α + β) ≤ Xn n ω p.1 := by
      have hlow := (abs_lt.mp (htotal p)).1
      linarith
    have hbounded : BddBelow (Set.range (fun p : winShrinkPair x y (ρ n) =>
        Xn n ω p.1)) :=
      ⟨X ω (x, y) - (α + β), fun z hz => by
        rcases hz with ⟨p, rfl⟩
        exact hlower p⟩
    have hinfLower : X ω (x, y) - (α + β) ≤ winShrinkInf (Xn n) x y ρ n ω := by
      change X ω (x, y) - (α + β) ≤ ⨅ p : winShrinkPair x y (ρ n), Xn n ω p.1
      exact le_ciInf hlower
    let p₀ : winShrinkPair x y (ρ n) := ⟨(x, y), by
      simp only [Set.mem_prod, Metric.mem_closedBall, dist_self,
        (hρpos n).le, and_self]⟩
    have hcenter : |Xn n ω (x, y) - X ω (x, y)| < α := by
      simpa [p₀] using hlocal p₀
    have hinfUpper : winShrinkInf (Xn n) x y ρ n ω ≤ X ω (x, y) + (α + β) := by
      change (⨅ p : winShrinkPair x y (ρ n), Xn n ω p.1) ≤
        X ω (x, y) + (α + β)
      calc
        (⨅ p : winShrinkPair x y (ρ n), Xn n ω p.1) ≤ Xn n ω p₀.1 :=
          ciInf_le hbounded p₀
        _ ≤ X ω (x, y) + (α + β) := by
          have habs := (abs_lt.mp hcenter).2
          linarith
    have hinfAbs : |winShrinkInf (Xn n) x y ρ n ω - X ω (x, y)| ≤ α + β := by
      rw [abs_le]
      constructor
      · linarith [hinfLower]
      · linarith [hinfUpper]
    have hsmallInf : edist (winShrinkInf (Xn n) x y ρ n ω) (X ω (x, y)) <
        ENNReal.ofReal δ := by
      rw [edist_dist, Real.dist_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 (lt_of_le_of_lt hinfAbs hsmall)
    exact (not_le_of_gt hsmallInf) hω
  have hprobBound : ∀ᶠ n in atTop, P (bad n) ≤ P (locBad n) + P (modBad n) := by
    filter_upwards [hρeventually] with n hnρ
    calc
      P (bad n) ≤ P (locBad n ∪ modBad n) := measure_mono (hcontain n hnρ)
      _ ≤ P (locBad n) + P (modBad n) := measure_union_le _ _
  have hsum : Tendsto (fun n => P (locBad n) + P (modBad n)) atTop (𝓝 0) := by
    simpa using hLoc.add hMod
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
    (Eventually.of_forall fun n => bot_le) hprobBound
