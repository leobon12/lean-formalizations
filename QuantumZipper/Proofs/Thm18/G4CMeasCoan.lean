import QuantumZipper.Proofs.Thm18.G4CMeasLusin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coanalytic conditions over a Polish parameter are universally null-measurable (task G4C-MEAS)

Tools for the remaining descriptive-set measurability nodes (G4 Core C: the all-parameter
predicate `Group1Good`; F1: `LenReadRegMeasStmt`, monotonicity and continuity of the read
lengths). None of these sets is a projection with unique witnesses, so the Lusin–Souslin trick
(`G4CMeasProj.lean`) does not apply to them; they are **coanalytic** (a universal quantifier over
a Polish parameter of a Borel condition), and Lusin's theorem (`G4CMeasLusin.lean`; Kechris,
*Classical Descriptive Set Theory*, Thm 21.10, with the closure of `Σ¹₁` under countable unions,
intersections and continuous images, Kechris Prop. 14.4) makes them null-measurable for every
s-finite measure.

* `nullMeasurableSet_forall`: `{k | ∀ θ, (k, θ) ∈ R}` for Borel `R ⊆ K × Θ`.
* `nullMeasurableSet_monotoneOn`: `{k | MonotoneOn (g (k, ·)) I}` for jointly measurable `g`.
* `nullMeasurableSet_continuousOn`: `{k | ContinuousOn (g (k, ·)) I}` for jointly measurable
  real `g`.

**Own elementary argument** on top of the cited theorems.
-/

namespace QuantumZipper.Thm18Asm.G4Core

open MeasureTheory Set Filter Topology

variable {K : Type*} [TopologicalSpace K] [PolishSpace K] [MeasurableSpace K] [BorelSpace K]

/-- **Universal quantification over a Polish parameter**: for a Borel set `R ⊆ K × Θ`, the set
`{k | ∀ θ, (k, θ) ∈ R}` is coanalytic, hence null-measurable for every s-finite measure. -/
theorem nullMeasurableSet_forall {Θ : Type*} [TopologicalSpace Θ] [PolishSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] {R : Set (K × Θ)} (hR : MeasurableSet R)
    (μ : Measure K) [SFinite μ] : NullMeasurableSet {k | ∀ θ, (k, θ) ∈ R} μ := by
  refine coanalyticSet_nullMeasurableSet_of_sFinite ?_ μ
  have e : {k | ∀ θ, (k, θ) ∈ R}ᶜ = Prod.fst '' Rᶜ := by
    ext k
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, mem_image, Prod.exists,
      exists_and_right, exists_eq_right]
  rw [e]
  exact hR.compl.analyticSet.image_of_continuous continuous_fst

/-- **Monotonicity in a real parameter** of a jointly measurable function is a universally
null-measurable condition. -/
theorem nullMeasurableSet_monotoneOn {β : Type*} [LinearOrder β] [TopologicalSpace β]
    [OrderClosedTopology β] [SecondCountableTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {g : K × ℝ → β} (hg : Measurable g) {I : Set ℝ}
    (hI : MeasurableSet I) (μ : Measure K) [SFinite μ] :
    NullMeasurableSet {k | MonotoneOn (fun t => g (k, t)) I} μ := by
  set R : Set (K × (ℝ × ℝ)) := {q | q.2.1 ∈ I}ᶜ ∪ ({q | q.2.2 ∈ I}ᶜ ∪
    ({q | q.2.1 ≤ q.2.2}ᶜ ∪ {q | g (q.1, q.2.1) ≤ g (q.1, q.2.2)})) with hRdef
  have hR : MeasurableSet R := by
    refine (hI.preimage (measurable_fst.comp measurable_snd)).compl.union
      ((hI.preimage (measurable_snd.comp measurable_snd)).compl.union
        ((measurableSet_le (measurable_fst.comp measurable_snd)
          (measurable_snd.comp measurable_snd)).compl.union
          (measurableSet_le (hg.comp (measurable_fst.prodMk
            (measurable_fst.comp measurable_snd)))
            (hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))))
  have e : {k | MonotoneOn (fun t => g (k, t)) I} = {k | ∀ θ, (k, θ) ∈ R} := by
    ext k
    simp only [mem_ofPred_eq, hRdef, mem_union, mem_compl_iff, Prod.forall, MonotoneOn]
    constructor
    · intro h s t
      by_cases hs : s ∈ I
      · by_cases ht : t ∈ I
        · by_cases hst : s ≤ t
          · exact Or.inr (Or.inr (Or.inr (h hs ht hst)))
          · exact Or.inr (Or.inr (Or.inl hst))
        · exact Or.inr (Or.inl ht)
      · exact Or.inl hs
    · intro h s hs t ht hst
      rcases h s t with h1 | h1 | h1 | h1
      · exact absurd hs h1
      · exact absurd ht h1
      · exact absurd hst h1
      · exact h1
  rw [e]
  exact nullMeasurableSet_forall hR μ

/-- `ContinuousWithinAt` for real functions with rational tolerances. -/
theorem continuousWithinAt_iff_nat {f : ℝ → ℝ} {I : Set ℝ} {t : ℝ} :
    ContinuousWithinAt f I t ↔ ∀ n : ℕ, ∃ m : ℕ, ∀ s ∈ I,
      dist s t < 1 / ((m : ℝ) + 1) → dist (f s) (f t) < 1 / ((n : ℝ) + 1) := by
  rw [Metric.continuousWithinAt_iff]
  constructor
  · intro h n
    obtain ⟨δ, hδ, hδf⟩ := h (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact ⟨m, fun s hs hst => hδf hs (hst.trans hm)⟩
  · intro h ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm⟩ := h n
    exact ⟨1 / ((m : ℝ) + 1), Nat.one_div_pos_of_nat,
      fun {s} hs hst => (hm s hs hst).trans hn⟩

/-- **Continuity in a real parameter** of a jointly measurable real function is a universally
null-measurable condition: the complement `∃ t ∈ I, ∃ n, ∀ m, ∃ s ∈ I, …` is analytic. -/
theorem nullMeasurableSet_continuousOn {g : K × ℝ → ℝ} (hg : Measurable g) {I : Set ℝ}
    (hI : MeasurableSet I) (μ : Measure K) [SFinite μ] :
    NullMeasurableSet {k | ContinuousOn (fun t => g (k, t)) I} μ := by
  refine coanalyticSet_nullMeasurableSet_of_sFinite ?_ μ
  -- the Borel "bad" sets in `(K × ℝ) × ℝ`: `t, s ∈ I`, `|s - t| < 1/(m+1)`,
  -- `|g s - g t| ≥ 1/(n+1)`
  set Bad : ℕ → ℕ → Set ((K × ℝ) × ℝ) := fun n m =>
    {q | q.1.2 ∈ I} ∩ ({q | q.2 ∈ I} ∩ ({q | dist q.2 q.1.2 < 1 / ((m : ℝ) + 1)} ∩
      {q | 1 / ((n : ℝ) + 1) ≤ dist (g (q.1.1, q.2)) (g q.1)})) with hBad
  have hBadm : ∀ n m, MeasurableSet (Bad n m) := by
    intro n m
    exact (hI.preimage (measurable_snd.comp measurable_fst)).inter
      ((hI.preimage measurable_snd).inter ((measurableSet_lt
      (measurable_snd.dist (measurable_snd.comp measurable_fst)) measurable_const).inter
      (measurableSet_le measurable_const ((hg.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd)).dist (hg.comp measurable_fst)))))
  set A : Set (K × ℝ) := ⋃ n : ℕ, ⋂ m : ℕ, Prod.fst '' Bad n m with hAdef
  have hA : AnalyticSet A :=
    AnalyticSet.iUnion fun n => AnalyticSet.iInter fun m =>
      (hBadm n m).analyticSet.image_of_continuous continuous_fst
  have e : {k | ContinuousOn (fun t => g (k, t)) I}ᶜ = Prod.fst '' A := by
    ext k
    constructor
    · intro hk
      simp only [mem_compl_iff, mem_ofPred_eq, ContinuousOn, not_forall] at hk
      obtain ⟨t, ht, hkt⟩ := hk
      rw [continuousWithinAt_iff_nat] at hkt
      push Not at hkt
      obtain ⟨n, hn⟩ := hkt
      refine ⟨(k, t), ?_, rfl⟩
      simp only [hAdef, mem_iUnion, mem_iInter]
      refine ⟨n, fun m => ?_⟩
      obtain ⟨s, hs, hst, hf⟩ := hn m
      exact ⟨((k, t), s), ⟨ht, hs, hst, hf⟩, rfl⟩
    · rintro ⟨⟨k', t⟩, hA', rfl⟩
      simp only [hAdef, mem_iUnion, mem_iInter] at hA'
      obtain ⟨n, hn⟩ := hA'
      simp only [mem_compl_iff, mem_ofPred_eq, ContinuousOn, not_forall]
      obtain ⟨⟨⟨k0, t0⟩, s0⟩, ⟨ht0, -⟩, h0⟩ := hn 0
      simp only [Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      refine ⟨t0, ht0, ?_⟩
      rw [continuousWithinAt_iff_nat]
      push Not
      refine ⟨n, fun m => ?_⟩
      obtain ⟨⟨⟨k1, t1⟩, s⟩, ⟨-, hs, hst, hf⟩, h1⟩ := hn m
      simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨s, hs, hst, hf⟩
  rw [e]
  exact hA.image_of_continuous continuous_fst

end QuantumZipper.Thm18Asm.G4Core
