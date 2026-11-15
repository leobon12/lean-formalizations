/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsSector

/-!
# The canonical boundary word of a component chart is piecewise constant

Packet PROVE-WALK-WORDS (`hMatch`'s finite word, `IsPiecewiseConstantBoundaryData`). By
`WalkWordsSector.walkComponentLandingStatement_of_walks`, every component chart lands along a continuous injective
map `ℓ : ℝ → ℂ`. Then the canonical word `componentWord` (`WalkWordsCompWire`, the only word satisfying (GW3.1) off its
jumps) is locally constant at every `y ≠ 0` whose landing is neither a junction of either walk nor a jump of `b`: at an
ordinary landing off the closure of the rest of its walk (the real start and connectors) the nearby landings are
ordinary points of the same walk (value `∓Λ`, real or not); at a landing off the (closed) ordinary set the nearby
landings are real points off it (value `b(ℓ x)`, locally constant). By injectivity of `ℓ` the exceptional `y` are
finitely many once each walk has finitely many **junctions** `ord ∩ cl(phys ∖ ord)` (piece ends on connectors):
**`exists_isPiecewiseConstant_componentWord`** (deterministic).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar isOpen_H)

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry WalkMean WalkNorm

/-- **The canonical word is piecewise constant** (deterministic): for a chart inverse `inv` landing along a continuous
injective `ℓ`, with positive (negative) landings in a set `PR` (`PL`) whose points are ordinary or real, closed ordinary
sets with finitely many **junctions** with the rest (`ordR ∩ cl(PR ∖ ordR)`: piece ends on connectors), and piecewise
constant `b`, the canonical word has a finite jump set: `0` and the `ℓ`-preimages of the junctions and of the jumps of
`b`. (Real points of ordinary pieces are not exceptional: the word is `∓Λ` there.) -/
theorem exists_isPiecewiseConstant_componentWord {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {PR PL ordR ordL : Set ℂ}
    (hPR : ∀ z ∈ PR, z ∈ ordR ∨ z.im = 0) (hPL : ∀ z ∈ PL, z ∈ ordL ∨ z.im = 0) (hoR : IsClosed ordR)
    (hoL : IsClosed ordL) (hfR : (ordR ∩ closure (PR \ ordR)).Finite) (hfL : (ordL ∩ closure (PL \ ordL)).Finite)
    {inv : ℂ → ℂ} {ℓ : ℝ → ℂ} (hℓc : Continuous ℓ) (hℓi : Injective ℓ)
    (hℓ : ∀ x : ℝ, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 (ℓ x))) (hℓR : ∀ x : ℝ, 0 < x → ℓ x ∈ PR)
    (hℓL : ∀ x : ℝ, x < 0 → ℓ x ∈ PL) :
    ∃ jumpsC : Finset ℝ, IsPiecewiseConstantBoundaryData (componentWord κ b ordR ordL inv) jumpsC := by
  have hF : ((ordR ∩ closure (PR \ ordR)) ∪ (ordL ∩ closure (PL \ ordL)) ∪
      (((↑) : ℝ → ℂ) '' (jumps : Set ℝ))).Finite :=
    (hfR.union hfL).union (jumps.finite_toSet.image _)
  have hS := hF.preimage hℓi.injOn
  refine ⟨insert 0 hS.toFinset, fun y hy => ?_⟩
  simp only [Finset.mem_insert, Set.Finite.mem_toFinset, mem_preimage, not_or] at hy
  obtain ⟨hy0, hyF⟩ := hy
  have hext : ∀ x : ℝ, extendFrom H inv x = ℓ x := fun x => by
    have hx : ((x : ℂ)) ∈ closure H := by rw [closure_H]; show (0 : ℝ) ≤ ((x : ℂ)).im; simp
    exact extendFrom_eq hx (hℓ x)
  have hevb : (ℓ y).re ∉ jumps → ∀ᶠ x in 𝓝 y, b (ℓ x).re = b (ℓ y).re := fun hyj =>
    ((continuous_re.comp hℓc).continuousAt.tendsto).eventually (hb _ hyj)
  -- the two local cases for one wall: an ordinary landing off the junctions, or a landing off the ordinary set
  have hloc : ∀ {o P : Set ℂ}, (∀ z ∈ P, z ∈ o ∨ z.im = 0) → IsClosed o → (∀ᶠ x in 𝓝 y, ℓ x ∈ P) →
      ℓ y ∈ P → (ℓ y ∈ o → ℓ y ∉ closure (P \ o)) →
      (∀ᶠ x in 𝓝 y, ℓ x ∈ o) ∧ ℓ y ∈ o ∨
        (∀ᶠ x in 𝓝 y, ℓ x ∉ o) ∧ ℓ y ∉ o ∧ (ℓ y).im = 0 ∧ (ℓ y).re ∉ jumps := by
    intro o P hP ho hevP hyP hyc
    by_cases hyo : ℓ y ∈ o
    · refine Or.inl ⟨?_, hyo⟩
      have hU : (closure (P \ o))ᶜ ∈ 𝓝 (ℓ y) := isClosed_closure.isOpen_compl.mem_nhds (hyc hyo)
      filter_upwards [hevP, hℓc.continuousAt.preimage_mem_nhds hU] with x hxP hxU
      by_contra hxo
      exact hxU (subset_closure ⟨hxP, hxo⟩)
    · have hyim : (ℓ y).im = 0 := (hP _ hyP).resolve_left hyo
      refine Or.inr ⟨hℓc.continuousAt.preimage_mem_nhds (ho.isOpen_compl.mem_nhds hyo), hyo, hyim, fun h => ?_⟩
      exact hyF (Or.inr ⟨_, h, Complex.ext (by simp) (by simp [hyim])⟩)
  rcases lt_or_gt_of_ne hy0 with hyn | hyp
  · have hev0 : ∀ᶠ x in 𝓝 y, x < 0 := Iio_mem_nhds hyn
    have hyp' : ¬ 0 < y := not_lt.2 hyn.le
    rcases hloc hPL hoL (hev0.mono fun x hx => hℓL x hx) (hℓL y hyn)
        (fun h hc => hyF (Or.inl (Or.inr ⟨h, hc⟩))) with ⟨hev, hyo⟩ | ⟨hev, hyo, -, hyj⟩
    · filter_upwards [hev0, hev] with x hx hxo
      simp only [componentWord, hext, hx, hyn, not_lt.2 hx.le, hyp', hxo, hyo, ↓reduceIte]
    · filter_upwards [hev0, hev, hevb hyj] with x hx hxo hxb
      simp only [componentWord, hext, hx, hyn, not_lt.2 hx.le, hyp', hxo, hyo, ↓reduceIte, hxb]
  · have hev0 : ∀ᶠ x in 𝓝 y, 0 < x := Ioi_mem_nhds hyp
    rcases hloc hPR hoR (hev0.mono fun x hx => hℓR x hx) (hℓR y hyp)
        (fun h hc => hyF (Or.inl (Or.inl ⟨h, hc⟩))) with ⟨hev, hyo⟩ | ⟨hev, hyo, -, hyj⟩
    · filter_upwards [hev0, hev] with x hx hxo
      simp only [componentWord, hext, hx, hyp, hxo, hyo, ↓reduceIte]
    · filter_upwards [hev0, hev, hevb hyj] with x hx hxo hxb
      simp only [componentWord, hext, hx, hyp, hxo, hyo, ↓reduceIte, hxb]

end InteractingSLE.Theorem14.WalkWords
