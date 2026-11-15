/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP6Retarget
import InteractingSLE.Spec.Supplement.LP1Seed

/-!
# Lemma LP8: the singleton extension of Aux. lemma 113, reduced to its transience part

Packet PROVE-LP14. Supplement §6.5, Lemma LP8 (`source/spec/p481-528.md` L109–L115, p. 485): "Fix `k > 0`, `N ≥ 3`,
and assume the complete continuity and transience theorem for every configuration with at most `N − 1` finite force
groups, together with the complete two-seed theorem. Besides the three alternatives stated in Aux. lemma 113, its
conclusion holds if one side is a single admissible group and the total weight of the other side exceeds
`d = k/2 − 4`."

LP8's proof is Aux. lemma 113's proof with a strengthened experiment: "Now repeat Aux. lemma 113's adapted midpoint
trials with this experiment. […] A finite successful left swallow therefore decreases the number of groups, unless it
is the continuation threshold. […] The finite-time continuity and finite-threshold endpoint assertion are already Aux.
lemma 103. These are all parts of Aux. lemma 113's proof, with the strengthened singleton experiment replacing its
two-total experiment."

This file proves everything in LP8 except the midpoint trials themselves, through the landed Aux. 113 machinery
(PROVE-SEC7-C4, PROVE-RANDRESTART2):

* finite-time continuity through the continuation threshold is Aux. lemma 103 (`Sec7.ae_isGeneratingTrace_lifetime`,
  with Theorem 2.2's existence `Theorem13.existsEvolutionStatement` and the seed entrance);
* the stop at the first merger of two same-side groups, the restart with fewer groups and the join of the traces are
  `Sec7.exists_countPrefix` and `Sec7.isCompleteForceWord_of_hasCountPrefix`;
* if the singleton weight exceeds `d`, the configuration is in Aux. lemma 113's third sector and its transience is
  `Sec7.LPAux113TransienceStatement`.

What remains is transience when no two groups ever merge in the new sector `−2 < r ≤ d < s`, the named input
`LP8TransienceStatement` (the midpoint trials with the strengthened Aux. 111 experiment: the reflected dipolar reference
for `d < s < c`, the opposite-side two-mark law with the nonhitting Bessel argument for `s ≥ c`, Aux. lemma 101 and the
terminal trial principle).

## Main results

* `isCompleteForceWord_of_noMergerTransience`: the general step "transience without merger ⇒ complete" for a
  two-sided word with `N` groups, under the smaller-count hypothesis and the two-seed premise.
* `lp8Statement_of_inputs`: the named input `LP8Statement κ` of Theorem LP10.
* `lp10Statement_of_open_lp14`: Theorem LP10 from the open inputs of `Theorem13Inputs.lean`, with Proposition LP6
  (`LP6Retarget.lean`) and the one-seed theorem (`LP1Seed.lean`) now proved and Lemma LP8 replaced by
  `LP8TransienceStatement`.

These are conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP

/-! ### The general step: transience without merger gives completeness -/

/-- **Transience without merger gives completeness** (Aux. lemma 113's structure, pp. 369–372, used verbatim by LP8,
p. 485): for a distinct-position word with `N` groups, at least one on each side, under the smaller-count hypothesis
and the two-seed premise, if every evolution almost surely has a transient trace on the event that the lifetime is
infinite and no two same-side groups ever merge, the word is complete. Finite-time continuity is Aux. lemma 103, and
the first merger is a stopping time at which the smaller-count theorem restarts the evolution. -/
theorem isCompleteForceWord_of_noMergerTransience {κ : ℝ} (hκ : 0 < κ)
    (hseed : Sec7.SeedEntranceStatement.{u} κ) (h2 : TwoSeedComplete.{u} κ) {N : ℕ}
    (hD : DistinctCompleteBelow.{u} κ N) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hd : IsDistinctForceWord xL xR) (hsum : nL + nR = N)
    (hL : 0 < nL) (hR : 0 < nR)
    (htr : ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ Sec7.SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  have hpre : Sec7.HasCountPrefix.{u} κ xL xR ρL ρR N := by
    intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
    have hstart : (∀ i j, xL i < xR j) ∨ ∀ᵐ ω ∂P, ζ ω = 0 ∨
        ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ε η := by
      by_cases hsep : ∀ i j, xL i < xR j
      · exact Or.inl hsep
      · exact Or.inr (hseed h2 xL xR ρL ρR hd.1 hsep P 𝓕 W VL VR B ζ hE)
    have htrace := Sec7.ae_isGeneratingTrace_lifetime hκ Theorem13.existsEvolutionStatement hD hE hd.1
      (by omega) (by omega) hstart
    obtain ⟨τ, hτ, hae⟩ := Sec7.exists_countPrefix hE htrace (htr P 𝓕 W VL VR B ζ hE)
    rw [← hsum]
    exact ⟨τ, hτ, hae⟩
  intro Ω mΩ
  exact Sec7.isCompleteForceWord_of_hasCountPrefix hκ hD hpre

/-! ### Lemma LP8 -/

/-- **Named input: transience in Lemma LP8's new sector when no two groups merge** (supplement p. 485, LP8's proof:
"Now repeat Aux. lemma 113's adapted midpoint trials with this experiment. […] An infinite successful reference branch
is transient. The same buffer half-rectangle gives no finite accumulation of failed trials. Every infinite one-sided
phase has finite angular clock by Aux. lemma 101 […]. If there are infinitely many midpoint trials, the uniformly
positive success probability excludes failure of all of them."; the strengthened singleton experiment of Aux. lemma
111, p. 485). For `N ≥ 3`, under the smaller-count hypothesis and the two-seed premise, every evolution of a
distinct-position word with `N − 1` left marks of total `s > d` and one right mark of weight `−2 < r ≤ d` almost
surely, if its lifetime is infinite and no two left groups ever merge, has a trace tending to infinity. (The singleton
weights `r > d` are Aux. lemma 113's third sector, `Sec7.LPAux113TransienceStatement`.) -/
def LP8TransienceStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → DistinctCompleteBelow.{u} κ N → TwoSeedComplete.{u} κ →
    ∀ {nL : ℕ} (xL : Fin nL → ℝ) (xR : Fin 1 → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin 1 → ℝ),
      IsDistinctForceWord xL xR → nL + 1 = N → -2 < ρR 0 → ρR 0 ≤ κ / 2 - 4 → κ / 2 - 4 < ∑ i, ρL i →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t, ¬ Sec7.SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t) →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- **Lemma LP8** (supplement p. 485) in the form consumed by Theorem LP10 (`LP8Statement κ`, right singleton), from
the seed entrance (Aux. lemma 103, `D₀ = 0`), Aux. lemma 113's transience (singleton weight `> d`) and LP8's transience
in its new sector (singleton weight `≤ d`). Conditional helper. -/
theorem lp8Statement_of_inputs {κ : ℝ} (hκ : 0 < κ) (hseed : Sec7.SeedEntranceStatement.{u} κ)
    (h113 : Sec7.LPAux113TransienceStatement.{u} κ) (h8 : LP8TransienceStatement.{u} κ) :
    LP8Statement.{u} κ := by
  intro N hN hD h2 nL xL xR ρL ρR hd hsum hr hl
  refine isCompleteForceWord_of_noMergerTransience hκ hseed h2 hD hd hsum (by omega) one_pos ?_
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  rcases le_or_gt (ρR 0) (κ / 2 - 4) with hle | hlt
  · exact h8 N hN hD h2 xL xR ρL ρR hd hsum hr hle hl P 𝓕 W VL VR B ζ hE
  · have hs : κ / 2 - 4 < ∑ i, ρR i := by rw [Fin.sum_univ_one]; exact hlt
    exact h113 N hN hD h2 xL xR ρL ρR hd hsum (by omega) one_pos (Or.inr (Or.inr ⟨hl, hs⟩)) P 𝓕 W VL VR
      B ζ hE

/-! ### Theorem LP10 from the open inputs, with LP6 and the one-seed theorem proved and LP8 reduced -/

/-- **Theorem LP10 from the open inputs** (supplement §6.5, p. 486; conditional helper). The induction
`isCompleteForceWord_of_reductions_noLP6` at each `k > 4`, under LP10's two-seed premise, with:

* the zero-force base (`Theorem13.zeroForceStatement`);
* the one-force base from Aux. lemma 99 and the one-seed theorem, the latter from the two-seed premise with left weight
  `0` (`oneForceStatement_of_twoSeedComplete`, `LP1Seed.lean`);
* Proposition LP6 from LP9 (`lp6Statement_of_lp9`, inside `isCompleteForceWord_of_reductions_noLP6`);
* Aux. lemma 113 in LP10's form from the seed entrance and transience without merger (`Sec7.lpAux113Statement_of_prefix`,
  `Sec7.lpAux113PrefixStatement_of_inputs`);
* Lemma LP8 from the seed entrance, Aux. lemma 113's transience and `LP8TransienceStatement` (`lp8Statement_of_inputs`);
* Lemma LP9 from its prefix part (`Sec7.lp9Statement_of_prefix`).

Compared with PROVE-T13-ASM's `Theorem13.lp10Statement_of_open`, the inputs `Theorem13.SeedOneForceGTFourStatement`
and `LP.LP6Statement` are gone, and `LP.LP8Statement` is replaced by `LP8TransienceStatement`. -/
theorem lp10Statement_of_open_lp14
    (h99 : ∀ κ : ℝ, 4 < κ → Sec7.Aux99StoppedStatement.{u} κ)
    (h106 : ∀ κ : ℝ, 4 < κ → Aux106Statement.{u} κ)
    (hseed : ∀ κ : ℝ, 4 < κ → Sec7.SeedEntranceStatement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Sec7.LPAux113TransienceStatement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP8TransienceStatement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 < κ → Sec7.LP9PrefixStatement.{u} κ) : LP10Statement.{u} := by
  intro κ hκ h2 nL nR xL xR ρL ρR hF
  have hκ0 : 0 < κ := by linarith
  intro Ω mΩ
  exact isCompleteForceWord_of_reductions_noLP6 (Theorem13.zeroForceStatement hκ0)
    (oneForceStatement_of_twoSeedComplete hκ0 (h99 κ hκ) h2) (h106 κ hκ)
    (Sec7.lpAux113Statement_of_prefix hκ0
      (Sec7.lpAux113PrefixStatement_of_inputs hκ0 Theorem13.existsEvolutionStatement (hseed κ hκ) (h113 κ hκ)))
    (lp8Statement_of_inputs hκ0 (hseed κ hκ) (h113 κ hκ) (h8 κ hκ)) (Sec7.lp9Statement_of_prefix hκ0 (h9 κ hκ))
    h2 xL xR ρL ρR hF

end InteractingSLE.LP
