import HigherDimLFPPAS.Sharp.Steps

/-!
# Proposition 5.1: sharp comparison with polynomial rate (packet P51)

Source: `planning/audits/MA2-sections-4-6.md` §§2.8–2.16 and Details D-B (items 1–6); MA4 §2.5 and
Details B.2–B.5; paper §5 (`source/higher-dimensional-lfpp-almost-sure.txt` l. 554–644).

**Theorem** `prop51_holds`: `Core.Prop51Stmt κ ξ D P h` from the standing hypotheses `Core.Setting` and
the interfaces `Prop41Stmt` (Proposition 4.1), `UnitSpeedAdmissible`, `Lemma33Stmt` (Lemma 3.3),
`Lemma27Stmt` (Lemma 2.7), `Lemma24Conv`, `Lemma24Confine` (Lemma 2.4).

Constants (MA2 D-B1, correcting m4): `A ≥ 1` from Lemma 3.3, `θ = A/(A+1)`; `C₀ ≥ 2`, `β₀ > 0` from
Lemma 2.7 at `q = 1/2`; for `δ ∈ (0,1)`: `t = δ/4`, `η = (1−θ)δ/30`, `m₋ = 1 − t`, `m₊ = (1 − t)⁻¹`, `N ≥ 1`
with `θ^N C₀ < δ/16`, windows `u_i = (3/8)^i`, `v_i = u_i/2`; `q_δ = v_{3N}`, `β_δ = min(β₀, u_{3N})`, both
independent of `R` (the order of the quantifiers of `Core.Prop51Stmt`).

Step 4 (MA2 §2.16, D-B5): for small `ε` (Steps 2–3: fewer than `N` low and fewer than `N` high windows,
`p51_low_eventually`, `p51_high_eventually`) at least `N` of the windows `1, …, 3N` are neither; in each,
more than half of the radii have `1 − t < c_ε(r) < (1 − t)⁻¹` (`Windows.winNeither_middle_majority`).
These deterministic selections, iterated forward (`c ≤ m₊`) and backward (`c⁻¹ ≤ m₊`), give both
comparison properties with constant `≤ θ^N C₀ + m₊(1 + δ/10) < 1 + δ` off the failure event of the
selection, whose outer probability is `≤ K_R ε^{β_δ}` by the uniform union bound (5.6) (`p51_failure`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.SharpComp

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open HigherDimLFPPAS.Windows

open Classical in
/-- **Proposition 5.1** (MA2 m3: outer-measure form; m4: explicit constants): for every
`δ ∈ (0,1)` there are `q_δ ∈ (0,1)` and `β_δ > 0`, independent of `R`, such that for every `R ≥ 2`
both sharp comparison properties `𝒞^{D→M}_{ε,R}(1+δ, q_δ)` and `𝒞^{M→D}_{ε,R}(1+δ, q_δ)` hold except on
an event of outer probability `≤ K_R ε^{β_δ}`, for all small `ε`. -/
theorem prop51_holds {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h41 : Core.Prop41Stmt d) (hus : Core.UnitSpeedAdmissible d)
    (h33 : Core.Lemma33Stmt κ ξ Q D P h) (h27 : Core.Lemma27Stmt κ ξ D P h)
    (h24c : Core.Lemma24Conv κ ξ D P h) (h24f : Core.Lemma24Confine κ ξ P h) :
    Core.Prop51Stmt κ ξ D P h := by
  intro δ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨A, hA, h33'⟩ := p51_h33 h33
  obtain ⟨C₀, β₀, hC₀, hβ₀, h27'⟩ := p51_h27 h27
  have hθ0 : 0 < A / (A + 1) := div_pos (by linarith) (by linarith)
  have hθ1 : A / (A + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  obtain ⟨N, -, hN, -⟩ := winIterations_exists (C₀ := C₀) hδ0 hθ0 hθ1
  refine ⟨winV (3 * N), min β₀ (winU (3 * N)), p51_winV_pos _, p51_winV_lt_one _,
    lt_min hβ₀ (winU_pos _), ?_⟩
  intro R hR
  have hη : 0 < winEta δ (A / (A + 1)) := winEta_pos hδ0 hθ1
  obtain ⟨K, hK⟩ := p51_failure h33' h27' hη (3 * N) (R := R) (by linarith)
  have hlow := p51_low_eventually hS h41 hus h24c hA hC₀ hβ₀ h33' h27' hδ0 hδ1 hN
  have hhigh := p51_high_eventually hS h41 hus h24c h24f hA hC₀ hβ₀ h33' h27' hδ0 hδ1 hN
  have hP41 := p51_P41_eventually (by linarith [hS.dim] : 1 ≤ d) h41 hA hη (3 * N)
  obtain ⟨ε₀, hε₀, hall⟩ := p51_Ioo_of_eventually
    (hK.and (hlow.and (hhigh.and (hP41.and (Ioo_mem_nhdsGT one_pos)))))
  refine ⟨K, ε₀, hε₀, fun ε hε => ?_⟩
  obtain ⟨hKε, hlowε, hhighε, hP41ε, hε01⟩ := hall ε hε
  have hε0 : 0 < ε := hε01.1
  have hε1 : ε < 1 := hε01.2
  -- Step 4: the middle windows and their middle radii (deterministic selections)
  let S : Finset ℕ := (Finset.Icc 1 (3 * N)).filter
    (fun i => ¬ winIsLow (p51W ε i) (Core.cRatio κ ξ Q ε) (winMMinus δ) ∧
      ¬ winIsHigh (p51W ε i) (Core.cRatio κ ξ Q ε) (winMPlus δ))
  let Rs : ℕ → Finset ℝ := fun b =>
    winMiddleRadii (p51W ε b) (Core.cRatio κ ξ Q ε) (winMMinus δ) (winMPlus δ)
  have hcard : (Finset.Icc 1 (3 * N)).card = 3 * N := by simp
  have hScard : N ≤ S.card := winNeither_card (Finset.Icc 1 (3 * N)) N _ _ hcard hlowε hhighε
  have hSmem : ∀ b ∈ S, (1 ≤ b ∧ b ≤ 3 * N) ∧
      ¬ winIsLow (p51W ε b) (Core.cRatio κ ξ Q ε) (winMMinus δ) ∧
      ¬ winIsHigh (p51W ε b) (Core.cRatio κ ξ Q ε) (winMPlus δ) := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    exact hb
  have hRsmem : ∀ b r, r ∈ Rs b → r ∈ p51W ε b ∧ winMMinus δ < Core.cRatio κ ξ Q ε r ∧
      Core.cRatio κ ξ Q ε r < winMPlus δ := fun b r hr => Finset.mem_filter.1 hr
  have hmlt := p51_winMMinus_lt_winMPlus hδ0 hδ1
  have hm0 := p51_winMMinus_pos hδ1
  have hbad : P (p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ R ε S Rs) ≤
      ENNReal.ofReal (K * ε ^ min β₀ (winU (3 * N))) := by
    refine hKε S Rs ?_
    intro b hb
    obtain ⟨hbI, hlo, hhi⟩ := hSmem b hb
    refine ⟨hbI.2, fun r hr => p51_mem_W hε0 hε1 (hRsmem b r hr).1, ?_⟩
    rw [p51_ncard_W hε0 hε1]
    have hmaj := winNeither_middle_majority (p51W ε b) (Core.cRatio κ ξ Q ε) hmlt hlo hhi
    show (p51W ε b).card ≤
      4 * (winMiddleRadii (p51W ε b) (Core.cRatio κ ξ Q ε) (winMMinus δ) (winMPlus δ)).card
    omega
  refine (measure_mono ?_).trans hbad
  intro ω hω
  by_contra hb
  apply hω
  obtain ⟨hinit, hcov⟩ := p51_not_bad hb
  have hmp := winMPlus_pos hδ0 hδ1
  have hmpC : winMPlus δ ≤ C₀ := (winMPlus_lt_four_thirds hδ1).le.trans (by linarith)
  have hiter : winIter (A / (A + 1)) (winEta δ (A / (A + 1))) (winMPlus δ) C₀ S.card ≤ 1 + δ :=
    (p51_winIter_le_of_ge hθ0 hθ1 (by linarith) hmp.le hδ0.le hScard).trans
      (p51_lambda_plus_lt hδ0 hδ1 hθ1 hN).le
  constructor
  · have hc := p51_good_forward hA hη hR hε0 hε1.le hmp.le hmpC hP41ε S
      (fun b hb => (hSmem b hb).1) Rs
      (fun b _ r hr => ⟨p51_mem_W hε0 hε1 (hRsmem b r hr).1,
        lt_trans hm0 (hRsmem b r hr).2.1, (hRsmem b r hr).2.2.le⟩) hinit hcov
    exact p51_comp_mono_C hiter hc
  · have hc := p51_good_reverse hA hη hR hε0 hε1.le hmp.le hmpC hP41ε S
      (fun b hb => (hSmem b hb).1) Rs
      (fun b _ r hr => ⟨p51_mem_W hε0 hε1 (hRsmem b r hr).1,
        lt_trans hm0 (hRsmem b r hr).2.1, inv_anti₀ hm0 (hRsmem b r hr).2.1.le⟩) hinit hcov
    exact p51_comp_mono_C hiter hc

end HigherDimLFPPAS.SharpComp
