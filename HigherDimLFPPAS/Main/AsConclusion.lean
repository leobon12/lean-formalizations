import HigherDimLFPPAS.Main.Pathwise
import HigherDimLFPPAS.Proper.Lemma22

/-!
# Proof of Theorem 1.2 from the interfaces (packet THM)

`asConclusion_of_parts`: the conclusion (1.7) of Theorem 1.2 (`Core.ASConclusion`, verbatim the conclusion of the frozen
anchor `asConvergence`) from the standing hypotheses `Core.Setting`, the deterministic admissibility of unit-speed
geodesics and the interface statements of Proposition 5.1, Lemmas 6.1, 6.2, 2.3 (i), (iii) and (2.10).

Route (MA2 §§2.21–2.25, Details D-E; paper l. 729–771):
1. comparison parameters `δ_j = 1/(j+2) → 0` (any sequence in `(0, 1)` tending to `0` works; the paper's `2^{-j}`
   plays no further role), `q_j, β_j` from Proposition 5.1 at `δ_j`, `C_*, β_*` from Lemma 6.1, and the exponents
   `a_j = 2/β_* + 2/β_j`, so that `a_j β_* > 1` and `a_j β_j > 1`;
2. Borel–Cantelli along `ε_n = n^{-a_j}` for Proposition 5.1 at every integer `R ≥ 2` (`thm_ae_eventually_of_rate`),
   Lemma 6.1 and Lemma 2.3 (iii) at `a_j`, for every `j` (countable intersections, `ae_all_iff`);
3. the events of Lemma 6.2, Lemma 2.3 (i), Lemma 2.2 (properness and escape of `D`, D2's
   `lemma22_ae_proper_and_geodesic`), the length property of `D` (axiom (I)) and the joint continuity of `h*_ε`;
4. on the intersection, the pathwise argument `thm_pathwise`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Main

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Theorem 1.2 from the interfaces** (MA2 D-E): under the standing hypotheses and the interface statements of
Proposition 5.1, Lemmas 6.1, 6.2, 2.3 (i), (iii) and (2.10), almost surely, for every compact `F`,
`sup_{F × F} |𝔞_ε⁻¹ D^ε_h − D_h| → 0` as `ε ↓ 0` (the `[0, ∞]`-supremum form of (1.7)). -/
theorem asConclusion_of_parts {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (hus : Core.UnitSpeedAdmissible d)
    (h51 : Core.Prop51Stmt κ ξ D P h) (h61 : Core.Lemma61Stmt κ ξ D P h)
    (h62 : Core.Lemma62Stmt κ ξ P h) (h23i : Core.Lemma23i κ P h) (h23iii : Core.Lemma23iii κ P h)
    (h25 : Core.Lemma25Window κ ξ) : Core.ASConclusion κ ξ D P h := by
  -- the comparison parameters `δ_j = 1/(j+2)`
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  have hδmem : ∀ j, δ j ∈ Ioo (0 : ℝ) 1 := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩
  have hδlim : ∀ θ : ℝ, 0 < θ → ∃ j, δ j ≤ θ := by
    intro θ hθ
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / θ)
    refine ⟨j, (div_le_iff₀ (by positivity)).2 ?_⟩
    have h1 : 1 < (j : ℝ) * θ := by rwa [div_lt_iff₀ hθ] at hj
    nlinarith
  -- Proposition 5.1 at `δ_j` and Lemma 6.1
  choose q β hq _ hβ hKε using fun j => h51 (δ j) (hδmem j)
  obtain ⟨C₆, β₆, -, hβ₆, h61'⟩ := h61
  -- the exponents `a_j = 2/β_* + 2/β_j`
  let a : ℕ → ℝ := fun j => 2 / β₆ + 2 / β j
  have ha : ∀ j, 0 < a j := fun j => by
    have := hβ j
    positivity
  have ha6 : ∀ j, 1 < a j * β₆ := fun j => by
    have h1 : a j * β₆ = 2 + 2 / β j * β₆ := by
      simp only [a, add_mul, div_mul_cancel₀ _ hβ₆.ne']
    have h2 : 0 < 2 / β j * β₆ := by
      have := hβ j
      positivity
    linarith
  have ha5 : ∀ j, 1 < a j * β j := fun j => by
    have h1 : a j * β j = 2 / β₆ * β j + 2 := by
      simp only [a, add_mul, div_mul_cancel₀ _ (hβ j).ne']
    have h2 : 0 < 2 / β₆ * β j := by
      have := hβ j
      positivity
    linarith
  -- Borel–Cantelli for Proposition 5.1 along `ε_n = n^{-a_j}`, for every `j` and every integer `R ≥ 2`
  have hBC : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ R : ℕ, 2 ≤ R → ∀ᶠ n : ℕ in atTop,
      Core.Comp (D (h ω)) (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) (h ω)) R ((n : ℝ) ^ (-a j)) (q j)
          (1 + δ j) ∧
        Core.Comp (Core.Meps κ ξ ((n : ℝ) ^ (-a j)) (h ω)) (D (h ω)) R ((n : ℝ) ^ (-a j)) (q j)
          (1 + δ j) := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun R => ?_
    by_cases hR : 2 ≤ R
    · obtain ⟨K, ε₀, hε₀, hbound⟩ := hKε j (R : ℝ) (by exact_mod_cast hR)
      filter_upwards [thm_ae_eventually_of_rate (ha j) (ha5 j) hε₀ hbound] with ω hω _
      filter_upwards [hω] with n hn
      simpa only [Set.mem_ofPred_eq, not_not] using hn
    · exact Eventually.of_forall fun ω hR' => absurd hR' hR
  -- Lemma 6.1 and Lemma 2.3 (iii) at every `a_j`
  have h61ae := ae_all_iff.2 fun j => h61' (a j) (ha6 j)
  have h23ae := ae_all_iff.2 fun j => h23iii (a j) (ha j)
  -- Lemma 2.2, axiom (I) and the joint continuity of `h*_ε`
  have hD2 := lemma22_ae_proper_and_geodesic hS.dim hS.xi_pos hS.subcrit P h hS.field D hS.strong
  have hlen := hS.strong.length P h hS.field.1.isLGFPlusCont
  have hjc := hS.seed.jointCont P h hS.field
  have hloc : ∀ g : DistRd d, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Continuous (locField κ ε g) := fun g =>
    hS.seed.locHyp.mono fun ε hε => continuous_locField hS.seed.kernelSmooth hε.2.2.1 g
  filter_upwards [hBC, h61ae, h23ae, h62, h23i, hD2, hlen, hjc]
    with ω hBCω h61ω h23ω h62ω h23iω hD2ω hlenω hjcω
  have : ProperSpace (D (h ω)).Space := hD2ω.1
  have hconv : ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε (h ω)) := fun ε hε =>
    (hjcω.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hε, mem_univ x⟩).congr
      fun _ => rfl
  exact thm_pathwise hus hS.xi_pos (fun ε hε => hS.seed.aEps_pos ξ ε hε) h25 (hloc (h ω)) hconv
    hlenω hD2ω.2.1 ha hq (fun j => (hδmem j).1.le) hδlim hBCω (fun j R hR => (h61ω j R hR).2)
    h23ω h62ω h23iω

end HigherDimLFPPAS.Main
