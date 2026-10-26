import SupercriticalLFPPAS.Main.Transfer
import SupercriticalLFPPAS.Inputs.Geodesics
import SupercriticalLFPPAS.Inputs.EuclideanRegularity

/-!
# §7: the probability-one event (packet T7)

Paper §7, l. 627–631; SB2 §2.8 "One event" and D11 "Event" (with M11): for integers `j, R ≥ 1`, Proposition 5.1 with
`u = 1/j` gives `s, β, c₁, ε₁`; along the mesh `δ_k = k^{-a}`, `a = a(j,R) = 2/β`, the failure probabilities
`c₁ δ_k^β = c₁ k^{-2}` are summable, so by Borel–Cantelli (outer measures, `MeasureTheory.ae_eventually_notMem`) both
comparisons (5.1)–(5.2) hold eventually on the mesh. The event `Ω₀` intersects these countably many events with (2.1),
(2.2) for every `a(j,R)`, Lemma 6.2, Pfeffer's geodesics ([4, Prop 1.12], `Inputs.ae_exists_pointGeodesic_of_finite`)
and the Euclidean continuity of finite-length `D`-curves (`Inputs.ae_strongLQGMetric_euclideanRegularity`).

`MainGood` records the deterministic content of `Ω₀` at one sample; `ae_mainGood` shows that it holds almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Main

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-- The deterministic content of the probability-one event `Ω₀` of §7 at one sample, for the field `g = h(ω)` and its
heat versions `Y ε = X ε ω`, with mesh exponents `a j R` and endpoint-radius exponents `s j R`. -/
structure MainGood (S : Core.Setup) (a s : ℕ → ℕ → ℝ) (g : DistC) (Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)) : Prop where
  a_pos : ∀ j R, 0 < a j R
  s_pos : ∀ j R, 0 < s j R
  /-- (5.1)–(5.2) with `u = 1/j`, eventually on the mesh `k^{-a(j,R)}`. -/
  mesh : ∀ j R : ℕ, 1 ≤ j → 1 ≤ R → ∀ᶠ k : ℕ in atTop, ∀ hδ : (k : ℝ) ^ (-a j R) ∈ Ioo (0 : ℝ) 1,
    Core.CompIn (S.D g) (Core.locMetric S _ hδ g) (ball 0 ((R : ℝ) + 2)) R (1 + 1 / (j : ℝ))
        (513 * ((k : ℝ) ^ (-a j R)) ^ s j R) ∧
      Core.CompIn (Core.locMetric S _ hδ g) (S.D g) (ball 0 ((R : ℝ) + 2)) R (1 + 1 / (j : ℝ))
        (513 * ((k : ℝ) ^ (-a j R)) ^ s j R)
  /-- (2.1). -/
  locApprox : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1, ∀ z ∈ K,
      |Y ⟨ε, hε.1⟩ z - SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 ε hε g z| ≤ η
  /-- (2.2) for every mesh exponent `a j R`. -/
  meshOsc : ∀ j R : ℕ, ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    ∀ ε δ : Set.Ioi (0 : ℝ), ((n : ℝ) + 1) ^ (-a j R) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a j R) →
      ((n : ℝ) + 1) ^ (-a j R) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a j R) → ∀ z ∈ K, |Y ε z - Y δ z| ≤ η
  /-- Lemma 6.2. -/
  confine : ∀ K : Set ℂ, IsCompact K → ∀ M : ℝ, ∃ R : ℝ, K ⊆ ball 0 R ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
      ENNReal.ofReal M < setDist (Core.locMetric S ε hε g) K (sphere 0 R) ∧
      ENNReal.ofReal M < setDist (Core.lfppM S ⟨ε, hε.1⟩ (Y ⟨ε, hε.1⟩)) K (sphere 0 R)
  /-- Pfeffer's geodesics between points at finite distance. -/
  geod : ∀ u v : ℂ, S.D g (u, v) < ⊤ → ∃ γ : ℝ → ℂ, ∃ T : ℝ,
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.SetGeodesic (S.D g) {u} {v} γ T
  /-- Finite-length `D`-curves are Euclidean continuous. -/
  eucl : SupercriticalLQGUniqueness.B2.PfeAxioms.FinitePathsEuclideanContinuous (S.D g)

/-- **Borel–Cantelli on the mesh** (SB2 §2.8, D11): for `u > 0`, `R ≥ 1` there are `a, s > 0` such that, almost
surely, eventually in `k`, both internal comparisons of Proposition 5.1 hold at the mesh point `k^{-a}`. -/
theorem ae_mesh (S : Core.Setup) (h51 : Core.Prop51Stmt S) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (u R : ℝ) (hu : 0 < u)
    (hR : 1 ≤ R) :
    ∃ a s : ℝ, 0 < a ∧ 0 < s ∧ ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ hδ : (k : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1,
      Core.CompIn (S.D (h ω)) (Core.locMetric S _ hδ (h ω)) (ball 0 (R + 2)) R (1 + u)
          (513 * ((k : ℝ) ^ (-a)) ^ s) ∧
        Core.CompIn (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R (1 + u)
          (513 * ((k : ℝ) ^ (-a)) ^ s) := by
  obtain ⟨s, β, c₁, ε₁, hs, hβ, hc₁, hε₁, hP⟩ := h51 u R hu hR
  have ha : 0 < 2 / β := by positivity
  refine ⟨2 / β, s, ha, hs, ?_⟩
  set a := 2 / β with ha_def
  -- the failure events on the mesh (empty outside the range of Proposition 5.1)
  set Bad : ℕ → Set Ω := fun k => {ω | ∃ hδ : (k : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1, (k : ℝ) ^ (-a) < ε₁ ∧
    ¬ (Core.CompIn (S.D (h ω)) (Core.locMetric S _ hδ (h ω)) (ball 0 (R + 2)) R (1 + u)
          (513 * ((k : ℝ) ^ (-a)) ^ s) ∧
        Core.CompIn (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R (1 + u)
          (513 * ((k : ℝ) ^ (-a)) ^ s))} with hBad
  have hbound : ∀ k : ℕ, P (Bad k) ≤ ENNReal.ofReal (c₁ * (k : ℝ) ^ (-2 : ℝ)) := by
    intro k
    by_cases hk : ∃ hδ : (k : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1, (k : ℝ) ^ (-a) < ε₁
    · obtain ⟨hδ, hδ₁⟩ := hk
      have hsub : Bad k ⊆ {ω | ¬ (Core.CompIn (S.D (h ω)) (Core.locMetric S _ hδ (h ω)) (ball 0 (R + 2)) R
            (1 + u) (513 * ((k : ℝ) ^ (-a)) ^ s) ∧
          Core.CompIn (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R (1 + u)
            (513 * ((k : ℝ) ^ (-a)) ^ s))} := fun ω hω => by
        obtain ⟨_, _, hω⟩ := hω
        exact hω
      have hpow : ((k : ℝ) ^ (-a)) ^ β = (k : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg k)]
        congr 1
        rw [ha_def]
        field_simp
      calc P (Bad k) ≤ _ := measure_mono hsub
        _ ≤ ENNReal.ofReal (c₁ * ((k : ℝ) ^ (-a)) ^ β) := hP P h hh _ hδ hδ₁
        _ = ENNReal.ofReal (c₁ * (k : ℝ) ^ (-2 : ℝ)) := by rw [hpow]
    · have hempty : Bad k = ∅ := by
        ext ω
        simp only [hBad, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hδ, hδ₁, -⟩
        exact hk ⟨hδ, hδ₁⟩
      rw [hempty, measure_empty]
      exact zero_le
  have hsumm : Summable fun k : ℕ => c₁ * (k : ℝ) ^ (-2 : ℝ) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left c₁
  have hsum : ∑' k, P (Bad k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc₁.le (Real.rpow_nonneg (Nat.cast_nonneg k) _))
      hsumm]
    exact ENNReal.ofReal_ne_top
  have hsmall : ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ (-a) < ε₁ :=
    ((tendsto_mesh_pow ha).mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hε₁)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω, hsmall] with k hk hkε hδ
  by_contra hcon
  exact hk ⟨hδ, hkε, hcon⟩

/-- **The probability-one event `Ω₀`** (SB2 D11): there are mesh exponents `a j R` and radius exponents `s j R` such
that `MainGood` holds almost surely. -/
theorem ae_mainGood (S : Core.Setup) (h51 : Core.Prop51Stmt S) (h62 : Core.Lemma62Stmt S) (hM : Core.MeshOscStmt)
    (hA : Core.LocApproxStmt) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : Core.IsJointHeatVersion P h X) :
    ∃ a s : ℕ → ℕ → ℝ, ∀ᵐ ω ∂P, MainGood S a s (h ω) (fun ε => X ε ω) := by
  have key : ∀ j R : ℕ, ∃ a s : ℝ, 0 < a ∧ 0 < s ∧ (1 ≤ j → 1 ≤ R → ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ hδ : (k : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1,
        Core.CompIn (S.D (h ω)) (Core.locMetric S _ hδ (h ω)) (ball 0 ((R : ℝ) + 2)) R (1 + 1 / (j : ℝ))
            (513 * ((k : ℝ) ^ (-a)) ^ s) ∧
          Core.CompIn (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (ball 0 ((R : ℝ) + 2)) R (1 + 1 / (j : ℝ))
            (513 * ((k : ℝ) ^ (-a)) ^ s)) := by
    intro j R
    by_cases hjR : 1 ≤ j ∧ 1 ≤ R
    · have hj : (0 : ℝ) < 1 / (j : ℝ) := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast hjR.1
        positivity
      obtain ⟨a, s, ha, hs, hae⟩ := ae_mesh S h51 P h hh (1 / (j : ℝ)) R hj (by exact_mod_cast hjR.2)
      exact ⟨a, s, ha, hs, fun _ _ => hae⟩
    · exact ⟨1, 1, one_pos, one_pos, fun hj hR => absurd ⟨hj, hR⟩ hjR⟩
  choose a s ha hs hmesh using key
  refine ⟨a, s, ?_⟩
  have hmesh' : ∀ᵐ ω ∂P, ∀ j R : ℕ, 1 ≤ j → 1 ≤ R → ∀ᶠ k : ℕ in atTop,
      ∀ hδ : (k : ℝ) ^ (-a j R) ∈ Ioo (0 : ℝ) 1,
        Core.CompIn (S.D (h ω)) (Core.locMetric S _ hδ (h ω)) (ball 0 ((R : ℝ) + 2)) R (1 + 1 / (j : ℝ))
            (513 * ((k : ℝ) ^ (-a j R)) ^ s j R) ∧
          Core.CompIn (Core.locMetric S _ hδ (h ω)) (S.D (h ω)) (ball 0 ((R : ℝ) + 2)) R (1 + 1 / (j : ℝ))
            (513 * ((k : ℝ) ^ (-a j R)) ^ s j R) := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun R => ?_
    by_cases hjR : 1 ≤ j ∧ 1 ≤ R
    · exact (hmesh j R hjR.1 hjR.2).mono fun ω hω _ _ => hω
    · exact Eventually.of_forall fun ω hj hR => absurd ⟨hj, hR⟩ hjR
  have hosc : ∀ᵐ ω ∂P, ∀ j R : ℕ, ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε δ : Set.Ioi (0 : ℝ), ((n : ℝ) + 1) ^ (-a j R) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a j R) →
        ((n : ℝ) + 1) ^ (-a j R) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a j R) →
          ∀ z ∈ K, |X ε ω z - X δ ω z| ≤ η :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun R => hM P h hh X hX (a j R) (ha j R)
  have hloc := hA P h hh X hX
  have hconf := h62 P h hh X hX
  have hgeod := Inputs.ae_exists_pointGeodesic_of_finite S.hD P h hh
  have heucl := Inputs.ae_strongLQGMetric_euclideanRegularity S.hD P h hh
  filter_upwards [hmesh', hosc, hloc, hconf, hgeod, heucl] with ω hω₁ hω₂ hω₃ hω₄ hω₅ hω₆
  exact
    { a_pos := ha
      s_pos := hs
      mesh := hω₁
      locApprox := hω₃
      meshOsc := hω₂
      confine := hω₄
      geod := hω₅
      eucl := hω₆.2.1 }

end SupercriticalLFPPAS.Main
