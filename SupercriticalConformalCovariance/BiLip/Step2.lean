import SupercriticalConformalCovariance.BiLip.Lemma21

/-!
# Lemma 2.1, step 2: the compactness argument over the normalized family

Paper l. 108–111 and 126–127: "We next justify the same marginal tightness for the pulled-back metric without
assuming the desired conformal covariance. Suppose otherwise. Then there are domains `U_n`, conformal maps `φ_n`,
points `z_n ∈ U_n`, and radii `r_n` with `r_n / dist(z_n, ∂U_n) → 0` along which the normalized estimate fails.
[…] This contradicts the assumed failure and proves uniform marginal tightness. Importantly, the compactness
argument is over the normalized family of univalent maps, so the resulting bounds depend only on `ξ`."

* `TargetTightSeq ξ Q D`: the sequential statement which l. 112–125 prove (Koebe, GM Lemma 2.4, affine
  covariance, Weyl scaling, circle average versus smooth normalization): along EVERY sequence of instances,
  centres `z_n` and radii `r_n` with `B_{s_n}(z_n) ⊆ U_n` and `r_n / s_n → 0`, the normalized target tails are
  eventually uniformly small. (`s_n` replaces `dist(z_n, ∂U_n)`: any disk in `U_n` will do, and the
  formulation needs no convention for `U_n = ℂ`.)
* `targetTightUniform_of_seq`: the contradiction argument, `TargetTightSeq → TargetTightUniform`.
* `lemma21_of_seq_inputs`: Lemma 2.1 from `TargetTightSeq` and `GoodEventsLocal`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails (nrm)
open SupercriticalConformalCovariance (IsConformalBijection domainMetric)
open LQGMetric (DistC)

theorem TargetTailsLE.mono {ξ : Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric} {V : Opens ℂ}
    {φ : ℂ → ℂ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h g₀ : Ω → DistC}
    {k : Ω → C(V, ℝ)} {M M' δ : ℝ} {z : ℂ} {r : ℝ} (hM : 0 < M) (hMM : M ≤ M')
    (hT : TargetTailsLE ξ Q D φ P h g₀ k M δ z r) :
    TargetTailsLE ξ Q D φ P h g₀ k M' δ z r :=
  tails_mono P _ _ _ hM hMM hT.1 hT.2

/-- **Step 2, sequential form** (what l. 112–125 prove). -/
def TargetTightSeq (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
  ∀ (U V : ℕ → Opens ℂ) (φ : ℕ → ℂ → ℂ) (hφ : ∀ n, IsConformalBijection (φ n) (U n) (V n))
    (Ω : ℕ → Type) (mΩ : ∀ n, MeasurableSpace (Ω n)) (P : ∀ n, @Measure (Ω n) (mΩ n))
    (_ : ∀ n, @IsProbabilityMeasure (Ω n) (mΩ n) (P n))
    (h g₀ : ∀ n, Ω n → DistC) (k : ∀ n, Ω n → C(V n, ℝ)),
    (∀ n, @IsInstance Q (U n) (V n) (φ n) (hφ n) (Ω n) (mΩ n) (P n) (h n) (g₀ n) (k n)) →
    ∀ (z : ℕ → ℂ) (r s : ℕ → ℝ), (∀ n, 0 < r n) → (∀ n, 0 < s n) →
      (∀ n, ball (z n) (s n) ⊆ U n) → Tendsto (fun n => r n / s n) atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop,
        @TargetTailsLE ξ Q D (V n) (φ n) (Ω n) (mΩ n) (P n) (h n) (g₀ n) (k n) M δ (z n) (r n)

/-- **The compactness argument** (l. 108–111, 126–127): the sequential statement implies the uniform one,
with `M` chosen before `(U, φ)`. -/
theorem targetTightUniform_of_seq {ξ : Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hseq : TargetTightSeq ξ Q D) : TargetTightUniform ξ Q D := by
  intro δ hδ
  by_contra hcon
  -- at each level `M = n + 1` an instance, a compact set and arbitrarily small failing radii
  have hfail : ∀ n : ℕ, ∃ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
      (_ : @IsProbabilityMeasure Ω mΩ P) (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)),
      @IsInstance Q U V φ hφ Ω mΩ P h g₀ k ∧ ∃ z : ℂ, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
        ball z s ⊆ U ∧ r ≤ s / (n + 1) ∧
        ¬ @TargetTailsLE ξ Q D V φ Ω mΩ P h g₀ k (n + 1) δ z r := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨n + 1, by positivity, ?_⟩
    intro U V φ hφ Ω mΩ P hP h g₀ k hI L hL hLU
    obtain ⟨ρ, hρ, hρU⟩ := hL.exists_cthickening_subset_open U.isOpen hLU
    refine ⟨ρ / (n + 1), by positivity, fun z hz r hr => ?_⟩
    by_contra hT
    exact hn ⟨U, V, φ, hφ, Ω, mΩ, P, hP, h, g₀, k, hI, z, r, ρ, hr.1, hρ,
      (ball_subset_thickening hz ρ).trans ((thickening_subset_cthickening ρ L).trans hρU),
      hr.2, hT⟩
  choose U V φ hφ Ω mΩ P hP h g₀ k hI z r s hr hs hball hrs hnot using hfail
  have hlim : Tendsto (fun n => r n / s n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (div_pos (hr n) (hs n)).le) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [div_le_iff₀ (hs n)]
    calc r n ≤ s n / (n + 1) := hrs n
      _ = 1 / ((n : ℝ) + 1) * s n := by ring
  obtain ⟨M, hM, hev⟩ := hseq U V φ hφ Ω mΩ P hP h g₀ k hI z r s hr hs hball hlim δ hδ
  obtain ⟨n, hgood, hn⟩ := (hev.and (eventually_ge_atTop ⌈M⌉₊)).exists
  apply hnot n
  exact hgood.mono hM (le_trans (Nat.le_ceil M) (by exact_mod_cast hn.trans (Nat.le_succ n)))

/-- **Lemma 2.1** from the sequential step-2 input and the event locality. -/
theorem lemma21_of_seq_inputs (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (hT : TargetTightSeq ξ Q D) (hloc : GoodEventsLocal ξ Q D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
        ∀ᵐ ω ∂P, ∀ u v : U,
          ENNReal.ofReal C⁻¹ * (D (h ω)).internal U (u, v) ≤
              domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
                (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
            domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
                (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
              ENNReal.ofReal C * (D (h ω)).internal U (u, v) :=
  lemma21_of_inputs ξ Q hQ D hD (targetTightUniform_of_seq hT) hloc

end SupercriticalConformalCovariance.BiLip
