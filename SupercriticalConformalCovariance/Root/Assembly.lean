import SupercriticalConformalCovariance.Root.General
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalConformalCovariance.Frozen.IsGreenian
import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric

/-!
# Theorem 1.1 (paper l. 22–28), end-to-end assembly in the candidate's exact form

`conformal_covariance_of_inputs` proves the revision-2.1 root R-A
(`SupercriticalConformalCovariance.conformal_covariance`, in its working copy
`SupercriticalConformalCovariance.Root.Cand.ConformalCovariance` with only its imports redirected) from exactly five
in-progress inputs:

| hypothesis | input | proved in |
| --- | --- | --- |
| `hTight` | `SupercriticalConformalCovariance.BiLip.TargetTightUniform` (Lemma 2.1 step 2; consumes Lemma 3.3) | the Lemma 2.1 proof / the Lemma 3.3 proof |
| `hGEL` | `SupercriticalConformalCovariance.BiLip.GoodEventsLocal` (Lemma 2.1 step 4, transported locality) | the Lemma 2.1 proof / the target-locality lemmas |
| `hP43` | `SupercriticalConformalCovariance.Root.Prop43Input` (Proposition 4.3) | the Proposition 4.3 proof |
| `hL51` | `SupercriticalConformalCovariance.Root.Lemma51LocalInput` (Lemma 5.1, locality of `F_{z,r}`) | the Lemma 5.1 proof |
| `hGPull` | `SupercriticalConformalCovariance.Root.GPullInput` (existence conjunct, G-PULL, Greenian) | the existence proof / the Markov decomposition |

The proof (paper l. 540–552):
1. `forward_general` (Lemma 7.1 on top of Proposition 6.1, Lemma 2.1 and the good covers) applied
   on `U` to the field `g = h ∘ φ + Q log |φ′|` and `φ`, whose forward pullback is
   `g^φ = h` (`SupercriticalConformalCovariance.Reversal.confPullbackField_inverse`, the reversal lemma's corrected order of the chain rule),
   gives `e ≤ d`: `D_h(φ u, φ v; V) ≤ D_g(u, v; U)`;
2. `forward_general` applied on `V` to `h` and `φ⁻¹` (target field `h^{φ⁻¹}`, which is literally `g`)
   gives `d ≤ e`, at the points `φ u, φ v`;
3. antisymmetry, simultaneously for all pairs, on every extension and for every realization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Root

open LQGMetric (DistC DistOn)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization
  domainMetric IsGreenian xiCrit)

/-- **G-PULL** (the existence conjunct of the root; ruling A14), in the exact shape of the existence proof's
in-progress `SupercriticalConformalCovariance.GPull.exists_confPullback_domainRealization_greenian` (`SupercriticalConformalCovariance/GPull/Existence.lean:14`),
with the candidate's `IsGreenian`: after a measure-preserving extension, `h ∘ φ + Q log |φ′|` has a
realization on `U`. -/
def GPullInput : Prop :=
  ∀ (U V : Opens ℂ), IsGreenian U → IsGreenian V →
    ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Q : ℝ) (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
      IsDomainRealization V P h h₀ f →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
          (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
        MeasurePreserving π P' P ∧
        IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k

/-- **Theorem 1.1, assembled.** The statement after the colon is, verbatim, the type of the
revision-2.1 candidate `conformal_covariance` (checked below by `conformal_covariance_closed`). -/
theorem conformal_covariance_of_inputs
    (hTight : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D)
    (hGEL : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.GoodEventsLocal ξ Q D)
    (hP43 : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → Prop43Input ξ Q D)
    (hL51 : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → Lemma51LocalInput ξ Q D)
    (hGPull : GPullInput) :
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ U V : Opens ℂ, IsConnected (U : Set ℂ) → IsConnected (V : Set ℂ) →
      IsGreenian U → IsGreenian V →
      ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f →
        (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
            (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)), MeasurePreserving π P' P ∧
          IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k) ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω), MeasurePreserving π P' P →
          ∀ (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
            IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k →
            ∀ᵐ ω' ∂P', ∀ u v : U,
              domainMetric (ξ : ℝ) D V (h₀ (π ω')) (f (π ω'))
                  (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) =
                domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') (u, v) := by
  intro ξ hξ Q hQ D hD U V _ _ hGU hGV φ hφ Ω _ P _ h h₀ f hR
  have hT := hTight ξ hξ Q hQ D hD
  have hloc := hGEL ξ hξ Q hQ D hD
  have h43 := hP43 ξ hξ Q hQ D hD
  have h51 := hL51 ξ hξ Q hQ D hD
  refine ⟨?_, ?_⟩
  · -- the existence conjunct
    exact hGPull U V hGU hGV φ hφ P Q h h₀ f hR
  · intro Ω' _ P' π hπ g₀ k hRk
    have : IsProbabilityMeasure P' := isProbabilityMeasure_of_measurePreserving hπ
    have hRπ : IsDomainRealization V P' (h ∘ π) (h₀ ∘ π) (f ∘ π) :=
      isDomainRealization_comp hπ hR
    have hψ := SupercriticalConformalCovariance.Reversal.inverse_conformal hφ
    have hψφ : ∀ x ∈ (U : Set ℂ), invFunOn φ U (φ x) = x := fun _ hx =>
      hφ.2.injOn.leftInvOn_invFunOn hx
    have hφψ : ∀ y ∈ (V : Set ℂ), φ (invFunOn φ U y) = y := fun _ hy =>
      hφ.2.surjOn.rightInvOn_invFunOn hy
    -- (1) `e ≤ d`: the forward inequality on `U` for `g = h ∘ φ + Q log |φ′|`, with `g^φ = h`
    have hRt : IsDomainRealization V P'
        (fun ω' => confPullbackField Q hψ (confPullbackField Q hφ (h (π ω')))) (h₀ ∘ π) (f ∘ π) := by
      have he : (fun ω' => confPullbackField Q hψ (confPullbackField Q hφ (h (π ω')))) = h ∘ π := by
        funext ω'
        exact SupercriticalConformalCovariance.Reversal.confPullbackField_inverse Q hφ (h (π ω'))
      rw [he]
      exact hRπ
    have h1 := forward_general ξ Q hQ D hD hT hloc h43 h51 U V φ (invFunOn φ U) hφ hψ hψφ P'
      (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k (h₀ ∘ π) (f ∘ π) hRk hRt
    -- (2) `d ≤ e`: the forward inequality on `V` for `h` and `φ⁻¹`, whose pullback is `g`
    have h2 := forward_general ξ Q hQ D hD hT hloc h43 h51 V U (invFunOn φ U) φ hψ hφ hφψ P'
      (h ∘ π) (h₀ ∘ π) (f ∘ π) g₀ k hRπ hRk
    filter_upwards [h1, h2] with ω' h1 h2 u v
    refine le_antisymm (h1 u v) ?_
    have h3 := h2 ⟨φ u, hφ.2.mapsTo u.2⟩ ⟨φ v, hφ.2.mapsTo v.2⟩
    have hu : (⟨invFunOn φ U (φ u), hψ.2.mapsTo (hφ.2.mapsTo u.2)⟩ : U) = u :=
      Subtype.ext (hψφ _ u.2)
    have hv : (⟨invFunOn φ U (φ v), hψ.2.mapsTo (hφ.2.mapsTo v.2)⟩ : U) = v :=
      Subtype.ext (hψφ _ v.2)
    simp only [hu, hv] at h3
    exact h3

/-- **The interface check**: the candidate root's type is exactly closed by the assembly. When the five
inputs are proved, the frozen body is `by exact conformal_covariance_of_inputs …`. -/
theorem conformal_covariance_closed
    (hTight : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D)
    (hGEL : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.GoodEventsLocal ξ Q D)
    (hP43 : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → Prop43Input ξ Q D)
    (hL51 : ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → Lemma51LocalInput ξ Q D)
    (hGPull : GPullInput) :
    (open MeasureTheory TopologicalSpace Set in
      open scoped ENNReal in
      open LQGMetric (DistC DistOn) in
      open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric) in
      open SupercriticalConformalCovariance in
      ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
        ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
        ∀ U V : Opens ℂ, IsConnected (U : Set ℂ) → IsConnected (V : Set ℂ) →
        IsGreenian U → IsGreenian V →
        ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V),
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
          IsDomainRealization V P h h₀ f →
          (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
              (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)), MeasurePreserving π P' P ∧
            IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k) ∧
          ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω), MeasurePreserving π P' P →
            ∀ (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
              IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k →
              ∀ᵐ ω' ∂P', ∀ u v : U,
                domainMetric (ξ : ℝ) D V (h₀ (π ω')) (f (π ω'))
                    (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) =
                  domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') (u, v)) := by
  exact conformal_covariance_of_inputs hTight hGEL hP43 hL51 hGPull

end SupercriticalConformalCovariance.Root
