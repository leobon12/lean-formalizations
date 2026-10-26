import SupercriticalConformalCovariance.Root.LocalDischarge
import SupercriticalConformalCovariance.P43Final.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Function TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Root
open LQGMetric (DistC DistOn)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization domainMetric IsGreenian)

/-- The assembly of `conformal_covariance_of_inputs` without the hypothesis `xiCrit < ξ`: none of its inputs
uses that hypothesis, so the same argument gives Theorem 1.1 for every `ξ > 0`. -/
theorem conformal_covariance_of_inputs_all_xi
    (hTight : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D)
    (hGEL : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.BiLip.GoodEventsLocal ξ Q D)
    (hP43 : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → Prop43Input ξ Q D)
    (hL51 : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D → Lemma51LocalInput ξ Q D)
    (hGPull : GPullInput) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
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
  intro ξ Q hQ D hD U V _ _ hGU hGV φ hφ Ω _ P _ h h₀ f hR
  have hT := hTight ξ Q hQ D hD
  have hloc := hGEL ξ Q hQ D hD
  have h43 := hP43 ξ Q hQ D hD
  have h51 := hL51 ξ Q hQ D hD
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

end SupercriticalConformalCovariance.Root

open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn)
namespace SupercriticalConformalCovariance.Root
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization domainMetric IsGreenian)

/-- **Theorem 1.1 for every `ξ > 0`.** The statement of the frozen `SupercriticalConformalCovariance.conformal_covariance`
with the hypothesis `xiCrit < ξ` removed. The proof of Theorem 1.1 never uses that hypothesis: the four proved
inputs (target tightness, local good events, Proposition 4.3, Lemma 5.1 locality) and the pullback existence hold
for every `ξ > 0`. -/
theorem conformal_covariance_all_xi :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
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
  exact SupercriticalConformalCovariance.Root.conformal_covariance_of_inputs_all_xi
    (fun ξ Q hQ D hD => SupercriticalConformalCovariance.BiLip.targetTightUniform_of_seq
      (SupercriticalConformalCovariance.BiLip.targetTightSeq_proved hQ hD))
    (fun ξ Q _ D hD => SupercriticalConformalCovariance.BiLip.goodEventsLocal_proved hD)
    (fun ξ Q hQ D hD => SupercriticalConformalCovariance.P43Final.prop43Input_proved ξ Q hQ D hD)
    (fun ξ Q _ D hD => SupercriticalConformalCovariance.BiLip.L51.lemma51LocalInput_proved hD)
    SupercriticalConformalCovariance.Root.gPullInput_proved

end SupercriticalConformalCovariance.Root
