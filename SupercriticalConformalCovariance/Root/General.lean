import SupercriticalConformalCovariance.Root.Forward
import SupercriticalConformalCovariance.Root.Transfer
import SupercriticalConformalCovariance.Root.Field

/-!
# Theorem 1.1, step 2: Lemma 7.1 in realization form

Paper l. 518–538. For a source field `s` on `U` realized as `a₀|_U + a` and a realization
`b₀|_V + b` of its conformal pullback `s^φ = s ∘ ψ + Q log |ψ′|` (`ψ = φ⁻¹`), almost surely
`D_{s^φ}(φ u, φ v; V) ≤ D_s(u, v; U)` for all `u, v ∈ U` (`forward_general`).

Route (no disk cover is needed, since realizations are global): decompose `a₀ = h̃ + F` with `h̃` a
normalized whole-plane GFF (sealed `exists_normalized_decomposition`); then `(h̃, G)`, `G = F|_U + a`,
realizes `s` (`restrictTo_addFun`), and `(b₀, b − G ∘ ψ)` realizes `(h̃|_U)^φ` (`confPullbackField_add`,
`precomp_ofFun_extZ`: "the same correction is composed with the inverse map"). Step 1
(`forward_wholePlane`) gives `e₀ ≤ d₀` for the uncorrected metrics; domain Weyl scaling
(`weylScaleOn_add_eq_weylDistOnWith`) writes both corrected metrics as Weyl scalings of `e₀`, `d₀`
by weights that agree under `φ` ("corresponding path weights agree exactly"), and
`weylDistOnWith_transfer` transfers the inequality pathwise. Realization independence
(`ae_domainMetric_eq_of_isDomainRealization`) returns to the given realization `(a₀, a)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Root

open LQGMetric (DistC DistOn restrictTo)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization
  domainMetric)
open SupercriticalConformalCovariance.Domain (SV wV dV wV_of_mem wV_pos continuousOn_wV isOpen_SV)

theorem ofFun_extZ_zero (V : Opens ℂ) :
    Distribution.ofFun V (Function.extend Subtype.val (⇑(0 : C(V, ℝ))) 0) volume ⊤ = 0 := by
  have : Function.extend Subtype.val (⇑(0 : C(V, ℝ))) (0 : ℂ → ℝ) = 0 := by
    funext z
    by_cases hz : z ∈ (V : Set ℂ)
    · have e := SupercriticalConformalCovariance.Domain.extZ_of_mem (0 : C(V, ℝ)) hz
      unfold SupercriticalConformalCovariance.Domain.extZ at e
      erw [e]
      rfl
    · have e := SupercriticalConformalCovariance.Domain.extZ_of_notMem (0 : C(V, ℝ)) hz
      unfold SupercriticalConformalCovariance.Domain.extZ at e
      erw [e]
      rfl
  rw [this, Distribution.ofFun_zero]

theorem measurable_restrict_add {U : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → C(ℂ, ℝ)} (hF : Measurable F) {a : Ω → C(U, ℝ)} (ha : Measurable a) :
    Measurable fun ω => (F ω).restrict (U : Set ℂ) + a ω := by
  have : LocallyCompactSpace (U : Set ℂ) := U.isOpen.locallyCompactSpace
  rw [ContinuousMap.measurable_iff_eval]
  intro x
  simp only [ContinuousMap.add_apply, ContinuousMap.restrict_apply]
  exact ((ContinuousMap.measurable_eval (x : ℂ)).comp hF).add
    ((ContinuousMap.measurable_eval x).comp ha)

theorem measurable_neg_comp {U V : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → C(U, ℝ)} (hG : Measurable G) (g : C(V, U)) :
    Measurable fun ω => -(G ω).comp g := by
  have : LocallyCompactSpace (V : Set ℂ) := V.isOpen.locallyCompactSpace
  rw [ContinuousMap.measurable_iff_eval]
  intro x
  simp only [ContinuousMap.neg_apply, ContinuousMap.comp_apply]
  exact ((ContinuousMap.measurable_eval (g x)).comp hG).neg

/-- The two conformal inverse presentations induce the same field on `V`. -/
theorem confPullbackField_inverse_choice (Q : ℝ) {U V : Opens ℂ} {φ ψ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (hψ : IsConformalBijection ψ V U)
    (hψφ : ∀ x ∈ (U : Set ℂ), ψ (φ x) = x) (s : DistOn U) :
    confPullbackField Q hψ s =
      confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) s := by
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (ψ y) = y := by
    intro y hy
    have hx : ψ y ∈ (U : Set ℂ) := hψ.2.mapsTo hy
    apply hψ.2.injOn (hφ.2.mapsTo hx) hy
    exact hψφ (ψ y) hx
  have hψeq : EqOn ψ (invFunOn φ U) (V : Set ℂ) := by
    intro y hy
    have hx : ψ y ∈ (U : Set ℂ) := hψ.2.mapsTo hy
    have hleft := hφ.2.injOn.leftInvOn_invFunOn hx
    rw [hφψ y hy] at hleft
    exact hleft.symm
  have hinv : EqOn (invFunOn ψ V) φ (U : Set ℂ) := by
    intro x hx
    have hy : φ x ∈ (V : Set ℂ) := hφ.2.mapsTo hx
    have hleft := hψ.2.injOn.leftInvOn_invFunOn hy
    rw [hψφ x hx] at hleft
    exact hleft
  have htest : ∀ g : LQGMetric.TestOn V,
      SupercriticalConformalCovariance.confPushTest hψ g =
        SupercriticalConformalCovariance.confPushTest
          (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) g := by
    intro g
    ext x
    change SmallGammaGeodesics.CC.confPullFun (invFunOn ψ V) U g x =
      SmallGammaGeodesics.CC.confPullFun (invFunOn (invFunOn φ U) V) U g x
    exact congrFun (SupercriticalConformalCovariance.BiLip.PortRev.confPullFun_congr_on
      (fun x hx => (hinv hx).trans (SupercriticalConformalCovariance.BiLip.PortRev.inverse_inverse_eqOn hφ hx).symm) g) x
  have hshift : Distribution.ofFun V (fun y => Q * Real.log ‖deriv ψ y‖) volume ⊤ =
      Distribution.ofFun V (fun y => Q * Real.log ‖deriv (invFunOn φ U) y‖) volume ⊤ := by
    apply Distribution.ofFun_congr_ae
    exact ae_restrict_of_forall_mem V.isOpen.measurableSet fun y hy => by
      have hd : deriv ψ y = deriv (invFunOn φ U) y :=
        Filter.EventuallyEq.deriv_eq
          (Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hy) hψeq)
      simpa only [hd]
  unfold confPullbackField
  rw [hshift]
  congr 1
  ext g
  exact congrArg s (htest g)

/-- **Lemma 7.1** (paper l. 518–538), realization form: the forward inequality `e ≤ d` for every
source field which is a GFF plus a continuous function on `U`. -/
theorem forward_general (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (hT : SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D) (hloc : SupercriticalConformalCovariance.BiLip.GoodEventsLocal ξ Q D)
    (hP43 : Prop43Input ξ Q D) (hL51 : Lemma51LocalInput ξ Q D) :
    ∀ (U V : Opens ℂ) (φ ψ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      (hψ : IsConformalBijection ψ V U), (∀ x ∈ (U : Set ℂ), ψ (φ x) = x) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (s : Ω → DistOn U) (a₀ : Ω → DistC) (a : Ω → C(U, ℝ)) (b₀ : Ω → DistC)
        (b : Ω → C(V, ℝ)),
        IsDomainRealization U P s a₀ a →
        IsDomainRealization V P (fun ω => confPullbackField Q hψ (s ω)) b₀ b →
        ∀ᵐ ω ∂P, ∀ u v : U,
          domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)
              (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
            domainMetric (ξ : ℝ) D U (a₀ ω) (a ω) (u, v) := by
  intro U V φ ψ hφ hψ hψφ Ω _ P _ s a₀ a b₀ b hRs hRt
  obtain ⟨h₁, F, hN, hC, hF, hdec⟩ :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.exists_normalized_decomposition
      hRs.2.1
  set G : Ω → C(U, ℝ) := fun ω => (F ω).restrict (U : Set ℂ) + a ω with hGdef
  have hG : Measurable G := measurable_restrict_add hF hRs.2.2.1
  -- `(h₁, G)` realizes `s`
  have hRs' : IsDomainRealization U P s h₁ G := by
    refine ⟨hRs.1, hC, hG, ?_⟩
    filter_upwards [hRs.2.2.2] with ω hω
    rw [hω, hdec ω, restrictTo_addFun, add_assoc]
    congr 1
    exact (SupercriticalConformalCovariance.Domain.ofFun_extZ_add U _ _).symm
  -- the corrected target realization of `(h₁|_U)^φ`
  set Gψ : Ω → C(V, ℝ) := fun ω => (G ω).comp (mapsToCM hψ) with hGψdef
  have hRt0 := SupercriticalConformalCovariance.Domain.isDomainRealization_add hRt (g := fun ω => -Gψ ω)
    (measurable_neg_comp hG (mapsToCM hψ))
  have hmeas : Measurable fun ω => confPullbackField Q hψ (restrictTo U (h₁ ω)) :=
    (measurable_confPullbackField Q hψ).comp
      (SupercriticalConformalCovariance.Domain.isDomainRealization_restrictTo U hC).1
  have hRt' : IsDomainRealization V P
      (fun ω => confPullbackField Q hψ (restrictTo U (h₁ ω))) b₀ (fun ω => b ω + -Gψ ω) := by
    refine isDomainRealization_congr hRt0 hmeas ?_
    filter_upwards [hRs'.2.2.2] with ω hω
    show confPullbackField Q hψ (restrictTo U (h₁ ω)) = confPullbackField Q hψ (s ω) +
      Distribution.ofFun V (Function.extend Subtype.val (⇑(-Gψ ω)) 0) volume ⊤
    rw [hω, confPullbackField_add, precomp_ofFun_extZ, add_assoc]
    erw [← SupercriticalConformalCovariance.Domain.ofFun_extZ_add V]
    rw [add_neg_cancel]
    erw [ofFun_extZ_zero, add_zero]
  have hfield : (fun ω => confPullbackField Q hψ (restrictTo U (h₁ ω))) =
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
        (restrictTo U (h₁ ω))) := by
    funext ω
    exact confPullbackField_inverse_choice Q hφ hψ hψφ _
  rw [hfield] at hRt'
  have hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h₁ b₀ (fun ω => b ω + -Gψ ω) :=
    ⟨hN, hRt'⟩
  have hfw := forward_wholePlane ξ Q hQ D hD hT hloc hP43 hL51 U V φ hφ P h₁ b₀ _ hI
  have hz := SupercriticalConformalCovariance.Domain.ae_domainMetric_zero_eq_internal hD U P hC
  have hind := SupercriticalConformalCovariance.Domain.ae_domainMetric_eq_of_isDomainRealization hD U hRs hRs'
  have hs₁ := SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P h₁ hC
  have hs₂ := SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P b₀ hRt.2.1
  filter_upwards [hfw, hz, hind, hs₁, hs₂] with ω hω hz hind hs₁ hs₂ u v
  rw [hind]
  have hb : b ω = (b ω + -Gψ ω) + Gψ ω := (neg_add_cancel_right _ _).symm
  have hG0 : G ω = 0 + G ω := (zero_add _).symm
  rw [hb, hG0]
  unfold domainMetric
  rw [SupercriticalConformalCovariance.Domain.weylScaleOn_add_eq_weylDistOnWith hs₂.1 V.isOpen,
    SupercriticalConformalCovariance.Domain.weylScaleOn_add_eq_weylDistOnWith hs₁.1 U.isOpen]
  set D₁ := D (h₁ ω) with hD₁
  set D₂ := D (b₀ ω) with hD₂
  let Φ : D₁.Space → D₂.Space := fun z => D₂.pt (φ (SupercriticalConformalCovariance.Domain.forget D₁ z))
  have hSo : IsOpen (SV D₁ U) := isOpen_SV hs₁.1 U.isOpen
  have hTo : IsOpen (SV D₂ V) := isOpen_SV hs₂.1 V.isOpen
  have hloc' : HigherDimLQGMetric.IsLocallyLengthOn (SV D₁ U) :=
    isLocallyLengthOn_of_isLengthSpace D₁ hs₁.2.1 hSo
  have hw₁ : ∀ x ∈ SV D₁ U, ContinuousAt (wV D₁ (ξ : ℝ) (0 : C(U, ℝ))) x := fun x hx =>
    (continuousOn_wV hs₁.1 _).continuousAt (hSo.mem_nhds hx)
  have hw₂ : ∀ y ∈ SV D₂ V, ContinuousAt (wV D₂ (ξ : ℝ) (b ω + -Gψ ω)) y := fun y hy =>
    (continuousOn_wV hs₂.1 _).continuousAt (hTo.mem_nhds hy)
  have hΦ : MapsTo Φ (SV D₁ U) (SV D₂ V) := fun x hx => hφ.2.mapsTo hx
  have hle : ∀ x ∈ SV D₁ U, ∀ y ∈ SV D₁ U,
      HigherDimLQGMetric.weylDistOn (wV D₂ (ξ : ℝ) (b ω + -Gψ ω)) (SV D₂ V) (Φ x) (Φ y) ≤
        HigherDimLQGMetric.weylDistOn (wV D₁ (ξ : ℝ) (0 : C(U, ℝ))) (SV D₁ U) x y := by
    intro x hx y hy
    have h1 := hω ⟨_, hx⟩ ⟨_, hy⟩
    rw [← hz] at h1
    unfold domainMetric at h1
    rw [SupercriticalConformalCovariance.Domain.weylScaleOn_eq_dV hs₂.1, SupercriticalConformalCovariance.Domain.weylScaleOn_eq_dV hs₁.1] at h1
    exact h1
  have hg : ∀ x ∈ SV D₁ U, wV D₂ (ξ : ℝ) (Gψ ω) (Φ x) = wV D₁ (ξ : ℝ) (G ω) x := by
    intro x hx
    rw [wV_of_mem (z := Φ x) _ (hφ.2.mapsTo hx)]
    erw [wV_of_mem (z := x) _ hx]
    congr 2
    show G ω ⟨ψ (φ (SupercriticalConformalCovariance.Domain.forget D₁ x)), _⟩ = G ω ⟨SupercriticalConformalCovariance.Domain.forget D₁ x, hx⟩
    congr 1
    exact Subtype.ext (hψφ _ hx)
  exact weylDistOnWith_transfer hloc' hw₁ hw₂ (fun y _ => wV_pos _ y) hΦ hle hg _ _

end SupercriticalConformalCovariance.Root
