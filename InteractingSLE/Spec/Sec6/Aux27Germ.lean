/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux27
import InteractingSLE.Spec.Sec6.Prop65Gauss
import InteractingSLE.GFF.LocalSets.MarkovNesting

/-!
# Aux. lemma 27 for a field with a deterministic harmonic mean, in germ form

Packet PROVE-SEC6-B (specification §6.1, `source/spec/p145-192.md`, `#aux-27`, pp. 160–162).

**Aux. lemma 27.** Let `h = h⁰ + F` be a GFF in `D` with deterministic harmonic mean `F`, `A` a local
set, `h = h_A + h^A` the local-set decomposition. Let `K` be bounded with `F` bounded on `D ∩ K⁺` for an
open neighbourhood `K⁺` of `K̄`. Then for every `ε > 0`, almost surely there is a finite `C` with
`|h_A(z)| ≤ C (1 + dist(z, A ∪ ∂D)^{−ε})` for `z ∈ K ∩ (D ∖ A)`.

PROVE-SEC6-A3 proved it (`aux27`) with the local-set mean in conditional-mean form, and for the
project's local-set mean `IsLocalSetMean` (germ σ-algebra) only for a zero-boundary field. Here
`h_A` is the project's local-set mean of `h` itself (`IsLocalSetMean A h P g`: `g` germ-measurable,
harmonic on `ℍ ∖ A`, and given the germ σ-algebra `𝒜 = germSigma A h`, `h − g` is a zero-boundary GFF on
`ℍ ∖ A`), for any harmonic mean `F` (`aux27_of_isLocalSetMean_of_mean`).

## Proof

The conditional law forces `E[(h − g)(φ) | 𝒜] = 0`: the conditional characteristic function of
`Y = (h − g)(φ)` is `exp(−t² V/2)` with `V = Var_{ℍ∖A}(φ) ∈ [0, Var_ℍ(φ)]`; `V` is almost surely the
`𝒜`-measurable `−2 log |E[e^{iY} | 𝒜]|` (clamped), so the conditional moment identities of
`Prop65Gauss` apply (`condExp_eq_zero_of_condCharFun`). Since `g(φ)` is `𝒜`-measurable,
`g(φ) = E[h(φ) | 𝒜]` — the conditional-mean hypothesis of `aux27_ae_forall`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Complex
open scoped ENNReal NNReal

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec6

/-- **A conditionally centred Gaussian has conditional mean zero**: if `E[e^{itY} | 𝒢] = e^{−t² V/2}` for
every `t`, with `0 ≤ V ≤ K` almost surely (`V` not assumed measurable), then `Y` is integrable and
`E[Y | 𝒢] = 0`. -/
theorem condExp_eq_zero_of_condCharFun {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    {K : ℝ} (hV : ∀ᵐ ω ∂P, 0 ≤ V ω ∧ V ω ≤ K)
    (hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ)) :
    Integrable Y P ∧ P[Y | 𝒢] =ᵐ[P] 0 := by
  -- an `𝒢`-measurable version of `V`
  set W : Ω → ℝ := fun ω =>
    max 0 (min K (-2 * Real.log ‖(P[fun ω => cexp (I * (((1 : ℝ) * Y ω : ℝ) : ℂ)) | 𝒢]) ω‖))
    with hWdef
  have hWm : Measurable[𝒢] W := by
    have h1 : Measurable[𝒢] fun ω =>
        (P[fun ω => cexp (I * (((1 : ℝ) * Y ω : ℝ) : ℂ)) | 𝒢]) ω :=
      stronglyMeasurable_condExp.measurable
    have h2 : Measurable fun x : ℂ => max 0 (min K (-2 * Real.log ‖x‖)) := by fun_prop
    exact h2.comp h1
  have hWV : W =ᵐ[P] V := by
    filter_upwards [hc 1, hV] with ω h1 hV
    simp only [hWdef, h1]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp]
    rw [show -2 * (-(1 / 2) * ((1 : ℝ) ^ 2 * V ω)) = V ω by ring, min_eq_right hV.2,
      max_eq_right hV.1]
  have hK : 0 ≤ K := by
    obtain ⟨ω, hω⟩ := hV.exists
    exact hω.1.trans hω.2
  have hc' : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * W ω)) : ℝ) : ℂ) := fun t => by
    filter_upwards [hc t, hWV] with ω h1 h2
    rw [h1, h2]
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => le_max_left _ _
  have hWK : ∀ ω, W ω ≤ K := fun ω => max_le hK (min_le_left _ _)
  have hi := Prop65.integrable_pow_of_condCharFun h𝒢 hY (hWm.mono h𝒢 le_rfl) hW0 hWK hc' 1
  have hce := Prop65.condExp_pow_eq_of_condCharFun h𝒢 hY hWm hW0 hWK hc' 1
  rw [Prop65.gmom_one] at hce
  simp only [pow_one, mul_zero] at hi hce
  exact ⟨hi, hce⟩

/-- **The local-set mean is the conditional mean** given the germ σ-algebra: for `IsLocalSetMean A h P g`
(with `ℍ ∖ A` almost surely open and `h(φ)` integrable), `g(φ) = E[h(φ) | 𝒜]` almost surely. -/
theorem IsLocalSetMean.ae_eq_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Ω → Set ℂ} {h g : Ω → DistOn upperHalfPlaneOpens}
    (hA : Measurable[mΩ, hittingSigma] A) (hhm : Measurable h) (hg : LocalSets.IsLocalSetMean A h P g)
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens)
    (hφi : Integrable (fun ω => h ω φ) P) :
    (fun ω => g ω φ) =ᵐ[P] P[fun ω => h ω φ | LocalSets.germSigma A h] := by
  have h𝒢 := LocalSets.germSigma_le hA hhm
  have hgm : Measurable[LocalSets.germSigma A h] fun ω => g ω φ :=
    (LQGMetric.measurable_distOn_apply φ).comp hg.1
  set Y : Ω → ℝ := fun ω => h ω φ - g ω φ with hYdef
  have hYm : Measurable Y :=
    ((LQGMetric.measurable_distOn_apply φ).comp hhm).sub (hgm.mono h𝒢 le_rfl)
  -- the conditional characteristic function of `Y`
  have hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | LocalSets.germSigma A h] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro t
    have hc' := hg.2.2 (t • φ)
    have e1 : (fun ω => cexp (I * (((h ω - g ω) (t • φ) : ℝ) : ℂ))) =
        fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) := by
      funext ω
      congr 3
      simp only [hYdef, sub_apply, map_smul, smul_eq_mul, mul_sub]
    rw [e1] at hc'
    filter_upwards [hc', hopen] with ω hω hUo
    rw [hω, LocalSets.zeroGFFTestCov_smul_self hUo sdiff_subset t φ]
  have hV : ∀ᵐ ω ∂P, 0 ≤ zeroGFFTestCov (H \ A ω) φ φ ∧
      zeroGFFTestCov (H \ A ω) φ φ ≤ zeroGFFTestCov upperHalfPlaneOpens φ φ := by
    filter_upwards [hopen] with ω hUo
    exact ⟨LocalSets.zeroGFFTestCov_self_nonneg hUo sdiff_subset φ,
      LocalSets.zeroGFFTestCov_mono hUo QuantumZipper.isOpen_H sdiff_subset subset_rfl φ⟩
  obtain ⟨hYi, hY0⟩ := condExp_eq_zero_of_condCharFun h𝒢 hYm hV hc
  have hgi : Integrable (fun ω => g ω φ) P :=
    (hφi.sub hYi).congr (Eventually.of_forall fun ω => by simp [hYdef])
  have hsplit : (fun ω => h ω φ) = fun ω => g ω φ + Y ω := by
    funext ω; simp [hYdef]
  rw [hsplit]
  have hadd := condExp_add (m := LocalSets.germSigma A h) hgi hYi
  filter_upwards [hadd, hY0] with ω h1 h2
  change g ω φ = (P[(fun ω => g ω φ) + Y | LocalSets.germSigma A h]) ω
  rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable h𝒢 hgm.stronglyMeasurable hgi]
  simp

/-- **Aux. lemma 27 for the project's local-set mean of a field with harmonic mean `F`.** Let `h` be a
measurable field with `h − F` a zero-boundary GFF on `ℍ` (`F` harmonic on `ℍ`), `A` a local set of `h`
(`IsLocalSet`, measurable for the hitting σ-algebra), `g` its local-set mean (`IsLocalSetMean A h P g`,
germ σ-algebra), and `K` bounded with `|F| ≤ M_F` on `ℍ ∩ K⁺`, `K̄ ⊆ K⁺`. Then almost surely, for every
`ε > 0` there is a finite `C` such that every harmonic representative `v` of `g` on `ℍ ∖ A` satisfies
`|v(z)| ≤ C (1 + dist(z, A ∪ ℝ)^{−ε})` on `K ∩ (ℍ ∖ A)` (one null set for all `ε`). -/
theorem aux27_of_isLocalSetMean_of_mean {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hh : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ x, F x * φ x) P)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : LocalSets.IsLocalSetMean A h P g) {K : Set ℂ}
    (hK : Bornology.IsBounded K) {Kp : Set ℂ} (hKp : closure K ⊆ Kp) {MF : ℝ}
    (hFK : ∀ z ∈ H ∩ Kp, |F z| ≤ MF) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ z ∈ K ∩ (H \ A ω),
        |v z| ≤ C * (1 + infDist z (A ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) := by
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω) := hloc.2.1.mono fun ω hω => hω.2
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => g ω φ) =ᵐ[P] P[fun ω => h ω φ | LocalSets.germSigma A h] := by
    intro φ
    have hφi : Integrable (fun ω => h ω φ) P := by
      have h1 : Integrable (fun ω => h ω φ - ∫ x, F x * φ x) P :=
        (hh.gaussian.hasGaussianLaw_eval φ).integrable
      refine (h1.add (integrable_const (∫ x, F x * φ x))).congr
        (Eventually.of_forall fun ω => ?_)
      simp
    exact IsLocalSetMean.ae_eq_condExp hA hhm hg hopen φ hφi
  exact aux27_ae_forall hhm hF hh (LocalSets.germSigma_le hA hhm) hmean hopen hK
    (fun z hz => hFK z ⟨hz.2, hKp (subset_closure hz.1)⟩)

end InteractingSLE.Sec6
