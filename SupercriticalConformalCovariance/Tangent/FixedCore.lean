import SupercriticalConformalCovariance.Tangent.DiskFunctional
import SupercriticalConformalCovariance.Tangent.Transfer

/-!
# Lemma 3.3, steps 2–3 and 7 combined: fixed confinement

Paper l. 212–223: after the smooth normalization, the transformed fields near `B̄_S` converge to
the normalized `h^a` in total variation (GM (2.6)) and, deterministically, in the distributional
sense (GM (2.5)); the closed-disk metrics then converge (l. 218–221), the smooth-average
restoration and the Weyl correction having vanishing multiplicative effect (l. 214–217).

`subseqLSC_fixedCore` is the abstract form: whole-plane GFFs plus continuous functions `G n`, `G∞`
whose restricted coordinates on an open `W ⊇ B̄_S` converge a.s. and in total variation; target
metrics `T n` multiplicatively sandwiched around the closed-disk metrics of `D (G n)` with factors
tending to `c ∈ (0, ∞)`; then `T n → c · (closed-disk metric of D(G∞))` in probability.

Route: the universal local functional (`exists_universal_diskMetric_functional`) turns the
closed-disk metrics into one Borel function `Φ` of the coordinates; the transfer lemma
(`exists_subseq_ae_tendsto_comp_of_tvDist`) gives a.s. convergence of `Φ` along subsequences; the
sandwich lemma (`lscTendsto_mul_sandwich`) carries the multiplicative errors. This replaces the
maximal coupling and Lemma 3.1 of the printed proof (repair `domain-measurable-functional`): the
coupling would only give convergence in law, and lifting it to the realizations needs a further
disintegration (the maximal-coupling analysis' caveat); the transfer lemma gives convergence in probability on the
original space directly, which is what the joint-law identification (l. 231–236) needs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric LSCTendsto)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf)
open LQGMetric (DistC IsGFFPlusCont CoordJ)
open QuantumZipper.TV (tvDist)

/-- **Fixed confinement, abstract form.** -/
theorem subseqLSC_fixedCore {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ) {S : ℝ}
    (hSW : closedBall (0 : ℂ) S ⊆ W) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : ℕ → Ω → DistC) (Glim : Ω → DistC)
    (hG : ∀ n, IsGFFPlusCont (G n) P) (hGlim : IsGFFPlusCont Glim P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => locCoord W (G n ω)) atTop (𝓝 (locCoord W (Glim ω))))
    (hTV : Tendsto (fun n => tvDist (P.map fun ω => locCoord W (G n ω))
      (P.map fun ω => locCoord W (Glim ω))) atTop (𝓝 0))
    (T : ℕ → Ω → ℂ × ℂ → ℝ≥0∞) (Tlim : Ω → ℂ × ℂ → ℝ≥0∞)
    (a b : ℕ → Ω → ℝ≥0∞) (c : Ω → ℝ≥0∞) (hc : ∀ᵐ ω ∂P, c ω ≠ 0 ∧ c ω ≠ ⊤)
    (hab : ∀ᵐ ω ∂P, Tendsto (fun n => a n ω) atTop (𝓝 (c ω)) ∧
      Tendsto (fun n => b n ω) atTop (𝓝 (c ω)))
    (hsand : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q : ℂ × ℂ,
      a n ω * closedBallPathInf (D (G n ω)) 0 S q.1 q.2 ≤ T n ω q ∧
        T n ω q ≤ b n ω * closedBallPathInf (D (G n ω)) 0 S q.1 q.2)
    (hlim : ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ, Tlim ω q = c ω * closedBallPathInf (D (Glim ω)) 0 S q.1 q.2) :
    SubseqLSC P (fun n ω q => (T n ω q : EReal)) (fun ω q => (Tlim ω q : EReal)) := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  -- one Borel functional for the countable family `G n`, `G∞`
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_universal_diskMetric_functional hD W hSW (Option ℕ)
    (fun _ => Ω) (fun _ => P) (fun i => Option.elim i Glim G)
    (fun i => by cases i with
      | none => exact hGlim
      | some n => exact hG n)
  have hΦn : ∀ᵐ ω ∂P, ∀ n, diskMetric S (D (G n ω)) = Φ (locCoord W (G n ω)) :=
    ae_all_iff.2 fun n => hΦ (some n)
  have hΦlim : ∀ᵐ ω ∂P, diskMetric S (D (Glim ω)) = Φ (locCoord W (Glim ω)) := hΦ none
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_tendsto_comp_of_tvDist (P := P) hΦm
    (fun n => (measurable_locCoord W).comp (hG n).1) ((measurable_locCoord W).comp hGlim.1)
    hconv hTV ns hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae, hΦn, hΦlim, hc, hab, hsand, hlim] with ω hω hn hl hcω habω hsω hlω
  -- the closed-disk metrics converge along the subsequence
  have hdisk : Tendsto (fun k => diskMetric S (D (G (ns (ms k)) ω))) atTop
      (𝓝 (diskMetric S (D (Glim ω)))) := by
    simp only [hn, hl]
    exact hω
  have hlsc := (SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto).1 hdisk
  have hsub : StrictMono (fun k => ns (ms k)) := hns.comp hms
  have hres := lscTendsto_mul_sandwich (F := fun k q => T (ns (ms k)) ω q)
    (G := fun k q => closedBallPathInf (D (G (ns (ms k)) ω)) 0 S q.1 q.2)
    (G₀ := fun q => closedBallPathInf (D (Glim ω)) 0 S q.1 q.2) hlsc hcω.1 hcω.2
    (habω.1.comp hsub.tendsto_atTop) (habω.2.comp hsub.tendsto_atTop)
    (hsub.tendsto_atTop.eventually hsω)
  simpa only [hlω] using hres

end SupercriticalConformalCovariance.Tangent
