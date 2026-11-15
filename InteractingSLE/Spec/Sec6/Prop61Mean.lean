/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux27
import InteractingSLE.Spec.Sec6.FiniteExceptionUniqueness
import InteractingSLE.GFF.LocalSets.Prop39Indep
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# Proposition 6.1: identifying the conditional mean on a component (Aux. 27 + Aux. 28)

Packet PROVE-SEC6-C (specification §6.1, `source/spec/p145-192.md`, `#prop-6.1` p. 154,
`#prop-6.1-proof` pp. 166–169; supplement §2.3, `source/spec/p433-480.md`, "Conditional-mean
consequence, with its inputs stated", pp. 454–455).

The proof of Proposition 6.1 identifies the conditional mean of the field in a complementary
component `C` of the local set `A(τ)` in two steps: boundary comparisons give the boundary values
of the actual mean `𝒞_A` at all but finitely many prime ends of `C`; then "Apply **Aux.** lemma 27
and then **Aux.** lemma 28 to each component. The difference is zero throughout the component"
(p. 169; also p. 167 for the pockets, and Remark 6.7, p. 171). This file proves the second step,
and the Gaussian-law conclusion, for any local set of the project's carrier:

* `ae_eqOn_component_of_tendsto` : for a local set `A` of a zero-boundary GFF `h⁰` on `ℍ`, a
  harmonic mean `F` bounded on bounded sets (the field is `h = h⁰ + F`), and a version `g` of
  `𝒞_A` (`IsLocalSetMean`),
  almost surely, in **every bounded component** `C` of `ℍ ∖ A` and for **every** chart
  (`f : 𝔻 → C` conformal, `φ : C → ℍ` conformal, `G` bounded harmonic on `ℍ`, a continuous branch
  `L` of `arg φ'`), the harmonic representative `v` of `g` satisfies `v + F = G ∘ φ − χ L` on `C`
  as soon as `(v + F) − (G ∘ φ − χ L)` tends to zero (read in the disk through `f`) at every point
  of the unit circle outside a finite set. One null set serves all components and all charts.
* `ae_condExp_exp_eq_of_component` : the conditional law of `h⁰` on a component given the germ
  σ-algebra is `𝒞_A` plus a zero-boundary GFF **of the component** (`σ²_{ℍ∖A}(φ) = σ²_C(φ)` for
  `supp φ ⊆ C`).
* `ae_condExp_exp_eq_of_eqOn_component` : once `𝒞_A + F = 𝔥` on a component `C` (by any route), on
  `{supp φ ⊆ C}` the field `h = h⁰ + F` has, given the germ σ-algebra, the conditional
  characteristic function of `𝔥 + GFF_C`.
* `ae_condExp_exp_eq_of_component_of_tendsto` : both together for the chart identification: the
  conclusion of Proposition 6.1, "the law of `h̃|_C` is equal to that of the sum of a zero boundary
  GFF in `C` plus `𝔥_C`", with `𝔥_C = G ∘ φ − χ L`.
* `condExp_ae_eq_on_of_le` and `ae_condExp_exp_eq_of_le_germSigma` : "Once the mean below has been
  identified, it and the residual covariance are functions of the labeled pair, so the same
  Gaussian law holds after those germs are forgotten" (p. 154): the same conditional
  characteristic function holds given any smaller σ-algebra for which the event, the mean pairing
  and the variance are measurable.

Deterministic inputs: `infDist_frontier_le_infDist_union_real` (for `z ∈ C`,
`dist(z, ∂C) ≤ dist(z, A ∪ ℝ)`, so Aux. 27's bound gives Aux. 28's growth hypothesis; the source:
"For `z ∈ C` we have `dist(z, A ∪ ∂S) = dist(z, ∂C)`", p. 167) and `eqOn_of_integral_mul_eq`
(harmonic representatives are unique).

## Carriers

Local sets live on `ℍ` (ruling R19 (5)); `h⁰` is the zero-boundary part and `F` the deterministic
harmonic mean of the field, so the conditional mean of `h` is `𝒞_A + F`. A chart is the data of
Aux. lemma 28 (`aux28_eqOn_of_tendsto_disk`): prime ends of `C` are the points of the unit circle
under `f`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open LocalSets

/-! ### Deterministic lemmas -/

/-- **Harmonic representatives are unique**: two functions harmonic on an open `O ⊆ ℍ` with the same
pairings against all test functions supported in `O` agree on `O` (mean-value property against
radial bumps). -/
theorem eqOn_of_integral_mul_eq {O : Set ℂ} (hO : IsOpen O) (hOH : O ⊆ H) {v₁ v₂ : ℂ → ℝ}
    (hv₁ : InnerProductSpace.HarmonicOnNhd v₁ O) (hv₂ : InnerProductSpace.HarmonicOnNhd v₂ O)
    (heq : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      ∫ z, v₁ z * φ z = ∫ z, v₂ z * φ z) :
    EqOn v₁ v₂ O := by
  intro z hz
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO z hz
  have hδ : (0 : ℝ) < ε / 2 := half_pos hε
  have hB : closedBall z (ε / 2) ⊆ O :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεO
  have hBH : closedBall z (ε / 2) ⊆ (upperHalfPlaneOpens : Set ℂ) := hB.trans hOH
  have e := heq (GFF.bumpTest z hδ hBH) ((GFF.tsupport_bumpFun_subset hδ).trans hB)
  rw [GFF.coe_bumpTest, GFF.integral_mul_bumpFun_of_harmonic hO hv₁ hδ hB,
    GFF.integral_mul_bumpFun_of_harmonic hO hv₂ hδ hB] at e
  have hpos : 0 < (ε / 2) ^ 2 * GFF.bumpMass := by
    have := GFF.bumpMass_pos; positivity
  exact mul_right_cancel₀ hpos.ne' e

/-- For an open `C` with nonempty complement and `z ∈ C`, the distance to the frontier is at most
the distance to the complement (the nearest point of the complement is a frontier point). -/
theorem infDist_frontier_le_infDist_compl {C : Set ℂ} (hCo : IsOpen C) (hC : Cᶜ.Nonempty)
    {z : ℂ} (hz : z ∈ C) : infDist z (frontier C) ≤ infDist z Cᶜ := by
  obtain ⟨p, hp, hpd⟩ := hCo.isClosed_compl.exists_infDist_eq_dist hC z
  have hd0 : 0 < infDist z Cᶜ :=
    (IsClosed.notMem_iff_infDist_pos hCo.isClosed_compl hC).1 (fun h => h hz)
  -- the open segment from `z` to `p` lies in `C`
  have hseg : ∀ t : ℝ, 0 ≤ t → t < 1 → z + (t : ℂ) * (p - z) ∈ C := by
    intro t ht0 ht1
    by_contra hmem
    have h1 := infDist_le_dist_of_mem (x := z) (show z + (t : ℂ) * (p - z) ∈ Cᶜ from hmem)
    have h2 : dist z (z + (t : ℂ) * (p - z)) = t * dist z p := by
      rw [dist_eq_norm, show z - (z + (t : ℂ) * (p - z)) = -((t : ℂ) * (p - z)) by ring,
        norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
        dist_eq_norm, ← norm_neg (z - p), neg_sub]
    rw [h2, ← hpd] at h1
    nlinarith
  have hpcl : p ∈ closure C := by
    have hlim : Tendsto (fun t : ℝ => z + (t : ℂ) * (p - z)) (𝓝[<] 1) (𝓝 p) := by
      have hc : Continuous fun t : ℝ => z + (t : ℂ) * (p - z) := by fun_prop
      have := hc.tendsto 1
      simp only [Complex.ofReal_one, one_mul, add_sub_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hseg t ht.1.le ht.2
  have hpfr : p ∈ frontier C := by
    rw [frontier, hCo.interior_eq]
    exact ⟨hpcl, hp⟩
  rw [hpd]
  exact infDist_le_dist_of_mem hpfr

/-- For `z` in a component `C` of `ℍ ∖ A` (`ℍ ∖ A` open), `dist(z, ∂C) ≤ dist(z, A ∪ ℝ)`
(the source: "For `z ∈ C` we have `dist(z, A ∪ ∂S) = dist(z, ∂C)`", p. 167), and
`0 < dist(z, ∂C)`. -/
theorem infDist_frontier_le_infDist_union_real {A : Set ℂ} (hA : IsOpen (H \ A)) {z₀ z : ℂ}
    (hz : z ∈ connectedComponentIn (H \ A) z₀) :
    0 < infDist z (frontier (connectedComponentIn (H \ A) z₀)) ∧
      infDist z (frontier (connectedComponentIn (H \ A) z₀)) ≤
        infDist z (A ∪ {w : ℂ | w.im = 0}) := by
  set C := connectedComponentIn (H \ A) z₀ with hCdef
  have hCo : IsOpen C := hA.connectedComponentIn
  have hCV : C ⊆ H \ A := connectedComponentIn_subset _ _
  have hzV : z ∈ H \ A := hCV hz
  have hCz : C = connectedComponentIn (H \ A) z := (connectedComponentIn_eq hz)
  have hCne : C ≠ univ := fun h => H_diff_ne_univ A (eq_univ_of_univ_subset (h ▸ hCV))
  have hCc : Cᶜ.Nonempty := nonempty_compl.2 hCne
  have h1 : infDist z Cᶜ = infDist z (H \ A)ᶜ := by
    rw [hCz]; exact infDist_compl_connectedComponentIn hA (H_diff_ne_univ A) hzV
  have hsub : A ∪ {w : ℂ | w.im = 0} ⊆ (H \ A)ᶜ := by
    rintro w (hw | hw)
    · exact fun h => h.2 hw
    · intro h
      have h0 : (0 : ℝ) < w.im := h.1
      have h1 : w.im = 0 := hw
      rw [h1] at h0
      exact lt_irrefl _ h0
  have hne : (A ∪ {w : ℂ | w.im = 0}).Nonempty := ⟨0, Or.inr (by simp)⟩
  have h2 : infDist z (H \ A)ᶜ ≤ infDist z (A ∪ {w : ℂ | w.im = 0}) :=
    infDist_le_infDist_of_subset hsub hne
  have h3 := infDist_frontier_le_infDist_compl hCo hCc hz
  have hpos : 0 < infDist z Cᶜ :=
    (IsClosed.notMem_iff_infDist_pos hCo.isClosed_compl hCc).1 (fun h => h hz)
  have h4 := infDist_compl_le_infDist_frontier hCo ⟨z, hz⟩ hCne z
  exact ⟨lt_of_lt_of_le hpos h4, h3.trans (h1 ▸ h2)⟩

/-! ### Aux. 27 + Aux. 28 on every bounded component -/

section Identification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ} {g : Ω → DistOn upperHalfPlaneOpens}

/-- Aux. lemma 27 on all balls `B(0, n)` on one null set. -/
theorem ae_aux27_ball (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ z ∈ ball (0 : ℂ) n ∩ (H \ A ω),
        |v z| ≤ C * (1 + infDist z (A ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) :=
  ae_all_iff.2 fun _ => aux27_of_isLocalSetMean hh hA hloc hg Metric.isBounded_ball

/-- **Proposition 6.1, identification step** (p. 167 for the pockets and p. 169: "Apply **Aux.**
lemma 27 and then **Aux.** lemma 28 to each component. The difference is zero throughout the
component"). Let `A` be a local set of the zero-boundary GFF `h` on `ℍ`, `g` a version of `𝒞_A`,
and `F` a harmonic function on `ℍ`, bounded on bounded sets (the deterministic mean; the field is
`h + F`). Almost surely, for every bounded component `C` of `ℍ ∖ A`, every harmonic representative
`v` of `g` on `ℍ ∖ A`, and every chart `(f, φ, G, L)` of Aux. lemma 28 (`f : 𝔻 → C` and
`φ : C → ℍ` conformal, `G` bounded harmonic on `ℍ`, `L` a continuous branch of `arg φ'` on `C`): if
`(v + F) − (G ∘ φ − χ L)` tends to zero at every prime end of `C` (point of the unit circle, read
through `f`) outside a finite set `E`, then `v + F = G ∘ φ − χ L` on `C`. -/
theorem ae_eqOn_component_of_tendsto (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ K : Set ℂ, Bornology.IsBounded K → ∃ M : ℝ, ∀ z ∈ K ∩ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, Bornology.IsBounded (connectedComponentIn (H \ A ω) z₀) →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ A ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ A ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ A ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (v (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ A ω) z₀, v z + F z = G (φc z) - χ * L z := by
  filter_upwards [ae_aux27_ball hh hA hloc hg, hloc.2.1] with ω hω ⟨_, hAo⟩ z₀ hz₀ hCb v hv
    hrep f φc G L E hf hφc hG hGb hLc hL hE hbd
  set C := connectedComponentIn (H \ A ω) z₀ with hCdef
  have hCo : IsOpen C := hAo.connectedComponentIn
  have hCV : C ⊆ H \ A ω := connectedComponentIn_subset _ _
  obtain ⟨r, hr⟩ := hCb.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hCn : C ⊆ ball (0 : ℂ) n := hr.trans (ball_subset_ball hn.le)
  obtain ⟨MF, hMF⟩ := hFb (ball (0 : ℂ) n) Metric.isBounded_ball
  have hH : InnerProductSpace.HarmonicOnNhd (fun z => v z + F z) C := fun z hz =>
    (hv z (hCV hz)).add (hF z (hCV hz).1)
  refine aux28_eqOn_of_tendsto_disk (Hh := fun z => v z + F z) hCo hf hH ?_ hφc hG hGb χ hLc hL
    hE hbd
  intro ε hε
  obtain ⟨K, hK⟩ := hω n ε hε
  refine ⟨max K 0 + max MF 0, fun z hz => ?_⟩
  obtain ⟨hd₁, hd₁₂⟩ := infDist_frontier_le_infDist_union_real hAo hz
  set D₁ := infDist z (frontier C)
  set D₂ := infDist z (A ω ∪ {w : ℂ | w.im = 0})
  have hpow : D₂ ^ (-ε) ≤ D₁ ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos hd₁ hd₁₂ (neg_nonpos.2 hε.le)
  have hD₁ : 0 ≤ D₁ ^ (-ε) := Real.rpow_nonneg hd₁.le _
  have hD₂ : 0 ≤ D₂ ^ (-ε) := Real.rpow_nonneg (infDist_nonneg) _
  have hv' : |v z| ≤ max K 0 * (1 + D₁ ^ (-ε)) := by
    calc |v z| ≤ K * (1 + D₂ ^ (-ε)) := hK v hv hrep z ⟨hCn hz, hCV hz⟩
      _ ≤ max K 0 * (1 + D₂ ^ (-ε)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max K 0 * (1 + D₁ ^ (-ε)) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
  have hF' : |F z| ≤ max MF 0 * (1 + D₁ ^ (-ε)) := by
    calc |F z| ≤ MF := hMF z ⟨hCn hz, (hCV hz).1⟩
      _ ≤ max MF 0 := le_max_left _ _
      _ ≤ max MF 0 * (1 + D₁ ^ (-ε)) := by
          have := le_max_right MF 0
          nlinarith
  calc |v z + F z| ≤ |v z| + |F z| := abs_add_le _ _
    _ ≤ (max K 0 + max MF 0) * (1 + D₁ ^ (-ε)) := by rw [add_mul]; exact add_le_add hv' hF'

end Identification

/-! ### The Gaussian law on a component -/

section Law

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ} {g : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional law on a component.** For a version `g` of `𝒞_A` and a test function `φ`,
almost surely, whenever `φ` is supported in a component `C` of `ℍ ∖ A`, the conditional
characteristic function of `h(φ)` given the germ σ-algebra is that of `g(φ)` plus a zero-boundary
GFF **of `C`**: `E[e^{i h(φ)} | 𝒜] = e^{i g(φ)} e^{−σ²_C(φ)/2}` (`σ²_{ℍ∖A}(φ) = σ²_C(φ)`). -/
theorem ae_condExp_exp_eq_of_component (hA : Measurable[mΩ, hittingSigma] A)
    (hhm : Measurable h) (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) (hg : IsLocalSetMean A h P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ →
      P[fun ω' => cexp (I * (h ω' φ : ℂ)) | germSigma A h] ω =
        cexp (I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hle := germSigma_le hA hhm
  have hgm : Measurable[germSigma A h] fun ω => g ω φ :=
    @Measurable.comp _ _ _ (germSigma A h) _ _ _ _ (LQGMetric.measurable_distOn_apply φ) hg.1
  have hhφ : Measurable fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hhm
  have hdm : Measurable fun ω => (h ω - g ω) φ := by
    have : (fun ω => (h ω - g ω) φ) = fun ω => h ω φ - g ω φ := by
      funext ω; rfl
    rw [this]; exact hhφ.sub (hgm.mono hle le_rfl)
  have hsplit : (fun ω => cexp (I * (h ω φ : ℂ))) =
      fun ω => cexp (I * (g ω φ : ℂ)) * cexp (I * ((h ω - g ω) φ : ℂ)) := by
    funext ω
    rw [← Complex.exp_add]
    congr 1
    have : (h ω - g ω) φ = h ω φ - g ω φ := rfl
    rw [this]; push_cast; ring
  have hpull := condExp_exp_mul_of_measurable (P := P) hgm (GFF.integrable_exp_I_mul hdm) hle
  filter_upwards [hpull, hg.2.2 φ, hopen] with ω hω hω' hωo z₀ hz₀ hφC
  rw [hsplit, hω, hω']
  have hCo : IsOpen (connectedComponentIn (H \ A ω) z₀) := hωo.connectedComponentIn
  have hCc : ∀ z ∈ connectedComponentIn (H \ A ω) z₀,
      connectedComponentIn (H \ A ω) z ⊆ connectedComponentIn (H \ A ω) z₀ := fun z hz => by
    rw [connectedComponentIn_eq hz]
  rw [zeroGFFTestCov_eq_of_isClopen hωo sdiff_subset hCo (connectedComponentIn_subset _ _)
    (isOpen_diff_of_forall_connectedComponentIn_subset hωo hCc) φ hφC]

/-- **The Gaussian law on a component, given an identified mean.** Almost surely: if the test
function `φ` is supported in a component `C` of `ℍ ∖ A` and a harmonic representative `v` of `g`
satisfies `v + F = 𝔥` on `C`, then, given the germ σ-algebra, `h(φ) + ∫ F φ` (the pairing of the
field `h + F`) has the conditional characteristic function of `(𝔥, φ) + GFF_C(φ)`. -/
theorem ae_condExp_exp_eq_of_eqOn_component (hA : Measurable[mΩ, hittingSigma] A)
    (hhm : Measurable h) (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) (hg : IsLocalSetMean A h P g)
    {F : ℂ → ℝ} (hF : ContinuousOn F H) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A ω → g ω ψ = ∫ x, v x * ψ x) →
      ∀ 𝔥 : ℂ → ℝ, (∀ z ∈ connectedComponentIn (H \ A ω) z₀, v z + F z = 𝔥 z) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | germSigma A h] ω =
        cexp (I * ((∫ x, 𝔥 x * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ) : ℝ) : ℂ) := by
  set c : ℂ := cexp (I * ((∫ x, F x * φ x : ℝ) : ℂ))
  have hsplit : (fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ))) =
      c • fun ω' => cexp (I * (h ω' φ : ℂ)) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul, c, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hsm := condExp_smul (μ := P) c (fun ω' => cexp (I * (h ω' φ : ℂ))) (germSigma A h)
  filter_upwards [hsm, ae_condExp_exp_eq_of_component hA hhm hopen hg φ, hopen] with ω hsmω hlaw
    hAo z₀ hz₀ hφC v hv hrep 𝔥 heq
  rw [hsplit, hsmω, Pi.smul_apply, hlaw z₀ hz₀ hφC, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  -- the mean pairing: `g(φ) + ∫ F φ = ∫ 𝔥 φ`
  have hCV : connectedComponentIn (H \ A ω) z₀ ⊆ H \ A ω := connectedComponentIn_subset _ _
  have hφV : tsupport φ ⊆ H \ A ω := hφC.trans hCV
  have hvc : ContinuousOn v (H \ A ω) := fun z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (H \ A ω) := hF.mono sdiff_subset
  have hsum : g ω φ + ∫ x, F x * φ x = ∫ x, 𝔥 x * φ x := by
    rw [hrep φ hφV, ← integral_add (integrable_mul_test hAo hvc φ hφV)
      (integrable_mul_test hAo hFc φ hφV)]
    congr 1; funext x
    by_cases hx : x ∈ connectedComponentIn (H \ A ω) z₀
    · rw [← heq x hx]; ring
    · simp only [image_eq_zero_of_notMem_tsupport (fun h' => hx (hφC h')), mul_zero, add_zero]
  rw [← hsum]; push_cast; ring

/-- **Proposition 6.1, the Gaussian law on a component** (identification through a chart).
Combining `ae_eqOn_component_of_tendsto` with `ae_condExp_exp_eq_of_eqOn_component`: almost
surely, if the test function `φ` is supported in a bounded component `C` of `ℍ ∖ A` and
`(v + F) − 𝔥_C` tends to zero at all but finitely many prime ends of `C`, `𝔥_C = G ∘ φ_C − χ L`,
then, given the germ σ-algebra, `h(φ) + ∫ F φ` has the conditional characteristic function of
`(𝔥_C, φ) + GFF_C(φ)`: "the law of `h̃|_C` is equal to that of the sum of a zero boundary GFF in `C`
plus `𝔥_C`". -/
theorem ae_condExp_exp_eq_of_component_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∀ K : Set ℂ, Bornology.IsBounded K → ∃ M : ℝ, ∀ z ∈ K ∩ H, |F z| ≤ M) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, Bornology.IsBounded (connectedComponentIn (H \ A ω) z₀) →
      tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A ω → g ω ψ = ∫ x, v x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ A ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ A ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ A ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (v (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | germSigma A h] ω =
        cexp (I * ((∫ x, (G (φc x) - χ * L x) * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hFc : ContinuousOn F H := fun z hz => (hF z hz).1.continuousAt.continuousWithinAt
  filter_upwards [ae_condExp_exp_eq_of_eqOn_component hA hh.measurable
      (hloc.2.1.mono fun _ h => h.2) hg hFc φ, ae_eqOn_component_of_tendsto hh hA hloc hg hF hFb χ]
    with ω hlaw hid z₀ hz₀ hCb hφC v hv hrep f φc G L E hf hφc hG hGb hLc hL hE hbd
  exact hlaw z₀ hz₀ hφC v hv hrep _
    (hid z₀ hz₀ hCb v hv hrep f φc G L E hf hφc hG hGb hLc hL hE hbd)

end Law

/-! ### Forgetting the germs -/

section Forget

variable {Ω : Type*} {𝒢 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
  {g : Ω → DistOn upperHalfPlaneOpens}

/-- **Forgetting information** (tower property on an event): if `E[X | 𝒦] = Y` almost surely on
`G`, with `𝒢 ≤ 𝒦`, `G ∈ 𝒢` and `Y` integrable and `𝒢`-measurable, then `E[X | 𝒢] = Y` almost
surely on `G`. -/
theorem condExp_ae_eq_on_of_le (h𝒢𝒦 : 𝒢 ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ)
    {X Y : Ω → ℂ} (hX : Integrable X P) (hY : StronglyMeasurable[𝒢] Y) (hYi : Integrable Y P)
    {G : Set Ω} (hG : MeasurableSet[𝒢] G) (hXY : ∀ᵐ ω ∂P, ω ∈ G → P[X | 𝒦] ω = Y ω) :
    ∀ᵐ ω ∂P, ω ∈ G → P[X | 𝒢] ω = Y ω := by
  have hG𝒦 : MeasurableSet[𝒦] G := h𝒢𝒦 G hG
  have h1 : P[G.indicator X | 𝒢] =ᵐ[P] G.indicator (P[X | 𝒢]) := condExp_indicator hX hG
  have h2 : P[P[G.indicator X | 𝒦] | 𝒢] =ᵐ[P] P[G.indicator X | 𝒢] :=
    condExp_condExp_of_le h𝒢𝒦 h𝒦
  have h3 : P[G.indicator X | 𝒦] =ᵐ[P] G.indicator Y := by
    filter_upwards [condExp_indicator (m := 𝒦) hX hG𝒦, hXY] with ω hω hω'
    rw [hω]
    by_cases hωG : ω ∈ G
    · rw [indicator_of_mem hωG, indicator_of_mem hωG, hω' hωG]
    · rw [indicator_of_notMem hωG, indicator_of_notMem hωG]
  have h4 : P[G.indicator Y | 𝒢] = G.indicator Y :=
    condExp_of_stronglyMeasurable (h𝒢𝒦.trans h𝒦) (hY.indicator hG) (hYi.indicator
      ((h𝒢𝒦.trans h𝒦) G hG))
  have h5 : P[P[G.indicator X | 𝒦] | 𝒢] =ᵐ[P] P[G.indicator Y | 𝒢] := condExp_congr_ae h3
  filter_upwards [h1, h2, h5] with ω e1 e2 e5 hωG
  have := e1.symm.trans (e2.symm.trans (e5.trans (congrFun h4 ω)))
  rwa [indicator_of_mem hωG, indicator_of_mem hωG] at this

/-- **Proposition 6.1, "after those germs are forgotten"** (p. 154): the conditional
characteristic function of `ae_condExp_exp_eq_of_component` holds given any `𝒢 ≤ 𝒜` (e.g. the
labeled pair) on an event `G ∈ 𝒢` on which `φ` is supported in a component of `ℍ ∖ A` and the mean
pairing `M` and the variance `S` are `𝒢`-measurable. -/
theorem ae_condExp_exp_eq_of_le_germSigma (hA : Measurable[mΩ, hittingSigma] A)
    (hhm : Measurable h) (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) (hg : IsLocalSetMean A h P g)
    (φ : TestOn upperHalfPlaneOpens) (h𝒢 : 𝒢 ≤ germSigma A h)
    {G : Set Ω} (hG : MeasurableSet[𝒢] G) {M S : Ω → ℝ} (hM : Measurable[𝒢] M)
    (hS : Measurable[𝒢] S)
    (hGC : ∀ᵐ ω ∂P, ω ∈ G → ∃ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ ∧
      g ω φ = M ω ∧
        QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ = S ω) :
    ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => cexp (I * (h ω' φ : ℂ)) | 𝒢] ω =
        cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * S ω) : ℝ) : ℂ) := by
  have hle := germSigma_le hA hhm
  set Y : Ω → ℂ := fun ω => cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * max (S ω) 0) : ℝ) : ℂ)
    with hYdef
  have hYm : Measurable[𝒢] Y := by
    let _ : MeasurableSpace Ω := 𝒢
    exact (GFF.measurable_exp_I_mul hM).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (hS.max measurable_const))))
  have hYi : Integrable Y P := by
    refine Integrable.of_bound ((hYm.mono (h𝒢.trans hle) le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => ?_)
    rw [hYdef, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [le_max_right (S ω) 0]
  have hX : Integrable (fun ω' => cexp (I * (h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hhm)
  have hXY : ∀ᵐ ω ∂P, ω ∈ G → P[fun ω' => cexp (I * (h ω' φ : ℂ)) | germSigma A h] ω = Y ω := by
    filter_upwards [ae_condExp_exp_eq_of_component hA hhm hopen hg φ, hGC, hopen] with ω hω hωG
      hωo hmem
    obtain ⟨z₀, hz₀, hφC, hgM, hσS⟩ := hωG hmem
    have hS0 : 0 ≤ S ω := by
      rw [← hσS]
      exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
        ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
    rw [hω z₀ hz₀ hφC, hgM, hσS]
    simp only [hYdef, max_eq_left hS0]
  filter_upwards [condExp_ae_eq_on_of_le h𝒢 hle hX hYm.stronglyMeasurable hYi hG hXY, hGC, hopen]
    with ω hω hωG hωo hmem
  obtain ⟨z₀, -, -, -, hσS⟩ := hωG hmem
  have hS0 : 0 ≤ S ω := by
    rw [← hσS]
    exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
  rw [hω hmem]
  simp only [hYdef, max_eq_left hS0]

end Forget


end InteractingSLE.Sec6
