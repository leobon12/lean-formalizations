/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# Aux. lemma 61, first half: the relative mean vanishes on the old boundary (marked nested Proposition 3.8)

Packet PROVE-AUX61-MEAN. Astra's follow-up 4 §1.2 (`source/external/AstraIG1/ig1_followup4_audited.txt` L150–L176,
ruling R71), the proof of identity (1.1): "Subtract the initial mean `M` from the nested Gaussian decomposition. The
remaining mean is a relative zero-GFF local-set mean. It has zero boundary values on the old boundary, irrespective of
the old singularities of `M`." This is Proposition 3.8's boundary-patch estimate (spec pp. 59–60) for NESTED sets with
retained records: the larger set `A₁ ∪ A₂` comes with the conditional Gaussian decomposition given a σ-algebra `𝒥`
(the germs of the larger set and the retained marks), the smaller set `A₂` is an ordinary local set with its mean
`𝒞_{A₂}`, and no conditional independence of the two sets is assumed (the restart's stop depends on both records,
Astra L95–L104).

* **`ae_tendsto_sub_of_condLaw`**: almost surely `g₀ − 𝒞_{A₂}` is, on `ℍ ∖ (A₁ ∪ A₂)`, a harmonic function `u` with
  `u(z) → 0` as `z → z₀` for every `z₀ ∈ A₂ ∪ ℝ` near which `A₁ ⊆ A₂` — in particular at every old kissing point and
  every old real point away from the new part.

The proof is the landed proof of `LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`, whose only use of the conditional
independence of the two sets is to produce the joint decomposition `g₀`; here `g₀` is given. The per-patch moment bound
(`LocalSets.lintegral_layer_indicator_le`) and the Borel–Cantelli layer argument (`ae_eventually_abs_lt_of_layer`) are
reused unchanged.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE.Sec5.Aux61MeanId

open QuantumZipper LQGMetric
open LocalSets
open GFF (layerSet bumpMass bumpMass_pos)

variable {Ω : Type u} {𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.8 for a given joint decomposition (marked, nested form).** Let `h` be a zero-boundary GFF on `ℍ`,
`A₁, A₂` hitting-measurable relatively closed random sets with every component of `A₂ ∪ {Im ≤ 0}` unbounded, `𝒥` a
σ-algebra containing the germs of `A₂` and the two sets, `g₀` a `𝒥`-measurable distribution harmonic off `A₁ ∪ A₂` with
`h − g₀` conditionally a zero-boundary GFF on `ℍ ∖ (A₁ ∪ A₂)` given `𝒥`, and `g₂` a version of `𝒞_{A₂}`. Almost surely
`g₀ − g₂` is, on `ℍ ∖ (A₁ ∪ A₂)`, a harmonic function `u` with `u(z) → 0` at every `z₀ ∈ A₂ ∪ ℝ` near which
`A₁ ⊆ A₂`. -/
theorem ae_tendsto_sub_of_condLaw (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    (h𝒥 : 𝒥 ≤ mΩ) (h₂𝒥 : germSigma A₂ h ≤ 𝒥)
    (h₁₂𝒥 : MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma ≤ 𝒥)
    {g₀ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₀m : Measurable[𝒥] g₀)
    (hg₀h : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ (A₁ ω ∪ A₂ ω)))
    (hg₀c : IsCondZeroBoundaryGFF P 𝒥 (fun ω => H \ (A₁ ω ∪ A₂ ω)) fun ω => h ω - g₀ ω)
    (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ (A₁ ω ∪ A₂ ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g₀ ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ A₂ ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A₁ ω ∩ ball z₀ r ⊆ A₂ ω) →
        Tendsto u (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0) := by
  classical
  have hhm := hh.measurable
  set A : Ω → Set ℂ := fun ω => A₁ ω ∪ A₂ ω with hAdef
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hA₁c, hA₂c] with ω ⟨hs₁, ho₁⟩ ⟨hs₂, ho₂⟩
    refine ⟨union_subset hs₁ hs₂, ?_⟩
    have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
      ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
    simp only [hAdef]
    rw [e]; exact ho₁.inter ho₂
  -- the difference `D = g₀ − g₂` and its harmonic representative `u`
  set D : Ω → DistOn upperHalfPlaneOpens := fun ω => g₀ ω - g₂ ω with hDdef
  have hDm : Measurable D := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp (hg₀m.mono h𝒥 le_rfl)).sub
      ((measurable_distOn_apply φ).comp (hg₂.1.mono (germSigma_le hA₂ hhm) le_rfl))
  have hDh : ∀ᵐ ω ∂P, IsHarmonicDistOn (D ω) (H \ A ω) := by
    filter_upwards [hg₀h, hg₂.2.1, hAc] with ω h0 h2 ⟨_, ho⟩
    exact IsHarmonicDistOn.sub' ho h0 (IsHarmonicDistOn.mono h2 (fun z hz =>
      ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩))
  set u : Ω → ℂ → ℝ := fun ω => if hω : IsHarmonicDistOn (D ω) (H \ A ω) then hω.choose else 0
    with hudef
  have hu : ∀ ω, IsHarmonicDistOn (D ω) (H \ A ω) →
      InnerProductSpace.HarmonicOnNhd (u ω) (H \ A ω) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → D ω φ = ∫ z, u ω z * φ z := by
    intro ω hω
    simp only [hudef, hω, dite_true]
    exact hω.choose_spec
  -- the patches `B(c_k, 4 R_j)`
  set cen : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with hcen
  set rad : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hrad
  have hrad0 : ∀ j, 0 < rad j := fun j => by positivity
  set O : Ω → Set ℂ := fun ω => H \ relClosureH (A₂ ω) with hOdef
  have hBC : ∀ p : ℕ × ℕ, ∀ m : ℕ, ∀ᵐ ω ∂P,
      ω ∈ inclEvent A₁ A₂ (ball (cen p.1) (4 * rad p.2)) → ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ O ω,
        dist w (cen p.1) < 2 * rad p.2 → (1 / 2 : ℝ) ^ (n + 1) ≤ infDist w (O ω)ᶜ →
          infDist w (O ω)ᶜ ≤ (1 / 2 : ℝ) ^ n → |u ω w| < 1 / ((m : ℝ) + 1) := by
    intro p m
    have hR := hrad0 p.2
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (GFF.eventually_params hR 1)
    have hE : MeasurableSet (inclEvent A₁ A₂ (ball (cen p.1) (4 * rad p.2))) :=
      sup_le hA₁.comap_le hA₂.comap_le _ (measurableSet_inclEvent A₁ A₂ _)
    refine ae_eventually_abs_lt_of_layer (O := O) (u := u)
      (G := fun n q => bumpPair D (bumpRad (rad p.2) n) (bumpRad_pos hR n) q /
        (bumpRad (rad p.2) n ^ 2 * bumpMass)) (n₁ := n₁) hE
      (fun n => (measurable_bumpPair hDm _).div_const _) hR
      (fun n => measurableSet_layerSet_compl hA₂ _ _ n) ?_ ?_ (by positivity)
    · filter_upwards [hA₁c, hA₂c, hDh, hAc] with ω h1 h2 hD hAω hωE
      obtain ⟨huh, hur⟩ := hu ω hD
      have hincl := (mem_inclEvent_iff isOpen_ball h1 h2).1 hωE
      have hO : O ω = H \ A₂ ω := by simp only [hOdef, relClosureH_eq h2.1 h2.2]
      have hsub : O ω ∩ ball (cen p.1) (4 * rad p.2) ⊆ H \ A ω := by
        rw [hO]
        rintro z ⟨⟨hzH, hz₂⟩, hzU⟩
        exact ⟨hzH, fun h' => h'.elim (fun hz₁ => hz₂ (hincl ⟨hz₁, hzU⟩)) hz₂⟩
      refine ⟨isOpen_H_diff_relClosureH _, fun z hz => huh z (hsub hz), fun n hn y hy => ?_⟩
      obtain ⟨hnR, hnτ, -⟩ := hn₁ n hn
      have hB : closedBall y (bumpRad (rad p.2) n) ⊆ H \ A ω := by
        refine fun z hz => hsub ⟨closedBall_bumpRad_subset hR hnτ hy hz, ?_⟩
        have hyc : dist y (cen p.1) < 3 * rad p.2 := hy.1.1.2
        have hδR : bumpRad (rad p.2) n < rad p.2 := (bumpRad_lt hR hnτ).trans_le hnR
        rw [mem_ball]
        have := dist_triangle z y (cen p.1)
        have := mem_closedBall.1 hz
        linarith
      exact bumpPair_eq_of_harmonic (T := D) (bumpRad_pos hR n) hAω.2 huh hur hB sdiff_subset
    · intro n hn y l hl
      exact lintegral_layer_indicator_le hh hA₁ hA₂ hA₁c hA₂c hunb h𝒥 h₂𝒥 h₁₂𝒥 hg₀m hg₀c hg₂
        hR (hn₁ n hn).2.1 y l hl
  -- assembly
  have hBC' := ae_all_iff.2 fun p => ae_all_iff.2 (hBC p)
  filter_upwards [hBC', hA₁c, hA₂c, hDh] with ω hω h1 h2 hD
  obtain ⟨huh, hur⟩ := hu ω hD
  refine ⟨u ω, huh, fun φ hφ => ?_, fun z₀ hz₀ ⟨r, hr, hrA⟩ => ?_⟩
  · rw [← hur φ hφ]
    rfl
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < r / 5 by positivity)
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z₀
      (rad j) (hrad0 j)
    have hkj : dist z₀ (cen k) < rad j := hk
    obtain ⟨mm, hmm⟩ := exists_nat_one_div_lt hε
    have hrj : rad j < r / 5 := hj
    have hU : ball (cen k) (4 * rad j) ⊆ ball z₀ r := fun w hw => by
      rw [mem_ball] at hw ⊢
      have := dist_triangle w (cen k) z₀
      rw [dist_comm (cen k) z₀] at this
      linarith
    have hE : ω ∈ inclEvent A₁ A₂ (ball (cen (k, j).1) (4 * rad (k, j).2)) :=
      (mem_inclEvent_iff isOpen_ball h1 h2).2 fun z hz => hrA ⟨hz.1, hU hz.2⟩
    obtain ⟨N, hN⟩ := hω (k, j) mm hE
    refine ⟨min (rad j) ((1 / 2 : ℝ) ^ N), lt_min (hrad0 j) (by positivity), fun {x} hxA hxz => ?_⟩
    have hrc := relClosureH_eq h2.1 h2.2
    have hxO : x ∈ O ω := by
      refine ⟨hxA.1, ?_⟩
      simp only [hrc]
      exact fun h' => hxA.2 (Or.inr h')
    have hz₀O : z₀ ∈ (O ω)ᶜ := by
      intro hzO
      rcases hz₀ with hz | hz
      · exact hzO.2 (by simp only [hrc]; exact hz)
      · have h0 : (0 : ℝ) < z₀.im := hzO.1
        have h0' : z₀.im = 0 := hz
        linarith
    have hOc : IsClosed (O ω)ᶜ := (isOpen_H_diff_relClosureH _).isClosed_compl
    have hd0 : 0 < infDist x (O ω)ᶜ :=
      (IsClosed.notMem_iff_infDist_pos hOc ⟨z₀, hz₀O⟩).1 (fun h => h hxO)
    have hdx : infDist x (O ω)ᶜ ≤ dist x z₀ := infDist_le_dist_of_mem hz₀O
    have hdN : infDist x (O ω)ᶜ < (1 / 2 : ℝ) ^ N :=
      lt_of_le_of_lt hdx (lt_of_lt_of_le hxz (min_le_right _ _))
    obtain ⟨n, hnN, hn1, hn2⟩ := GFF.exists_layer_index hd0 hdN
    have hxc : dist x (cen k) < 2 * rad j := by
      have := dist_triangle x z₀ (cen k)
      have := lt_of_lt_of_le hxz (min_le_left _ _)
      linarith
    have := hN n hnN x hxO hxc hn1 hn2
    rw [Real.dist_eq, sub_zero]
    linarith

end InteractingSLE.Sec5.Aux61MeanId
