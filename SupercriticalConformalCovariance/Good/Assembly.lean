import SupercriticalConformalCovariance.Good.Probability

/-!
The Lemma 5.1 to Proposition 6.1 spine. Parameters q, a, K, θ and the
deterministic scale sequence are selected before η. For the transported metric,
the locality and Proposition 4.3 premises are discharged by
`BiLip.L51.lemma51LocalInput_proved` and `P43Final.prop43Input_proved`;
`Root.conformal_covariance_of_prop43` and `P43Final.prop43_input_slot`
apply them in the root closure.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Good

open LQGMetric (DistC IsWholePlaneGFF)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)

/-- Choose the same kind of compact exhaustion required by the Proposition 6.1 proof. This
construction is independent of η and of the probability space. -/
theorem exists_compact_exhaustion (U : Set ℂ) (hU : IsOpen U) :
    ∃ exhaustion : ℕ → Set ℂ,
      (∀ n, IsCompact (exhaustion n)) ∧
      (∀ n, exhaustion n ⊆ U) ∧
      (∀ A : Set ℂ, IsCompact A → A ⊆ U →
        ∃ N, A ⊆ exhaustion N) := by
  let V : TopologicalSpace.Opens ℂ := ⟨U, hU⟩
  let E : CompactExhaustion V := CompactExhaustion.choice V
  let exhaustion : ℕ → Set ℂ := fun n => Subtype.val '' E n
  refine ⟨exhaustion, ?_, ?_, ?_⟩
  · intro n
    exact Subtype.isCompact_iff.1 (E.isCompact n)
  · intro n
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro A hA hAU
    have hA' : IsCompact (Subtype.val ⁻¹' A : Set V) := by
      rw [Subtype.isCompact_iff,
        image_preimage_eq_of_subset fun x hx => ⟨⟨x, hAU hx⟩, rfl⟩]
      exact hA
    obtain ⟨N, hN⟩ := E.exists_superset_of_isCompact hA'
    exact ⟨N, fun x hx => ⟨⟨x, hAU hx⟩, hN hx, rfl⟩⟩

/-- Assemble Lemma 5.1 and display (10) into precisely the almost-sure
GoodCover consumed by the Proposition 6.1 proof. The probability threshold is fixed by the
cover theorem before the source geometric parameters are chosen; none depends
on η. -/
theorem ae_goodCover_of_locality_and_prop43
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (k : ℝ) (hk : 0 < k) :
    ∃ (p : ℝ) (θ : Ioi (0 : ℝ)) (n : ℕ)
      (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      0 < p ∧ p < 1 ∧ (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P →
        ∀ (e : Ω → ℂ × ℂ → ℝ≥0∞)
          (U : Set ℂ), IsOpen U →
        ∀ (exhaustion : ℕ → Set ℂ),
          (∀ m, IsCompact (exhaustion m)) →
          (∀ m, exhaustion m ⊆ U) →
          ∀ η : ℝ, 0 < η →
          (∀ L : Set ℂ, IsCompact L → L ⊆ U →
            ∃ r₀ : ℝ, 0 < r₀ ∧
              ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
                LQGMetric.Blueprint.AEEventIn P
                  (SupercriticalConformalCovariance.Cover.localSigma h z r)
                  (GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r)) →
          (∀ L : Set ℂ, IsCompact L → L ⊆ U →
            ∃ r₀ : ℝ, 0 < r₀ ∧
              ∀ z ∈ L, ∀ r : Ioi (0 : ℝ), (r : ℝ) ≤ r₀ →
                P (RegularBadEvent h (D ∘ h) e ξ Q q a θ η z r) ≤
                  ENNReal.ofReal ((1 - p) / 2)) →
          ∀ᵐ ω ∂P,
            SupercriticalConformalCovariance.Improve.GoodCover (D (h ω)) (e ω) ξ Q q a K θ k η
              exhaustion coverScale := by
  obtain ⟨p, hp0, hp1, Hcov⟩ :=
    SupercriticalConformalCovariance.Cover.goodCovers_everyCompact 1 (by norm_num)
  obtain ⟨θ, Hprob⟩ :=
    goodEvent_uniform_probability_of_prop43 ξ Q hQ D hD
  obtain ⟨n, q, a, K, hqd, Hprob⟩ := Hprob k p hk hp0 hp1
  refine ⟨p, θ, n, q, a, K, hp0, hp1, hqd, ?_⟩
  intro Ω _ P _ h hh e U hU exhaustion hKc hKU η hη hlocal hbad
  have h51 : ∀ L : Set ℂ, IsCompact L → L ⊆ U →
      ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
          LQGMetric.Blueprint.AEEventIn P (SupercriticalConformalCovariance.Cover.localSigma h z r)
            (GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r) ∧
          ENNReal.ofReal p ≤
            P (GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r) := by
    intro L hLc hLU
    obtain ⟨rL, hrL, hL⟩ := hlocal L hLc hLU
    obtain ⟨rP, hrP, hP⟩ := Hprob P h hh e η L hη hLc (hbad L hLc hLU)
    refine ⟨min rL rP, lt_min hrL hrP, ?_⟩
    intro z hz r hr
    exact ⟨hL z hz r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩,
      hP z hz r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩⟩
  have hcov := Hcov P h hh U hU
    (GoodEvent h (D ∘ h) e ξ Q q a K θ k η) h51
    coverScale (fun j => (coverScale_pos_le_one j).1)
    SupercriticalConformalCovariance.Cover.tendsto_two_pow
    (SupercriticalConformalCovariance.Cover.summable_two_pow (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcov] with ω hω
  apply goodCover_of_eventual_cover h (D ∘ h) e ξ Q q a K θ k η exhaustion ω
  intro m
  exact hω (exhaustion m) (hKc m) (hKU m)

end SupercriticalConformalCovariance.Good
