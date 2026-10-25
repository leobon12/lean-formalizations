import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLeftVerticalArc
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalContinuousLimit
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 


theorem laneC_physical_left_vertical_resampling_le_around_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
      (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) (hr0 : 0 < r)
    (hrSmall : 2 * r < 1 / 8) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      let c := T20.dyCenter K b
      let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
      2 * r ≤ c.im → c.im + 2 * r ≤ 1 → c.re + 2 * r ≤ 1 →
      ∀ γ : ℝ → ℂ,
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
        (rectAB 1 1).side₂ γ →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
      ∀ m : ℝ, m ∈ Icc (0 : ℝ) 1 → dist (γ m) c ≤ r →
      2 * r ≤ dist (γ 1) c →
      ∀ M : ℝ, 0 < M →
      (lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)).aroundDist A
          (sphere c r) (sphere c (2 * r)) < ENNReal.ofReal M →
      (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
        (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal + M := by
  filter_upwards [laneC_physical_boundary_resampling_le_of_continuous_arc
      hW Q ξ hKn hσ hr] with z hz
  intro b hb
  dsimp only
  intro hclo hchi hcri γ hγ hγfin m hm hmid hend M hM haround
  let c := T20.dyCenter K b
  let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
  let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
  obtain ⟨a, d, ρ, had, hρcont, hρA, hsep, hρlen⟩ :=
    laneC_exists_around_witness_of_lt D A
      (sphere c r) (sphere c (2 * r)) haround
  obtain ⟨z₀, hz₀, z₁, hz₁, hpath, hγsq⟩ := hγ
  obtain ⟨α, t₀, t₁, ht₀, ht₁, htord, hα, hαcar,
      hbegin, hmeet, hafter, hlen⟩ :=
    laneC_left_vertical_source_separator_arc D hr0 hrSmall
      hclo hchi hcri had hρcont
      (by intro s hs; exact hρA ⟨s, hs, rfl⟩)
      hsep hpath.continuousOn hγsq
      (by simpa only [hpath.source] using hz₀)
      hm hmid hend
  have hαring : ∀ t ∈ Icc (0 : ℝ) 1,
      r < dist (α t) c ∧ dist (α t) c < 2 * r :=
    fun t ht => ⟨(hαcar t ht).1, (hαcar t ht).2.1⟩
  have hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet :=
    fun t ht => (hαcar t ht).2.2
  have hαM : D.len α 0 1 < ENNReal.ofReal M := lt_of_le_of_lt hlen hρlen
  exact hz b hb α γ hα hαring hαsq
    ⟨z₀, hz₀, z₁, hz₁, hpath, hγsq⟩ hγfin M hM hαM
    t₀ t₁ ht₀ ht₁ htord hbegin (Or.inl ⟨hmeet, hafter⟩)

 
theorem laneC_physical_left_vertical_resampling_le_around
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
      (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) (hr0 : 0 < r)
    (hrSmall : 2 * r < 1 / 8) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      let c := T20.dyCenter K b
      let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
      2 * r ≤ c.im → c.im + 2 * r ≤ 1 → c.re + 2 * r ≤ 1 →
      ∀ γ : ℝ → ℂ,
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
        (rectAB 1 1).side₂ γ →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
      ∀ m : ℝ, m ∈ Icc (0 : ℝ) 1 → dist (γ m) c ≤ r →
      2 * r ≤ dist (γ 1) c →
      let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
      D.aroundDist A (sphere c r) (sphere c (2 * r)) ≠ ⊤ →
      (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
        (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal +
          (D.aroundDist A (sphere c r) (sphere c (2 * r))).toReal := by
  filter_upwards [laneC_physical_left_vertical_resampling_le_around_of_lt
      hW Q ξ hKn hσ hr hr0 hrSmall] with z hz
  intro b hb
  dsimp only
  intro hclo hchi hcri γ hγ hγfin m hm hmid hend hfin
  let c := T20.dyCenter K b
  let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
  let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
  apply le_of_forall_pos_le_add
  intro η hη
  have hM : 0 < (D.aroundDist A (sphere c r) (sphere c (2 * r))).toReal + η :=
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hη
  have hlt : D.aroundDist A (sphere c r) (sphere c (2 * r)) <
      ENNReal.ofReal ((D.aroundDist A (sphere c r) (sphere c (2 * r))).toReal + η) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 (lt_add_of_pos_right _ hη)
  simpa only [add_assoc] using
    (hz b hb hclo hchi hcri γ hγ hγfin m hm hmid hend _ hM hlt)

end SupercriticalLQGUniqueness.B2.DG20Conc
