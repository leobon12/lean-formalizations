import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerSourceArc
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalContinuousLimit
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneC_physical_upper_left_resampling_le_around_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
      (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) (hr0 : 0 < r) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      let c := T20.dyCenter K b
      let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
      0 ≤ c.re → c.re ≤ r →
      c.im ≤ 1 → 1 - c.im ≤ r →
      2 * r ≤ c.im → c.re + 2 * r ≤ 1 →
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
  intro hc0 hcr hci hct hcb hcright γ hγ hγfin m hm hmid hend M hM haround
  let c := T20.dyCenter K b
  let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
  let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
  obtain ⟨a, d, ρ, had, hρcont, hρA, hsep, hρlen⟩ :=
    laneC_exists_around_witness_of_lt D A
      (sphere c r) (sphere c (2 * r)) haround
  obtain ⟨z₀, hz₀, z₁, hz₁, hpath, hγsq⟩ := hγ
  obtain ⟨δ, t₁, ht₁, hδ, hδcar, hδleft, hhit, hsafe, hcost⟩ :=
    laneC_upper_left_source_separator_arc D had hρcont hr0
      (by intro x hx; exact hρA ⟨x, hx, rfl⟩) hend hsep
      hc0 hcr hci hct hcb hcright
      hpath.continuousOn hγsq
      (by simpa only [hpath.target] using (mem_rectAB_side₂.mp hz₁).1) hm hmid
  have hδring : ∀ t ∈ Icc (0 : ℝ) 1,
      r < dist (δ t) c ∧ dist (δ t) c < 2 * r :=
    fun t ht => ⟨(hδcar t ht).1, (hδcar t ht).2.1⟩
  have hδsq : ∀ t ∈ Icc (0 : ℝ) 1, δ t ∈ (rectAB 1 1).toSet :=
    fun t ht => (hδcar t ht).2.2
  have hδM : D.len δ 0 1 < ENNReal.ofReal M := lt_of_le_of_lt hcost hρlen
  exact hz b hb δ γ hδ hδring hδsq
    ⟨z₀, hz₀, z₁, hz₁, hpath, hγsq⟩ hγfin M hM hδM
    0 t₁ (by simp) ⟨hm.1.trans ht₁.1, ht₁.2⟩
    (hm.1.trans ht₁.1) (Or.inr ⟨rfl, hδleft⟩) (Or.inl ⟨hhit, hsafe⟩)

theorem laneC_physical_upper_left_resampling_le_around
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
      (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) (hr0 : 0 < r) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      let c := T20.dyCenter K b
      let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
      0 ≤ c.re → c.re ≤ r →
      c.im ≤ 1 → 1 - c.im ≤ r →
      2 * r ≤ c.im → c.re + 2 * r ≤ 1 →
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
  filter_upwards [laneC_physical_upper_left_resampling_le_around_of_lt
      hW Q ξ hKn hσ hr hr0] with z hz
  intro b hb
  dsimp only
  intro hc0 hcr hci hct hcb hcright γ hγ hγfin m hm hmid hend hfin
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
    (hz b hb hc0 hcr hci hct hcb hcright γ hγ hγfin m hm hmid hend _ hM hlt)

end SupercriticalLQGUniqueness.B2.DG20Conc
