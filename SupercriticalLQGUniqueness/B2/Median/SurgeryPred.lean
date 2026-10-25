import SupercriticalLQGUniqueness.B2.Median.Cutting
import SupercriticalLQGUniqueness.B2.Median.Chain
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas

 
















set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 
def ratRect (u₀ : ℝ) (q : ℚ × ℚ × ℚ × ℚ) : Set ℂ :=
  {z | (q.1 : ℝ) ≤ z.re ∧ z.re ≤ (q.2.1 : ℝ) ∧
    (q.2.2.1 : ℝ) - u₀ ≤ z.im ∧ z.im ≤ (q.2.2.2 : ℝ) - u₀}

 


def SideRemovable (d : LSCMetric) (u₀ : ℝ) : Prop :=
  ∀ V E F : ℚ × ℚ × ℚ × ℚ,
    ContinuousAt (upperPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F)) 0 ∧
    ContinuousAt (lowerPathInf d (ratRect u₀ V) (ratRect u₀ E) (ratRect u₀ F)) 1

 




def GoodLoops (d : LSCMetric) : Prop :=
  ∀ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b → Bornology.IsBounded (P '' Icc a b) →
    d.len P a b ≠ ∞ → P a ≠ P b →
    ∀ ρ η : ℝ, 0 < ρ → 0 < η →
      ∃ (c : ℂ) (r : ℝ), 0 < r ∧ 3 * r < ρ ∧ dist (P a) c < r ∧
        ∃ (L : ℝ → ℂ) (s t : ℝ), d.IsCurve L s t ∧
          (∀ u ∈ Icc s t, r < dist (L u) c ∧ dist (L u) c < 2 * r) ∧
          Disconnects (L '' Icc s t) (sphere c r) (sphere c (2 * r)) ∧
          d.len L s t < ENNReal.ofReal η

theorem isCompact_ratRect (u₀ : ℝ) (q : ℚ × ℚ × ℚ × ℚ) : IsCompact (ratRect u₀ q) := by
  have hb : Bornology.IsBounded (ratRect u₀ q) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
      ⟨|(q.1 : ℝ)| + |(q.2.1 : ℝ)| + |(q.2.2.1 : ℝ) - u₀| + |(q.2.2.2 : ℝ) - u₀|, ?_⟩
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    have h1 : |z.re| ≤ |(q.1 : ℝ)| + |(q.2.1 : ℝ)| := by
      rw [abs_le]; constructor <;>
        cases abs_cases (q.1 : ℝ) <;> cases abs_cases (q.2.1 : ℝ) <;> linarith [hz.1, hz.2.1]
    have h2 : |z.im| ≤ |(q.2.2.1 : ℝ) - u₀| + |(q.2.2.2 : ℝ) - u₀| := by
      rw [abs_le]; constructor <;>
        cases abs_cases ((q.2.2.1 : ℝ) - u₀) <;> cases abs_cases ((q.2.2.2 : ℝ) - u₀) <;>
          linarith [hz.2.2.1, hz.2.2.2]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ _ := by linarith
  have hc : IsClosed (ratRect u₀ q) := by
    have hre : Continuous fun z : ℂ => z.re := Complex.continuous_re
    have him : Continuous fun z : ℂ => z.im := Complex.continuous_im
    exact (isClosed_le continuous_const hre).inter ((isClosed_le hre continuous_const).inter
      ((isClosed_le continuous_const him).inter (isClosed_le him continuous_const)))
  exact Metric.isCompact_of_isClosed_isBounded hc hb

 

theorem exists_ratRect_mem_subset_ball (u₀ : ℝ) {a c : ℂ} {r : ℝ}
    (h : dist a c < r) :
    ∃ q : ℚ × ℚ × ℚ × ℚ, a ∈ ratRect u₀ q ∧ ratRect u₀ q ⊆ ball c r := by
  set ε := (r - dist a c) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨x₁, hx₁⟩ := exists_rat_btwn (show a.re - ε < a.re by linarith)
  obtain ⟨x₂, hx₂⟩ := exists_rat_btwn (show a.re < a.re + ε by linarith)
  obtain ⟨y₁, hy₁⟩ := exists_rat_btwn (show a.im + u₀ - ε < a.im + u₀ by linarith)
  obtain ⟨y₂, hy₂⟩ := exists_rat_btwn (show a.im + u₀ < a.im + u₀ + ε by linarith)
  refine ⟨(x₁, x₂, y₁, y₂), ⟨hx₁.2.le, hx₂.1.le, by linarith [hy₁.2], by linarith [hy₂.1]⟩, ?_⟩
  intro z hz
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have hre : |z.re - a.re| ≤ ε := by
    rw [abs_le]; constructor <;> linarith [hx₁.1, hx₂.2]
  have him : |z.im - a.im| ≤ ε := by
    rw [abs_le]; constructor <;> simp only at hz3 hz4 <;> linarith [hy₁.1, hy₂.2]
  have hza : dist z a ≤ 2 * ε := by
    rw [Complex.dist_eq]
    calc ‖z - a‖ ≤ |(z - a).re| + |(z - a).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re - a.re| + |z.im - a.im| := by simp
      _ ≤ 2 * ε := by linarith
  rw [mem_ball]
  calc dist z c ≤ dist z a + dist a c := dist_triangle z a c
    _ ≤ 2 * ε + dist a c := by linarith
    _ < r := by rw [hε]; linarith

 

theorem meets_of_crosses_annulus {K : Set ℂ} {P : ℝ → ℂ} {s t : ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hst : s ≤ t) (hP : ContinuousOn P (Icc s t))
    (hK : Disconnects K (sphere c r) (sphere c (2 * r)))
    {u v : ℝ} (hu : u ∈ Icc s t) (hv : v ∈ Icc s t)
    (hin : P u ∈ closedBall c r) (hout : P v ∉ ball c (2 * r)) :
    (K ∩ P '' Icc s t).Nonempty := by
  have hX : IsPathConnected (P '' Icc s t) :=
    ((convex_Icc s t).isPathConnected (nonempty_Icc.mpr hst)).image' hP
  exact SupercriticalLQGUniqueness.disconnects_meets_pathConnected_crossing
    (by linarith) hK hX ⟨P u, ⟨u, hu, rfl⟩, hin⟩ ⟨P v, ⟨v, hv, rfl⟩, hout⟩

 

theorem exists_left_point_of_disconnects {K : Set ℂ} {s₀ c : ℂ} {r : ℝ} (hr : 0 < r)
    (hs₀ : dist s₀ c < r) (hK : Disconnects K (sphere c r) (sphere c (2 * r)))
    (hKout : ∀ q ∈ K, r < dist q c) :
    ∃ q ∈ K, q.re < s₀.re ∧ q.im = s₀.im ∧ dist q s₀ ≤ 3 * r := by
  let P : ℝ → ℂ := fun x => s₀ - (x : ℂ)
  have hPc : ContinuousOn P (Icc 0 (3 * r)) :=
    (continuous_const.sub Complex.continuous_ofReal).continuousOn
  have hin : P 0 ∈ closedBall c r := by
    simp only [P, Complex.ofReal_zero, sub_zero, mem_closedBall]; exact hs₀.le
  have hout : P (3 * r) ∉ ball c (2 * r) := by
    simp only [P, mem_ball, not_lt]
    have h1 : dist (s₀ - ((3 * r : ℝ) : ℂ)) s₀ = 3 * r := by
      rw [Complex.dist_eq]; simp [abs_of_pos hr]
    have := dist_triangle (s₀ - ((3 * r : ℝ) : ℂ)) c s₀
    rw [dist_comm c s₀] at this
    linarith
  obtain ⟨q, hqK, x, hx, rfl⟩ := meets_of_crosses_annulus hr (by linarith) hPc hK
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ hin hout
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hKout _ hqK
    simp only [P, Complex.ofReal_zero, sub_zero] at this
    linarith
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  refine ⟨P x, hqK, ?_, ?_, ?_⟩
  · simp [P]; linarith
  · simp [P]
  · simp only [P]
    rw [Complex.dist_eq]
    simp [abs_of_pos hxpos]
    linarith [hx.2]

 
theorem exists_right_point_of_disconnects {K : Set ℂ} {s₀ c : ℂ} {r : ℝ} (hr : 0 < r)
    (hs₀ : dist s₀ c < r) (hK : Disconnects K (sphere c r) (sphere c (2 * r)))
    (hKout : ∀ q ∈ K, r < dist q c) :
    ∃ q ∈ K, s₀.re < q.re ∧ q.im = s₀.im ∧ dist q s₀ ≤ 3 * r := by
  let P : ℝ → ℂ := fun x => s₀ + (x : ℂ)
  have hPc : ContinuousOn P (Icc 0 (3 * r)) :=
    (continuous_const.add Complex.continuous_ofReal).continuousOn
  have hin : P 0 ∈ closedBall c r := by
    simp only [P, Complex.ofReal_zero, add_zero, mem_closedBall]; exact hs₀.le
  have hout : P (3 * r) ∉ ball c (2 * r) := by
    simp only [P, mem_ball, not_lt]
    have h1 : dist (s₀ + ((3 * r : ℝ) : ℂ)) s₀ = 3 * r := by
      rw [Complex.dist_eq]; simp [abs_of_pos hr]
    have := dist_triangle (s₀ + ((3 * r : ℝ) : ℂ)) c s₀
    rw [dist_comm c s₀] at this
    linarith
  obtain ⟨q, hqK, x, hx, rfl⟩ := meets_of_crosses_annulus hr (by linarith) hPc hK
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ hin hout
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hKout _ hqK
    simp only [P, Complex.ofReal_zero, add_zero] at this
    linarith
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  refine ⟨P x, hqK, ?_, ?_, ?_⟩
  · simp [P]; linarith
  · simp [P]
  · simp only [P]
    rw [Complex.dist_eq]
    simp [abs_of_pos hxpos]
    linarith [hx.2]

end SupercriticalLQGUniqueness.B2.Median
