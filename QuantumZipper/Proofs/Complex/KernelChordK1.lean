import QuantumZipper.Proofs.Complex.KernelChordDoubled

/-!
# KT2 input K, part 1: chordal versus Euclidean closeness of chords

Elementary lemmas for `LeftDoubledKernel`: chordal closeness to a bounded point gives Euclidean
closeness (`norm_sub_lt_of_chordalDist_lt`); under sphere-uniform convergence the chords
`η n` eventually keep away from a compact set that the limit chord keeps away from
(`eventually_le_dist_chord`); a disk around a negative real point that misses the chord lies,
in `ℍ`, in the left component (`inter_ball_subset_leftComponent`) and entirely in the doubled
domain (`ball_subset_leftDoubled`); a preconnected set meeting an open set and its complement
meets its frontier (`inter_frontier_nonempty_of_isPreconnected`).

Own elementary proofs (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open QuantumZipper.CA.Uniformizer
open scoped ComplexConjugate

namespace QuantumZipper.CA.Kernel

theorem chordalDist_comm (z w : ℂ) : chordalDist z w = chordalDist w z := by
  unfold chordalDist; rw [norm_sub_rev, mul_comm (Real.sqrt _)]

theorem sqrt_one_add_sq_le {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (1 + a ^ 2) ≤ 1 + a :=
  (Real.sqrt_le_left (by linarith)).2 (by nlinarith)

/-- Chordal closeness to a point of norm `≤ R` gives Euclidean closeness. -/
theorem norm_sub_lt_of_chordalDist_lt {z w : ℂ} {ε R : ℝ} (h : chordalDist z w < ε)
    (hz : ‖z‖ ≤ R) (hε : ε * (1 + R) ≤ 1) : ‖z - w‖ < ε * (1 + R) ^ 2 := by
  set d := ‖z - w‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hz
  have hA : Real.sqrt (1 + ‖z‖ ^ 2) ≤ 1 + R :=
    (sqrt_one_add_sq_le (norm_nonneg z)).trans (by linarith)
  have hw : ‖w‖ ≤ R + d := by
    have := norm_sub_norm_le w z
    rw [norm_sub_rev] at this
    linarith
  have hB : Real.sqrt (1 + ‖w‖ ^ 2) ≤ 1 + R + d :=
    (sqrt_one_add_sq_le (norm_nonneg w)).trans (by linarith)
  have hApos : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hBpos : 0 < Real.sqrt (1 + ‖w‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hc0 : 0 ≤ chordalDist z w := by unfold chordalDist; positivity
  have hε0 : 0 ≤ ε := hc0.trans h.le
  unfold chordalDist at h
  rw [div_lt_iff₀ (mul_pos hApos hBpos)] at h
  have h2 : ε * (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2)) ≤
      ε * ((1 + R) * (1 + R + d)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hA hB hBpos.le (by linarith)) hε0
  have h3 : ε * (1 + R) * d ≤ d := by nlinarith
  nlinarith

theorem exists_eps_chordal {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ ε > 0, ε * (1 + R) ≤ 1 ∧ ε * (1 + R) ^ 2 ≤ δ / 2 := by
  have h1 : 0 < 1 + R := by linarith
  refine ⟨min (1 / (1 + R)) (δ / 2 / (1 + R) ^ 2), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · calc min (1 / (1 + R)) (δ / 2 / (1 + R) ^ 2) * (1 + R) ≤ 1 / (1 + R) * (1 + R) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) h1.le
      _ = 1 := by field_simp
  · calc min (1 / (1 + R)) (δ / 2 / (1 + R) ^ 2) * (1 + R) ^ 2 ≤
          δ / 2 / (1 + R) ^ 2 * (1 + R) ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = δ / 2 := by field_simp

/-- Under sphere-uniform convergence, `η n t → ηi t` for each `t ≥ 0`. -/
theorem tendsto_of_sphereUniformConv {η : ℕ → ℝ → ℂ} {ηi : ℝ → ℂ}
    (hc : SphereUniformConv η ηi) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => η n t) atTop (𝓝 (ηi t)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε, hε, hε1, hε2⟩ := exists_eps_chordal (norm_nonneg (ηi t)) hδ
  filter_upwards [hc ε hε] with n hn
  have h := norm_sub_lt_of_chordalDist_lt (z := ηi t) (w := η n t)
    (by rw [chordalDist_comm]; exact hn t ht) le_rfl hε1
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Under sphere-uniform convergence, the chords `η n` eventually keep distance `δ/2` from a
bounded set that the limit chord keeps distance `δ` from. -/
theorem eventually_le_dist_chord {η : ℕ → ℝ → ℂ} {ηi : ℝ → ℂ} (hc : SphereUniformConv η ηi)
    {K : Set ℂ} {R δ : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (hKR : ∀ z ∈ K, ‖z‖ ≤ R)
    (hK : ∀ z ∈ K, ∀ t ≥ (0 : ℝ), δ ≤ dist z (ηi t)) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ∀ t ≥ (0 : ℝ), δ / 2 ≤ dist z (η n t) := by
  obtain ⟨ε, hε, hε1, hε2⟩ := exists_eps_chordal (R := R + δ / 2) (by linarith) hδ
  filter_upwards [hc ε hε] with n hn z hz t ht
  by_contra hlt
  push Not at hlt
  have hb : ‖η n t‖ ≤ R + δ / 2 := by
    have := norm_sub_norm_le (η n t) z
    rw [← dist_eq_norm, dist_comm] at this
    linarith [hKR z hz]
  have h1 := norm_sub_lt_of_chordalDist_lt (hn t ht) hb hε1
  have h2 := dist_triangle z (η n t) (ηi t)
  rw [dist_eq_norm (η n t)] at h2
  linarith [hK z hz t ht]

/-- A disk around a negative real point that misses the chord lies, in `ℍ`, in the left
component (segment to the centre). -/
theorem inter_ball_subset_leftComponent {η : ℝ → ℂ} {x r : ℝ} (hx : x < 0)
    (hK : ∀ t ≥ (0 : ℝ), η t ∉ ball (x : ℂ) r) : H ∩ ball (x : ℂ) r ⊆ leftComponent η := by
  rintro z ⟨hzH, hzB⟩
  have hslit : ∀ w ∈ H ∩ ball (x : ℂ) r, w ∈ H \ η '' Ici 0 := fun w hw =>
    ⟨hw.1, by rintro ⟨t, ht, rfl⟩; exact hK t ht hw.2⟩
  refine ⟨hslit z ⟨hzH, hzB⟩, x, hx, Path.segment z x, fun t ht => hslit _ ⟨?_, ?_⟩⟩
  · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht (Subtype.ext h)
    have hz : 0 < z.im := hzH
    show 0 < (AffineMap.lineMap z (x : ℂ) (t : ℝ)).im
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_im, smul_im, sub_im, ofReal_im, smul_eq_mul]
    have h0 : 0 ≤ (t : ℝ) := t.2.1
    nlinarith
  · show AffineMap.lineMap z (x : ℂ) (t : ℝ) ∈ ball (x : ℂ) r
    rw [mem_ball, dist_lineMap_right]
    have h0 : 0 ≤ (t : ℝ) := t.2.1
    have h1 : (t : ℝ) ≤ 1 := t.2.2
    have hn : ‖(1 : ℝ) - (t : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    calc ‖(1 : ℝ) - (t : ℝ)‖ * dist z (x : ℂ) ≤ 1 * dist z (x : ℂ) :=
          mul_le_mul_of_nonneg_right hn dist_nonneg
      _ < r := by rw [one_mul]; exact hzB

/-- A disk around a negative real point that misses the chord lies in the doubled domain. -/
theorem ball_subset_leftDoubled {η : ℝ → ℂ} {x r : ℝ} (hx : x < 0) (hr : r ≤ -x)
    (hK : ∀ t ≥ (0 : ℝ), η t ∉ ball (x : ℂ) r) : ball (x : ℂ) r ⊆ leftDoubled η := by
  have h := inter_ball_subset_leftComponent hx hK
  intro w hw
  rcases lt_trichotomy w.im 0 with him | him | him
  · refine Or.inl (Or.inr ⟨conj w, h ⟨?_, ?_⟩, conj_conj w⟩)
    · show 0 < (conj w).im; rw [conj_im]; linarith
    · rw [mem_ball, ← conj_ofReal, dist_conj_conj]; exact hw
  · refine Or.inr ⟨him, ?_⟩
    have : |w.re - x| < -x := by
      have := abs_re_le_norm (w - x)
      rw [mem_ball, dist_eq_norm] at hw
      simp only [sub_re, ofReal_re] at this
      linarith
    have := (abs_lt.1 this).2
    linarith
  · exact Or.inl (Or.inl (h ⟨him, hw⟩))

/-- A preconnected set meeting an open set and its complement meets its frontier. -/
theorem inter_frontier_nonempty_of_isPreconnected {S G : Set ℂ} (hS : IsPreconnected S)
    (hG : IsOpen G) {z a : ℂ} (hzS : z ∈ S) (hzG : z ∈ G) (haS : a ∈ S) (haG : a ∉ G) :
    (S ∩ frontier G).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : S ⊆ G ∪ (closure G)ᶜ := fun y hy => by
    by_cases hyG : y ∈ G
    · exact Or.inl hyG
    · right; intro hyc
      have : y ∈ S ∩ frontier G := ⟨hy, by rw [hG.frontier_eq]; exact ⟨hyc, hyG⟩⟩
      rw [hne] at this; exact this
  have ha : a ∈ (closure G)ᶜ := (hsub haS).resolve_left haG
  obtain ⟨y, -, hy1, hy2⟩ := hS G (closure G)ᶜ hG isClosed_closure.isOpen_compl hsub
    ⟨z, hzS, hzG⟩ ⟨a, haS, ha⟩
  exact hy2 (subset_closure hy1)

/-- Chord points are not in the doubled domain. -/
theorem chord_notMem_leftDoubled {η : ℝ → ℂ} (hη : IsSimpleChord η) {t : ℝ} (ht : 0 ≤ t) :
    η t ∉ leftDoubled η ∧ conj (η t) ∉ leftDoubled η := by
  have hHbar : 0 ≤ (η t).im := by
    rcases ht.eq_or_lt with rfl | ht'
    · rw [hη.1]; simp
    · exact (hη.2.2.2.1 t ht').le
  have hreal : (η t).im = 0 → η t = 0 := fun h0 => by
    rcases ht.eq_or_lt with rfl | ht'
    · exact hη.1
    · have : 0 < (η t).im := hη.2.2.2.1 t ht'
      linarith
  have hch : η t ∉ leftComponent η := fun h => h.1.2 ⟨t, ht, rfl⟩
  constructor
  · rintro ((h | ⟨w, hw, hwe⟩) | ⟨h0, hneg⟩)
    · exact hch h
    · have h1 : 0 < w.im := leftComponent_subset_H η hw
      have : (η t).im = -w.im := by rw [← hwe, conj_im]
      linarith
    · rw [hreal h0] at hneg; simp at hneg
  · rintro ((h | ⟨w, hw, hwe⟩) | ⟨h0, hneg⟩)
    · have h1 : 0 < (conj (η t)).im := leftComponent_subset_H η h
      rw [conj_im] at h1; linarith
    · have : w = η t := by rw [← conj_conj w, hwe, conj_conj]
      exact hch (this ▸ hw)
    · rw [conj_im] at h0
      rw [hreal (by linarith)] at hneg; simp at hneg

/-- Non-negative reals are not in the doubled domain. -/
theorem nonneg_notMem_leftDoubled (η : ℝ → ℂ) {w : ℂ} (h0 : w.im = 0) (hre : 0 ≤ w.re) :
    w ∉ leftDoubled η := by
  rintro ((h | ⟨v, hv, hve⟩) | ⟨-, hneg⟩)
  · have : 0 < w.im := leftComponent_subset_H η h
    linarith
  · have h1 : 0 < v.im := leftComponent_subset_H η hv
    have : w.im = -v.im := by rw [← hve, conj_im]
    linarith
  · linarith

theorem zero_mem_frontier_leftDoubled {η : ℝ → ℂ} (hη : IsSimpleChord η) :
    (0 : ℂ) ∈ frontier (leftDoubled η) := by
  rw [(isOpen_leftDoubled hη).frontier_eq]
  exact ⟨closure_mono (leftComponent_subset_leftDoubled η) (zero_mem_closure_leftComponent hη),
    nonneg_notMem_leftDoubled η (by simp) (by simp)⟩

end QuantumZipper.CA.Kernel
