import HigherDimLQGMetric.Coord.Lemma25

/-! # Attainment for confined weighted distances -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

theorem tendsto_ennreal_of_additive_bounds
    {a : ℝ≥0∞} {u : ℕ → ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      u n ≤ a + ENNReal.ofReal ε ∧ a ≤ u n + ENNReal.ofReal ε) :
    Tendsto u atTop (𝓝 a) := by
  apply ENNReal.tendsto_nhds_of_Icc
  intro ε hε
  by_cases htop : ε = ∞
  · simp [htop]
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hr : 0 < ε.toReal := ENNReal.toReal_pos hε0 htop
  have heq : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal htop
  filter_upwards [h ε.toReal hr] with n hn
  rw [← heq]
  exact ⟨(tsub_le_iff_right).2 hn.2, hn.1⟩

theorem confined_distance_tendsto_of_uniform_bounds
    {X : Type*} {Y : Set X}
    (Dseq : ℕ → X → X → ℝ≥0∞) (D : X → X → ℝ≥0∞)
    (xseq yseq : ℕ → X) (x y : X)
    (hmem : ∀ n, xseq n ∈ Y ∧ yseq n ∈ Y)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a ∈ Y, ∀ b ∈ Y,
      Dseq n a b ≤ D a b + ENNReal.ofReal ε ∧
      D a b ≤ Dseq n a b + ENNReal.ofReal ε)
    (hcont : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      D (xseq n) (yseq n) ≤ D x y + ENNReal.ofReal ε ∧
      D x y ≤ D (xseq n) (yseq n) + ENNReal.ofReal ε) :
    Tendsto (fun n => Dseq n (xseq n) (yseq n)) atTop (𝓝 (D x y)) := by
  apply tendsto_ennreal_of_additive_bounds
  intro ε hε
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsum : ENNReal.ofReal η + ENNReal.ofReal η = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hη.le hη.le]
    congr 1
    dsimp [η]
    ring
  filter_upwards [huni η hη, hcont η hη] with n hu hc
  obtain ⟨hu₁, hu₂⟩ := hu (xseq n) (hmem n).1 (yseq n) (hmem n).2
  constructor
  · calc
      Dseq n (xseq n) (yseq n) ≤ D (xseq n) (yseq n) + ENNReal.ofReal η := hu₁
      _ ≤ (D x y + ENNReal.ofReal η) + ENNReal.ofReal η := add_le_add hc.1 le_rfl
      _ = D x y + ENNReal.ofReal ε := by rw [add_assoc, hηsum]
  · calc
      D x y ≤ D (xseq n) (yseq n) + ENNReal.ofReal η := hc.2
      _ ≤ (Dseq n (xseq n) (yseq n) + ENNReal.ofReal η) + ENNReal.ofReal η :=
        add_le_add hu₂ le_rfl
      _ = Dseq n (xseq n) (yseq n) + ENNReal.ofReal ε := by rw [add_assoc, hηsum]

theorem eventually_cost_le_real_bound
    (Dseq : ℕ → ℝ≥0∞) (D : ℝ≥0∞) (hDfin : D ≠ ∞)
    (hD : Tendsto Dseq atTop (𝓝 D))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (cost : ℕ → ℝ≥0∞)
    (hcost : ∀ n, cost n ≤ Dseq n + ENNReal.ofReal (e n)) :
    ∀ᶠ n in atTop, cost n ≤ ENNReal.ofReal (D.toReal + 2) := by
  have hDlt : D < D + ENNReal.ofReal (1 : ℝ) :=
    ENNReal.lt_add_right hDfin (by norm_num)
  have hDbd : ∀ᶠ n in atTop, Dseq n ≤ D + ENNReal.ofReal (1 : ℝ) :=
    (hD.eventually (gt_mem_nhds hDlt)).mono (fun n hn => hn.le)
  have hebd : ∀ᶠ n in atTop, e n ≤ 1 :=
    (he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun n hn => hn.le)
  filter_upwards [hDbd, hebd] with n hdn hen
  have hnonneg : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  calc
    cost n ≤ Dseq n + ENNReal.ofReal (e n) := hcost n
    _ ≤ (D + ENNReal.ofReal (1 : ℝ)) + ENNReal.ofReal (1 : ℝ) := by
      exact add_le_add hdn (ENNReal.ofReal_le_ofReal hen)
    _ = (ENNReal.ofReal D.toReal + ENNReal.ofReal (1 : ℝ)) +
        ENNReal.ofReal (1 : ℝ) := by rw [ENNReal.ofReal_toReal hDfin]
    _ = ENNReal.ofReal (D.toReal + 2) := by
      rw [← ENNReal.ofReal_add hnonneg (by norm_num : (0 : ℝ) ≤ 1)]
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ D.toReal + 1)
        (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      ring

theorem eventually_coordinate_speed_of_weighted_speed
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (hρ : ∀ n, IsCoordinate (ρ n))
    (w : X → ℝ) (P : ℕ → I →ᵇ X)
    {m B : ℝ} (hm : 0 < m) (hB : 0 ≤ B)
    (hw : ∀ n t, m ≤ w (P n t))
    (hspeed : ∀ n : ℕ, ∀ s t : I, (s : ℝ) ≤ t →
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) s t ≤
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 *
        ENNReal.ofReal ((t : ℝ) - s))
    (hbound : ∀ᶠ n in atTop,
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 ≤ ENNReal.ofReal B) :
    ∀ᶠ n in atTop, ∀ s t : I,
      ρ n (P n s, P n t) ≤ (B / m) * dist s t := by
  filter_upwards [hbound] with n hbn s t
  apply weighted_speed_coordinate_speed (ρ n) (hρ n).metric w (P n) hm hB
    (hw n)
  intro a b hab
  calc
    weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) a b ≤
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 *
        ENNReal.ofReal ((b : ℝ) - a) := hspeed n a b hab
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal ((b : ℝ) - a) := by
      gcongr
    _ = ENNReal.ofReal (B * ((b : ℝ) - a)) := (ENNReal.ofReal_mul hB).symm

theorem confined_attainment_of_distance_convergence
    {X : Type*} [MetricSpace X] {Y' : Set X} (hY'c : IsCompact Y')
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n))
    (hconv : TendstoUniformlyOn ρ ρlim atTop (Y' ×ˢ Y'))
    (hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      ∀ n, ∀ u ∈ Y', ∀ v ∈ Y', ρ n (u, v) < b → dist u v < χ)
    (w : X → ℝ) (hw : ContinuousOn w Y')
    (hpos : ∀ z ∈ Y', 0 < w z)
    (xseq yseq : ℕ → X) (x y : X)
    (hxn : Tendsto xseq atTop (𝓝 x)) (hyn : Tendsto yseq atTop (𝓝 y))
    (Dseq : ℕ → ℝ≥0∞) (D : ℝ≥0∞)
    (hD : Tendsto Dseq atTop (𝓝 D)) (hDfin : D ≠ ∞)
    (P : ℕ → I →ᵇ X) (hPY : ∀ n t, P n t ∈ Y')
    (hP0 : ∀ n, P n 0 = xseq n) (hP1 : ∀ n, P n 1 = yseq n)
    (hspeed : ∀ n : ℕ, ∀ s t : I, (s : ℝ) ≤ t →
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) s t ≤
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 *
        ENNReal.ofReal ((t : ℝ) - s))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcost : ∀ n,
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 ≤ Dseq n + ENNReal.ofReal (e n))
    (hlower : ∀ Q : I →ᵇ X, (∀ t, Q t ∈ Y') → Q 0 = x → Q 1 = y →
      D ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ Y') ∧ Q 0 = x ∧ Q 1 = y ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 = D ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n t => P (φ n) t) Q atTop := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := compact_positive_weight_bounds hY'c hw hpos
  have hB : 0 ≤ D.toReal + 2 := by have := ENNReal.toReal_nonneg (a := D); positivity
  have hcostBound := eventually_cost_le_real_bound Dseq D hDfin hD e he
    (fun n => weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
      (Set.IccExtend zero_le_one (P n)) 0 1) hcost
  have hspeedEventually := eventually_coordinate_speed_of_weighted_speed ρ hρ w P
    hm hB (fun n t => (hbounds (P n t) (hPY n t)).1) hspeed hcostBound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hspeedEventually
  let ns : ℕ → ℕ := fun k => k + N
  have hns : Tendsto ns atTop atTop := tendsto_add_atTop_nat N
  have hNspeed : ∀ k s t, ρ (ns k) (P (ns k) s, P (ns k) t) ≤
      ((D.toReal + 2) / m) * dist s t := by
    intro k s t
    exact hN (ns k) (by dsimp [ns]; omega) s t
  have hmodtail : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      ∀ k, ∀ u ∈ Y', ∀ v ∈ Y', ρ (ns k) (u, v) < b → dist u v < χ := by
    intro χ hχ
    obtain ⟨b, hb, hmb⟩ := hmod χ hχ
    exact ⟨b, hb, fun k => hmb (ns k)⟩
  obtain ⟨Q, hQY, hQ0, hQ1, hQcost, φ, hφ, hPconv⟩ :=
    lemma25b_of_distance_convergence hY'c (fun k => ρ (ns k)) ρlim
      (fun k => (hρ (ns k)).continuous.continuousOn)
      (tendstoUniformlyOn_subseq hconv ns hns) hmodtail w hw
      (fun k => xseq (ns k)) (fun k => yseq (ns k)) x y
      (hxn.comp hns) (hyn.comp hns)
      (fun k => Dseq (ns k)) D (hD.comp hns) hDfin
      (fun k => P (ns k)) (fun k t => hPY (ns k) t)
      (fun k => hP0 (ns k)) (fun k => hP1 (ns k))
      ((D.toReal + 2) / m) hNspeed
      (fun k => e (ns k)) (he.comp hns) (fun k => hcost (ns k)) hlower
  refine ⟨Q, hQY, hQ0, hQ1, hQcost, ns ∘ φ, ?_, ?_⟩
  · intro a b hab
    dsimp [ns, Function.comp_def]
    exact Nat.add_lt_add_right (hφ hab) N
  · simpa only [Function.comp_def] using hPconv

end HigherDimLQGMetric
