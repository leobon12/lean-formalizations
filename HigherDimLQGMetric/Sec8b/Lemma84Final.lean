import HigherDimLQGMetric.Sec8b.Lemma84Parameters

/-! Uniform parameter choice in [S] Lemma 8.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- For a nonempty trap family, the pruning fraction is positive and at most one. -/
theorem s7b_pruning_fraction_bounds {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt) (hξ : 0 < ξ)
    (hJ : 0 < T.J) :
    0 < T.g / (4 * T.H) ∧ T.g / (4 * T.H) ≤ 1 := by
  rcases T.constants with ⟨ha, _, _, hg, hH, _, _⟩
  have hMf : 0 ≤ T.Mf := by
    rcases T.bumps 0 hJ with ⟨_, _, _, hnonneg, _, hupper⟩
    have h0 := hnonneg 0
    have h1 := hupper 0
    linarith only [h0, h1]
  have hexp : 1 ≤ Real.exp (ξ * T.Mf) :=
    Real.one_le_exp (mul_nonneg hξ.le hMf)
  have hHpos : 0 < T.H := by rw [hH]; positivity
  have hgpos : 0 < T.g := by rw [hg]; exact ha
  constructor
  · exact div_pos hgpos (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < 4 * T.H)).mpr
    rw [hg, hH]
    have hmul := mul_le_mul_of_nonneg_left hexp ha.le
    nlinarith only [hmul, ha]

/-- If there are no trap labels, the common covering event is empty. -/
theorem s7b_cover_implies_Jpos {ξ Q ε R : ℝ}
    {D Dt : DistRd d → ContMetric d} {J : ℕ}
    {N : ℕ → Set (Config d)} (hR : 0 < R) (g : DistRd d)
    (hc : g ∈ sec8CoverEvent D Dt ξ Q J N ε R) : 0 < J := by
  have hzero : (0 : Rd d) ∈ ball 0 (5 * R) := by
    simp only [Metric.mem_ball, dist_self]
    positivity
  obtain ⟨j, _, k, _, hsite⟩ := hc 0 hzero
  obtain ⟨label, hlabel, _⟩ := hsite
  omega

/-- A uniform sampling threshold; it is independent of `k`, `R`, the field,
and the deterministic endpoints. -/
theorem s7b_exists_sampling_threshold (d : ℕ) {B η : ℝ}
    (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {ε R : ℝ}, (hε : 0 < ε) → ε < ε₀ → (hR : 0 < R) →
        0 ≤ B → ε < η / 18 ∧ ε ≤ 1 / 2 ∧
          (s7b_classSet d hε hR B).card *
            ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ ≤ s7b_sampleCount η ε := by
  obtain ⟨εc, hεc, hc⟩ := s7b_exists_class_threshold d hη
  let ε₀ := min εc (min (η / 18) (1 / 2))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε R hε hεlt hR hB
  have hc' : ε < εc := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hη' : ε < η / 18 :=
    lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_left _ _))
  have hhalf : ε ≤ 1 / 2 :=
    (le_of_lt hεlt).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by linarith only [hhalf]
  exact ⟨hη', hhalf, hc hε hc' hε1 hR hB⟩

/-- [S] Lemma 8.4. A class with at least the required favorable-set count
exists on the common covering and bin event. -/
theorem lemma84 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs B η : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hη : 0 < η) (hη1 : η ≤ 1) (hB : 0 < B)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {ε R : ℝ}, (hε : 0 < ε) → ε < ε₀ → (hR : 0 < R) →
      ∀ x y : Rd d, ‖x‖ < 3 * R → ‖y‖ < 3 * R →
        η * R ≤ ‖x - y‖ →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ) →
        ∀ᵐ ω ∂P,
          h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
          sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω) →
          ∃ c ∈ s7b_classSet d hε hR B,
            let r := (64 : ℝ) ^ c.1
            let q := (2 : ℝ) ^ c.2.2
            ∃ s : Finset (Rd d × ℕ),
              IsSec8LabeledSet d T.J r R x y c.2.1 s ∧
              (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
                  ⌈T.g / (4 * T.H) * k⌉₊ ≤
                (((s.powerset.filter fun t =>
                  1 ≤ t.card ∧ t.card ≤ k ∧
                    h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N
                      T.V T.f x y t).card : ℕ) : ℝ) := by
  obtain ⟨ε₀, hε₀, hthreshold⟩ :=
    s7b_exists_sampling_threshold d hη
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε R hε hεlt hR x y hx hy hxy k hk hkup
  obtain ⟨hεη, hεhalf, hclass⟩ := hthreshold hε hεlt hR hB.le
  by_cases hJ : 0 < T.J
  · let κ := T.g / (4 * T.H)
    let n := ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊
    let m := ⌈κ * k⌉₊
    obtain ⟨hκpos, hκle⟩ := s7b_pruning_fraction_bounds T hξ hJ
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hmpos : 1 ≤ m := by
      have h : 0 < κ * (k : ℝ) := mul_pos hκpos hkpos
      change 0 < ⌈κ * (k : ℝ)⌉₊
      exact Nat.ceil_pos.mpr h
    have hnpos : 1 ≤ n := by
      have h : 0 < (ε⁻¹) ^ (1 / 2 : ℝ) := by positivity
      change 0 < ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊
      exact Nat.ceil_pos.mpr h
    have hmk : m ≤ k := by
      apply Nat.ceil_le.mpr
      have hmul := mul_le_mul_of_nonneg_right hκle
        (show 0 ≤ (k : ℝ) by positivity)
      simpa only [one_mul] using hmul
    have hkn : k ≤ n := by
      have hn := Nat.le_ceil ((ε⁻¹) ^ (1 / 2 : ℝ))
      exact_mod_cast le_trans hkup hn
    have hm : ∀ t : ℕ, κ * k ≤ t → m ≤ t := by
      intro t ht
      exact Nat.ceil_le.mpr ht
    have hcount := lemma84_of_class_count P h hh hd hξ hQ hR hη hη1
      hε hεη hεhalf hD hDt hcomp T x y hx hy hxy
      hnpos hmpos hmk hkn hm hclass
    filter_upwards [hcount] with ω hω hevent
    obtain ⟨c, hc, s, hns, hZs, hbound⟩ := hω hevent
    have hdiv : ((ε⁻¹) ^ (1 / 2 : ℝ)) / k ≤ (n : ℝ) / k := by
      have hn := Nat.le_ceil ((ε⁻¹) ^ (1 / 2 : ℝ))
      exact div_le_div_of_nonneg_right hn (by positivity)
    have hpow : (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^ m ≤
        ((n : ℝ) / k) ^ m :=
      pow_le_pow_left₀ (by positivity) hdiv m
    exact ⟨c, hc, s, hZs, hpow.trans hbound⟩
  · filter_upwards [] with ω hevent
    have hJ' := s7b_cover_implies_Jpos hR (h ω) hevent.1.1
    exact False.elim (hJ hJ')

end HigherDimLQGMetric
