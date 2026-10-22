import HigherDimLQGMetric.Sec8b.Lemma84Uniform

/-! The sampling, bin, and pruning count of [S] Lemma 8.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric MeasureTheory unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The lower scale-bin bound and (C2) force the dyadic bin parameter to be
at least half the lower endpoint `ε^B`. -/
theorem s7b_bin_q_lower {ξ Q cs Cs B ε R r q : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt) (g : DistRd d)
    (_hε : 0 < ε) (hR : 0 < R)
    (hrwin : ∃ j ∈ scaleWin ε R, r = (64 : ℝ) ^ j)
    (x y : Rd d) (colour : Fin d → ℤ)
    (s : Finset (Rd d × ℕ))
    (hsnonempty : s.Nonempty)
    (hZ : IsSec8LabeledSet d T.J r R x y colour s)
    (hC2 : sec8C2 D Dt ξ Q q R r T.J T.N s g)
    (hbin : g ∈ sec8BinEvent d ξ Q B ε R) :
    ε ^ B / 2 ≤ q := by
  obtain ⟨site, hsite⟩ := hsnonempty
  obtain ⟨k, hk, _, hz, _, _, _⟩ := hZ.1 site hsite
  obtain ⟨j, hj, hrj⟩ := hrwin
  have hrlo : ε ^ 2 * R ≤ r := by rw [hrj]; exact hj.1
  have hrhi : r ≤ ε * R := by rw [hrj]; exact hj.2
  have hbin' := (hbin r ⟨j, hrj⟩ hrlo hrhi site.1 hz
    ⟨k, by rw [hk]; exact s7b_latPt_coordinates r k⟩).1
  have hS : 0 < macroS ξ Q g R := by dsimp [macroS]; positivity
  have hmul := (le_div_iff₀ hS).mp hbin'
  have hhi := (hC2 site hsite).2.2.2
  nlinarith only [hmul, hhi, hS]

/-- A larger `q` makes the near-extreme inequality (C1) weaker. -/
theorem s7b_C1_mono {ξ Q Cs R q₀ q : ℝ}
    {D Dt : DistRd d → ContMetric d} (g : DistRd d)
    (hR : 0 < R) (hq : q₀ ≤ q)
    (x y : Rd d)
    (hC1 : sec8C1 D Dt ξ Q Cs q₀ R x y g) :
    sec8C1 D Dt ξ Q Cs q R x y g := by
  have hS : 0 ≤ macroS ξ Q g R := by dsimp [macroS]; positivity
  have hmul := mul_le_mul_of_nonneg_right hq hS
  dsimp only [sec8C1] at hC1 ⊢
  linarith only [hC1, hmul]

/-- For `ε ≤ 1/2`, the bin's `q ≥ ε^B/2` is large enough to pass from
(27) to (C1). -/
theorem s7b_near_to_bin_C1 {ξ Q Cs B ε R q : ℝ}
    {D Dt : DistRd d → ContMetric d} (g : DistRd d)
    (hR : 0 < R) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hq : ε ^ B / 2 ≤ q) (x y : Rd d)
    (hnear : sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y g) :
    sec8C1 D Dt ξ Q Cs q R x y g := by
  have hpow : ε ^ (B + 1) = ε ^ B * ε := by
    rw [Real.rpow_add hε]
    simp only [Real.rpow_one]
  have hpowpos : 0 ≤ ε ^ B := by positivity
  have hle : ε ^ (B + 1) ≤ q := by
    rw [hpow]
    nlinarith only [hq, hεhalf, hpowpos,
      mul_le_mul_of_nonneg_left hεhalf hpowpos]
  exact s7b_C1_mono g hR hle x y hnear

/-- Lemma 8.4 with the explicit finite-class sampling condition. The
parameter estimate below will supply this condition for all small `ε`. -/
theorem lemma84_of_class_count {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs B ε R η : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hR : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hεη : ε < η / 18) (hεhalf : ε ≤ 1 / 2)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (hx : ‖x‖ < 3 * R) (_hy : ‖y‖ < 3 * R)
    (hxy : η * R ≤ ‖x - y‖)
    {n k m : ℕ} (hnpos : 1 ≤ n) (hmpos : 1 ≤ m)
    (hmk : m ≤ k) (hkn : k ≤ n)
    (hm : ∀ t : ℕ, T.g / (4 * T.H) * k ≤ t → m ≤ t)
    (hclasses : (s7b_classSet d hε hR B).card * n ≤ s7b_sampleCount η ε) :
    ∀ᵐ ω ∂P,
      h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
      sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω) →
      ∃ c ∈ s7b_classSet d hε hR B,
        let r := (64 : ℝ) ^ c.1
        let q := (2 : ℝ) ^ c.2.2
        ∃ s : Finset (Rd d × ℕ), n ≤ s.card ∧
          IsSec8LabeledSet d T.J r R x y c.2.1 s ∧
          ((n : ℝ) / k) ^ m ≤
            (((s.powerset.filter fun t =>
              1 ≤ t.card ∧ t.card ≤ k ∧
                h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t).card : ℕ) : ℝ) := by
  have huniform := lemma84_class_ae_all_indexed P h hh hd hξ hQ hR
    hD hDt hcomp T x y
  filter_upwards [hD.length P h hh.isLGFPlusCont,
    lemma27_proper hd hξ hQ hD P h hh, huniform] with ω hlen hproper huni hEvent
  letI : ProperSpace (D (h ω)).Space := hproper
  have hsel : IsConstSpeedGeod (D (h ω)) x y (sec8Sel x y (D (h ω)).1) :=
    ((exists_measurable_geodSelector x y).choose_spec.2 _
      (sec8_exists_constSpeedGeod (D (h ω)) hlen x y)).1
  let path := sec8Sel x y (D (h ω)).1
  obtain ⟨hcover, hbin⟩ := hEvent.1
  have hnear := hEvent.2
  obtain ⟨a, ha⟩ := s7b_choose_samples T (h ω) hR hε hεη hη le_rfl hη1
    x y hx hxy path hsel.1 hsel.2.1 hcover hbin
  obtain ⟨c, hcmem, hfiber⟩ := s7b_pigeonhole_samples hε hR hη
    (by omega : 1 ≤ d) a (fun l => (ha l).2.1)
    (fun l => (ha l).2.2.2.1) hclasses
  obtain ⟨s, hns, hZs, hC2s, hC3s⟩ :=
    s7b_class_sites T (h ω) hε hR x y path a ha c hfiber
  have hrwin : ∃ j ∈ scaleWin ε R, (64 : ℝ) ^ c.1 = (64 : ℝ) ^ j := by
    have hfibpos : 0 < (Finset.univ.filter
        (fun l : Fin (s7b_sampleCount η ε) => (a l).class = c)).card :=
      lt_of_lt_of_le hnpos hfiber
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hfibpos
    have heq := (a l).class_eq c (Finset.mem_filter.mp hl).2
    refine ⟨c.1, ?_, rfl⟩
    simpa only [heq.1] using (ha l).2.1
  have hsnonempty : s.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le hnpos hns)
  have hqlo := s7b_bin_q_lower T (h ω) hε hR hrwin
    x y c.2.1 s hsnonempty hZs hC2s hbin
  have hC1q := s7b_near_to_bin_C1 (h ω) hR hε hεhalf
    hqlo x y hnear
  obtain ⟨W, hW⟩ := s7b_labeled_index_rep hZs
  have hcount := huni c.1 c.2.2 c.2.1 W k m
  dsimp only at hcount
  rw [hW] at hcount
  have hclassCount := hcount hZs hmpos hmk (hkn.trans hns) hm
    hC1q hC2s hC3s
  have hdiv : (n : ℝ) / k ≤ (s.card : ℝ) / k := by
    gcongr
  have hpow : ((n : ℝ) / k) ^ m ≤ ((s.card : ℝ) / k) ^ m := by
    exact pow_le_pow_left₀ (by positivity) hdiv m
  exact ⟨c, hcmem, s, hns, hZs, hpow.trans hclassCount⟩

end HigherDimLQGMetric
