import HigherDimLFPPAS.Sharp.Basic

/-!
# Proposition 5.1: the good events and the union bound (5.6) (packet P51)

Source: `planning/audits/MA2-sections-4-6.md` §2.13, Details D-B3 and D-B5 (5), §4.1 item 3 (outer
measures); MA4 Details B.5.

* `p51H33`, `p51H27`: the unpacked bodies of `Core.Lemma33Stmt` (for its constant `A`) and of
  `Core.Lemma27Stmt` at `q = 1/2` (constants `C₀`, `β₀`), with the extraction lemmas `p51_h33`, `p51_h27`.
* `p51Cov`: the covering condition of the window pair `(a, b)` with radius set `Rε`.
* `p51Bad R ε S Rs`: the failure event of a deterministic selection `S` of windows with radius sets
  `Rs b ⊆ 𝒩_ε(u_b)`: the initial coarse failure (Lemma 2.7 at `q = 1/2`, `ρ = R + 1`) or the covering
  failure of some pair `a < b ∈ S`.
* `p51_failure` ((5.6), uniform over all selections): `P*(p51Bad) ≤ K_R ε^{min(β₀, u_M)}` for all small
  `ε`, with `K_R` independent of the selection (finitely many pairs `a < b ≤ M`; Lemma 3.3 is uniform
  over the deterministic radius sets of a quarter of the window).
* `p51_good_forward`, `p51_good_reverse`: off `p51Bad`, the iteration lemma gives
  `Comp(winIter C₀ |S|, v_M)` in the forward direction (ratio bound `c ≤ m`) and in the reverse
  direction (ratio bound `c⁻¹ ≤ m`, through `Core.goodAnnulus_symm`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.SharpComp

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open HigherDimLFPPAS.Core
open HigherDimLFPPAS.Windows

variable {d : ℕ}

/-! ### The unpacked inputs -/

/-- The body of `Core.Lemma33Stmt` for a fixed constant `A`. -/
def p51H33 (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistRd d) (A : ℝ) : Prop :=
  ∀ η u q₀ R : ℝ, 0 < η → 0 < u → u < q₀ → q₀ < 1 → 0 ≤ R →
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ Rε : Finset ℝ, (↑Rε : Set ℝ) ⊆ window ε u →
      (window ε u).ncard ≤ 4 * Rε.card →
      P {ω | ¬ ∀ z ∈ mesh d ε u R, ∃ r ∈ Rε,
          GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε r) (8 * ε ^ q₀) z r} ≤
        ENNReal.ofReal (K * ε ^ u)

theorem p51_h33 {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d} (h33 : Lemma33Stmt κ ξ Q D P h) :
    ∃ A : ℝ, 1 ≤ A ∧ p51H33 κ ξ Q D P h A :=
  h33

/-- The body of `Core.Lemma27Stmt` at `q = 1/2`, for fixed constants `C`, `β`. -/
def p51H27 (κ : Rd d → ℝ) (ξ : ℝ) (D : DistRd d → ContMetric d) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistRd d) (C β : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
    P {ω | ¬ ∀ x ∈ ball (0 : Rd d) ρ, ∀ y ∈ ball (0 : Rd d) ρ,
        setDistIn (Meps κ ξ ε (h ω)) (thickening (ε ^ (1 / 2 : ℝ)) (ball 0 ρ))
            (ball x (ε ^ (1 / 2 : ℝ))) (ball y (ε ^ (1 / 2 : ℝ))) ≤
          ENNReal.ofReal C * (D (h ω)).internal (ball 0 ρ) x y ∧
        setDistIn (D (h ω)) (thickening (ε ^ (1 / 2 : ℝ)) (ball 0 ρ))
            (ball x (ε ^ (1 / 2 : ℝ))) (ball y (ε ^ (1 / 2 : ℝ))) ≤
          ENNReal.ofReal C * (Meps κ ξ ε (h ω)).internal (ball 0 ρ) x y} ≤
      ENNReal.ofReal (K * ε ^ β)

theorem p51_h27 {κ : Rd d → ℝ} {ξ : ℝ} {D : DistRd d → ContMetric d} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d} (h27 : Lemma27Stmt κ ξ D P h) :
    ∃ C β : ℝ, 2 ≤ C ∧ 0 < β ∧ p51H27 κ ξ D P h C β :=
  h27 (1 / 2) ⟨by norm_num, by norm_num⟩

/-! ### Covering conditions and the failure event -/

/-- The covering condition of the window pair `(a, b)` with radius set `Rε` for the pair `(G, G')`
and ratio function `c` (connection radius `8 ε^{v_a}`). -/
def p51Cov (G G' : ContMetric d) (A η : ℝ) (c : ℝ → ℝ) (R ε : ℝ) (a b : ℕ) (Rε : Finset ℝ) :
    Prop :=
  ∀ z ∈ mesh d ε (winU b) R, ∃ r ∈ Rε, GoodAnnulus G G' A η (c r) (8 * ε ^ (winV a)) z r

/-- The failure event of a selection `S` of windows with radius sets `Rs`: the initial coarse
comparison fails, or the covering condition of some pair `a < b ∈ S` fails. -/
def p51Bad (κ : Rd d → ℝ) (ξ Q : ℝ) (D : DistRd d → ContMetric d) {Ω : Type}
    (h : Ω → DistRd d) (A η C₀ R ε : ℝ) (S : Finset ℕ) (Rs : ℕ → Finset ℝ) : Set Ω :=
  {ω | ¬ p51Init (D (h ω)) (Meps κ ξ ε (h ω)) C₀ R ε} ∪
    ⋃ b ∈ S, ⋃ a ∈ Finset.range b,
      {ω | ¬ p51Cov (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε) R ε a b (Rs b)}

theorem p51_not_bad {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d} {Ω : Type}
    {h : Ω → DistRd d} {A η C₀ R ε : ℝ} {S : Finset ℕ} {Rs : ℕ → Finset ℝ} {ω : Ω}
    (hω : ω ∉ p51Bad κ ξ Q D h A η C₀ R ε S Rs) :
    p51Init (D (h ω)) (Meps κ ξ ε (h ω)) C₀ R ε ∧
      ∀ b ∈ S, ∀ a ∈ Finset.range b,
        p51Cov (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε) R ε a b (Rs b) := by
  simp only [p51Bad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    not_not] at hω
  exact ⟨hω.1, fun b hb a ha => hω.2 b hb a ha⟩

/-- **(5.6), uniform over the selections**: for fixed `R`, there is `K` such that for all small `ε`
and every selection `S ⊆ [0, M]` with radius sets of at least a quarter of their windows, the failure
event has outer probability `≤ K ε^{min(β₀, u_M)}`. -/
theorem p51_failure {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    {A η C₀ β₀ : ℝ} (h33 : p51H33 κ ξ Q D P h A) (h27 : p51H27 κ ξ D P h C₀ β₀)
    (hη : 0 < η) (M : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (S : Finset ℕ) (Rs : ℕ → Finset ℝ),
      (∀ b ∈ S, b ≤ M ∧ (↑(Rs b) : Set ℝ) ⊆ window ε (winU b) ∧
        (window ε (winU b)).ncard ≤ 4 * (Rs b).card) →
      P (p51Bad κ ξ Q D h A η C₀ R ε S Rs) ≤ ENNReal.ofReal (K * ε ^ (min β₀ (winU M))) := by
  obtain ⟨K₀, ε₀, hε₀, hK₀⟩ := h27 (R + 1) (by linarith)
  have hpair : ∀ a b : ℕ, ∃ K : ℝ, a < b → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ Rε : Finset ℝ,
      (↑Rε : Set ℝ) ⊆ window ε (winU b) → (window ε (winU b)).ncard ≤ 4 * Rε.card →
      P {ω | ¬ p51Cov (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε) R ε a b Rε} ≤
        ENNReal.ofReal (K * ε ^ winU b) := by
    intro a b
    by_cases hab : a < b
    · obtain ⟨K, ε₁, hε₁, hK⟩ := h33 η (winU b) (winV a) R hη (winU_pos b)
        (winV_gt_winU_of_lt hab) (p51_winV_lt_one a) hR
      exact ⟨K, fun _ => p51_eventually_of_Ioo ⟨ε₁, hε₁, hK⟩⟩
    · exact ⟨0, fun h' => absurd h' hab⟩
  choose Kf hKf using hpair
  let Ksum : ℝ := ∑ b ∈ Finset.range (M + 1), ∑ a ∈ Finset.range b, max (Kf a b) 0
  have hKsum : 0 ≤ Ksum :=
    Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun a _ => le_max_right _ _
  refine ⟨max K₀ 0 + Ksum, ?_⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ Finset.range (M + 1), ∀ a ∈ Finset.range b,
      ∀ Rε : Finset ℝ, (↑Rε : Set ℝ) ⊆ window ε (winU b) →
      (window ε (winU b)).ncard ≤ 4 * Rε.card →
      P {ω | ¬ p51Cov (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε) R ε a b Rε} ≤
        ENNReal.ofReal (Kf a b * ε ^ winU b) := by
    rw [Filter.eventually_all_finset]
    intro b _
    rw [Filter.eventually_all_finset]
    intro a ha
    exact hKf a b (Finset.mem_range.1 ha)
  filter_upwards [hev, Ioo_mem_nhdsGT (lt_min hε₀ one_pos)] with ε hεK hε S Rs hSRs
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hpowβ : 0 ≤ ε ^ min β₀ (winU M) := Real.rpow_nonneg hε0.le _
  have hinit : P {ω | ¬ p51Init (D (h ω)) (Meps κ ξ ε (h ω)) C₀ R ε} ≤
      ENNReal.ofReal (max K₀ 0 * ε ^ min β₀ (winU M)) := by
    have h1 : P {ω | ¬ p51Init (D (h ω)) (Meps κ ξ ε (h ω)) C₀ R ε} ≤
        ENNReal.ofReal (K₀ * ε ^ β₀) := hK₀ ε ⟨hε0, hεε₀⟩
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : ε ^ β₀ ≤ ε ^ min β₀ (winU M) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left _ _)
    calc K₀ * ε ^ β₀ ≤ max K₀ 0 * ε ^ β₀ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε0.le _)
      _ ≤ max K₀ 0 * ε ^ min β₀ (winU M) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  have hcov : ∀ b ∈ S, ∀ a ∈ Finset.range b,
      P {ω | ¬ p51Cov (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε) R ε a b (Rs b)} ≤
        ENNReal.ofReal (max (Kf a b) 0 * ε ^ min β₀ (winU M)) := by
    intro b hb a ha
    obtain ⟨hbM, hsub, hcard⟩ := hSRs b hb
    have hbR : b ∈ Finset.range (M + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hbM)
    refine (hεK b hbR a ha (Rs b) hsub hcard).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : ε ^ winU b ≤ ε ^ min β₀ (winU M) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le
      ((min_le_right _ _).trans (winU_antitone hbM))
    calc Kf a b * ε ^ winU b ≤ max (Kf a b) 0 * ε ^ winU b :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε0.le _)
      _ ≤ max (Kf a b) 0 * ε ^ min β₀ (winU M) :=
          mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  have hSsub : S ⊆ Finset.range (M + 1) := fun b hb =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (hSRs b hb).1)
  have hsum : ∑ b ∈ S, ∑ a ∈ Finset.range b,
        ENNReal.ofReal (max (Kf a b) 0 * ε ^ min β₀ (winU M)) ≤
      ENNReal.ofReal (Ksum * ε ^ min β₀ (winU M)) := by
    calc ∑ b ∈ S, ∑ a ∈ Finset.range b, ENNReal.ofReal (max (Kf a b) 0 * ε ^ min β₀ (winU M))
        ≤ ∑ b ∈ Finset.range (M + 1), ∑ a ∈ Finset.range b,
            ENNReal.ofReal (max (Kf a b) 0 * ε ^ min β₀ (winU M)) :=
          Finset.sum_le_sum_of_subset hSsub
      _ = ENNReal.ofReal (Ksum * ε ^ min β₀ (winU M)) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun b _ =>
            mul_nonneg (Finset.sum_nonneg fun a _ => le_max_right _ _) hpowβ)]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun a _ =>
            mul_nonneg (le_max_right _ _) hpowβ)]
  calc P (p51Bad κ ξ Q D h A η C₀ R ε S Rs)
      ≤ P {ω | ¬ p51Init (D (h ω)) (Meps κ ξ ε (h ω)) C₀ R ε} +
          P (⋃ b ∈ S, ⋃ a ∈ Finset.range b,
            {ω | ¬ p51Cov (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε) R ε a b (Rs b)}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (max K₀ 0 * ε ^ min β₀ (winU M)) +
          ∑ b ∈ S, ∑ a ∈ Finset.range b,
            ENNReal.ofReal (max (Kf a b) 0 * ε ^ min β₀ (winU M)) := by
        refine add_le_add hinit ((measure_biUnion_finset_le S _).trans
          (Finset.sum_le_sum fun b hb => ?_))
        exact (measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun a ha => hcov b hb a ha)
    _ ≤ ENNReal.ofReal (max K₀ 0 * ε ^ min β₀ (winU M)) +
          ENNReal.ofReal (Ksum * ε ^ min β₀ (winU M)) := add_le_add le_rfl hsum
    _ = ENNReal.ofReal ((max K₀ 0 + Ksum) * ε ^ min β₀ (winU M)) := by
        rw [add_mul, ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) hpowβ)
          (mul_nonneg hKsum hpowβ)]

/-! ### Consequences on the good event (deterministic) -/

/-- Off the failure event, the forward iteration along the selection gives
`Comp(G → G', winIter C₀ |S|, v_M)` (ratio bound `c ≤ m` on the selected radii). -/
theorem p51_good_forward {G G' : ContMetric d} {A η R ε m C₀ : ℝ} {M : ℕ} {c : ℝ → ℝ}
    (hA : 1 ≤ A) (hη : 0 < η) (hR : 2 ≤ R) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 ≤ m)
    (hmC : m ≤ C₀) (hP41 : ∀ a b, a < b → b ≤ M → p51P41At d A η ε a b)
    (S : Finset ℕ) (hS : ∀ b ∈ S, 1 ≤ b ∧ b ≤ M) (Rs : ℕ → Finset ℝ)
    (hRs : ∀ b ∈ S, ∀ r ∈ Rs b, r ∈ window ε (winU b) ∧ 0 < c r ∧ c r ≤ m)
    (hinit : p51Init G G' C₀ R ε)
    (hcov : ∀ b ∈ S, ∀ a ∈ Finset.range b, p51Cov G G' A η c R ε a b (Rs b)) :
    Comp G G' R ε (winV M) (winIter (A / (A + 1)) η m C₀ S.card) := by
  have h0 : Comp G G' R ε (winV 0) C₀ := by
    rw [p51_winV_zero]
    exact (p51_comp_of_init hε0 hε1 hinit).1
  exact p51_select hA hη hR hε0 hε1 hm hmC hP41 S hS Rs c hRs
    (fun b hb a hab => hcov b hb a (Finset.mem_range.2 hab)) h0

/-- Off the failure event, the reverse iteration along the selection gives
`Comp(G' → G, winIter C₀ |S|, v_M)` (ratio bound `c⁻¹ ≤ m`; the covering conditions transfer through
`Core.goodAnnulus_symm`). -/
theorem p51_good_reverse {G G' : ContMetric d} {A η R ε m C₀ : ℝ} {M : ℕ} {c : ℝ → ℝ}
    (hA : 1 ≤ A) (hη : 0 < η) (hR : 2 ≤ R) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 ≤ m)
    (hmC : m ≤ C₀) (hP41 : ∀ a b, a < b → b ≤ M → p51P41At d A η ε a b)
    (S : Finset ℕ) (hS : ∀ b ∈ S, 1 ≤ b ∧ b ≤ M) (Rs : ℕ → Finset ℝ)
    (hRs : ∀ b ∈ S, ∀ r ∈ Rs b, r ∈ window ε (winU b) ∧ 0 < c r ∧ (c r)⁻¹ ≤ m)
    (hinit : p51Init G G' C₀ R ε)
    (hcov : ∀ b ∈ S, ∀ a ∈ Finset.range b, p51Cov G G' A η c R ε a b (Rs b)) :
    Comp G' G R ε (winV M) (winIter (A / (A + 1)) η m C₀ S.card) := by
  have h0 : Comp G' G R ε (winV 0) C₀ := by
    rw [p51_winV_zero]
    exact (p51_comp_of_init hε0 hε1 hinit).2
  refine p51_select hA hη hR hε0 hε1 hm hmC hP41 S hS Rs (fun r => (c r)⁻¹) ?_ ?_ h0
  · intro b hb r hr
    obtain ⟨hw, hc, hcm⟩ := hRs b hb r hr
    exact ⟨hw, inv_pos.2 hc, hcm⟩
  · intro b hb a hab z hz
    obtain ⟨r, hr, hgood⟩ := hcov b hb a (Finset.mem_range.2 hab) z hz
    exact ⟨r, hr, (goodAnnulus_symm G G' A η (c r) _ z r).1 hgood⟩

end HigherDimLFPPAS.SharpComp
