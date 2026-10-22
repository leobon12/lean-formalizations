import HigherDimLQGContinuity.UnifCompare.Cor52
import HigherDimLQGContinuity.Unif4.Sec42
import HigherDimLQGContinuity.Unif4.Quant
import HigherDimLQGMetric.DGZ.TightHolder

/-!
# Uniform DGZ Lemma 6.1: the self-internal Hölder bound (packet U4)

Blueprint Part D, `d:lem-u61`(a) (NA3 §2.7, §2.15 row 17; [8]-bp `r2:lem:61`). Port of
`HigherDimLQGMetric.DGZ.holder_selfInternal` (`DGZ/TightHolder.lean`) with every constant chosen before `ξ`.

**Statement** (`holder_selfInternal_unif`). Let `d ≥ 2`, `κ` admissible, `b, μ > 0` and `0 < β < μ`. There is
`q₀ = q₀(d, κ, b, μ, β) ∈ (0, 1)` such that for every `q ∈ [q₀, 1)` and `θ > 0` there is
`M = M(d, κ, b, μ, β, q, θ) > 0` with
`P[∃ x, y ∈ B_ρ(0) : D_n(x, y; B_ρ(0)) > M a^ξ_n(q) ‖x - y‖^β] ≤ θ`
for every `ξ ∈ S(b, μ)` (`UHyp d κ b μ ξ`), every dyadic realization, every `ρ ∈ [1, 3/2]` and every `n`
(`B_ρ(0)` is the open cube `obox 0 ρ`).

**Proof** (the sealed proof with the uniform constants of the blueprint). `ε' := (μ - β)/3`, `η := β + 2ε'`, so
`β + ε' < η < μ ≤ ξ(Q(ξ) - √(2d))`. The event `𝒜_{r,n}` at margin `η` has the uniform probability bound of U1's
`prob_eventA_compl_le_unif` (`c₄ = c₄(d, κ)`, `C_A = C_A(d, κ, b, μ, η)`); U3's `uCor52` replaces `Cor52Shape`
(`C₅` before `ξ`), U1's `exists_le_aQ_unif` gives `a^ξ_n(q) ≥ c 2^{-(1-ϕ(ξ)+ε')n}` with `c` before `ξ`;
`DGZ.chain_selfInternal` and `DGZ.holder_det` are deterministic. For the finitely many `n ≤ r`, the factors of the
sealed proof that depend on `ξ` are bounded uniformly: `e^{ξ L_n} ≤ e^{b L_n}` (`L_n ≥ 0`, `ξ ≤ b`) and
`2^{(1-ϕ(ξ)+ε')n} ≤ 2^{(1+ε')n}` (`ϕ(ξ) ≥ μ > 0`, `UHyp.mu_le_phi`). `β < 1` follows from
`β < μ ≤ ξ(Q(ξ) - √(2d)) ≤ 1` (`UHyp.gap_le_one`), inside the proof only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- `ϕ(ξ) = ξ Q(ξ) ≥ 0` under the uniform hypothesis (`μ ≤ ϕ(ξ)`, `UHyp.mu_le_phi`). -/
lemma u4_phi_nonneg {κ : Rd d → ℝ} {b μ ξ : ℝ} (hμ : 0 < μ) (hU : UHyp d κ b μ ξ) :
    0 ≤ ξ * distExp d ξ :=
  hμ.le.trans hU.mu_le_phi

/-- `2^{(1-ϕ+ε)n} ≤ 2^{(1+ε)n}` for `ϕ ≥ 0`. -/
lemma u4_two_rpow_le_of_phi_nonneg {φ ε : ℝ} (hφ : 0 ≤ φ) (n : ℕ) :
    (2 : ℝ) ^ ((1 - φ + ε) * n) ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `e^{ξ L} ≤ e^{b L}` for `L ≥ 0` and `ξ ≤ b`. -/
lemma u4_exp_mul_le {ξ b L : ℝ} (hξb : ξ ≤ b) (hL : 0 ≤ L) :
    Real.exp (ξ * L) ≤ Real.exp (b * L) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hξb hL)

/-- **Uniform DGZ Lemma 6.1** (Part D `d:lem-u61`(a); port of `DGZ.holder_selfInternal`): for `d ≥ 2`, `κ`
admissible, `b, μ > 0` and `0 < β < μ` there is `q₀ ∈ (0, 1)` such that for every `q ∈ [q₀, 1)` and `θ > 0` there is
`M > 0` with `P[∃ x, y ∈ B_ρ(0) : D_n(x, y; B_ρ(0)) > M a^ξ_n(q) ‖x - y‖^β] ≤ θ` for every `ξ ∈ S(b, μ)`, every
dyadic realization, every `ρ ∈ [1, 3/2]` and every `n`. -/
theorem holder_selfInternal_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {β : ℝ} (hβ0 : 0 < β) (hβ : β < μ) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧ ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 → ∀ θ : ℝ, 0 < θ →
      ∃ M : ℝ, 0 < M ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 3 / 2 →
          ∀ n : ℕ, P {ω | ∃ x ∈ obox (0 : Rd d) ρ, ∃ y ∈ obox (0 : Rd d) ρ,
            M * aQ P H ξ n q * ‖x - y‖ ^ β <
              lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y} ≤ ENNReal.ofReal θ := by
  set ε' : ℝ := (μ - β) / 3 with hε'
  set η : ℝ := β + 2 * ε' with hη
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  have hημ : η < μ := by rw [hη, hε']; linarith
  have hβη : β + ε' < η := by rw [hη]; linarith
  obtain ⟨c₄, hc₄, hA⟩ := prob_eventA_compl_le_unif hd hκ
  obtain ⟨CA, hCA, hAb⟩ := hA b μ η hημ
  obtain ⟨qA, hc₄qA, hqA1⟩ := exists_between hc₄
  obtain ⟨q₀, hqAq₀, hq₀1⟩ := exists_between hqA1
  obtain ⟨C₀, hC₀, hchain⟩ := chain_selfInternal.{0} hd
  have hqA0 : 0 < qA := lt_of_le_of_lt zero_le hc₄qA
  refine ⟨q₀, hqA0.trans hqAq₀, hq₀1, fun q hq₀q hq1 θ hθ => ?_⟩
  have hqAq : qA < q := lt_of_lt_of_le hqAq₀ hq₀q
  have hq0 : 0 < q := lt_trans hqA0 hqAq
  obtain ⟨C₅, hC₅, hcor⟩ := uCor52 hd hκ b μ hb hμ ε' hε'0 qA q hqA0 hqAq hq1
  obtain ⟨c, hc, hlow⟩ := exists_le_aQ_unif.{0} hd hκ hb hq0 hq1 hε'0
  -- the scale `r` of the event `𝒜_{r,n}`
  obtain ⟨k₀, hk₀⟩ := exists_mul_exp_neg_div_le hCA hθ
  set r := max 110 k₀ with hr
  have hr110 : 110 ≤ r := le_max_left _ _
  -- the finitely many small levels
  have hL : ∀ n : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WN d → Ω → ℝ}, IsWhiteNoise P W → ∀ {X : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 X → ∀ c : Rd d,
          P {ω | ∃ z ∈ cbox c 3, L < |X z ω|} ≤ ENNReal.ofReal θ := fun n =>
    exists_sup_tail_level_tight hκ n (by norm_num) hθ
  choose L hL0 hLt using hL
  set Msmall : ℝ := ∑ n ∈ Finset.range (r + 1),
    Real.exp (b * L n) * (1 + 3 * Real.sqrt d) * (2 : ℝ) ^ ((1 + ε') * n) / c with hMsmall
  have hMsmall0 : 0 ≤ Msmall := Finset.sum_nonneg fun n _ => by positivity
  set K := max C₅ c⁻¹ * holderSumConst d (η - ε' - β) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (le_trans hC₅.le (le_max_left _ _)) (holderSumConst_nonneg d _)
  set Mlarge := C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) + Real.sqrt d / c with hMlarge
  have hMlarge0 : 0 ≤ Mlarge := by positivity
  refine ⟨Mlarge + Msmall + 1, by positivity, fun ξ hU Ω _ P W H hH ρ hρ1 hρ2 n => ?_⟩
  have hξ : 0 < ξ := hU.base.xi_pos
  have hξb : ξ ≤ b := hU.le_b
  have hφ0 : 0 ≤ ξ * distExp d ξ := u4_phi_nonneg hμ hU
  have hβ1 : β ≤ 1 := by
    have h1 := hU.gap
    have h2 := hU.gap_le_one
    linarith
  have ha := hlow ξ hξ hξb Ω P W H hH n
  set a := aQ P H ξ n q with ha_def
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos two_pos _)) ha
  by_cases hnr : n ≤ r
  · -- small `n`: `D_n ≤ e^{ξ L_n} ‖x - y‖`
    refine (measure_mono ?_).trans (hLt n hH.whiteNoise (hH.band n) 0)
    intro ω hω
    by_contra hgood
    simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hgood hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    have hM : ∀ z ∈ obox (0 : Rd d) ρ, ξ * H n z ω ≤ ξ * L n := fun z hz => by
      have hz3 : z ∈ cbox (0 : Rd d) 3 := fun i => by
        have := hz i
        simp only [PiLp.zero_apply, sub_zero] at this ⊢
        linarith
      have h1 := hgood z hz3
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hξ.le
    have hD := lfppDistOn_le_exp_mul_norm_of_convex ((hH.band n).continuous ω)
      (HigherDimLFPP.DGZ.convex_obox 0 ρ) hx hy hM
    rw [norm_sub_rev] at hD
    have hxy3 : ‖x - y‖ ≤ 3 * Real.sqrt d := by
      have := norm_sub_le_of_forall_abs_le (x := x) (y := y) (s := 3) fun i => by
        have h1 := hx i
        have h2 := hy i
        simp only [PiLp.zero_apply, sub_zero] at h1 h2
        rw [abs_lt] at h1 h2
        rw [abs_le]; constructor <;> linarith
      linarith
    have hnorm := th_le_rpow_mul (norm_nonneg (x - y)) hxy3 hβ0 hβ1
    have hterm : Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) ≤ Msmall * a := by
      have hsingle : Real.exp (b * L n) * (1 + 3 * Real.sqrt d) *
          (2 : ℝ) ^ ((1 + ε') * n) / c ≤ Msmall :=
        Finset.single_le_sum (f := fun n => Real.exp (b * L n) * (1 + 3 * Real.sqrt d) *
          (2 : ℝ) ^ ((1 + ε') * n) / c) (fun n _ => by positivity)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hnr))
      have hexp := u4_exp_mul_le hξb (hL0 n)
      have hpow := u4_two_rpow_le_of_phi_nonneg (ε := ε') hφ0 n
      have hunif : Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) *
          (2 : ℝ) ^ ((1 - ξ * distExp d ξ + ε') * n) / c ≤ Msmall := by
        refine le_trans ?_ hsingle
        gcongr
      have e : (2 : ℝ) ^ ((1 - ξ * distExp d ξ + ε') * n) *
          (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε') * n) = 1 := by
        rw [← Real.rpow_add two_pos,
          show (1 - ξ * distExp d ξ + ε') * (n : ℝ) + -(1 - ξ * distExp d ξ + ε') * n = 0 by ring,
          Real.rpow_zero]
      calc Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d)
          = Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) *
              ((2 : ℝ) ^ ((1 - ξ * distExp d ξ + ε') * n) *
                (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε') * n)) * (c / c) := by
            rw [e, div_self hc.ne']; ring
        _ = Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) *
              (2 : ℝ) ^ ((1 - ξ * distExp d ξ + ε') * n) / c *
              (c * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε') * n)) := by ring
        _ ≤ Msmall * a := mul_le_mul hunif ha (by positivity) hMsmall0
    have hfin : lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y ≤
        (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
      have hsβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
      calc lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y
          ≤ Real.exp (ξ * L n) * ‖x - y‖ := hD
        _ ≤ Real.exp (ξ * L n) * (‖x - y‖ ^ β * (1 + 3 * Real.sqrt d)) :=
            mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
        _ = Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) * ‖x - y‖ ^ β := by ring
        _ ≤ Msmall * a * ‖x - y‖ ^ β := mul_le_mul_of_nonneg_right hterm hsβ
        _ ≤ (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
            gcongr
            linarith
    exact absurd hlt (not_lt.2 hfin)
  · -- large `n`: on `𝒜_{r,n}`, the deterministic core
    push Not at hnr
    refine (measure_mono ?_).trans ((hAb ξ (distExp d ξ) hξ hξb hU.gap qA hc₄qA hqA1 hH r n
      (by omega) hnr).trans (ENNReal.ofReal_le_ofReal (hk₀ r (le_max_right _ _))))
    intro ω hω hgood
    simp only [mem_ofPred_eq] at hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    obtain ⟨hI, hII⟩ := hchain P H ξ (distExp d ξ) η qA r n ρ ω hξ hr110 hnr hρ1 hρ2
      ((hH.band n).continuous ω) hgood
    have hG := (mem_eventA_iff.1 hgood).1
    have hcomp : ∀ k, k < n →
        aQ P H ξ (n - k) qA ≤ C₅ * (2 : ℝ) ^ ((1 - ξ * distExp d ξ + ε') * k) * a :=
      fun k hk => hcor ξ hU Ω P W H hH n k hk.le
    have hcs : ∀ j, j ≤ n →
        chainSum P H ξ (distExp d ξ) η qA j n ≤ K * a * ((2 : ℝ) ^ (-β)) ^ j :=
      fun j hj => by
        have := chainSum_le_aQ_holder (d := d) (P := P) (H := H) (η := η) hc hC₅.le ha0.le
          hβ0.le hβη hcomp ha hj
        calc _ ≤ _ := this
          _ = K * a * ((2 : ℝ) ^ (-β)) ^ j := by rw [hK]; ring
    have hdet := holder_det ((hH.band n).continuous ω) hξ hβ0 hβ1 hβη.le hc hK0 hC₀.le hρ2
      hnr.le ha (fun j => chainSum P H ξ (distExp d ξ) η qA j n) hcs hI hII hG x hx y hy
    have hfin : lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y ≤
        (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
      calc _ ≤ Mlarge * a * ‖x - y‖ ^ β := hdet
        _ ≤ (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
            gcongr
            linarith
    exact absurd hlt (not_lt.2 hfin)

end HigherDimLQGContinuity
