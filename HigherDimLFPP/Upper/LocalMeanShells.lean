import HigherDimLFPP.Upper.LocalMeanSetup
import HigherDimLFPP.Upper.Records
import Mathlib.Data.List.GetD

/-!
# Lemma 4.3, Step 1b–1c: uniform bounds and shells for the unit good family

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.2, proof of Lemma 4.3, Step 1 ((4.12) and
the shell paragraph), as completed by the planning audit HA3 (`planning/audits/HA3-section-4.md`),
Details D5, Steps 1b and 1c (with the fix F6); packet P-U4.

Throughout, `G = G_K(0, e₁)` is the good family of the unit chord (`K = 2ⁿ`, threshold
`a₀ = a0 n`), `ν_I` is the uniform measure on `I = [0, e₁]`, and `κ` is an admissible kernel used
only to realize the all-scale covariance `Λ` as a Gram kernel: `shapeV κ Q` is the white-noise
vector of `⟨h, ν_I - ν_Q⟩`, so that `⟪shapeV κ Q, shapeV κ Q'⟫ = Λ(ν_I - ν_Q, ν_I - ν_{Q'})`.  The
process is `Z(Q) = δ^{-1/2} ⟨h, ν_I - ν_Q⟩` and the penalty `E_δ(Q) = δ^{-2} log len(Q)`.

* **Polygon couplings** (`coupledWithin_polyMeasure_of_close`): two polygons with `m` edges of
  lengths in `[c, D]`, total lengths `≥ 1`, and vertices within `η` have normalized arclength
  measures coupled within `cplConst m c D · η` (arclength parametrizations as ramp paths, HA3 D5
  1b "parametrization bound").
* **Uniform bounds (4.12)** for `Q ∈ G` with `E_δ(Q) ≤ R`: `Var Z(Q) ≤ 2 C_tr √R`
  (`norm_shapeV_sq_le`, from D4 (b) and Lemma 3.1) and the modulus
  `E(Z(Q) - Z(Q'))² ≤ C_tr cplConst · max_i |z_i - z_i'| / δ` (`norm_shapeV_sub_sq_le`).
  With the vertex coordinates `p(Q) = (z_i/δ)` (`vparam`) the canonical metric is
  `≤ L² ‖p(Q) - p(Q')‖_∞` and the parameters have sup-diameter `≤ 4 √R` (D4 (c)), so chaining on a
  box gives `E max Z ≤ C₂ √(R + 1)` (`gEM_shell_le`).
* **Shells** (`exists_shell_bound`, HA3 D5 1c with the fix F6): for `α, β, θ > 0` there is
  `R₀` such that for every `δ > 0` and every finite `F ⊆ G` containing a reference polygon of
  value `0` (`Q_δ(0)`, the subdivided chord),
  `E max_F (αZ - βE_δ) ≤ E max_{F ∩ {E_δ < R₀}} (αZ - βE_δ) + θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

variable {d : ℕ}

/-! ## Couplings of polygons with nearby vertices -/

section Coupling

theorem plen_mono (V : ℕ → Rd d) {i j : ℕ} (hij : i ≤ j) : plen V i ≤ plen V j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hij)
    fun _ _ _ => norm_nonneg _

theorem plen_nonneg (V : ℕ → Rd d) (i : ℕ) : 0 ≤ plen V i :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Partial lengths of polygons with nearby vertices. -/
theorem abs_plen_sub_plen_le {V V' : ℕ → Rd d} {η : ℝ} {m : ℕ}
    (hη : ∀ i ≤ m, ‖V i - V' i‖ ≤ η) : ∀ i ≤ m, |plen V i - plen V' i| ≤ 2 * i * η := by
  intro i
  induction i with
  | zero => intro _; simp [plen]
  | succ i ih =>
    intro hi
    rw [plen_succ, plen_succ]
    have h1 := ih (by omega)
    have h2 : |‖V (i + 1) - V i‖ - ‖V' (i + 1) - V' i‖| ≤ 2 * η := by
      refine (abs_norm_sub_norm_le _ _).trans ?_
      have a1 := hη (i + 1) hi
      have a2 := hη i (by omega)
      calc ‖(V (i + 1) - V i) - (V' (i + 1) - V' i)‖ =
            ‖(V (i + 1) - V' (i + 1)) - (V i - V' i)‖ := by congr 1; abel
        _ ≤ ‖V (i + 1) - V' (i + 1)‖ + ‖V i - V' i‖ := norm_sub_le _ _
        _ ≤ 2 * η := by linarith
    have e : plen V i + ‖V (i + 1) - V i‖ - (plen V' i + ‖V' (i + 1) - V' i‖) =
        (plen V i - plen V' i) + (‖V (i + 1) - V i‖ - ‖V' (i + 1) - V' i‖) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith

/-- The elementary ramp comparison: `|(s-a)/(b-a) - (s-a')/(b'-a')| ≤ 2ε/h₀² + ε/h₀` for
`s, a ∈ [0,1]`, gaps `≥ h₀ > 0` and endpoint errors `≤ ε`. -/
theorem abs_ramp_div_sub_le {s a b a' b' h₀ ε : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hh₀ : 0 < h₀) (hh : h₀ ≤ b - a) (hh' : h₀ ≤ b' - a') (hda : |a - a'| ≤ ε)
    (hdb : |b - b'| ≤ ε) :
    |(s - a) / (b - a) - (s - a') / (b' - a')| ≤ 2 * ε / h₀ ^ 2 + ε / h₀ := by
  have hp : 0 < b - a := hh₀.trans_le hh
  have hp' : 0 < b' - a' := hh₀.trans_le hh'
  have hε : 0 ≤ ε := (abs_nonneg _).trans hda
  have key : (s - a) / (b - a) - (s - a') / (b' - a') =
      ((s - a) * ((b' - a') - (b - a)) + (a' - a) * (b - a)) / ((b - a) * (b' - a')) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (mul_pos hp hp')]
  have e1 : |s - a| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |(b' - a') - (b - a)| ≤ 2 * ε := by
    have : (b' - a') - (b - a) = -(b - b') + (a - a') := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith
  have hnum : |(s - a) * ((b' - a') - (b - a)) + (a' - a) * (b - a)| ≤ 2 * ε + ε * (b - a) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hp]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_right (by rwa [abs_sub_comm]) hp.le)
    calc |s - a| * |(b' - a') - (b - a)| ≤ 1 * (2 * ε) :=
          mul_le_mul e1 e2 (abs_nonneg _) zero_le_one
      _ = 2 * ε := one_mul _
  rw [div_le_iff₀ (mul_pos hp hp')]
  have t1 : 2 * ε ≤ 2 * ε / h₀ ^ 2 * ((b - a) * (b' - a')) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : h₀ ^ 2 ≤ (b - a) * (b' - a') := by
      rw [sq]; exact mul_le_mul hh hh' hh₀.le hp.le
    nlinarith
  have t2 : ε * (b - a) ≤ ε / h₀ * ((b - a) * (b' - a')) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hh₀]
    have := mul_le_mul_of_nonneg_left hh' (mul_nonneg hε hp.le)
    nlinarith
  linarith

/-- The coupling constant of `coupledWithin_polyMeasure_of_close`. -/
def cplConst (m : ℕ) (c D : ℝ) : ℝ :=
  1 + m * (2 + D * (8 * m * (m * D / c) ^ 2 + 4 * m * (m * D / c)))

theorem cplConst_nonneg (m : ℕ) {c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D) : 0 ≤ cplConst m c D := by
  unfold cplConst; positivity

/-- **Coupling of polygons with nearby vertices** (HA3 D5, Step 1b, "parametrization bound"):
two polygons with `m ≥ 1` edges of lengths in `[c, D]` (`c > 0`), total lengths `≥ 1`, and
vertices within `η` have normalized arclength measures coupled within `cplConst m c D · η`. -/
theorem coupledWithin_polyMeasure_of_close {m : ℕ} (hm : 0 < m) {V V' : ℕ → Rd d} {c D η : ℝ}
    (hc : 0 < c) (hℓ : ∀ i < m, c ≤ ‖V (i + 1) - V i‖ ∧ ‖V (i + 1) - V i‖ ≤ D)
    (hℓ' : ∀ i < m, c ≤ ‖V' (i + 1) - V' i‖ ∧ ‖V' (i + 1) - V' i‖ ≤ D)
    (hS : 1 ≤ plen V m) (hS' : 1 ≤ plen V' m) (hη : ∀ i ≤ m, ‖V i - V' i‖ ≤ η) :
    HigherDimLFPP.CoupledWithin (polyMeasure ((List.range (m + 1)).map V))
      (polyMeasure ((List.range (m + 1)).map V')) (cplConst m c D * η) := by
  have hpos : ∀ i < m, 0 < ‖V (i + 1) - V i‖ := fun i hi => hc.trans_le (hℓ i hi).1
  have hpos' : ∀ i < m, 0 < ‖V' (i + 1) - V' i‖ := fun i hi => hc.trans_le (hℓ' i hi).1
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 (Nat.zero_le _))
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hD : c ≤ D := (hℓ 0 hm).1.trans (hℓ 0 hm).2
  have hD0 : 0 < D := hc.trans_le hD
  rw [polyMeasure_eq_map_rampPath hm V hpos, polyMeasure_eq_map_rampPath hm V' hpos']
  refine coupledWithin_map (continuous_rampPath _ _ _).measurable
    (continuous_rampPath _ _ _).measurable fun s hs => ?_
  refine (norm_rampPath_sub_le m _ _ V V' s).trans ?_
  set S := plen V m with hSdef
  set S' := plen V' m with hS'def
  have hS0 : 0 < S := lt_of_lt_of_le one_pos hS
  have hS0' : 0 < S' := lt_of_lt_of_le one_pos hS'
  -- the lengths
  have hSle : S ≤ m * D := by
    rw [hSdef, plen]
    calc ∑ j ∈ Finset.range m, ‖V (j + 1) - V j‖ ≤ ∑ _j ∈ Finset.range m, D :=
          Finset.sum_le_sum fun j hj => (hℓ j (Finset.mem_range.1 hj)).2
      _ = m * D := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSle' : S' ≤ m * D := by
    rw [hS'def, plen]
    calc ∑ j ∈ Finset.range m, ‖V' (j + 1) - V' j‖ ≤ ∑ _j ∈ Finset.range m, D :=
          Finset.sum_le_sum fun j hj => (hℓ' j (Finset.mem_range.1 hj)).2
      _ = m * D := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hP := abs_plen_sub_plen_le hη
  have hT : ∀ i ≤ m, |plen V i / S - plen V' i / S'| ≤ 4 * m * η := by
    intro i hi
    have hPi : |plen V i - plen V' i| ≤ 2 * m * η :=
      (hP i hi).trans (by gcongr)
    have hSS : |S - S'| ≤ 2 * m * η := (hP m le_rfl)
    have hP'i : plen V' i ≤ S' := plen_mono V' hi
    have e : plen V i / S - plen V' i / S' =
        (plen V i - plen V' i) / S + plen V' i * (S' - S) / (S * S') := by
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hS0, abs_div, abs_mul, abs_of_nonneg (plen_nonneg V' i),
      abs_of_pos (mul_pos hS0 hS0'), abs_sub_comm S' S]
    have t1 : |plen V i - plen V' i| / S ≤ 2 * m * η :=
      (div_le_self (abs_nonneg _) hS).trans hPi
    have t2 : plen V' i * |S - S'| / (S * S') ≤ 2 * m * η := by
      rw [div_le_iff₀ (mul_pos hS0 hS0')]
      have h1 : plen V' i * |S - S'| ≤ S' * (2 * m * η) :=
        mul_le_mul hP'i hSS (abs_nonneg _) hS0'.le
      have h2 : S' * (2 * m * η) ≤ 2 * m * η * (S * S') := by
        have : S' ≤ S * S' := le_mul_of_one_le_left hS0'.le hS
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg m)) hη0]
      linarith
    linarith
  have hT01 : ∀ i ≤ m, 0 ≤ plen V i / S ∧ plen V i / S ≤ 1 := fun i hi =>
    ⟨div_nonneg (plen_nonneg V i) hS0.le, (div_le_one hS0).2 (plen_mono V hi)⟩
  have hc' : 0 < c / (m * D) := by positivity
  have hgap : ∀ i < m, c / (m * D) ≤ plen V (i + 1) / S - plen V i / S := by
    intro i hi
    rw [plen_succ, ← sub_div, add_sub_cancel_left]
    calc c / (m * D) ≤ c / S := div_le_div_of_nonneg_left hc.le hS0 hSle
      _ ≤ ‖V (i + 1) - V i‖ / S := div_le_div_of_nonneg_right (hℓ i hi).1 hS0.le
  have hgap' : ∀ i < m, c / (m * D) ≤ plen V' (i + 1) / S' - plen V' i / S' := by
    intro i hi
    rw [plen_succ, ← sub_div, add_sub_cancel_left]
    calc c / (m * D) ≤ c / S' := div_le_div_of_nonneg_left hc.le hS0' hSle'
      _ ≤ ‖V' (i + 1) - V' i‖ / S' := div_le_div_of_nonneg_right (hℓ' i hi).1 hS0'.le
  set X := 8 * m * (m * D / c) ^ 2 + 4 * m * (m * D / c) with hX
  have hX0 : 0 ≤ X := by positivity
  have hramp : ∀ i < m, |ramp (plen V i / S) (plen V (i + 1) / S) s -
      ramp (plen V' i / S') (plen V' (i + 1) / S') s| ≤ X * η := by
    intro i hi
    refine (abs_ramp_sub_le _ _ _ _ s).trans ?_
    refine (abs_ramp_div_sub_le hs.1 hs.2 (hT01 i hi.le).1 (hT01 i hi.le).2 hc' (hgap i hi)
      (hgap' i hi) (hT i hi.le) (hT (i + 1) hi)).trans (le_of_eq ?_)
    rw [hX]
    field_simp
    ring
  -- assemble
  have hdiff : ∀ i < m, ‖(V (i + 1) - V i) - (V' (i + 1) - V' i)‖ ≤ 2 * η := by
    intro i hi
    calc ‖(V (i + 1) - V i) - (V' (i + 1) - V' i)‖ =
          ‖(V (i + 1) - V' (i + 1)) - (V i - V' i)‖ := by congr 1; abel
      _ ≤ ‖V (i + 1) - V' (i + 1)‖ + ‖V i - V' i‖ := norm_sub_le _ _
      _ ≤ 2 * η := by linarith [hη (i + 1) hi, hη i hi.le]
  calc ‖V 0 - V' 0‖ + ∑ i ∈ Finset.range m, (‖(V (i + 1) - V i) - (V' (i + 1) - V' i)‖ +
        |ramp (plen V i / S) (plen V (i + 1) / S) s -
          ramp (plen V' i / S') (plen V' (i + 1) / S') s| * ‖V' (i + 1) - V' i‖)
      ≤ η + ∑ _i ∈ Finset.range m, (2 * η + X * η * D) := by
        refine add_le_add (hη 0 (Nat.zero_le _)) (Finset.sum_le_sum fun i hi => ?_)
        have hi' := Finset.mem_range.1 hi
        exact add_le_add (hdiff i hi') (mul_le_mul (hramp i hi') (hℓ' i hi').2 (norm_nonneg _)
          (by positivity))
    _ = cplConst m c D * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, cplConst, ← hX]
        ring

end Coupling

/-! ## The unit good family -/

section UnitFamily

/-- The `i`-th vertex of a vertex list (`0` past its end). -/
def vtx (Q : List (Rd d)) (i : ℕ) : Rd d := Q.getD i 0

theorem vtx_range_map (V : ℕ → Rd d) {m i : ℕ} (hi : i ≤ m) :
    vtx ((List.range (m + 1)).map V) i = V i := by
  rw [vtx, List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- The facts about a polygon `Q ∈ G_K(0, e₁)` (threshold `a₀ ≤ 1/2`) used in Step 1: its vertex
form, edge lengths in `[1/K, 2]`, total length in `[1, 2]`, vertices in the ball of radius `2`,
and the vertex closeness of HA3 D4 (c). -/
theorem unitGood_facts (hd : 0 < d) {K : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d)) :
    1 ≤ K ∧ Q = (List.range (K + 1)).map (vtx Q) ∧ vtx Q 0 = 0 ∧ vtx Q K = e₁ d ∧
      (∀ i < K, 1 / (K : ℝ) ≤ ‖vtx Q (i + 1) - vtx Q i‖ ∧ ‖vtx Q (i + 1) - vtx Q i‖ ≤ 2) ∧
      polyLen Q = plen (vtx Q) K ∧ 1 ≤ plen (vtx Q) K ∧ plen (vtx Q) K ≤ 2 ∧
      (∀ i ≤ K, ‖vtx Q i‖ ≤ 2) ∧
      (∀ i ≤ K, ‖vtx Q i - ((i : ℝ) / K) • e₁ d‖ ≤ 2 * Real.sqrt (Real.log (polyLen Q))) := by
  have he : ‖e₁ d - 0‖ = 1 := by rw [sub_zero, Lower.norm_e₁ hd]
  have hne : (0 : Rd d) ≠ e₁ d := by
    intro h
    have := Lower.norm_e₁ hd (d := d)
    rw [← h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨V, hQV, hV0, hVK, hreg, -, hpoly⟩ := goodFamily_vertex hQ
  have hK : 1 ≤ K := by
    by_contra h
    have hK0 : K = 0 := by omega
    rw [hK0] at hVK
    exact hne (hV0.symm.trans hVK)
  have hvtx : ∀ i ≤ K, vtx Q i = V i := fun i hi => by rw [hQV]; exact vtx_range_map V hi
  have hplen : plen (vtx Q) K = plen V K :=
    Finset.sum_congr rfl fun j hj => by
      have hj' := Finset.mem_range.1 hj
      rw [hvtx (j + 1) hj', hvtx j hj'.le]
  have hpolyQ : polyLen Q = plen V K := by rw [hQV, polyLen_range_map]; rfl
  have hS1 : 1 ≤ plen V K := by
    have := norm_sub_le_plen V K
    rwa [hV0, hVK, sub_zero, Lower.norm_e₁ hd] at this
  have hexp : Real.exp a₀ ≤ 2 := by
    rcases le_total a₀ 0 with h0 | h0
    · exact (Real.exp_le_one_iff.2 h0).trans (by norm_num)
    · have := exp_le_one_add_add_sq h0 (by linarith)
      nlinarith
  have hS2 : plen V K ≤ 2 := by
    rw [he, mul_one] at hpoly
    linarith
  have hlast := goodFamily_lastEdge hQ hne
  rw [he] at hlast
  have hedge : ∀ i < K, 1 / (K : ℝ) ≤ ‖V (i + 1) - V i‖ ∧ ‖V (i + 1) - V i‖ ≤ 2 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · by_cases hi' : i + 1 < K
      · rw [hreg i hi', he]
      · have hiK : i = K - 1 := by omega
        have := hlast (V (K - 1), V K) (by
          rw [hQV, getLast?_edges hK]; rfl)
        rw [hiK, Nat.sub_add_cancel hK]
        exact this
    · calc ‖V (i + 1) - V i‖ ≤ plen V K :=
            Finset.single_le_sum (f := fun j => ‖V (j + 1) - V j‖) (fun j _ => norm_nonneg _)
              (Finset.mem_range.2 hi)
        _ ≤ 2 := hS2
  refine ⟨hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [hQV]
    exact List.map_congr_left fun i hi => (hvtx i (by
      have := List.mem_range.1 hi; omega)).symm
  · rw [hvtx 0 (Nat.zero_le _), hV0]
  · rw [hvtx K le_rfl, hVK]
  · intro i hi
    rw [hvtx (i + 1) hi, hvtx i hi.le]
    exact hedge i hi
  · rw [hplen, hpolyQ]
  · rwa [hplen]
  · rwa [hplen]
  · intro i hi
    rw [hvtx i hi]
    have h1 := norm_sub_le_plen V i
    rw [hV0, sub_zero] at h1
    exact h1.trans ((plen_mono V hi).trans hS2)
  · intro i hi
    have hlen : i < Q.length := by rw [hQ.1]; omega
    have h := goodFamily_vertex_close hQ hne (by linarith) i hlen
    simp only [sub_zero] at h
    rw [Lower.norm_e₁ hd, mul_one, div_one] at h
    rwa [vtx, List.getD_eq_getElem _ _ hlen]

end UnitFamily

/-! ## The process `Z` on the unit good family -/

section ShapeVectors

variable {κ : Rd d → ℝ}

/-- The white-noise vector of `⟨h, ν_I - ν_Q⟩`, `I = [0, e₁]`, for the all-scale field of the
kernel `κ`: `⟪shapeV κ Q, shapeV κ Q'⟫ = Λ(ν_I - ν_Q, ν_I - ν_{Q'})`. -/
def shapeV (κ : Rd d → ℝ) (Q : List (Rd d)) : WN d :=
  bandVecM κ (Ioi 0) (segMeasure 0 (e₁ d)) (polyMeasure Q)

/-- The penalty `E_δ(Q) = δ^{-2} log len(Q)` of a polygon of the unit chord. -/
def eDelta (δ : ℝ) (Q : List (Rd d)) : ℝ := (δ ^ 2)⁻¹ * Real.log (polyLen Q)

/-- The covariance `α² δ⁻¹ Λ(ν_I - ν_Q, ν_I - ν_{Q'})` of `α Z`. -/
def zKer (κ : Rd d → ℝ) (α δ : ℝ) (Q Q' : List (Rd d)) : ℝ :=
  α ^ 2 * (δ⁻¹ * ⟪shapeV κ Q, shapeV κ Q'⟫)

theorem psdOn_zKer (F : Finset (List (Rd d))) (α : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    PSDOn F (zKer κ α δ) :=
  HigherDimLFPP.Var.psdOn_const_mul (HigherDimLFPP.Var.psdOn_const_mul
    (show PSDOn F (fun Q Q' => ⟪shapeV κ Q, shapeV κ Q'⟫) from
      LQGDimension.posSemidef_gramOn F (shapeV κ)) (inv_nonneg.2 hδ)) (sq_nonneg α)

theorem eDelta_nonneg (hd : 0 < d) {K : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d)) (δ : ℝ) : 0 ≤ eDelta δ Q := by
  obtain ⟨-, -, -, -, -, hpoly, hS1, -⟩ := unitGood_facts hd ha₀ hQ
  exact mul_nonneg (inv_nonneg.2 (sq_nonneg δ)) (Real.log_nonneg (by rw [hpoly]; exact hS1))

theorem zero_ne_e₁ (hd : 0 < d) : (0 : Rd d) ≠ e₁ d := by
  intro h
  have := Lower.norm_e₁ hd (d := d)
  rw [← h, norm_zero] at this
  exact zero_ne_one this

/-- Lemma 3.1 inputs for `Q ∈ G`: probability, growth `3` at scale `1`, and the chord coupling of
HA3 D4 (b) within `2 √a`, `a = log len(Q)`. -/
theorem unitGood_pair (hd : 0 < d) {K : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)}
    (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d)) :
    IsProbabilityMeasure (polyMeasure Q) ∧ HigherDimLFPP.GrowthBound (polyMeasure Q) 3 1 ∧
      HigherDimLFPP.GrowthBound (segMeasure 0 (e₁ d)) 3 1 ∧
      HigherDimLFPP.CoupledWithin (segMeasure 0 (e₁ d)) (polyMeasure Q)
        (2 * Real.sqrt (Real.log (polyLen Q))) := by
  have hne := zero_ne_e₁ hd
  have he : ‖e₁ d - 0‖ = 1 := by rw [sub_zero, Lower.norm_e₁ hd]
  refine ⟨goodFamily_isProbabilityMeasure hQ hne, ?_, ?_, ?_⟩
  · have := goodFamily_growthBound hQ hne
    rwa [he] at this
  · have := segMeasure_growthBound hne
    rw [he] at this
    exact HigherDimLFPP.GrowthBound.mono_const (μ := segMeasure 0 (e₁ d)) this one_pos
      (by norm_num)
  · have := goodFamily_coupled hQ hne (by linarith)
    rwa [he, mul_one, div_one] at this

variable {C : ℝ}

/-- The transport hypothesis (`transport_var_bound` for growth constant `3`). -/
abbrev TransportVar3 (κ : Rd d → ℝ) (C : ℝ) : Prop :=
  ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 →
    ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (R u : ℝ),
      0 < R → 0 ≤ u → HigherDimLFPP.GrowthBound μ 3 R → HigherDimLFPP.GrowthBound ν 3 R →
      HigherDimLFPP.CoupledWithin μ ν u → IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ C * u / R

theorem isPairable_shape (hd : 0 < d) (hC : TransportVar3 κ C) {K : ℕ} {a₀ : ℝ}
    (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)} (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d)) :
    IsPairable κ (Ioi 0) (segMeasure 0 (e₁ d)) (polyMeasure Q) := by
  obtain ⟨hp, g1, g2, cpl⟩ := unitGood_pair hd ha₀ hQ
  exact (hC (Ioi 0) measurableSet_Ioi subset_rfl _ _ 1 _ one_pos (by positivity) g2 g1 cpl).1

/-- **The variance bound of (4.12)**: `Λ(ν_I - ν_Q) ≤ C · 2 √(log len Q)` for `Q ∈ G`. -/
theorem norm_shapeV_sq_le (hd : 0 < d) (hC : TransportVar3 κ C) {K : ℕ} {a₀ : ℝ}
    (ha₀ : a₀ ≤ 1 / 2) {Q : List (Rd d)} (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d)) :
    ‖shapeV κ Q‖ ^ 2 ≤ C * (2 * Real.sqrt (Real.log (polyLen Q))) := by
  obtain ⟨hp, g1, g2, cpl⟩ := unitGood_pair hd ha₀ hQ
  have h := (hC (Ioi 0) measurableSet_Ioi subset_rfl _ _ 1 _ one_pos (by positivity) g2 g1 cpl).2
  rw [div_one] at h
  rw [shapeV, ← scaleCov_self]
  exact h

/-- Increments of `Z`: `shapeV Q - shapeV Q' = v(ν_{Q'}, ν_Q)`. -/
theorem shapeV_sub (hκ : IsLFPPKernel κ) {Q Q' : List (Rd d)} [IsFiniteMeasure (polyMeasure Q)]
    [IsFiniteMeasure (polyMeasure Q')]
    (h : IsPairable κ (Ioi 0) (segMeasure 0 (e₁ d)) (polyMeasure Q))
    (h' : IsPairable κ (Ioi 0) (segMeasure 0 (e₁ d)) (polyMeasure Q')) :
    shapeV κ Q - shapeV κ Q' = bandVecM κ (Ioi 0) (polyMeasure Q') (polyMeasure Q) := by
  rw [shapeV, shapeV, bandVecM_sub_bandVecM hκ h h',
    add_comm (segMeasure 0 (e₁ d)) (polyMeasure Q'), bandVecM_add_right hκ]

/-- **The modulus of (4.12)**: for `Q, Q' ∈ G` (threshold `≤ 1/2`, `K ≥ 1` edges) with vertices
within `η`, `Λ(ν_Q - ν_{Q'}) ≤ C · cplConst K (1/K) 2 · η`. -/
theorem norm_shapeV_sub_sq_le (hd : 0 < d) (hκ : IsLFPPKernel κ) (hC : TransportVar3 κ C)
    {K : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {Q Q' : List (Rd d)} (hQ : Q ∈ goodFamily K a₀ 0 (e₁ d))
    (hQ' : Q' ∈ goodFamily K a₀ 0 (e₁ d)) {η : ℝ} (hη : ∀ i ≤ K, ‖vtx Q' i - vtx Q i‖ ≤ η) :
    ‖shapeV κ Q - shapeV κ Q'‖ ^ 2 ≤ C * (cplConst K (1 / K) 2 * η) := by
  obtain ⟨hp, g1, g2, -⟩ := unitGood_pair hd ha₀ hQ
  obtain ⟨hp', g1', -, -⟩ := unitGood_pair hd ha₀ hQ'
  obtain ⟨hK, hQV, -, -, hedge, -, hS1, -, -, -⟩ := unitGood_facts hd ha₀ hQ
  obtain ⟨-, hQV', -, -, hedge', -, hS1', -, -, -⟩ := unitGood_facts hd ha₀ hQ'
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 (Nat.zero_le _))
  have hcpl : HigherDimLFPP.CoupledWithin (polyMeasure Q') (polyMeasure Q)
      (cplConst K (1 / K) 2 * η) := by
    have h := coupledWithin_polyMeasure_of_close (m := K) hK (V := vtx Q') (V' := vtx Q)
      (c := 1 / K) (D := 2) (η := η) (by positivity) hedge' hedge hS1' hS1 hη
    rwa [← hQV, ← hQV'] at h
  have hu : 0 ≤ cplConst K (1 / K) 2 * η :=
    mul_nonneg (cplConst_nonneg K (by positivity) (by norm_num)) hη0
  have h := (hC (Ioi 0) measurableSet_Ioi subset_rfl _ _ 1 _ one_pos hu g1' g1 hcpl).2
  rw [div_one] at h
  rw [shapeV_sub hκ (isPairable_shape hd hC ha₀ hQ) (isPairable_shape hd hC ha₀ hQ'),
    ← scaleCov_self]
  exact h

end ShapeVectors

/-! ## Vertex coordinates and chaining on shells -/

section Chaining

/-- The Euclidean norm is at most `√d` times the sup norm of the coordinates. -/
theorem norm_le_sqrt_mul_sup (z : Rd d) : ‖z‖ ≤ Real.sqrt d * ‖WithLp.ofLp z‖ := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d, ‖z.ofLp i‖ ^ 2 ≤ d * ‖WithLp.ofLp z‖ ^ 2 := by
    calc ∑ i : Fin d, ‖z.ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, ‖WithLp.ofLp z‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
            (norm_le_pi_norm (WithLp.ofLp z) i) 2
      _ = d * ‖WithLp.ofLp z‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin d, ‖z.ofLp i‖ ^ 2) ≤ Real.sqrt (d * ‖WithLp.ofLp z‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ‖WithLp.ofLp z‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The rescaled vertex coordinates `p(Q) = (z_i/δ)_{i ≤ K}` of a polygon, `K = 2ⁿ`. -/
def vparam (n : ℕ) (δ : ℝ) (Q : List (Rd d)) : Fin ((2 ^ n + 1) * d) → ℝ := fun k =>
  (vtx Q (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 / δ

theorem norm_vtx_sub_le_vparam {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (Q Q' : List (Rd d)) {i : ℕ}
    (hi : i ≤ 2 ^ n) :
    ‖vtx Q i - vtx Q' i‖ ≤ Real.sqrt d * δ * ‖vparam n δ Q - vparam n δ Q'‖ := by
  refine (norm_le_sqrt_mul_sup _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have h := norm_le_pi_norm (vparam n δ Q - vparam n δ Q')
    (finProdFinEquiv ((⟨i, Nat.lt_succ_of_le hi⟩ : Fin (2 ^ n + 1)), j))
  simp only [Pi.sub_apply, vparam, Equiv.symm_apply_apply, Real.norm_eq_abs] at h ⊢
  rw [← sub_div, abs_div, abs_of_pos hδ, div_le_iff₀ hδ] at h
  simp only [WithLp.ofLp_sub, Pi.sub_apply]
  linarith

theorem abs_vparam_sub_le (hd : 0 < d) {n : ℕ} {a₀ : ℝ} (ha₀ : a₀ ≤ 1 / 2) {δ : ℝ} (hδ : 0 < δ)
    {Q Q' : List (Rd d)} (hQ : Q ∈ goodFamily (2 ^ n) a₀ 0 (e₁ d))
    (hQ' : Q' ∈ goodFamily (2 ^ n) a₀ 0 (e₁ d)) {R : ℝ} (hR : eDelta δ Q ≤ R)
    (hR' : eDelta δ Q' ≤ R) : ‖vparam n δ Q - vparam n δ Q'‖ ≤ 4 * Real.sqrt R := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hclose⟩ := unitGood_facts hd ha₀ hQ
  obtain ⟨-, -, -, -, -, -, -, -, -, hclose'⟩ := unitGood_facts hd ha₀ hQ'
  have hlog : ∀ P : List (Rd d), eDelta δ P ≤ R →
      2 * Real.sqrt (Real.log (polyLen P)) ≤ 2 * δ * Real.sqrt R := by
    intro P hP
    have h1 : Real.log (polyLen P) ≤ δ ^ 2 * R := by
      rw [eDelta, inv_mul_le_iff₀ (by positivity)] at hP
      exact hP
    calc 2 * Real.sqrt (Real.log (polyLen P)) ≤ 2 * Real.sqrt (δ ^ 2 * R) := by
          gcongr
      _ ≤ 2 * δ * Real.sqrt R := by
          rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le, mul_assoc]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  simp only [Pi.sub_apply, vparam, Real.norm_eq_abs]
  rw [← sub_div, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
  set ij := finProdFinEquiv.symm k
  have hik : (ij.1 : ℕ) ≤ 2 ^ n := Nat.le_of_lt_succ ij.1.2
  have h1 := (hclose ij.1 hik).trans (hlog Q hR)
  have h2 := (hclose' ij.1 hik).trans (hlog Q' hR')
  have h3 : ‖vtx Q ij.1 - vtx Q' ij.1‖ ≤ 2 * δ * Real.sqrt R + 2 * δ * Real.sqrt R := by
    calc ‖vtx Q ij.1 - vtx Q' ij.1‖ =
          ‖(vtx Q ij.1 - ((ij.1 : ℕ) / (2 ^ n : ℕ) : ℝ) • e₁ d) -
            (vtx Q' ij.1 - ((ij.1 : ℕ) / (2 ^ n : ℕ) : ℝ) • e₁ d)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
  have h4 := PiLp.norm_apply_le (vtx Q ij.1 - vtx Q' ij.1) ij.2
  rw [WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at h4
  linarith

theorem a0_le_half (n : ℕ) : a0 n ≤ 1 / 2 := by
  unfold a0
  have h : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The constant of the shell bound: `40 √5 √(C · cplConst · √d) √(D + 1)`, `D = (2ⁿ+1) d`. -/
def shellConst (d n : ℕ) (C : ℝ) : ℝ :=
  40 * Real.sqrt 5 * Real.sqrt (C * cplConst (2 ^ n) (1 / (2 ^ n : ℕ)) 2 * Real.sqrt d) *
    Real.sqrt ((((2 ^ n + 1) * d : ℕ) : ℝ) + 1)

theorem shellConst_nonneg (d n : ℕ) (C : ℝ) : 0 ≤ shellConst d n C := by
  unfold shellConst; positivity

/-- The canonical distance of `αZ` (`zKer`) in terms of `shapeV`. -/
theorem zKer_dist {κ : Rd d → ℝ} (α δ : ℝ) (Q Q' : List (Rd d)) :
    zKer κ α δ Q Q + zKer κ α δ Q' Q' - 2 * zKer κ α δ Q Q' =
      α ^ 2 * (δ⁻¹ * ‖shapeV κ Q - shapeV κ Q'‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [zKer]
  rw [real_inner_comm (shapeV κ Q') (shapeV κ Q)]
  ring

/-- **The mean bound of (4.12) by chaining** (HA3 D5, Step 1b): for finite `F ⊆ G` with
`E_δ ≤ R` on `F` (`R ≥ 1`), `E max_F αZ ≤ α · shellConst · √R`. -/
theorem gEM_shell_le (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : TransportVar3 κ C) (n : ℕ) {α δ R : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hR : 1 ≤ R)
    (F : Finset (List (Rd d))) (hF : ↑F ⊆ goodFamily (2 ^ n) (a0 n) 0 (e₁ d))
    (hFR : ∀ Q ∈ F, eDelta δ Q ≤ R) :
    gaussianExpectedMax F (zKer κ α δ) (fun _ => 0) ≤ α * shellConst d n C * Real.sqrt R := by
  have ha₀ : a0 n ≤ 1 / 2 := a0_le_half n
  rcases F.eq_empty_or_nonempty with rfl | ⟨Q₁, hQ₁⟩
  · rw [HigherDimLFPP.Var.gEM_empty]
    have := shellConst_nonneg d n C
    positivity
  obtain ⟨v, hv, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F _
    (psdOn_zKer (κ := κ) F α hδ.le)
  rw [hvE]
  set cc := cplConst (2 ^ n) (1 / (2 ^ n : ℕ)) 2 with hcc
  have hcc0 : 0 ≤ cc := cplConst_nonneg _ (by positivity) (by norm_num)
  set L := α * Real.sqrt (C * cc * Real.sqrt d) with hL
  have hL0 : 0 ≤ L := by positivity
  have hvv : ∀ Q ∈ F, ∀ Q' ∈ F, ‖v Q - v Q'‖ ^ 2 ≤
      L ^ 2 * ‖vparam n δ Q - vparam n δ Q'‖ := by
    intro Q hQ Q' hQ'
    rw [norm_sub_sq_eq_of_gram hv hQ hQ', zKer_dist]
    have hm := norm_shapeV_sub_sq_le hd hκ hC ha₀ (hF hQ) (hF hQ')
      (η := Real.sqrt d * δ * ‖vparam n δ Q - vparam n δ Q'‖) fun i hi => by
        rw [norm_sub_rev]
        exact norm_vtx_sub_le_vparam hδ Q Q' hi
    have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    rw [hcast] at hm
    rw [hL, mul_pow, Real.sq_sqrt (by positivity)]
    have e : α ^ 2 * (δ⁻¹ * (C * (cc * (Real.sqrt d * δ * ‖vparam n δ Q - vparam n δ Q'‖)))) =
        α ^ 2 * (C * cc * Real.sqrt d) * ‖vparam n δ Q - vparam n δ Q'‖ := by
      field_simp
    rw [← e, hcc]
    have hcast' : (1 / ((2 ^ n : ℕ) : ℝ)) = 1 / (2 : ℝ) ^ n := by rw [hcast]
    rw [hcast']
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (inv_nonneg.2 hδ.le))
      (sq_nonneg α)
  have hp : ∀ Q ∈ F, ∀ Q' ∈ F, ‖vparam n δ Q - vparam n δ Q'‖ ≤ 4 * Real.sqrt R :=
    fun Q hQ Q' hQ' => abs_vparam_sub_le hd ha₀ hδ (hF hQ) (hF hQ') (hFR Q hQ) (hFR Q' hQ')
  have hSF : vecExpectedMax F v (fun _ => 0) ≤
      vecExpectedMax F (fun Q => v Q - v Q₁) (fun _ => 0) :=
    LQGDimension.sudakovFernique (List (Rd d)) (EuclideanSpace ℝ F) (EuclideanSpace ℝ F) F v
      (fun Q => v Q - v Q₁) (fun _ => 0) (fun i _ j _ => by rw [sub_sub_sub_cancel_right])
  have hch := LQGDimension.ChainBox.chainingBox_bound F (vparam n δ) v hL0 hp hvv hQ₁
  refine hSF.trans (hch.trans ?_)
  -- `√((D+1) · 4√R) ≤ 2 √(D+1) √R`
  have hRR : Real.sqrt R ≤ R := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hD : (0 : ℝ) ≤ (((2 ^ n + 1) * d : ℕ) : ℝ) + 1 := by positivity
  have h1 : Real.sqrt (((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * (4 * Real.sqrt R)) ≤
      2 * Real.sqrt ((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * Real.sqrt R := by
    calc Real.sqrt (((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * (4 * Real.sqrt R))
        ≤ Real.sqrt (((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * (4 * R)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hD)
      _ = 2 * Real.sqrt ((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * Real.sqrt R := by
          rw [Real.sqrt_mul hD, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          ring
  calc 20 * Real.sqrt 5 * L * Real.sqrt (((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * (4 * Real.sqrt R))
      ≤ 20 * Real.sqrt 5 * L * (2 * Real.sqrt ((((2 ^ n + 1) * d : ℕ) : ℝ) + 1) * Real.sqrt R) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = α * shellConst d n C * Real.sqrt R := by
        rw [shellConst, hL, hcc]
        ring

end Chaining

/-! ## Shells (HA3 D5, Step 1c) -/

section Shells

/-- A geometric tail: `Σ_{k ∈ S} r^k ≤ r^{R₀}/(1 - r)` if every `k ∈ S` is `≥ R₀`. -/
theorem sum_pow_le_of_forall_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ) (R₀ : ℕ)
    (hS : ∀ k ∈ S, R₀ ≤ k) : ∑ k ∈ S, r ^ k ≤ r ^ R₀ / (1 - r) := by
  have hinj : Set.InjOn (fun k => k - R₀) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hS a ha
    have h2 := hS b hb
    simp only at hab
    omega
  have e : ∑ k ∈ S, r ^ k = r ^ R₀ * ∑ j ∈ S.image (fun k => k - R₀), r ^ j := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← pow_add, Nat.add_sub_cancel' (hS k hk)]
  rw [e, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr0 _)
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun _ _ => pow_nonneg hr0 _

/-- **Shells** (HA3 D5, Step 1c, with the fix F6): for `α, β, θ > 0` there is `R₀ ≥ 1` such that
for every `δ > 0` and every finite `F ⊆ G_K(0, e₁)` containing a polygon `Q₀` of value `0`
(`shapeV κ Q₀ = 0`, `E_δ(Q₀) = 0`; in the application the subdivided chord `Q_δ(0)`),
`E max_F (αZ - βE_δ) ≤ E max_{F ∩ {E_δ < R₀}} (αZ - βE_δ) + θ`. -/
theorem exists_shell_bound (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (n : ℕ)
    {α β θ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hθ : 0 < θ) :
    ∃ R₀ : ℕ, 1 ≤ R₀ ∧ ∀ δ : ℝ, 0 < δ → ∀ F : Finset (List (Rd d)),
      ↑F ⊆ goodFamily (2 ^ n) (a0 n) 0 (e₁ d) → ∀ Q₀ ∈ F, shapeV κ Q₀ = 0 → eDelta δ Q₀ = 0 →
      gaussianExpectedMax F (zKer κ α δ) (fun Q => -(β * eDelta δ Q)) ≤
        gaussianExpectedMax (F.filter (fun Q => eDelta δ Q < R₀)) (zKer κ α δ)
          (fun Q => -(β * eDelta δ Q)) + θ := by
  classical
  obtain ⟨C, hC0, hC⟩ := transport_var_bound hκ 3
  have ha₀ : a0 n ≤ 1 / 2 := a0_le_half n
  set A : ℝ := α * shellConst d n C + Real.pi ^ 2 / 8 * (2 * α ^ 2 * C) with hA
  have hA0 : 0 ≤ A := by have := shellConst_nonneg d n C; positivity
  set R₁ : ℕ := ⌈8 * A ^ 2 / β ^ 2⌉₊ + 1 with hR₁
  have key : ∀ k : ℕ, R₁ ≤ k → A * Real.sqrt ((k : ℝ) + 1) ≤ β * k / 2 := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_left 1 _).trans hk
    have hk8 : 8 * A ^ 2 / β ^ 2 ≤ k := by
      have := Nat.le_ceil (8 * A ^ 2 / β ^ 2)
      have h2 : ((⌈8 * A ^ 2 / β ^ 2⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.le_succ _).trans hk
      linarith
    rw [div_le_iff₀ (by positivity)] at hk8
    -- `A √(k+1) ≤ A √(2k) ≤ βk/2`
    have hsq : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt (2 * k) := Real.sqrt_le_sqrt (by linarith)
    have h2k : (A * Real.sqrt (2 * k)) ^ 2 ≤ (β * k / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
    have h3 : A * Real.sqrt (2 * k) ≤ β * k / 2 :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h2k
    exact (mul_le_mul_of_nonneg_left hsq hA0).trans h3
  set r := Real.exp (-β / 2) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hθ (sub_pos.2 hr1)) hr1
  refine ⟨max R₁ N, le_max_of_le_left (Nat.le_add_left 1 _), fun δ hδ F hF Q₀ hQ₀ hv₀ hE₀ => ?_⟩
  set R₀ := max R₁ N with hR₀
  obtain ⟨v, hv, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F _
    (psdOn_zKer (κ := κ) F α hδ.le)
  set b : List (Rd d) → ℝ := fun Q => -(β * eDelta δ Q) with hb
  set F' := F.filter (fun Q => eDelta δ Q < R₀) with hF'
  set sh : List (Rd d) → ℕ := fun Q => ⌊eDelta δ Q⌋₊ with hsh
  set S := (F.filter (fun Q => ¬ eDelta δ Q < R₀)).image sh with hS
  have hE0 : ∀ Q ∈ F, 0 ≤ eDelta δ Q := fun Q hQ => eDelta_nonneg hd ha₀ (hF hQ) δ
  -- the reference element
  have hQ₀' : Q₀ ∈ F' := Finset.mem_filter.2 ⟨hQ₀, by rw [hE₀]; positivity⟩
  have hvQ₀ : v Q₀ = 0 := by
    have h := hv Q₀ hQ₀ Q₀ hQ₀
    rw [zKer, hv₀, inner_zero_left, mul_zero, mul_zero, real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  have hcov : ∀ Q ∈ F, Q ∉ F' → sh Q ∈ S ∧ b Q ≤ -(fun k : ℕ => β * k) (sh Q) := by
    intro Q hQ hQ'
    have hnot : ¬ eDelta δ Q < R₀ := fun h => hQ' (Finset.mem_filter.2 ⟨hQ, h⟩)
    refine ⟨Finset.mem_image.2 ⟨Q, Finset.mem_filter.2 ⟨hQ, hnot⟩, rfl⟩, ?_⟩
    simp only [hb, hsh, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (hE0 Q hQ)) hβ.le
  have hmain := vecEM_le_add_sum_shells F F' v b hQ₀' hvQ₀ (by simp [hb, hE₀]) S sh
    (fun k : ℕ => β * k) hcov
  -- each shell
  have hterm : ∀ k ∈ S, ∫ x, max 0 ((⨆ i : F.filter (fun i => i ∉ F' ∧ sh i = k),
      ⟪v i, x⟫ + (fun _ => (0 : ℝ)) i) - (fun k : ℕ => β * k) k)
        ∂(stdGaussian (EuclideanSpace ℝ F)) ≤ r ^ k := by
    intro k hk
    obtain ⟨Q, hQ, hQk⟩ := Finset.mem_image.1 hk
    obtain ⟨hQF, hQnot⟩ := Finset.mem_filter.1 hQ
    have hkR₀ : R₀ ≤ k := by
      rw [← hQk]
      exact Nat.le_floor (le_of_not_gt hQnot)
    set Fk := F.filter (fun i => i ∉ F' ∧ sh i = k) with hFk
    have hFkF : Fk ⊆ F := Finset.filter_subset _ _
    have hFkE : ∀ P ∈ Fk, eDelta δ P ≤ (k : ℝ) + 1 := by
      intro P hP
      obtain ⟨-, -, hPk⟩ := Finset.mem_filter.1 hP
      have := Nat.lt_floor_add_one (eDelta δ P)
      simp only [hsh] at hPk
      rw [hPk] at this
      exact this.le
    -- variance bound on the shell
    have hσ : ∀ P ∈ Fk, ‖v P‖ ≤ Real.sqrt (2 * α ^ 2 * C * Real.sqrt ((k : ℝ) + 1)) := by
      intro P hP
      have hPF := hFkF hP
      refine Real.le_sqrt_of_sq_le ?_
      have h1 : ‖v P‖ ^ 2 = zKer κ α δ P P := by rw [← real_inner_self_eq_norm_sq, hv P hPF P hPF]
      rw [h1, zKer, real_inner_self_eq_norm_sq]
      have h2 := norm_shapeV_sq_le hd hC ha₀ (hF hPF)
      have h3 : Real.sqrt (Real.log (polyLen P)) ≤ δ * Real.sqrt ((k : ℝ) + 1) := by
        have h4 : Real.log (polyLen P) ≤ δ ^ 2 * ((k : ℝ) + 1) := by
          have := hFkE P hP
          rw [eDelta, inv_mul_le_iff₀ (by positivity)] at this
          exact this
        calc Real.sqrt (Real.log (polyLen P)) ≤ Real.sqrt (δ ^ 2 * ((k : ℝ) + 1)) :=
              Real.sqrt_le_sqrt h4
          _ = δ * Real.sqrt ((k : ℝ) + 1) := by
              rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
      calc α ^ 2 * (δ⁻¹ * ‖shapeV κ P‖ ^ 2) ≤ α ^ 2 * (δ⁻¹ * (C * (2 * (δ * Real.sqrt
            ((k : ℝ) + 1))))) := by
            gcongr
            exact h2.trans (by gcongr)
        _ = 2 * α ^ 2 * C * Real.sqrt ((k : ℝ) + 1) := by
            field_simp
    have hint := integral_max_zero_iSup_sub_le Fk v (fun _ => 0) hσ ((fun k : ℕ => β * k) k)
    -- the mean on the shell
    have hmean : vecExpectedMax Fk v (fun _ => 0) ≤
        α * shellConst d n C * Real.sqrt ((k : ℝ) + 1) := by
      have e : vecExpectedMax Fk v (fun _ => 0) =
          gaussianExpectedMax Fk (zKer κ α δ) (fun _ => 0) := by
        rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
        exact LQGDimension.gaussianExpectedMax_congr Fk _ fun i hi j hj =>
          hv i (hFkF hi) j (hFkF hj)
      rw [e]
      exact gEM_shell_le hd hκ hC0 hC n hα.le hδ (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
        Fk (fun P hP => hF (hFkF hP)) hFkE
    refine hint.trans ?_
    rw [Real.sq_sqrt (by positivity), hr, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hkR₁ : R₁ ≤ k := (le_max_left _ _).trans hkR₀
    have := key k hkR₁
    have hsplit : α * shellConst d n C * Real.sqrt ((k : ℝ) + 1) +
        Real.pi ^ 2 / 8 * (2 * α ^ 2 * C * Real.sqrt ((k : ℝ) + 1)) =
        A * Real.sqrt ((k : ℝ) + 1) := by rw [hA]; ring
    simp only
    nlinarith
  have hsum : ∑ k ∈ S, ∫ x, max 0 ((⨆ i : F.filter (fun i => i ∉ F' ∧ sh i = k),
      ⟪v i, x⟫ + (fun _ => (0 : ℝ)) i) - (fun k : ℕ => β * k) k)
        ∂(stdGaussian (EuclideanSpace ℝ F)) ≤ θ := by
    refine (Finset.sum_le_sum hterm).trans ?_
    have hS0 : ∀ k ∈ S, R₀ ≤ k := by
      intro k hk
      obtain ⟨Q, hQ, hQk⟩ := Finset.mem_image.1 hk
      rw [← hQk]
      exact Nat.le_floor (le_of_not_gt (Finset.mem_filter.1 hQ).2)
    refine (sum_pow_le_of_forall_le hr0.le hr1 S R₀ hS0).trans ?_
    rw [div_le_iff₀ (sub_pos.2 hr1)]
    have h1 : r ^ R₀ ≤ r ^ N := pow_le_pow_of_le_one hr0.le hr1.le (le_max_right _ _)
    linarith
  have hF'E : gaussianExpectedMax F' (zKer κ α δ) b = vecExpectedMax F' v b := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact LQGDimension.gaussianExpectedMax_congr F' _ fun i hi j hj =>
      (hv i (Finset.filter_subset _ _ hi) j (Finset.filter_subset _ _ hj)).symm
  rw [hvE, hF'E]
  linarith

end Shells

end HigherDimLFPP.Upper
