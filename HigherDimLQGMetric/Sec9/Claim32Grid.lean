import HigherDimLQGMetric.Sec9.Claim32Basic
import HigherDimLQGMetric.Sec6.Cor63
import HigherDimLQGMetric.Modulus.Grid
import HigherDimLQGMetric.Events.ScaledEvent

/-!
# Claim (32), part 2: the grid pair and the union bound (packet S8e)

Source: [S] §9, l. 1450–1475; MA4 Details (a) A17; planning draft
`planning/drafts/S7b-S8-plan.md` §3 (S8e, steps 5, 9, 10).

* `s8e_card_gridPairs_le`: the grid `w3bGrid d 3 R e` (W3b; lattice `(eR/(8d))ℤ^d` in `B_{4R}`)
  has at most `K_g/e^d` points, `K_g = (16d(3+1)+5)^d`, so at most `(K_g/e^d)²` ordered pairs.
* `s8e_gridPair_of_witEvent` (step 9, deterministic, for one distribution `g`): on the upper
  witness event `H⁺_R(t)` of the pair `(D, D̃)` (with length metrics and `D̃ ≤ C_* D` at `g`), on
  the macro-normalizer event `s_R(0) ≤ L S` ((33)) and on the upper-modulus event at scale `e`
  ([S] Lemma 2.6 with `L = 3`), there is a grid pair `(x′, y′)` in `B_{3R}` with
  `|x′ − y′| ≥ (β/2) R` satisfying (27) at `q` (`sec8C1 … Cs q R x′ y′ g`). The witness pair comes
  from D-H (v) (`s6b_witEvent_subset_gEvent`).
* `s8e_measure_lt` (step 10): outer-measure subadditivity for a set covered by four exceptional
  sets and a finite union of pair events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The number of ordered pairs of points of the grid `w3bGrid d 3 R e` (`0 < e ≤ 1`), restricted
by any predicate, is at most `((16d(3+1)+5)^d / e^d)²`. -/
theorem s8e_card_gridPairs_le (hd : 1 ≤ d) {R e : ℝ} (hR : 0 < R) (he0 : 0 < e) (he1 : e ≤ 1)
    (p : Rd d × Rd d → Prop) [DecidablePred p] :
    ((((w3bGrid d 3 R e) ×ˢ (w3bGrid d 3 R e)).filter p).card : ℝ) ≤
      ((16 * (d : ℝ) * (3 + 1) + 5) ^ d / e ^ d) ^ 2 := by
  set G := w3bGrid d 3 R e with hG_def
  have hG : (G.card : ℝ) ≤ (16 * (d : ℝ) * (3 + 1) + 5) ^ d / e ^ d :=
    w3b_card_grid_le hd (by norm_num) hR he0 he1
  have h1 : ((G ×ˢ G).filter p).card ≤ G.card * G.card := by
    rw [← Finset.card_product]
    exact Finset.card_filter_le _ _
  have h2 : ((((G ×ˢ G).filter p).card : ℕ) : ℝ) ≤ (G.card : ℝ) * G.card := by
    exact_mod_cast h1
  calc ((((G ×ˢ G).filter p).card : ℕ) : ℝ) ≤ (G.card : ℝ) * G.card := h2
    _ = (G.card : ℝ) ^ 2 := by ring
    _ ≤ ((16 * (d : ℝ) * (3 + 1) + 5) ^ d / e ^ d) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hG 2

/-- **Step 9 of (32), deterministic** ([S] l. 1460–1472; MA4 A17). Fix a distribution `g` at
which `D_g`, `D̃_g` are length metrics with `D̃_g ≤ C_* D_g`. Suppose `g` lies in the upper witness
event `H⁺_R(t) = WitEvent D Dt ξ Q C_* aU A₀U ℓU β₀U t R 0`, the macro-normalizer bound
`s_R(0) ≤ L S` holds, and the upper modulus at scale `e` holds on `B_{3R}`
(`|x − y| ≤ eR ⇒ D_g(x, y) ≤ e^α s_R(0)`). If `0 < β ≤ min(β₀U, ℓU/2, ℓU⁻¹)`,
`0 < e ≤ min(1, 2β)`, `C_* − t = βq/(4L)` and `4 C_* e^α L ≤ (3/4) q`, then some pair of grid
points `(x′, y′)` of `w3bGrid d 3 R e`, both in `B_{3R}`, with `|x′ − y′| ≥ (β/2) R`, satisfies (27)
at `q`: `C_* D_g(x′, y′) − q S ≤ D̃_g(x′, y′)`. -/
theorem s8e_gridPair_of_witEvent {D Dt : DistRd d → ContMetric d}
    {ξ Q Cs aU A₀U ℓU β₀U t β L R e α q : ℝ} {g : DistRd d}
    (hd : 1 ≤ d) (hR : 0 < R) (hℓU : 0 < ℓU) (hβ : 0 < β) (hββ₀ : β ≤ β₀U)
    (hβℓ : β ≤ ℓU / 2) (hβℓ' : β ≤ ℓU⁻¹) (hCs : 0 ≤ Cs) (hL : 0 < L) (hq : 0 ≤ q)
    (he0 : 0 < e) (he1 : e ≤ 1) (he2 : e ≤ 2 * β)
    (ht : Cs - t = β * q / (4 * L)) (hδ : 4 * Cs * e ^ α * L ≤ 3 / 4 * q)
    (hmac : sNorm ξ Q g R 0 ≤ L * macroS ξ Q g R)
    (hmod : ∀ x y : Rd d, ‖x‖ < 3 * R → ‖y‖ < 3 * R → ‖x - y‖ ≤ e * R →
      (D g).1 (x, y) ≤ e ^ α * sNorm ξ Q g R 0)
    (hlen : (D g).IsLength) (hlent : (Dt g).IsLength)
    (hcomp : ∀ u v : Rd d, (Dt g).1 (u, v) ≤ Cs * (D g).1 (u, v))
    (hw : g ∈ WitEvent D Dt ξ Q Cs aU A₀U ℓU β₀U t R 0) :
    ∃ p ∈ ((w3bGrid d 3 R e) ×ˢ (w3bGrid d 3 R e)).filter
        (fun p : Rd d × Rd d => ‖p.1‖ < 3 * R ∧ ‖p.2‖ < 3 * R ∧ β / 2 * R ≤ ‖p.1 - p.2‖),
      sec8C1 D Dt ξ Q Cs q R p.1 p.2 g := by
  obtain ⟨x, hx, y, hy, hxy, -, hDxy, hrat⟩ :=
    s6b_witEvent_subset_gEvent hR hℓU hlen hlent hcomp hβ hββ₀ hβℓ hβℓ' hw
  have hx2 : ‖x‖ ≤ 2 * R := mem_closedBall_zero_iff.1 hx
  have hy2 : ‖y‖ ≤ 2 * R := mem_closedBall_zero_iff.1 hy
  have hx3 : ‖x‖ < 3 * R := by linarith
  have hy3 : ‖y‖ < 3 * R := by linarith
  obtain ⟨x', hx'G, hxx'⟩ := w3b_exists_grid_near hd (by norm_num : (0 : ℝ) < 3) hR he0 he1 hx3
  obtain ⟨y', hy'G, hyy'⟩ := w3b_exists_grid_near hd (by norm_num : (0 : ℝ) < 3) hR he0 he1 hy3
  have hx'3 : ‖x'‖ < 3 * R := s8e_norm_lt_three hR he1 hx2 hxx'
  have hy'3 : ‖y'‖ < 3 * R := s8e_norm_lt_three hR he1 hy2 hyy'
  have hsep : β / 2 * R ≤ ‖x' - y'‖ := s8e_sep hR he2 hxy hxx' hyy'
  refine ⟨(x', y'), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx'G, hy'G⟩, hx'3, hy'3, hsep⟩, ?_⟩
  have hS0 : 0 ≤ macroS ξ Q g R := by
    unfold macroS
    exact mul_nonneg (Real.rpow_nonneg hR.le _) (Real.exp_pos _).le
  exact s8e_c1_of_near hCs hβ hL hS0 hq (Real.rpow_nonneg he0.le _) hcomp ht hDxy hrat hmac
    (hmod x x' hx3 hx'3 (s8e_norm_sub_le hR he0 hxx'))
    (hmod y y' hy3 hy'3 (s8e_norm_sub_le hR he0 hyy')) hδ

/-- **Step 10 of (32)**: outer-measure subadditivity. If `A` is covered by four exceptional sets
of outer measures `≤ x₀, x₁, x₂, 0` and a finite union of events of outer measure `≤ x_N` each,
and `x₀ + x₁ + x₂ + #s·x_N < p`, then `P(A) < p`. No measurability is used. -/
theorem s8e_measure_lt {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A S0 S1 S2 S3 : Set Ω} {s : Finset ι} {E : ι → Set Ω} {x0 x1 x2 xN p : ℝ}
    (hsub : A ⊆ S0 ∪ S1 ∪ S2 ∪ S3 ∪ ⋃ i ∈ s, E i)
    (h0 : P S0 ≤ ENNReal.ofReal x0) (h1 : P S1 ≤ ENNReal.ofReal x1)
    (h2 : P S2 ≤ ENNReal.ofReal x2) (h3 : P S3 = 0)
    (hE : ∀ i ∈ s, P (E i) ≤ ENNReal.ofReal xN)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hxN : 0 ≤ xN)
    (hsum : x0 + x1 + x2 + s.card * xN < p) :
    P A < ENNReal.ofReal p := by
  have hcN : 0 ≤ (s.card : ℝ) * xN := mul_nonneg (Nat.cast_nonneg _) hxN
  have hp : 0 < p := by linarith
  have hU : P (⋃ i ∈ s, E i) ≤ ENNReal.ofReal (s.card * xN) := by
    calc P (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, P (E i) := measure_biUnion_finset_le s E
      _ ≤ ∑ _i ∈ s, ENNReal.ofReal xN := Finset.sum_le_sum hE
      _ = s.card * ENNReal.ofReal xN := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (s.card * xN) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc P A ≤ P (S0 ∪ S1 ∪ S2 ∪ S3 ∪ ⋃ i ∈ s, E i) := measure_mono hsub
    _ ≤ P S0 + P S1 + P S2 + P S3 + P (⋃ i ∈ s, E i) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal x0 + ENNReal.ofReal x1 + ENNReal.ofReal x2 + 0 +
          ENNReal.ofReal (s.card * xN) := by
        rw [h3]
        gcongr
    _ = ENNReal.ofReal (x0 + x1 + x2 + s.card * xN) := by
        rw [add_zero, ← ENNReal.ofReal_add hx0 hx1, ← ENNReal.ofReal_add (by linarith) hx2,
          ← ENNReal.ofReal_add (by linarith) hcN]
    _ < ENNReal.ofReal p := (ENNReal.ofReal_lt_ofReal_iff hp).2 hsum

end HigherDimLQGMetric
