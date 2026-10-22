import HigherDimLQGContinuity.Endpoint.Asymp
import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGContinuity.Norm.Rho

/-!
# The Euclidean endpoint (packet E3), part 4: the bad events of a block and their probabilities

Blueprint Part C `c:def-end` (the events `Base(a)`, `Bridge(a)`, `Fine(a)`, `Bad(a)`), `c:lem-end-seed`,
`c:lem-end-base`, `c:lem-end-bridge`, `c:lem-end-fine`; NA4 §1.2 items 8–10, Details (a) A6.

For a family `Dt : ℝ → DistRd d → ContMetric d` (in use: a strong assignment at every grid parameter), a radius `R`,
the base exponent `L` and the fine growth `D`, block `k` has
* `endBase`: some base node `t` (level `L k`) has `supd_R(lp ρ^t, lp eu) > ε_k`;
* `endBridge`: some level-`0` node `t` has `supd_R(lp ρ^{t_b}, lp ρ^t) > ε_k / 8`, `t_b` its base parent;
* `endFine`: for some `j`, some level-`(j+1)` node `t` has `supd_R(lp ρ^{t'}, lp ρ^t) > δ_j = ε_k 2^{-j-6}`, `t'` its
  level-`j` parent;
and `endBad = endBase ∪ endBridge ∪ endFine`. Probabilities are outer measures (no measurability is claimed).

* `end_seed`: the cheap seed (S) of `Prop37Shape` from Lemma 5.1 under the radius-ten pin at radius `1` (moment `4`,
  rate `3/4`), by Markov's inequality (`end_seed_block` in block form);
* `measure_endBase_le`: Markov with the moment `4(L+2)` under the unit pin and a union bound;
* `measure_endBridge_le`, `measure_endFine_le`: `Prop37Shape` (with (S), resp. (G)) and union bounds.

`EndP37` is the inner statement of `Prop37Shape d` after its existential choices (an abbreviation for these proofs;
`Prop37Shape d` unfolds to it, `endpt_p37_of`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The inner statement of `Prop37Shape` -/

/-- The inner statement of `Prop37Shape d` after the choices of `ξbar` (subcritical), `ps, c'` and, at radius `R`,
of `B, M, C, c` (used only inside packet E3's proofs). -/
def EndP37 (d : ℕ) (ξbar ps c' R B M C c : ℝ) : Prop :=
  ∀ a ∈ Ioc (0 : ℝ) ξbar, ∀ ξ ∈ Icc a ξbar, ∀ η ∈ Icc a ξbar, ∀ D E : DistRd d → ContMetric d,
    IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
    ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → ∀ n : ℝ,
      C * δ ^ (-M) * Real.log (C / δ) ≤ n → |ξ - η| * n ≤ c * δ →
      (|ξ - η| ≤ Real.exp (-(C * a ^ (-B) * δ ^ (-B))) ∨
        pinLaw d 10 {g | ENNReal.ofReal (c' * δ) < supDistLU d 1 (rho D g).1 (rho E g).1} ≤
          ENNReal.ofReal ps) →
      normLGFLaw d {g | ENNReal.ofReal δ <
          supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)} ≤
        ENNReal.ofReal (C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)))

theorem endpt_p37_of (hP : Prop37Shape d) {ξbar : ℝ} (h0 : 0 < ξbar)
    (h1 : Real.sqrt (2 * d) < distExp d ξbar) :
    ∃ ps c' : ℝ, 0 < ps ∧ ps < 1 ∧ 0 < c' ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ B M C c : ℝ, 0 < B ∧ 0 < M ∧ 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧ EndP37 d ξbar ps c' R B M C c :=
  hP ξbar h0 h1

/-! ## The events -/

/-- The base event of block `k` at radius `R` (base level `L k`). -/
def endBase (Dt : ℝ → DistRd d → ContMetric d) (R : ℝ) (L k : ℕ) : Set (DistRd d) :=
  ⋃ m ∈ Finset.range (2 ^ (L * k) + 1),
    {g | ENNReal.ofReal (endEps k) <
      supDistLU d R (logProfile (rho (Dt (endNode k (L * k) m)) g).1) (logProfile (euclidDistC d))}

/-- The bridge event of block `k` at radius `R`: level-`0` nodes against their base parents. -/
def endBridge (Dt : ℝ → DistRd d → ContMetric d) (R : ℝ) (L D k : ℕ) : Set (DistRd d) :=
  ⋃ m ∈ Finset.range (2 ^ endLevel D k 0 + 1),
    {g | ENNReal.ofReal (endEps k / 8) <
      supDistLU d R (logProfile (rho (Dt (endNode k (L * k) (endPar (endLevel D k 0) (L * k) m))) g).1)
        (logProfile (rho (Dt (endNode k (endLevel D k 0) m)) g).1)}

/-- The fine event of block `k` at radius `R`: level-`(j+1)` nodes against their level-`j` parents. -/
def endFine (Dt : ℝ → DistRd d → ContMetric d) (R : ℝ) (D k : ℕ) : Set (DistRd d) :=
  ⋃ j : ℕ, ⋃ m ∈ Finset.range (2 ^ endLevel D k (j + 1) + 1),
    {g | ENNReal.ofReal (endDelta k j) <
      supDistLU d R
        (logProfile (rho (Dt (endNode k (endLevel D k j)
          (endPar (endLevel D k (j + 1)) (endLevel D k j) m))) g).1)
        (logProfile (rho (Dt (endNode k (endLevel D k (j + 1)) m)) g).1)}

/-- The bad event of block `k` at radius `R` (`c:def-end`). -/
def endBad (Dt : ℝ → DistRd d → ContMetric d) (R : ℝ) (L D k : ℕ) : Set (DistRd d) :=
  endBase Dt R L k ∪ endBridge Dt R L D k ∪ endFine Dt R D k

/-! ## Union bounds -/

/-- A finite union bound with a common bound. -/
theorem endpt_measure_biUnion_range_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (E : ℕ → Set Ω) {b : ℝ} (h : ∀ m ≤ N, μ (E m) ≤ ENNReal.ofReal b) :
    μ (⋃ m ∈ Finset.range (N + 1), E m) ≤ ENNReal.ofReal ((N + 1) * b) := by
  calc μ (⋃ m ∈ Finset.range (N + 1), E m) ≤ ∑ m ∈ Finset.range (N + 1), μ (E m) :=
        measure_biUnion_finset_le _ _
    _ ≤ (Finset.range (N + 1)).card • ENNReal.ofReal b :=
        Finset.sum_le_card_nsmul _ _ _ fun m hm => h m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))
    _ = ENNReal.ofReal ((N + 1) * b) := by
        rw [Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) zero_le_one]
        simp

/-! ## Measurability and Markov's inequality for the marginal bound -/

theorem endpt_measurable_supDistLU_rho {D : DistRd d → ContMetric d} (hD : Measurable D) (R : ℝ) :
    Measurable fun g => supDistLU d R (rho D g).1 (euclidDistC d) :=
  endpt_measurable_supDistLU (fun p => p2_measurable_contMetric_apply (measurable_rho hD) p)
    (fun _ => measurable_const) R

/-- Markov's inequality for `supd_R(ρ^D, eu)` under any law. -/
theorem endpt_markov_rho {D : DistRd d → ContMetric d} (hD : Measurable D) (μ : Measure (DistRd d))
    {R x p B : ℝ} (hx : 0 < x) (hp : 0 < p)
    (hB : ∫⁻ g, supDistLU d R (rho D g).1 (euclidDistC d) ^ p ∂μ ≤ ENNReal.ofReal B) :
    μ {g | ENNReal.ofReal x < supDistLU d R (rho D g).1 (euclidDistC d)} ≤ ENNReal.ofReal (B / x ^ p) :=
  endpt_meas_lt_le (endpt_measurable_supDistLU_rho hD R).aemeasurable hx hp hB

/-! ## The seed (`c:lem-end-seed`) -/

/-- **The cheap seed** (`c:lem-end-seed`): the triangle inequality through `eu` and Markov's inequality with the
fourth moments of Lemma 5.1 under the radius-ten pin at radius `1`. -/
theorem end_seed {D₁ D₂ : DistRd d → ContMetric d} (h₁ : Measurable D₁) (h₂ : Measurable D₂)
    {x B₁ B₂ : ℝ} (hx : 0 < x)
    (hm₁ : ∫⁻ g, supDistLU d 1 (rho D₁ g).1 (euclidDistC d) ^ (4 : ℝ) ∂(pinLaw d 10) ≤ ENNReal.ofReal B₁)
    (hm₂ : ∫⁻ g, supDistLU d 1 (rho D₂ g).1 (euclidDistC d) ^ (4 : ℝ) ∂(pinLaw d 10) ≤ ENNReal.ofReal B₂) :
    pinLaw d 10 {g | ENNReal.ofReal (2 * x) < supDistLU d 1 (rho D₁ g).1 (rho D₂ g).1} ≤
      ENNReal.ofReal (B₁ / x ^ (4 : ℝ)) + ENNReal.ofReal (B₂ / x ^ (4 : ℝ)) := by
  have hsub : {g | ENNReal.ofReal (2 * x) < supDistLU d 1 (rho D₁ g).1 (rho D₂ g).1} ⊆
      {g | ENNReal.ofReal x < supDistLU d 1 (rho D₁ g).1 (euclidDistC d)} ∪
        {g | ENNReal.ofReal x < supDistLU d 1 (rho D₂ g).1 (euclidDistC d)} := by
    intro g hg
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon hg
    have htri := endpt_supDistLU_triangle (R := 1) (F := (rho D₁ g).1) (G := euclidDistC d)
      (H := (rho D₂ g).1)
    rw [endpt_supDistLU_comm (F := euclidDistC d)] at htri
    have : supDistLU d 1 (rho D₁ g).1 (rho D₂ g).1 ≤ ENNReal.ofReal (2 * x) := by
      rw [two_mul, ENNReal.ofReal_add hx.le hx.le]
      exact htri.trans (add_le_add hcon.1 hcon.2)
    exact absurd hg (not_lt.2 this)
  calc pinLaw d 10 {g | ENNReal.ofReal (2 * x) < supDistLU d 1 (rho D₁ g).1 (rho D₂ g).1}
      ≤ pinLaw d 10 ({g | ENNReal.ofReal x < supDistLU d 1 (rho D₁ g).1 (euclidDistC d)} ∪
        {g | ENNReal.ofReal x < supDistLU d 1 (rho D₂ g).1 (euclidDistC d)}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (endpt_markov_rho h₁ _ hx (by norm_num) hm₁)
        (endpt_markov_rho h₂ _ hx (by norm_num) hm₂)

/-- `ξ^{(3/4)·4} = ξ³`. -/
theorem endpt_rpow_three (ξ : ℝ) : ξ ^ ((3 / 4 : ℝ) * 4) = ξ ^ 3 := by
  rw [show (3 / 4 : ℝ) * 4 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The seed in block form**: for `s, t ∈ [a_k, 2a_k]` with the fourth-moment bound `C₂ ξ^3` of Lemma 5.1 (rate
`3/4`), `P_{10}{c' ε_k / 8 < supd_1(ρ^s, ρ^t)} ≤ 16^5 C₂ a_k / c'^4`. -/
theorem end_seed_block {D₁ D₂ : DistRd d → ContMetric d} (h₁ : Measurable D₁) (h₂ : Measurable D₂)
    {c' C₂ : ℝ} (hc' : 0 < c') (hC₂ : 0 ≤ C₂) {k : ℕ} {s t : ℝ}
    (hs : s ∈ Icc (endA k) (2 * endA k)) (ht : t ∈ Icc (endA k) (2 * endA k))
    (hm₁ : ∫⁻ g, supDistLU d 1 (rho D₁ g).1 (euclidDistC d) ^ (4 : ℝ) ∂(pinLaw d 10) ≤
      ENNReal.ofReal (C₂ * s ^ ((3 / 4 : ℝ) * 4)))
    (hm₂ : ∫⁻ g, supDistLU d 1 (rho D₂ g).1 (euclidDistC d) ^ (4 : ℝ) ∂(pinLaw d 10) ≤
      ENNReal.ofReal (C₂ * t ^ ((3 / 4 : ℝ) * 4))) :
    pinLaw d 10 {g | ENNReal.ofReal (c' * (endEps k / 8)) < supDistLU d 1 (rho D₁ g).1 (rho D₂ g).1} ≤
      ENNReal.ofReal (16 ^ 5 * C₂ * endA k / c' ^ 4) := by
  set x := c' * endEps k / 16 with hxdef
  have hx : 0 < x := by have := endEps_pos k; positivity
  have h2x : c' * (endEps k / 8) = 2 * x := by rw [hxdef]; ring
  have hA := endA_pos k
  rw [endpt_rpow_three s] at hm₁
  rw [endpt_rpow_three t] at hm₂
  have hseed := end_seed h₁ h₂ hx hm₁ hm₂
  rw [h2x]
  refine hseed.trans ?_
  have hx4 : x ^ (4 : ℝ) = c' ^ 4 * endA k ^ 2 / 16 ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hxdef, div_pow, mul_pow,
      endEps_pow_four]
  have hbound : ∀ ξ ∈ Icc (endA k) (2 * endA k), C₂ * ξ ^ 3 / x ^ (4 : ℝ) ≤ 8 * 16 ^ 4 * C₂ * endA k / c' ^ 4 := by
    intro ξ hξ
    have hξ0 : 0 ≤ ξ := hA.le.trans hξ.1
    have h3 : ξ ^ 3 ≤ (2 * endA k) ^ 3 := pow_le_pow_left₀ hξ0 hξ.2 3
    have hA' : endA k ≠ 0 := hA.ne'
    have hc'' : c' ≠ 0 := hc'.ne'
    calc C₂ * ξ ^ 3 / x ^ (4 : ℝ) ≤ C₂ * (2 * endA k) ^ 3 / x ^ (4 : ℝ) := by gcongr
      _ = 8 * 16 ^ 4 * C₂ * endA k / c' ^ 4 := by
          rw [hx4]
          field_simp
          ring
  calc ENNReal.ofReal (C₂ * s ^ 3 / x ^ (4 : ℝ)) + ENNReal.ofReal (C₂ * t ^ 3 / x ^ (4 : ℝ))
      ≤ ENNReal.ofReal (8 * 16 ^ 4 * C₂ * endA k / c' ^ 4) +
          ENNReal.ofReal (8 * 16 ^ 4 * C₂ * endA k / c' ^ 4) :=
        add_le_add (ENNReal.ofReal_le_ofReal (hbound s hs)) (ENNReal.ofReal_le_ofReal (hbound t ht))
    _ = ENNReal.ofReal (16 ^ 5 * C₂ * endA k / c' ^ 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## Base nodes (`c:lem-end-base`) -/

/-- **Base nodes** (`c:lem-end-base`): with the moment `p = 4(L+2)` of Lemma 5.1 under the unit pin (rate `3/4`),
`P(Base) ≤ 2 C₁ 2^{3(L+2)} a_k²`. -/
theorem measure_endBase_le {Dt : ℝ → DistRd d → ContMetric d} {R C₁ : ℝ} (hC₁ : 0 ≤ C₁) {L k : ℕ}
    (hmeas : ∀ m ≤ 2 ^ (L * k), Measurable (Dt (endNode k (L * k) m)))
    (hmom : ∀ m ≤ 2 ^ (L * k),
      ∫⁻ g, supDistLU d R (rho (Dt (endNode k (L * k) m)) g).1 (euclidDistC d) ^
          ((4 * (L + 2) : ℕ) : ℝ) ∂(normLGFLaw d) ≤
        ENNReal.ofReal (C₁ * endNode k (L * k) m ^ ((3 / 4 : ℝ) * ((4 * (L + 2) : ℕ) : ℝ)))) :
    normLGFLaw d (endBase Dt R L k) ≤ ENNReal.ofReal (2 * C₁ * 2 ^ (3 * (L + 2)) * endA k ^ 2) := by
  set a := endA k
  have ha : 0 < a := endA_pos k
  set b := C₁ * 2 ^ (3 * (L + 2)) * a ^ (L + 2) with hbdef
  have hb : 0 ≤ b := by positivity
  have hnode : ∀ m ≤ 2 ^ (L * k), normLGFLaw d
      {g | ENNReal.ofReal (endEps k) <
        supDistLU d R (logProfile (rho (Dt (endNode k (L * k) m)) g).1) (logProfile (euclidDistC d))} ≤
      ENNReal.ofReal b := by
    intro m hm
    set t := endNode k (L * k) m
    have ht := endNode_mem (k := k) hm
    have ht0 : 0 ≤ t := ha.le.trans ht.1
    have hsub : {g | ENNReal.ofReal (endEps k) <
        supDistLU d R (logProfile (rho (Dt t) g).1) (logProfile (euclidDistC d))} ⊆
        {g | ENNReal.ofReal (endEps k) < supDistLU d R (rho (Dt t) g).1 (euclidDistC d)} :=
      fun g hg => lt_of_lt_of_le hg (endpt_supDistLU_logProfile_le _ _)
    refine (measure_mono hsub).trans ((endpt_markov_rho (hmeas m hm) _ (endEps_pos k)
      (by positivity) (hmom m hm)).trans (ENNReal.ofReal_le_ofReal ?_))
    have hexp : (3 / 4 : ℝ) * ((4 * (L + 2) : ℕ) : ℝ) = ((3 * (L + 2) : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_natCast, Real.rpow_natCast]
    have hε : endEps k ^ (4 * (L + 2)) = a ^ (2 * (L + 2)) := by
      rw [pow_mul, endEps_pow_four, ← pow_mul]
    rw [hε, div_le_iff₀ (by positivity), hbdef]
    have h1 : t ^ (3 * (L + 2)) ≤ (2 * a) ^ (3 * (L + 2)) := pow_le_pow_left₀ ht0 ht.2 _
    calc C₁ * t ^ (3 * (L + 2)) ≤ C₁ * (2 * a) ^ (3 * (L + 2)) := by gcongr
      _ = C₁ * 2 ^ (3 * (L + 2)) * a ^ (L + 2) * a ^ (2 * (L + 2)) := by
          rw [mul_pow, show 3 * (L + 2) = (L + 2) + 2 * (L + 2) by ring, pow_add a]
          ring
  have hU := endpt_measure_biUnion_range_le (normLGFLaw d) (2 ^ (L * k)) _ hnode
  refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
  have h2 : ((2 ^ (L * k) : ℕ) : ℝ) + 1 ≤ 2 * 2 ^ (L * k) := by
    push_cast
    have : (1 : ℝ) ≤ 2 ^ (L * k) := one_le_pow₀ (by norm_num)
    linarith
  have h3 : (2 : ℝ) ^ (L * k) * a ^ L = 1 := by
    have h2a : (2 : ℝ) ^ k * a = 1 := by rw [mul_comm]; exact endA_mul_two_pow k
    rw [mul_comm L k, pow_mul, ← mul_pow, h2a, one_pow]
  calc ((2 ^ (L * k) : ℕ) + 1 : ℝ) * b ≤ 2 * 2 ^ (L * k) * b := by gcongr
    _ = 2 * C₁ * 2 ^ (3 * (L + 2)) * a ^ 2 * (2 ^ (L * k) * a ^ L) := by
        rw [hbdef, pow_add a L 2]
        ring
    _ = 2 * C₁ * 2 ^ (3 * (L + 2)) * a ^ 2 := by rw [h3, mul_one]

/-! ## The bridge (`c:lem-end-bridge`) and the fine levels (`c:lem-end-fine`) -/

/-- **The bridge** (`c:lem-end-bridge`): `Prop37Shape` with the seed (S) for each level-`0` node and its base parent,
`δ = ε_k / 8`, `n = c δ / (a_k 2^{-Lk})`, and a union bound. -/
theorem measure_endBridge_le {Dt : ℝ → DistRd d → ContMetric d} {ξbar ps c' R B M C c : ℝ}
    (h37 : EndP37 d ξbar ps c' R B M C c) (hC : 0 ≤ C) (hc : 0 < c) {L D k : ℕ} (hk1 : 1 ≤ k)
    (hk : 2 * endA k ≤ ξbar)
    (hDt : ∀ t ∈ Icc (endA k) (2 * endA k), IsStrongExpMetric d t (distExp d t) (Dt t))
    (hseed : ∀ s ∈ Icc (endA k) (2 * endA k), ∀ t ∈ Icc (endA k) (2 * endA k),
      pinLaw d 10 {g | ENNReal.ofReal (c' * (endEps k / 8)) <
        supDistLU d 1 (rho (Dt s) g).1 (rho (Dt t) g).1} ≤ ENNReal.ofReal ps)
    (hdepth : C * (endEps k / 8) ^ (-M) * Real.log (C / (endEps k / 8)) ≤
      c * (endEps k / 8) / endA (k + L * k))
    (hfail : ((2 : ℝ) ^ endLevel D k 0 + 1) *
        (C * (endEps k / 8) ^ (-M) * Real.exp (-(c * (endEps k / 8) ^ M *
          (c * (endEps k / 8) / endA (k + L * k))))) ≤ (1 / 2) ^ k) :
    normLGFLaw d (endBridge Dt R L D k) ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  set δ := endEps k / 8 with hδdef
  set w := endA (k + L * k) with hwdef
  set n := c * δ / w with hndef
  set q := endLevel D k 0 with hqdef
  set b := C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)) with hbdef
  have hδ0 : 0 < δ := by have := endEps_pos k; positivity
  have hδ8 : δ < 1 / 8 := by
    have := endEps_lt_one hk1
    rw [hδdef]
    linarith
  have hw : 0 < w := endA_pos _
  have hn0 : 0 ≤ n := by positivity
  have hA := endA_pos k
  have hb : 0 ≤ b :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hδ0 _).le) (Real.exp_pos _).le
  have hnode : ∀ m ≤ 2 ^ q, normLGFLaw d
      {g | ENNReal.ofReal δ < supDistLU d R
        (logProfile (rho (Dt (endNode k (L * k) (endPar q (L * k) m))) g).1)
        (logProfile (rho (Dt (endNode k q m)) g).1)} ≤ ENNReal.ofReal b := by
    intro m hm
    have ht := endNode_mem (k := k) (q := q) hm
    have htb := endNode_mem (k := k) (q := L * k) (endPar_le (q' := L * k) hm)
    have hdrift : |endNode k (L * k) (endPar q (L * k) m) - endNode k q m| * n ≤ c * δ := by
      calc |endNode k (L * k) (endPar q (L * k) m) - endNode k q m| * n ≤ w * n := by
            gcongr
            exact abs_endNode_sub_par_le k q (L * k) m
        _ = c * δ := by rw [hndef]; field_simp
    exact h37 (endA k) ⟨hA, by linarith⟩ _ ⟨htb.1, htb.2.trans hk⟩ _ ⟨ht.1, ht.2.trans hk⟩ _ _
      (hDt _ htb) (hDt _ ht) δ hδ0 hδ8 n hdepth hdrift (Or.inr (hseed _ htb _ ht))
  have hU := endpt_measure_biUnion_range_le (normLGFLaw d) (2 ^ q) _ hnode
  refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
  push_cast
  exact hfail

/-- **The fine levels** (`c:lem-end-fine`): `Prop37Shape` with (G) for each level-`(j+1)` node and its level-`j`
parent, `δ = δ_j`, `n = c δ_j / (a_k 2^{-q_j})`, union bounds over the nodes and the levels. -/
theorem measure_endFine_le {Dt : ℝ → DistRd d → ContMetric d} {ξbar ps c' R B M C c : ℝ}
    (h37 : EndP37 d ξbar ps c' R B M C c) (hC : 0 ≤ C) (hc : 0 < c) {D k : ℕ}
    (hk : 2 * endA k ≤ ξbar)
    (hDt : ∀ t ∈ Icc (endA k) (2 * endA k), IsStrongExpMetric d t (distExp d t) (Dt t))
    (hcond : ∀ j : ℕ,
      endA (k + endLevel D k j) ≤ Real.exp (-(C * endA k ^ (-B) * endDelta k j ^ (-B))) ∧
      C * endDelta k j ^ (-M) * Real.log (C / endDelta k j) ≤
        c * endDelta k j / endA (k + endLevel D k j) ∧
      ((2 : ℝ) ^ endLevel D k (j + 1) + 1) *
        (C * endDelta k j ^ (-M) * Real.exp (-(c * endDelta k j ^ M *
          (c * endDelta k j / endA (k + endLevel D k j))))) ≤ (1 / 2) ^ (k + j + 1)) :
    normLGFLaw d (endFine Dt R D k) ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  have hA := endA_pos k
  have hlevel : ∀ j : ℕ, normLGFLaw d (⋃ m ∈ Finset.range (2 ^ endLevel D k (j + 1) + 1),
      {g | ENNReal.ofReal (endDelta k j) <
        supDistLU d R
          (logProfile (rho (Dt (endNode k (endLevel D k j)
            (endPar (endLevel D k (j + 1)) (endLevel D k j) m))) g).1)
          (logProfile (rho (Dt (endNode k (endLevel D k (j + 1)) m)) g).1)}) ≤
      ENNReal.ofReal ((1 / 2) ^ (k + j + 1)) := by
    intro j
    obtain ⟨hG, hdepth, hfail⟩ := hcond j
    set δ := endDelta k j with hδdef
    set qj := endLevel D k j
    set qj1 := endLevel D k (j + 1)
    set w := endA (k + qj) with hwdef
    set n := c * δ / w with hndef
    set b := C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)) with hbdef
    have hδ0 : 0 < δ := endDelta_pos k j
    have hδ8 : δ < 1 / 8 := endDelta_lt_eighth k j
    have hw : 0 < w := endA_pos _
    have hn0 : 0 ≤ n := by positivity
    have hb : 0 ≤ b :=
      mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hδ0 _).le) (Real.exp_pos _).le
    have hnode : ∀ m ≤ 2 ^ qj1, normLGFLaw d
        {g | ENNReal.ofReal δ < supDistLU d R
          (logProfile (rho (Dt (endNode k qj (endPar qj1 qj m))) g).1)
          (logProfile (rho (Dt (endNode k qj1 m)) g).1)} ≤ ENNReal.ofReal b := by
      intro m hm
      have ht := endNode_mem (k := k) (q := qj1) hm
      have htp := endNode_mem (k := k) (q := qj) (endPar_le (q' := qj) hm)
      have hclose := abs_endNode_sub_par_le k qj1 qj m
      have hdrift : |endNode k qj (endPar qj1 qj m) - endNode k qj1 m| * n ≤ c * δ := by
        calc |endNode k qj (endPar qj1 qj m) - endNode k qj1 m| * n ≤ w * n := by gcongr
          _ = c * δ := by rw [hndef]; field_simp
      exact h37 (endA k) ⟨hA, by linarith⟩ _ ⟨htp.1, htp.2.trans hk⟩ _ ⟨ht.1, ht.2.trans hk⟩ _ _
        (hDt _ htp) (hDt _ ht) δ hδ0 hδ8 n hdepth hdrift (Or.inl (hclose.trans hG))
    have hU := endpt_measure_biUnion_range_le (normLGFLaw d) (2 ^ qj1) _ hnode
    refine hU.trans (ENNReal.ofReal_le_ofReal ?_)
    push_cast
    exact hfail
  have hsum : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (k + j + 1)) ((1 / 2) ^ k) := by
    have h := (hasSum_geometric_two).mul_left ((1 / 2 : ℝ) ^ (k + 1))
    have e1 : (fun j : ℕ => (1 / 2 : ℝ) ^ (k + j + 1)) = fun j => (1 / 2 : ℝ) ^ (k + 1) * (1 / 2) ^ j := by
      funext j
      rw [← pow_add]
      congr 1
      ring
    have e2 : (1 / 2 : ℝ) ^ (k + 1) * 2 = (1 / 2) ^ k := by rw [pow_succ]; ring
    rw [e1, ← e2]
    exact h
  calc normLGFLaw d (endFine Dt R D k) ≤ ∑' j : ℕ, normLGFLaw d (⋃ m ∈ Finset.range
        (2 ^ endLevel D k (j + 1) + 1), {g | ENNReal.ofReal (endDelta k j) <
          supDistLU d R
            (logProfile (rho (Dt (endNode k (endLevel D k j)
              (endPar (endLevel D k (j + 1)) (endLevel D k j) m))) g).1)
            (logProfile (rho (Dt (endNode k (endLevel D k (j + 1)) m)) g).1)}) :=
        measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + j + 1)) := ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal ((1 / 2) ^ k) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum.summable, hsum.tsum_eq]

end HigherDimLQGContinuity
