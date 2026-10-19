import HigherDimLFPP.Lower.DecisionTree

/-!
# Occupation weights of the depth-`k` construction (lower comparison, source (5.25))

Packet P-L2a, target T3, first half (ruling H6; audit HA4, "Details for later use" D7,
"Occupation weights").  For the rule `dec_k` of `DecisionTree.lean` and the left Riemann points
`p = S(l/N e₁)` of the leaf edges:

* `occ k p Y = Σ_{leaf edges e} |e| N⁻¹ Σ_{l<N} 1{e(l/N) = p} e^{ζ Y(ρq^k, ρ, p)}`: the weighted
  occupation of `p` (integrand of `M_k(p)`); `occH k h Y`: the same with a deterministic test
  weight `h` (`occ k p = occH k (dlt p 1)`, `RC k = occH k 1`);
* `Mw κ k p = M_k(p) = E occ k p Y`, `RC k Y` (the Riemann cost in the cost band `(ρq^k, ρ]`),
  `mm κ k = m_k = E RC k Y`, `mu κ k = μ_k = M_k / m_k`, all under `gLawD κ (Qs k)`.
* `Good.mm_eq_sum`: `m_k = Σ_p M_k(p)`; `Good.Mw_eq_zero_of_not_mem`: `M_k` lives on `S k`;
  `Good.mm_pos`: `m_k > 0`; `Good.mu_isFinProb`: `μ_k` is a probability on `S k`.
* `Good.mm_zero`, `Good.Mw_zero`: at `k = 0` the band `(ρ, ρ]` is empty, so `m₀ = 1` and
  `μ₀ = ν₀^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}`; `Good.mu_zero_inCDelta`: `μ₀ ∈ C_δ` when
  `1/N ≤ Bδ²` (P-L1's `refMeasure_inCDelta`).
* Measurability, locality (`occ`, `RC` read only `Qs k`) and integrability (domination by one
  exponential of a Gaussian coordinate, `occ_le`).

2D source: `LQGDimension/LFPP/BlockConstructionAux5.lean` (`occ`, `Mw_eq`, `occ_nonneg`,
`occ_eq`, `measurable_occ`, `Good.occ_loc`, `Lb`, `occ_le`, `integrable_occ`, `RC_eq_sum`,
`measurable_RC`, `Good.RC_loc`, `Good.mm_eq_sum`, `Good.mm_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## Measurability helpers -/

theorem measurable_list_sum {α β : Type*} [MeasurableSpace α] (l : List β) {F : α → β → ℝ}
    (hF : ∀ e, Measurable fun x => F x e) : Measurable fun x => (l.map (F x)).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact measurable_const
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF e).add ih

theorem measurable_rcW {α : Type*} [MeasurableSpace α] (N : ℕ) (z : List (Rd d))
    {G : α → Rd d → ℝ} (hG : ∀ w, Measurable fun x => G x w) :
    Measurable fun x => rcW N z (G x) := by
  unfold rcW
  refine measurable_list_sum _ fun e => ?_
  unfold ew
  exact measurable_const.mul (Finset.measurable_sum _ fun l _ => hG _)

theorem measurable_exp_eval (ζ : ℝ) (t : TriD d) :
    Measurable fun Y : TriD d → ℝ => Real.exp (ζ * Y t) :=
  (measurable_const.mul (measurable_pi_apply t)).exp

theorem rcW_zero (N : ℕ) (z : List (Rd d)) : rcW N z (fun _ => 0) = 0 := by
  have h := rcW_const_mul N z 0 fun _ => (0 : ℝ)
  simp only [zero_mul] at h
  exact h

theorem dlt_mul_eq (p : Rd d) (g : Rd d → ℝ) :
    dlt p g = fun w => dlt p (fun _ => (1 : ℝ)) w * g w := by
  funext w
  simp only [dlt]
  split_ifs <;> ring

/-- A list whose head is `0` and whose last element is `e₁` has at least one edge. -/
theorem edges_ne_nil_of_ends (hd : 0 < d) {z : List (Rd d)} (h0 : z.head? = some 0)
    (h1 : z.getLast? = some (e₁ d)) : edges z ≠ [] := by
  intro he
  have hlen : (edges z).length = z.length - 1 := by
    show (z.zip z.tail).length = z.length - 1
    rw [List.length_zip, List.length_tail]
    omega
  rw [he, List.length_nil] at hlen
  have hne : z ≠ [] := by
    intro hz
    rw [hz] at h0
    simp at h0
  have hz1 : z.length = 1 := by
    have := List.length_pos_iff.mpr hne
    omega
  have heq : z.head? = z.getLast? := by
    rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?, hz1]
  rw [h0, h1] at heq
  have h01 : (0 : Rd d) = e₁ d := Option.some.inj heq
  have := norm_e₁ hd
  rw [← h01, norm_zero] at this
  exact zero_ne_one this

namespace LParams

variable (P : LParams d) (κ : Rd d → ℝ)

/-! ## Definitions -/

/-- Weighted occupation with a deterministic test weight `h`:
`rcW N (poly_k (dec_k Y)) (h · e^{ζ Y(ρq^k, ρ, ·)})`. -/
def occH (k : ℕ) (h : Rd d → ℝ) (Y : TriD d → ℝ) : ℝ :=
  rcW P.N (P.polyOf k (P.dec k Y)) fun z => h z * Real.exp (P.ζ * Y (P.ρ * P.q ^ k, P.ρ, z))

/-- The Riemann-weighted occupation of the point `p` by the depth-`k` rule under the field `Y`
(the integrand of `M_k(p)`). -/
def occ (k : ℕ) (p : Rd d) (Y : TriD d → ℝ) : ℝ :=
  rcW P.N (P.polyOf k (P.dec k Y)) (dlt p fun z => Real.exp (P.ζ * Y (P.ρ * P.q ^ k, P.ρ, z)))

/-- `M_k(p)`: the expected weighted occupation (5.25) of the Riemann point `p`. -/
def Mw (k : ℕ) (p : Rd d) : ℝ := ∫ Y, P.occ k p Y ∂gLawD κ (P.Qs k)

/-- The Riemann cost of the depth-`k` rule in the cost band `(ρ q^k, ρ]`. -/
def RC (k : ℕ) (Y : TriD d → ℝ) : ℝ :=
  riemannCost P.ζ P.N (P.polyOf k (P.dec k Y)) fun z => Y (P.ρ * P.q ^ k, P.ρ, z)

/-- `m_k`, the total expected weighted occupation. -/
def mm (k : ℕ) : ℝ := ∫ Y, P.RC k Y ∂gLawD κ (P.Qs k)

/-- `μ_k = M_k / m_k`. -/
def mu (k : ℕ) (p : Rd d) : ℝ := P.Mw κ k p / P.mm κ k

/-- A bound for the occupation counts of all depth-`k` polygons. -/
def Lb (k : ℕ) (p : Rd d) : ℝ := ∑ t : DT P.J P.K k, rcW P.N (P.polyOf k t) (dlt p fun _ => 1)

variable {P}

theorem occ_eq_occH (k : ℕ) (p : Rd d) : P.occ k p = P.occH k (dlt p fun _ => 1) := by
  funext Y
  unfold occ occH
  rw [dlt_mul_eq]

theorem RC_eq_occH (k : ℕ) : P.RC k = P.occH k fun _ => 1 := by
  funext Y
  unfold RC occH
  rw [riemannCost_eq_rcW]
  simp only [one_mul]

theorem occ_eq (k : ℕ) (p : Rd d) (Y : TriD d → ℝ) :
    P.occ k p Y = Real.exp (P.ζ * Y (P.ρ * P.q ^ k, P.ρ, p)) *
      rcW P.N (P.polyOf k (P.dec k Y)) (dlt p fun _ => 1) := by
  unfold occ
  rw [rcW_dlt]

theorem occ_nonneg (k : ℕ) (p : Rd d) (Y : TriD d → ℝ) : 0 ≤ P.occ k p Y := by
  rw [occ_eq]
  exact mul_nonneg (Real.exp_pos _).le (rcW_nonneg _ _ (dlt_one_nonneg p))

theorem rcW_le_Lb (k : ℕ) (p : Rd d) (t : DT P.J P.K k) :
    rcW P.N (P.polyOf k t) (dlt p fun _ => 1) ≤ P.Lb k p :=
  Finset.single_le_sum (f := fun t => rcW P.N (P.polyOf k t) (dlt p fun _ => 1))
    (fun _ _ => rcW_nonneg _ _ (dlt_one_nonneg p)) (Finset.mem_univ t)

theorem occ_le (k : ℕ) (p : Rd d) (Y : TriD d → ℝ) :
    P.occ k p Y ≤ P.Lb k p * Real.exp (P.ζ * Y (P.ρ * P.q ^ k, P.ρ, p)) := by
  rw [occ_eq, mul_comm (P.Lb k p)]
  exact mul_le_mul_of_nonneg_left (rcW_le_Lb k p _) (Real.exp_pos _).le

/-! ## Measurability and locality -/

theorem Good.measurable_occH (hP : P.Good) (k : ℕ) (h : Rd d → ℝ) :
    Measurable (P.occH k h) :=
  hP.measurable_of_dec (Φ := fun t Y => rcW P.N (P.polyOf k t)
    fun z => h z * Real.exp (P.ζ * Y (P.ρ * P.q ^ k, P.ρ, z)))
    fun _ => measurable_rcW _ _ fun _ => measurable_const.mul (measurable_exp_eval _ _)

theorem Good.measurable_occ (hP : P.Good) (k : ℕ) (p : Rd d) : Measurable (P.occ k p) := by
  rw [occ_eq_occH]
  exact hP.measurable_occH k _

theorem Good.measurable_RC (hP : P.Good) (k : ℕ) : Measurable (P.RC k) := by
  rw [RC_eq_occH]
  exact hP.measurable_occH k _

/-- `occH` reads only the triples `Qs k`. -/
theorem Good.occH_loc (hP : P.Good) (k : ℕ) (h : Rd d → ℝ) : IsLoc (P.Qs k) (P.occH k h) := by
  intro Y Y' hY
  unfold occH
  rw [hP.dec_loc k Y Y' hY]
  refine rcW_congr _ _ fun z hz => ?_
  have hzS : z ∈ P.S k := hP.riemannPts_polyOf_subset k _ hz
  rw [hY _ (mem_Qs_cost hzS)]

theorem Good.occ_loc (hP : P.Good) (k : ℕ) (p : Rd d) : IsLoc (P.Qs k) (P.occ k p) := by
  rw [occ_eq_occH]
  exact hP.occH_loc k _

theorem Good.RC_loc (hP : P.Good) (k : ℕ) : IsLoc (P.Qs k) (P.RC k) := by
  rw [RC_eq_occH]
  exact hP.occH_loc k _

/-- `M_k` lives on the Riemann points `S k`. -/
theorem Good.occ_eq_zero_of_not_mem (hP : P.Good) (k : ℕ) {p : Rd d} (hp : p ∉ P.S k)
    (Y : TriD d → ℝ) : P.occ k p Y = 0 := by
  unfold occ
  rw [← rcW_zero P.N (P.polyOf k (P.dec k Y))]
  refine rcW_congr _ _ fun z hz => ?_
  have hzS : z ∈ P.S k := hP.riemannPts_polyOf_subset k _ hz
  have hzp : z ≠ p := fun h => hp (h ▸ hzS)
  simp [dlt, hzp]

/-- The Riemann cost is the sum of the occupations of the Riemann points. -/
theorem Good.RC_eq_sum (hP : P.Good) (k : ℕ) (Y : TriD d → ℝ) :
    P.RC k Y = ∑ p ∈ P.S k, P.occ k p Y := by
  unfold RC occ
  rw [riemannCost_eq_rcW, rcW_eq_sum_dlt _ _ _ (hP.riemannPts_polyOf_subset k _)]

/-! ## Integrability -/

section Integrability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem Good.integrable_occ_x (hP : P.Good) (k : ℕ) (p : Rd d) (β : TriD d → E) :
    Integrable (fun x => P.occ k p (Yf β x)) (stdGaussian E) := by
  refine integrable_of_le_exp (((hP.measurable_occ k p).comp
    (measurable_Yf β)).aestronglyMeasurable) (P.Lb k p) P.ζ (β (P.ρ * P.q ^ k, P.ρ, p))
    fun x => ?_
  rw [abs_of_nonneg (occ_nonneg k p _)]
  exact occ_le k p _

theorem Good.integrable_occ (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (p : Rd d) :
    Integrable (P.occ k p) (gLawD κ (P.Qs k)) := by
  obtain ⟨m, β, hβ⟩ := exists_gram_kapD hκ (P.Qs k) (hP.Qs_pos k)
  exact (transfer_integrable (kapD κ) (P.Qs k) β hβ (hP.measurable_occ k p)
    (hP.occ_loc k p)).1 (hP.integrable_occ_x k p β)

theorem Good.integrable_RC (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    Integrable (P.RC k) (gLawD κ (P.Qs k)) := by
  have h : P.RC k = fun Y => ∑ p ∈ P.S k, P.occ k p Y := funext (hP.RC_eq_sum k)
  rw [h]
  exact integrable_finsetSum _ fun p _ => hP.integrable_occ κ hκ k p

end Integrability

/-! ## Total mass and support -/

theorem Mw_nonneg (k : ℕ) (p : Rd d) : 0 ≤ P.Mw κ k p :=
  integral_nonneg fun Y => occ_nonneg k p Y

theorem Good.Mw_eq_zero_of_not_mem (hP : P.Good) (k : ℕ) {p : Rd d} (hp : p ∉ P.S k) :
    P.Mw κ k p = 0 := by
  unfold Mw
  simp_rw [hP.occ_eq_zero_of_not_mem k hp, integral_zero]

/-- `m_k = Σ_p M_k(p)`. -/
theorem Good.mm_eq_sum (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    P.mm κ k = ∑ p ∈ P.S k, P.Mw κ k p := by
  unfold mm Mw
  simp_rw [hP.RC_eq_sum k]
  rw [integral_finsetSum _ fun p _ => hP.integrable_occ κ hκ k p]

theorem Good.mm_nonneg (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) : 0 ≤ P.mm κ k := by
  rw [hP.mm_eq_sum κ hκ]
  exact Finset.sum_nonneg fun p _ => Mw_nonneg κ k p

/-- The Riemann cost of every polygon is positive. -/
theorem Good.RC_pos (hP : P.Good) (k : ℕ) (Y : TriD d → ℝ) : 0 < P.RC k Y := by
  unfold RC riemannCost
  have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.N_pos
  obtain ⟨h0, h1⟩ := hP.polyOf_ends k (P.dec k Y)
  refine List.sum_pos _ ?_ ?_
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rw [hP.norm_edge_polyOf k _ e he]
    refine mul_pos (mul_pos (hP.q_pow_pos k) (by positivity)) ?_
    exact Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨0, Finset.mem_range.2 hP.N_pos⟩
  · rw [Ne, List.map_eq_nil_iff]
    exact edges_ne_nil_of_ends hP.d_pos h0 h1

/-- `m_k > 0`. -/
theorem Good.mm_pos (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) : 0 < P.mm κ k := by
  unfold mm
  rw [integral_pos_iff_support_of_nonneg (fun Y => (hP.RC_pos k Y).le) (hP.integrable_RC κ hκ k)]
  have hsupp : Function.support (P.RC k) = univ :=
    Function.support_eq_univ fun Y => (hP.RC_pos k Y).ne'
  rw [hsupp, measure_univ]
  exact one_pos

/-- `μ_k` is a probability measure on the Riemann points `S k`. -/
theorem Good.mu_isFinProb (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) :
    IsFinProb (P.S k) (P.mu κ k) := by
  have hm := hP.mm_pos κ hκ k
  refine ⟨fun p _ => div_nonneg (Mw_nonneg κ k p) hm.le, ?_⟩
  unfold mu
  rw [← Finset.sum_div, ← hP.mm_eq_sum κ hκ, div_self hm.ne']

theorem Good.mu_nonneg (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (p : Rd d) :
    0 ≤ P.mu κ k p :=
  div_nonneg (Mw_nonneg κ k p) (hP.mm_pos κ hκ k).le

theorem Good.Mw_eq_mm_mul_mu (hP : P.Good) (hκ : IsLFPPKernel κ) (k : ℕ) (p : Rd d) :
    P.Mw κ k p = P.mm κ k * P.mu κ k p := by
  unfold mu
  rw [mul_div_cancel₀ _ (hP.mm_pos κ hκ k).ne']

/-! ## Depth zero: `m₀ = 1` and `μ₀ = ν₀^N` -/

/-- At depth `0` the cost band `(ρ, ρ]` is empty: in any Gram realization its vectors vanish. -/
theorem Good.gram_zero_eq_zero (hP : P.Good) (hκ : IsLFPPKernel κ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs 0, ∀ t' ∈ P.Qs 0, ⟪β t, β t'⟫ = kapD κ t t') :
    ∀ t ∈ P.Qs 0, β t = 0 := by
  intro t ht
  have h1 := hβ t ht t ht
  simp only [Qs, costTris, Finset.mem_image] at ht
  obtain ⟨p, -, rfl⟩ := ht
  have h2 : kapD κ (P.ρ * P.q ^ 0, P.ρ, p) (P.ρ * P.q ^ 0, P.ρ, p) = 0 := by
    rw [kapD_diag hκ (hP.rho_q_pow_pos 0) (hP.rho_q_pow_le 0), pow_zero, mul_one,
      div_self hP.ρ_pos.ne', Real.log_one]
  rw [h2] at h1
  exact inner_self_eq_zero.1 h1

/-- The Riemann weight of the unit segment: `rcW N [0, e₁] g = N⁻¹ Σ_{l<N} g((l/N) e₁)`. -/
theorem rcW_unit (hd : 0 < d) (N : ℕ) (g : Rd d → ℝ) :
    rcW N [0, e₁ d] g = (1 / (N : ℝ)) * ∑ l ∈ Finset.range N, g (refPt N l) := by
  simp only [rcW, edges_cons_cons, edges_single, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, ew, sub_zero, norm_e₁ hd, one_mul, zero_add, refPt]

theorem Good.occ_zero_x (hP : P.Good) (hκ : IsLFPPKernel κ) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {β : TriD d → E}
    (hβ : ∀ t ∈ P.Qs 0, ∀ t' ∈ P.Qs 0, ⟪β t, β t'⟫ = kapD κ t t') (x : E) (h : Rd d → ℝ) :
    P.occH 0 h (Yf β x) = (1 / (P.N : ℝ)) * ∑ l ∈ Finset.range P.N, h (refPt P.N l) := by
  unfold occH
  have hcongr : rcW P.N (P.polyOf 0 (P.dec 0 (Yf β x)))
      (fun z => h z * Real.exp (P.ζ * Yf β x (P.ρ * P.q ^ 0, P.ρ, z))) =
      rcW P.N (P.polyOf 0 (P.dec 0 (Yf β x))) h := by
    refine rcW_congr _ _ fun z hz => ?_
    have hzS := hP.riemannPts_polyOf_subset 0 _ hz
    rw [Yf_apply, hP.gram_zero_eq_zero κ hκ hβ _ (mem_Qs_cost hzS), inner_zero_left, mul_zero,
      Real.exp_zero, mul_one]
  rw [hcongr]
  exact rcW_unit hP.d_pos P.N h

/-- **`m₀ = 1`**. -/
theorem Good.mm_zero (hP : P.Good) (hκ : IsLFPPKernel κ) : P.mm κ 0 = 1 := by
  obtain ⟨m, β, hβ⟩ := exists_gram_kapD hκ (P.Qs 0) (hP.Qs_pos 0)
  unfold mm
  rw [gLawD, ← transfer_integral (kapD κ) (P.Qs 0) β hβ (hP.measurable_RC 0) (hP.RC_loc 0)]
  have hN : (P.N : ℝ) ≠ 0 := by exact_mod_cast hP.N_pos.ne'
  have hRC : ∀ x, P.RC 0 (Yf β x) = 1 := by
    intro x
    rw [RC_eq_occH, hP.occ_zero_x κ hκ hβ x, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, one_div, inv_mul_cancel₀ hN]
  simp [hRC]

/-- **`μ₀ = ν₀^N`**: `M₀(p) = 1/N` at each reference point `p = (l/N) e₁`. -/
theorem Good.Mw_zero (hP : P.Good) (hκ : IsLFPPKernel κ) {p : Rd d} (hp : p ∈ P.S 0) :
    P.Mw κ 0 p = 1 / (P.N : ℝ) := by
  obtain ⟨m, β, hβ⟩ := exists_gram_kapD hκ (P.Qs 0) (hP.Qs_pos 0)
  unfold Mw
  rw [gLawD, ← transfer_integral (kapD κ) (P.Qs 0) β hβ (hP.measurable_occ 0 p) (hP.occ_loc 0 p)]
  obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.1 hp
  have hinj := refPt_injective (d := d) hP.d_pos hP.N_pos
  have hocc : ∀ x, P.occ 0 (refPt P.N l₀) (Yf β x) = 1 / (P.N : ℝ) := by
    intro x
    rw [occ_eq_occH, hP.occ_zero_x κ hκ hβ x]
    have hs : ∑ l ∈ Finset.range P.N,
        dlt (refPt (d := d) P.N l₀) (fun _ => (1 : ℝ)) (refPt (d := d) P.N l) =
        ∑ l ∈ Finset.range P.N, if l = l₀ then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [dlt]
      by_cases hl : l = l₀
      · simp [hl]
      · have : refPt (d := d) P.N l ≠ refPt P.N l₀ := fun h => hl (hinj h)
        simp [this, hl]
    rw [hs, Finset.sum_ite_eq' (Finset.range P.N) l₀ fun _ => (1 : ℝ),
      ite_eq_left hl₀, mul_one]
  simp [hocc]

theorem Good.mu_zero (hP : P.Good) (hκ : IsLFPPKernel κ) {p : Rd d} (hp : p ∈ P.S 0) :
    P.mu κ 0 p = 1 / (P.N : ℝ) := by
  rw [mu, hP.mm_zero κ hκ, div_one, hP.Mw_zero κ hκ hp]

/-- `InCDelta` only depends on the weights on the support. -/
theorem inCDelta_congr {δ M B : ℝ} {S : Finset (Rd d)} {w w' : Rd d → ℝ}
    (h : ∀ z ∈ S, w z = w' z) (hw : InCDelta δ M B S w) : InCDelta δ M B S w' := by
  obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hw
  refine ⟨⟨fun z hz => h z hz ▸ h0 z hz, ?_⟩, fun z hz hz' => h2 z hz (h z hz ▸ hz'), ?_⟩
  · rw [← h1]
    exact Finset.sum_congr rfl fun z hz => (h z hz).symm
  · have hcdf : hCDF S w' = hCDF S w := by
      funext x
      unfold hCDF
      exact Finset.sum_congr rfl fun z hz => (h z (Finset.mem_filter.1 hz).1).symm
    unfold HorizW
    rw [hcdf]
    exact h3

/-- **`μ₀ ∈ C_δ`** (HA4 D7, start of the iteration) when `1/N ≤ Bδ²`. -/
theorem Good.mu_zero_inCDelta (hP : P.Good) (hκ : IsLFPPKernel κ) {δ M B : ℝ}
    (hM : 0 ≤ M * δ) (hNB : 1 / (P.N : ℝ) ≤ B * δ ^ 2) :
    InCDelta δ M B (P.S 0) (P.mu κ 0) :=
  inCDelta_congr (fun _ hp => (hP.mu_zero κ hκ hp).symm)
    (refMeasure_inCDelta hP.d_pos hP.N_pos hM hNB)

end LParams

end HigherDimLFPP.Lower
