import HigherDimLFPP.Lower.Iteration
import HigherDimLFPP.Lower.Polygon

/-!
# The existence-free lower comparison at fixed `n` and `δ` (source (5.28); HA4 D8)

Packet P-L4, target T2 (ruling H6; audit HA4, §4 "What the lower comparison proves without
`λ_d`", items 1–2, and "Details for later use" D8; findings HA4-1, HA4-13).  The field is the
frozen white-noise model (ruling H10): `IsWhiteNoise P W` and continuous versions `H ε` of
`H_{ε,1}` for `ε ∈ (0,1)`; `D_ε = lfppDistance d ζ (H ε)` with `ζ = δ^{3/2}`.

* `polyOf_mk_eq`: the polygons of the construction do not depend on the Riemann parameter (nor
  on the scales or the selection statistic), so the family `Poly_r` is fixed before `N → ∞`.
* `measure_lt_lfppDistance_le` (**D8 for one window**): if for all large `N` the construction has
  `m_r ≤ m`, then for every cutoff `ε ∈ [ρq^{r+1}, ρq^r]` and `t > 0`,
  `P*(D_ε > t) ≤ (ρq)^{-ζ²/2} m / t`.  Proof: by the Riemann limit (P-L1's
  `tendsto_riemannCost_polyPath`, continuity of the paths of `H_{ε,1}`), `D_ε > t` forces every
  depth-`r` polygon to have Riemann cost `> t` for all large `N`; for each `N` that event has
  probability `≤ (ρq)^{-ζ²/2} m_r / t` (P-L2a's transfer, unused bands and Markov,
  `Good.measure_allCostGt_le`); continuity of measure along the increasing union over `N`.
  No measurability of `D_ε` is needed (`P` of a set is its outer measure).
* `windowBound`, `LowerComparisonWindow` (**item 1**): for every `r ≥ 1`,
  `ε ∈ (ρq^{r+1}, ρq^r]` and every `η`,
  `P*(D_ε > e^{-r(δ²(β_{n,d} - 7) - η)}) ≤ (ρq)^{-ζ²/2} e^{-ηr}`.
* `LowerComparisonFixed` (**item 2**): for every `θ > 0`,
  `P*(log D_ε / log ε < Λ_n(δ) - θ) → 0` as `ε ↓ 0` through all values, where
  `Λ_n(δ) = δ²(β_{n,d} - 7)/log(1/q)`.  Real analysis (`le_div_log_of_window`,
  `tendsto_measure_div_log_lt`): `D_ε > 0` (P-L1's `lfppDistance_pos`), and in the `r`-th window
  `|log ρ| + r log(1/q) ≤ |log ε| < |log ρ| + (r+1) log(1/q)`, so on `{D_ε ≤ e^{-rc}}`,
  `log D_ε / log ε ≥ c/log(1/q) - |c|(|log ρ| + log(1/q))/(r log(1/q)²)`; take
  `η = θ log(1/q)/2` and `c = δ²(β - 7) - η`.

All statements are conditional only on P-L3's Lemma 5.3 (`Lemma53Holds`), through the iteration
`IterD` (`iterD_of_lemma53`).

2D source: `LQGDimension/LFPP/LowerAssembly.lean` (`key_tendsto`), simplified: the cutoff is
arbitrary (no sequence `ε_j`, no exponent assumed), no oscillation event, no coupling to circle
averages; the unused bands are handled by independence (P-L2a).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## The polygon family does not depend on the Riemann parameter -/

/-- The polygons of the construction depend only on `J`, `K`, `q` and the replacement polygons
`v`: not on the Riemann parameter, the scales or the selection statistic. -/
theorem polyOf_mk_eq {J K N N' : ℕ} {ζ ζ' ρ ρ' q : ℝ} {v : Fin (J + 1) → ℕ → Rd d}
    {R R' : Finset (Rd d)} {s s' : Fin (J + 1) → (Rd d → ℝ) → ℝ} :
    ∀ (r : ℕ) (T : DT J K r), (LParams.mk J K N ζ ρ q v R s).polyOf r T =
      (LParams.mk J K N' ζ' ρ' q v R' s').polyOf r T
  | 0, _ => rfl
  | r + 1, T => by
    simp only [LParams.polyOf]
    congr 1
    funext i
    rw [polyOf_mk_eq r]
    rfl

/-! ## D8 for one window: transfer, unused bands, Markov and the Riemann limit -/

/-- **D8 for one window** (HA4 "Details for later use" D8, "Transfer" and "Riemann limit").  Let
`⟨J, K, N, ζ, ρ, q, v, R N, stat N⟩` be the construction with Riemann parameter `N`, and suppose
that for all large `N` it satisfies the standing hypotheses, its depth-`r` polygons lie in `U`
and `m_r ≤ m`.  Then for every white noise `W`, every cutoff `ε ∈ [ρq^{r+1}, ρq^r]` (`ρ ≤ 1`),
every continuous version `H` of `H_{ε,1}` and every `t > 0`,
`P*(D_ε > t) ≤ (ρq)^{-ζ²/2} m / t`. -/
theorem measure_lt_lfppDistance_le (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {J K : ℕ}
    {ζ ρ q : ℝ} {v : Fin (J + 1) → ℕ → Rd d} {R : ℕ → Finset (Rd d)}
    {stat : ℕ → Fin (J + 1) → (Rd d → ℝ) → ℝ} {r : ℕ} {m : ℝ}
    (hfam : ∀ᶠ N in atTop, (LParams.mk J K N ζ ρ q v (R N) (stat N)).Good ∧
      (∀ T : DT J K r, ∀ z ∈ (LParams.mk J K N ζ ρ q v (R N) (stat N)).polyOf r T,
        z ∈ cube d) ∧
      (LParams.mk J K N ζ ρ q v (R N) (stat N)).mm κ r ≤ m)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise Pr W)
    {ε : ℝ} (hε1 : ρ * q ^ (r + 1) ≤ ε) (hε2 : ε ≤ ρ * q ^ r) (hρ1 : ρ ≤ 1)
    {H : Rd d → Ω → ℝ} (hH : IsBandVersion Pr W κ ε 1 H) {t : ℝ} (ht : 0 < t) :
    Pr {ω | t < lfppDistance d ζ fun z => H z ω} ≤
      ENNReal.ofReal ((ρ * q) ^ (-(ζ ^ 2) / 2) * m / t) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hfam
  -- the events "every depth-`r` polygon costs more than `t`", Riemann parameter `N`
  let A : ℕ → Set Ω := fun N =>
    {ω | (LParams.mk J K N ζ ρ q v (R N) (stat N)).AllCostGt r t fun z => H z ω}
  have hA : ∀ N ≥ N₁, Pr (A N) ≤ ENNReal.ofReal ((ρ * q) ^ (-(ζ ^ 2) / 2) * m / t) := by
    intro N hN
    obtain ⟨hG, -, hm⟩ := hN₁ N hN
    refine (hG.measure_allCostGt_le κ hκ hW r hε1 hε2 hρ1 hH ht).trans
      (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ ht.le
    exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (mul_pos hG.ρ_pos hG.q_pos).le _)
  -- the polygon family, fixed before `N`
  let poly : DT J K r → List (Rd d) := fun T =>
    (LParams.mk J K N₁ ζ ρ q v (R N₁) (stat N₁)).polyOf r T
  have hpoly : ∀ N (T : DT J K r),
      (LParams.mk J K N ζ ρ q v (R N) (stat N)).polyOf r T = poly T :=
    fun N T => polyOf_mk_eq r T
  obtain ⟨hG₁, hcube₁, -⟩ := hN₁ N₁ le_rfl
  have hends : ∀ T : DT J K r, (poly T).head? = some 0 ∧ (poly T).getLast? = some (e₁ d) :=
    fun T => hG₁.polyOf_ends r T
  -- `D_ε > t` forces every polygon to cost more than `t` for all large `N`
  have hsub : {ω | t < lfppDistance d ζ fun z => H z ω} ⊆ ⋃ k, {ω | ∀ N ≥ k, ω ∈ A N} := by
    intro ω hω
    have hω' : t < lfppDistance d ζ fun z => H z ω := hω
    have hcont : Continuous fun z => H z ω := hH.continuous ω
    have hev : ∀ T : DT J K r, ∀ᶠ N in atTop, t < riemannCost ζ N (poly T) fun z => H z ω := by
      intro T
      have hadm := isAdmissiblePath_listPoly hd (hends T).1 (hends T).2 (hcube₁ T)
      have hle := lfppDistance_le_listPoly hd (hends T).1 (hends T).2 (hcube₁ T) ζ
        fun z => H z ω
      exact (tendsto_riemannCost_polyPath ζ (poly T) hadm.1 hcont).eventually
        (lt_mem_nhds (lt_of_lt_of_le hω' hle))
    obtain ⟨k, hk⟩ := eventually_atTop.1 (Filter.eventually_all.2 hev)
    refine mem_iUnion.2 ⟨k, fun N hN T => ?_⟩
    show t < riemannCost ζ N ((LParams.mk J K N ζ ρ q v (R N) (stat N)).polyOf r T) _
    rw [hpoly N T]
    exact hk N hN T
  -- continuity of measure along the increasing union over `N`
  have hmono : Monotone fun k => {ω | ∀ N ≥ k, ω ∈ A N} :=
    fun k k' hkk' ω hω N hN => hω N (hkk'.trans hN)
  refine (measure_mono hsub).trans (le_of_tendsto' (tendsto_measure_iUnion_atTop hmono)
    fun k => ?_)
  exact (measure_mono fun ω (hω : ∀ N ≥ k, ω ∈ A N) => hω (max k N₁) (le_max_left _ _)).trans
    (hA _ (le_max_right _ _))

/-! ## Item 1: the quantitative bound in every window -/

/-- From an eventual property in `𝓝[>] 0` to an interval `(0, δ₀)`. -/
theorem exists_Ioo_of_eventually {p : ℝ → Prop} (h : ∀ᶠ δ in 𝓝[>] 0, p δ) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀, p δ := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun δ hδ => hsub hδ⟩

theorem rho_mul_pow_lt_one {ρ q : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℕ) : ρ * q ^ r < 1 :=
  lt_of_le_of_lt (mul_le_of_le_one_right hρ0.le (pow_le_one₀ hq0.le hq1.le)) hρ1

/-- **The window bound** (HA4 §4 item 1, D8), from the iteration: for every block level
`n ≥ N₀` there is `δ₀ > 0` such that for `δ ∈ (0, δ₀)`: `ρ < 1`, `q < 1`, and for every white-noise
model, every depth `r`, every cutoff `ε ∈ [ρq^{r+1}, ρq^r]` and every `η`,
`P*(D_ε > e^{-r(δ²(β_{n,d} - 7) - η)}) ≤ (ρq)^{-ζ²/2} e^{-ηr}`. -/
theorem windowBound (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hI : IterD d κ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      rhoStep n δ < 1 ∧ qStep d n δ < 1 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      ∀ r : ℕ, ∀ ε ∈ Icc (rhoStep n δ * qStep d n δ ^ (r + 1)) (rhoStep n δ * qStep d n δ ^ r),
      ∀ η : ℝ,
        P {ω | Real.exp (-(r * (δ ^ 2 * (betaN n d - 7) - η))) <
            lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)} ≤
          ENNReal.ofReal ((rhoStep n δ * qStep d n δ) ^ (-((δ ^ (3 / 2 : ℝ)) ^ 2) / 2) *
            Real.exp (-(η * r))) := by
  obtain ⟨N₀, hN₀⟩ := hI
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨J, hJ⟩ := hN₀ n hn
  obtain ⟨δ₀, hδ₀, hsub⟩ := exists_Ioo_of_eventually
    ((hJ.and (eventually_rhoStep_lt_one n)).and (eventually_qStep_lt_one d n))
  refine ⟨δ₀, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨⟨⟨v, R, stat, hfam⟩, hρ1⟩, hq1⟩ := hsub δ hδ
  refine ⟨hρ1, hq1, fun Ω _ P W hW H hH r ε hε η => ?_⟩
  have hρ0 := rhoStep_pos n hδ.1
  have hq0 := qStep_pos d n δ
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε.1
  have hε1 : ε < 1 := lt_of_le_of_lt hε.2 (rho_mul_pow_lt_one hρ0 hρ1 hq0 hq1 r)
  have h := measure_lt_lfppDistance_le hd hκ (r := r)
    (m := Real.exp (-(r * (δ ^ 2 * (betaN n d - 7)))))
    (hfam.mono fun N hN => ⟨hN.1, hN.2.1 r, hN.2.2 r⟩) hW hε.1 hε.2 hρ1.le (hH ε ⟨hε0, hε1⟩)
    (Real.exp_pos (-(r * (δ ^ 2 * (betaN n d - 7) - η))))
  refine h.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
  rw [mul_div_assoc, ← Real.exp_sub]
  congr 2
  ring

/-- **Item 1 of HA4 §4** (existence-free (5.28)): for every admissible kernel there is `N₀` such
that for every block level `n ≥ N₀` there is `δ₀ > 0` such that for `δ ∈ (0, δ₀)`, with
`ζ = δ^{3/2}`, `ρ = δ(n+2)⁴` and `q = q_δ`: for every white-noise model, every depth `r ≥ 1`,
every cutoff `ε ∈ (ρq^{r+1}, ρq^r]` and every `η`,
`P*(D^ζ_{ε,d} > exp(-r(δ²(β_{n,d} - 7) - η))) ≤ (ρq)^{-ζ²/2} e^{-ηr}`. -/
def LowerComparisonWindow (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
    ∀ r : ℕ, 1 ≤ r →
    ∀ ε ∈ Ioc (rhoStep n δ * qStep d n δ ^ (r + 1)) (rhoStep n δ * qStep d n δ ^ r), ∀ η : ℝ,
      P {ω | Real.exp (-(r * (δ ^ 2 * (betaN n d - 7) - η))) <
          lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)} ≤
        ENNReal.ofReal ((rhoStep n δ * qStep d n δ) ^ (-((δ ^ (3 / 2 : ℝ)) ^ 2) / 2) *
          Real.exp (-(η * r)))

/-- **Item 1** from the iteration `IterD`. -/
theorem lowerComparisonWindow_of_iterD (hd : 0 < d)
    (hI : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → IterD d κ) : LowerComparisonWindow d := by
  intro κ hκ
  obtain ⟨N₀, hN₀⟩ := windowBound hd hκ (hI κ hκ)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨δ₀, hδ₀, h⟩ := hN₀ n hn
  exact ⟨δ₀, hδ₀, fun δ hδ Ω _ P W hW H hH r _ ε hε η =>
    (h δ hδ).2.2 Ω P W hW H hH r ε ⟨hε.1.le, hε.2⟩ η⟩

/-- **Item 1** (existence-free (5.28)), conditional only on Lemma 5.3. -/
theorem lowerComparisonWindow_of_lemma53 (hd : 0 < d)
    (h53 : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Lemma53Holds d κ) : LowerComparisonWindow d :=
  lowerComparisonWindow_of_iterD hd fun κ hκ => iterD_of_lemma53 hd hκ (h53 κ hκ)

/-! ## Item 2: the fixed-parameter limit through all cutoffs -/

/-- Every `ε ∈ (0, ρ]` lies in a window `(ρq^{r+1}, ρq^r]`. -/
theorem exists_window {ρ q ε : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hε0 : 0 < ε) (hερ : ε ≤ ρ) :
    ∃ r : ℕ, ρ * q ^ (r + 1) < ε ∧ ε ≤ ρ * q ^ r := by
  have hx : 1 ≤ ρ / ε := (one_le_div hε0).2 hερ
  have hy : 1 < q⁻¹ := (one_lt_inv₀ hq0).2 hq1
  obtain ⟨r, hr1, hr2⟩ := exists_nat_pow_near hx hy
  refine ⟨r, ?_, ?_⟩
  · have hq' : 0 < q ^ (r + 1) := pow_pos hq0 _
    rw [inv_pow, div_lt_iff₀ hε0, inv_mul_eq_div, lt_div_iff₀ hq'] at hr2
    exact hr2
  · have hq' : 0 < q ^ r := pow_pos hq0 _
    rw [inv_pow, le_div_iff₀ hε0, inv_mul_eq_div, div_le_iff₀ hq'] at hr1
    exact hr1

/-- **The logarithmic ratio in the `r`-th window**: if `ρ q^{r+1} < ε ≤ ρ q^r` (`0 < ρ ≤ 1`,
`0 < q < 1`, `r ≥ 1`) and `x ≤ -r c`, then
`x / log ε ≥ c / log(1/q) - |c| (log(1/ρ) + log(1/q)) / log(1/q)² / r`. -/
theorem le_div_log_of_window {ρ q ε x c : ℝ} {r : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hr : 1 ≤ r) (hε1 : ρ * q ^ (r + 1) < ε) (hε2 : ε ≤ ρ * q ^ r)
    (hx : x ≤ -(r * c)) :
    c / Real.log q⁻¹ - |c| * (Real.log ρ⁻¹ + Real.log q⁻¹) / Real.log q⁻¹ ^ 2 / r ≤
      x / Real.log ε := by
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log q⁻¹ := ⟨_, rfl⟩
  obtain ⟨lρ, hlρ_def⟩ : ∃ lρ, lρ = Real.log ρ⁻¹ := ⟨_, rfl⟩
  rw [← hL_def, ← hlρ_def]
  have hL : 0 < L := by
    rw [hL_def]
    exact Real.log_pos ((one_lt_inv₀ hq0).2 hq1)
  have hlρ : 0 ≤ lρ := by
    rw [hlρ_def]
    exact Real.log_nonneg ((one_le_inv₀ hρ0).2 hρ1)
  have hlq : Real.log q = -L := by rw [hL_def, Real.log_inv, neg_neg]
  have hlρ' : Real.log ρ = -lρ := by rw [hlρ_def, Real.log_inv, neg_neg]
  have hε0 : 0 < ε := lt_trans (by positivity) hε1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨X, hX_def⟩ : ∃ X, X = -Real.log ε := ⟨_, rfl⟩
  have hlogε : Real.log ε = -X := by rw [hX_def, neg_neg]
  have hX1 : lρ + r * L ≤ X := by
    have h := Real.log_le_log hε0 hε2
    rw [Real.log_mul hρ0.ne' (pow_ne_zero _ hq0.ne'), Real.log_pow, hlq, hlρ'] at h
    linarith
  have hX2 : X < lρ + r * L + L := by
    have h := Real.log_lt_log (by positivity) hε1
    rw [Real.log_mul hρ0.ne' (pow_ne_zero _ hq0.ne'), Real.log_pow, hlq, hlρ'] at h
    push_cast at h
    linarith
  have hrL : L ≤ r * L := by nlinarith
  have hXpos : 0 < X := by linarith
  -- `x / log ε ≥ r c / X`
  have h1 : r * c / X ≤ x / Real.log ε := by
    rw [hlogε, div_neg, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hXpos.le
  -- `r c / X ≥ c / L - |c| (lρ + L) / L² / r`
  have h2 : c / L - |c| * (lρ + L) / L ^ 2 / r ≤ r * c / X := by
    have hdiff : r * c / X - c / L = c * (r * L - X) / (X * L) := by
      field_simp
    have hnum : |r * L - X| ≤ lρ + L := by
      rw [abs_le]
      constructor <;> linarith
    have hden : (r : ℝ) * L ^ 2 ≤ X * L := by
      have : (r : ℝ) * L ≤ X := by linarith
      calc (r : ℝ) * L ^ 2 = (r * L) * L := by ring
        _ ≤ X * L := mul_le_mul_of_nonneg_right this hL.le
    have hrL2 : 0 < (r : ℝ) * L ^ 2 := by positivity
    have habs : |c * (r * L - X) / (X * L)| ≤ |c| * (lρ + L) / L ^ 2 / r := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hXpos hL)]
      calc |c| * |r * L - X| / (X * L) ≤ |c| * (lρ + L) / (X * L) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (abs_nonneg c))
              (mul_pos hXpos hL).le
        _ ≤ |c| * (lρ + L) / (r * L ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hrL2 hden
        _ = |c| * (lρ + L) / L ^ 2 / r := by
            rw [div_div, mul_comm (L ^ 2)]
    have := (abs_le.1 habs).1
    linarith
  linarith

/-- **From the window bounds to the limit through all cutoffs** (HA4 D8, item 2).  Let
`0 < ρ < 1`, `0 < q < 1`, `C ≥ 0`, `D_ε > 0` for `ε ∈ (0,1)`, and suppose that in every window
`[ρq^{r+1}, ρq^r]`, `P*(D_ε > e^{-r(a - η)}) ≤ C e^{-ηr}` for every `η`.  Then for every `θ > 0`,
`P*(log D_ε / log ε < a / log(1/q) - θ) → 0` as `ε ↓ 0`. -/
theorem tendsto_measure_div_log_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : ℝ → Ω → ℝ} {ρ q a C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hC : 0 ≤ C) (hD : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ ω, 0 < D ε ω)
    (hwin : ∀ r : ℕ, ∀ ε ∈ Icc (ρ * q ^ (r + 1)) (ρ * q ^ r), ∀ η : ℝ,
      P {ω | Real.exp (-(r * (a - η))) < D ε ω} ≤ ENNReal.ofReal (C * Real.exp (-(η * r))))
    {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε => P {ω | Real.log (D ε ω) / Real.log ε < a / Real.log q⁻¹ - θ})
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log q⁻¹ := ⟨_, rfl⟩
  obtain ⟨lρ, hlρ_def⟩ : ∃ lρ, lρ = Real.log ρ⁻¹ := ⟨_, rfl⟩
  have hL : 0 < L := by
    rw [hL_def]
    exact Real.log_pos ((one_lt_inv₀ hq0).2 hq1)
  have hlρ : 0 ≤ lρ := by
    rw [hlρ_def]
    exact Real.log_nonneg ((one_le_inv₀ hρ0).2 hρ1.le)
  rw [← hL_def]
  obtain ⟨η, hη_def⟩ : ∃ η, η = θ * L / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hη_def]
    positivity
  obtain ⟨c, hc_def⟩ : ∃ c, c = a - η := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ B, B = |c| * (lρ + L) / L ^ 2 := ⟨_, rfl⟩
  have hB : 0 ≤ B := by
    rw [hB_def]
    positivity
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (2 * B / θ)
  -- the decay `C e^{-ηR} → 0`
  have hdec : Tendsto (fun R : ℕ => ENNReal.ofReal (C * Real.exp (-(η * R)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℕ => η * (R : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hη tendsto_natCast_atTop_atTop
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    rw [mul_zero] at h2
    have h3 := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at h3
  refine ENNReal.tendsto_nhds_zero.2 fun e he => ?_
  obtain ⟨R, hR⟩ := ((ENNReal.tendsto_nhds_zero.1 hdec e he).and
    (eventually_ge_atTop (max R₀ 1))).exists
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans hR.2
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR.2
  have hpos : 0 < ρ * q ^ R := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  have hqR : q ^ R ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hερ : ε ≤ ρ := hε.2.le.trans (mul_le_of_le_one_right hρ0.le hqR)
  have hε1 : ε < 1 := lt_of_le_of_lt hερ hρ1
  obtain ⟨r, hr1, hr2⟩ := exists_window hq0 hq1 hε.1 hερ
  have hRr : R ≤ r := by
    have h : q ^ (r + 1) < q ^ R := lt_of_mul_lt_mul_left (hr1.trans hε.2) hρ0.le
    have := (pow_lt_pow_iff_right_of_lt_one₀ hq0 hq1).1 h
    omega
  have hr : 1 ≤ r := hR1.trans hRr
  have hrR₀ : (R₀ : ℝ) ≤ r := by exact_mod_cast hRR₀.trans hRr
  -- the inclusion
  have hsub : {ω | Real.log (D ε ω) / Real.log ε < a / L - θ} ⊆
      {ω | Real.exp (-(r * (a - η))) < D ε ω} := by
    intro ω hω
    have hω' : Real.log (D ε ω) / Real.log ε < a / L - θ := hω
    show Real.exp (-(r * (a - η))) < D ε ω
    by_contra hcon
    rw [not_lt] at hcon
    have hD0 := hD ε ⟨hε.1, hε1⟩ ω
    have hlog : Real.log (D ε ω) ≤ -(r * c) := by
      rw [hc_def, Real.log_le_iff_le_exp hD0]
      exact hcon
    have key := le_div_log_of_window hρ0 hρ1.le hq0 hq1 hr hr1 hr2 hlog
    rw [← hL_def, ← hlρ_def, ← hB_def] at key
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
    have hBr : B / r ≤ θ / 2 := by
      rw [div_le_iff₀ hrpos]
      have h2B : 2 * B < θ * R₀ := by
        rw [div_lt_iff₀ hθ] at hR₀
        linarith
      nlinarith
    have hcL : c / L = a / L - θ / 2 := by
      rw [hc_def, hη_def]
      field_simp
    linarith
  calc P {ω | Real.log (D ε ω) / Real.log ε < a / L - θ}
      ≤ P {ω | Real.exp (-(r * (a - η))) < D ε ω} := measure_mono hsub
    _ ≤ ENNReal.ofReal (C * Real.exp (-(η * r))) := hwin r ε ⟨hr1.le, hr2⟩ η
    _ ≤ ENNReal.ofReal (C * Real.exp (-(η * R))) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC)
        refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hη.le))
        exact_mod_cast hRr
    _ ≤ e := hR.1

/-- **Item 2 of HA4 §4** (the fixed-parameter form of (5.28), existence-free): for every
admissible kernel there is `N₀` such that for every block level `n ≥ N₀` there is `δ₀ > 0` such
that for `δ ∈ (0, δ₀)`, `ζ = δ^{3/2}`, every `θ > 0` and every white-noise model,
`P*(log D^ζ_{ε,d} / log ε < Λ_n(δ) - θ) → 0` as `ε ↓ 0` through all values, where
`Λ_n(δ) = δ²(β_{n,d} - 7)/log(1/q_δ)`. -/
def LowerComparisonFixed (d : ℕ) : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ → ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ θ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ),
    IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      Tendsto (fun ε => P {ω | Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ)) (fun z => H ε z ω)) /
          Real.log ε < δ ^ 2 * (betaN n d - 7) / Real.log (qStep d n δ)⁻¹ - θ})
        (𝓝[>] 0) (𝓝 0)

/-- **Item 2** for one kernel, from the iteration `IterD`. -/
theorem lowerComparisonFixed_kernel (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (hI : IterD d κ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      ∀ θ > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ),
      IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
        Tendsto (fun ε => P {ω | Real.log (lfppDistance d (δ ^ (3 / 2 : ℝ))
            (fun z => H ε z ω)) / Real.log ε <
              δ ^ 2 * (betaN n d - 7) / Real.log (qStep d n δ)⁻¹ - θ}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := windowBound hd hκ hI
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨δ₀, hδ₀, h⟩ := hN₀ n hn
  refine ⟨δ₀, hδ₀, fun δ hδ θ hθ Ω _ P W hW H hH => ?_⟩
  obtain ⟨hρ1, hq1, hwin⟩ := h δ hδ
  have hρ0 := rhoStep_pos n hδ.1
  have hq0 := qStep_pos d n δ
  exact tendsto_measure_div_log_lt hρ0 hρ1 hq0 hq1
    (Real.rpow_nonneg (mul_pos hρ0 hq0).le _)
    (fun ε hε ω => lfppDistance_pos hd _ ((hH ε hε).continuous ω))
    (hwin Ω P W hW H hH) hθ

/-- **Item 2** from the iteration `IterD`. -/
theorem lowerComparisonFixed_of_iterD (hd : 0 < d)
    (hI : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → IterD d κ) : LowerComparisonFixed d :=
  fun _ hκ => lowerComparisonFixed_kernel hd hκ (hI _ hκ)

/-- **Item 2** (existence-free fixed-parameter lower comparison), conditional only on
Lemma 5.3. -/
theorem lowerComparisonFixed_of_lemma53 (hd : 0 < d)
    (h53 : ∀ κ : Rd d → ℝ, IsLFPPKernel κ → Lemma53Holds d κ) : LowerComparisonFixed d :=
  lowerComparisonFixed_of_iterD hd fun κ hκ => iterD_of_lemma53 hd hκ (h53 κ hκ)

end HigherDimLFPP.Lower
