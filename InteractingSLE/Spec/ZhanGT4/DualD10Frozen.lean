/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD10

/-!
# (D10), II: the mapped driver under the tilted measure

Packet PROVE-ZHAN-GT4-A10. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L341–L353, R38):
"By (D8) and Girsanov, with the other curve stopped, the new drift of `W_j` is `κ_j q_j` … Apply (D3) to the mapped
driver `A_{j,0}`. Its `A_{j,2}`-drift cancels, leaving

  `dA_{j,0} = A_{j,1} √κ_j dB̂_j + A²_{j,1}(−κ_j/(2E_{j,0}) + Σ_m ρ_{j,m}/E_{j,m}) dt_j`.   (D10)"

For ordinary `SLE_κ` (`W = √κB`) with the other curve frozen and the (D9) hypotheses up to a stopping time `S`
(`FrzMartHyp`, plus the bound `|A_{j,0}| ≤ Γ` of the mapped driver: `FrzD10Hyp`), and `Q = (M̃_S/M̃_0) · P` (the
measure under which `W` has the Girsanov drift `κ q_j`, `FrzMartHyp.isFilteredBrownianReal_girs`), we prove (D10) in
exponential-martingale form: for every `ν ∈ ℝ`,

  `exp(ν (A_{j,0}(t∧S) − A_{j,0}(0) − J_{t∧S})/√κ − ν² a(t∧S)/2)`,  `J_t = ∫₀ᵗ A²_{j,1}(−κ/(2E_{j,0}) + Σ ρ_m/E_{j,m})`,

is a `Q`-martingale of `𝓕` (**`FrzD10Hyp.martingale_d10`**), where `A_{j,0}(t) = W'(a(t))` is the mapped driver and
`a(t) = ∫₀ᵗ A²_{j,1}` the image capacity clock: i.e. `A_{j,0} − J` is a continuous `Q`-martingale with quadratic
variation `κ a(t)`, which is (D10).

Proof: the field `ψ(t, x) = (ν/√κ)(F_t(x) − A_{j,0}(0)) + ∫₀ᵗ g`, `F_t = Re ownExt_t` (the reflected `h_j`),
`g = −(ν/√κ) J' − (ν²/2) A²_{j,1}`, is added to `ℓ = log M̃`; `ℓ + ψ` is again a driver log-field
(`FrzD10Hyp.isDriverLogField_d10`): the generator at the driver is
`[ℓ_t + κ/2(ℓ_xx + ℓ_x²)] + (ν/√κ)(Re D̂(W) + κ/2 F''(W) + κ ℓ_x F'(W)) + ν²/2 F'(W)² + g = 0`
by A8's generator identity, (D2) `Re D̂(W) = −3A₂`, `ℓ_x(W) = q_j` and A9's `dualD10_drift`. Then
`IsDriverLogField.martingale_addExp`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### The (D10) drift -/

/-- **The (D10) drift of the mapped driver**, `A²_{j,1}(−κ/(2E_{j,0}) + Σ ρ_m/E_{j,m})` with `E_{j,0} = A_{j,0} −
A_{k,0}`, `E_{j,m} = A_{j,0} − B_{m,0}` and `ρ_m = κ r_m`. -/
def FrzData.d10Rate {n : ℕ} (d : FrzData n) (t : ℝ) : ℝ :=
  d.A 1 t ^ 2 * (-(d.κ / (2 * (d.A 0 t - d.A20 t))) + ∑ m, d.κ * d.r m / (d.A 0 t - d.B0 t m))

/-- The bound `|κ|/γ · (1 + Σ |r_m|)` of the (D10) drift on the protected rectangle. -/
def d10Bound (κ γ : ℝ) {n : ℕ} (r : Fin n → ℝ) : ℝ := |κ| / γ * (1 + ∑ m, |r m|)

namespace FrzData

variable {n : ℕ} (d : FrzData n) {A : Set ℂ} {T : ℝ} (h : OwnData d.W A d.φ T d.a d.W') {r a₀ γ Γ lam : ℝ}
  (hc : d.D9Const A T r a₀ γ Γ lam)
include h hc

/-- `|J'| ≤ |κ|/γ (1 + Σ|r_m|)` on the protected rectangle. -/
theorem abs_d10Rate_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : |d.d10Rate t| ≤ d10Bound d.κ γ d.r := by
  obtain ⟨ha1, ha1', -, -⟩ := d.driver_bounds h hc ht
  have hγ := hc.g0
  have ha := hc.a0
  have hA1sq : d.A 1 t ^ 2 ≤ 1 := by nlinarith
  have hfrac : ∀ X E : ℝ, γ ≤ |E| → |X / E| ≤ |X| / γ := fun X E hE => by
    rw [abs_div]; exact div_le_div_of_nonneg_left (abs_nonneg X) hγ hE
  have h0 : |d.κ / (2 * (d.A 0 t - d.A20 t))| ≤ |d.κ| / γ := by
    have hE := (hc.E0 t ht).1
    have : γ ≤ |2 * (d.A 0 t - d.A20 t)| := by
      rw [abs_mul, abs_two, abs_sub_comm]; linarith [abs_nonneg (d.A20 t - d.A 0 t)]
    exact hfrac _ _ this
  have hm : ∀ m, |d.κ * d.r m / (d.A 0 t - d.B0 t m)| ≤ |d.κ| / γ * |d.r m| := fun m => by
    have hE := (hc.Em t ht m).1
    rw [abs_sub_comm] at hE
    calc _ ≤ |d.κ * d.r m| / γ := hfrac _ _ hE
      _ = |d.κ| / γ * |d.r m| := by rw [abs_mul]; ring
  have hsum : |-(d.κ / (2 * (d.A 0 t - d.A20 t))) + ∑ m, d.κ * d.r m / (d.A 0 t - d.B0 t m)| ≤
      d10Bound d.κ γ d.r := by
    unfold d10Bound
    calc _ ≤ |d.κ / (2 * (d.A 0 t - d.A20 t))| + ∑ m, |d.κ * d.r m / (d.A 0 t - d.B0 t m)| :=
          (abs_add_le _ _).trans (add_le_add (abs_neg _).le (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ |d.κ| / γ + ∑ m, |d.κ| / γ * |d.r m| := add_le_add h0 (Finset.sum_le_sum fun m _ => hm m)
      _ = _ := by rw [← Finset.mul_sum]; ring
  unfold FrzData.d10Rate
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc _ ≤ 1 * d10Bound d.κ γ d.r := mul_le_mul hA1sq hsum (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The (D10) drift is continuous on `[0, T]`. -/
theorem continuousOn_d10Rate {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀) {v : Fin n → ℝ → ℂ}
    (hv : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (v m)) : ContinuousOn d.d10Rate (Icc 0 T) := by
  have hA0 : ContinuousOn (d.A 0) (Icc 0 T) := h.continuousOn_frzA 0
  have hA1 : ContinuousOn (d.A 1) (Icc 0 T) := h.continuousOn_frzA 1
  have h20 := d.continuousOn_A20 h hv₀
  have hB0 := d.continuousOn_B0 h hv
  have hγ := hc.g0
  have ne : ∀ E : ℝ, γ ≤ |E| → E ≠ 0 := fun E hE h0 => by rw [h0, abs_zero] at hE; linarith
  unfold FrzData.d10Rate
  refine (hA1.pow 2).mul ((continuousOn_const.div (continuousOn_const.mul (hA0.sub h20)) fun t ht => ?_).neg.add
    (continuousOn_finsetSum _ fun m _ => continuousOn_const.div (hA0.sub (hB0 m)) fun t ht => ?_))
  · exact mul_ne_zero two_ne_zero (ne _ (by rw [Pi.sub_apply, abs_sub_comm]; exact (hc.E0 t ht).1))
  · exact ne _ (by rw [abs_sub_comm]; exact (hc.Em t ht m).1)

end FrzData

/-- **The capacity clock is the integral of `A²_{j,1}`**: `a(t) = ∫₀ᵗ A_{j,1}(u)² du` on `[0, T]`. -/
theorem OwnData.integral_frzA_one_sq {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData W A φ T a W') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ u in (0 : ℝ)..t, frzA W W' a φ 1 u ^ 2 = a t := by
  have hcont : ContinuousOn (fun u => frzA W W' a φ 1 u ^ 2) (Icc 0 T) := (h.continuousOn_frzA 1).pow 2
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (h.contA.mono (Icc_subset_Icc_right ht.2))
    (fun u hu => ?_) ((hcont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1), h.a0, sub_zero]
  have hu' : u ∈ Icc (0 : ℝ) T := ⟨hu.1.le, hu.2.le.trans ht.2⟩
  have hnhds : Icc (0 : ℝ) T ∈ 𝓝 u := Icc_mem_nhds hu.1 (lt_of_lt_of_le hu.2 ht.2)
  exact ((h.hasDerivWithinAt_clock hu').1.hasDerivAt hnhds).hasDerivWithinAt

/-! ### The (D10) field along the frozen data -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Field

variable {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (φ : ℂ → ℂ) (rr : Fin n → ℝ) (ζ₀ : ℝ)
  (ζ : Fin n → ℝ) (ν : ℝ)

/-- **The time rate of the (D10) field**, `g = −(ν/√κ) J' − (ν²/2) A²_{j,1}`. -/
def d10G (ω : Ω) (t : ℝ) : ℝ :=
  -(ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate t) -
    ν ^ 2 / 2 * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 1 t ^ 2

/-- **The (D10) field** `ψ(t, x) = (ν/√κ)(F_t(x) − A_{j,0}(0)) + ∫₀ᵗ g` (`g` cut at `S`). -/
def d10Psi (S : Ω → ℝ≥0) (ω : Ω) (t x : ℝ) : ℝ :=
  ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).F 0 t x +
    (-(ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 0) + cutInt S (d10G κ B W' a φ rr ζ₀ ζ ν) ω t)

/-- `∂^k_x ψ = (ν/√κ) F_t^{(k)}`. -/
def d10PsiX (k : ℕ) (ω : Ω) (t x : ℝ) : ℝ := ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).F k t x

/-- `∂_t ψ = (ν/√κ) Re D̂_t(x) + g_t` ((D1)). -/
def d10PsiT (ω : Ω) (t x : ℝ) : ℝ :=
  ν / Real.sqrt κ * (dHat (ownExt (drive κ B ω) (W' ω) (a ω) φ t) ((drive κ B ω t : ℝ) : ℂ) (x : ℂ)).re +
    d10G κ B W' a φ rr ζ₀ ζ ν ω t

end Field

/-- The bound of the (D10) field and its derivatives on the boxes. -/
def d10K (κ ν γ Γ L Tmax : ℝ) {n : ℕ} (rr : Fin n → ℝ) : ℝ :=
  |ν / Real.sqrt κ| * (2 * Real.exp L + 3 * Γ) + (|ν / Real.sqrt κ| * d10Bound κ γ rr + ν ^ 2 / 2) * (Tmax + 1)

/-- **The hypotheses of (D10)**: those of the frozen-curve martingale (`FrzMartHyp`) and the bound `|A_{j,0}| =
|W'(a(t))| ≤ Γ` of the mapped driver (`TwoCurveD9.drv`). -/
structure FrzD10Hyp {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ)
    (rr : Fin n → ℝ) (ζ₀ : ℝ) (ζ : Fin n → ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ) (r a₀ γ Γ lam L Tmax : ℝ) : Prop
    extends FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax where
  drv : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω), |W' ω (a ω t)| ≤ Γ

/-- **The hypotheses of (D10) from the enclosure data** (§A.1.3; `exists_frzMartHyp` with `TwoCurveD9.drv`). -/
theorem exists_frzD10Hyp {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hqH : Disjoint (Metric.ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {n : ℕ} {p : Fin n → ℝ}
    (hpH : ∀ m, Disjoint (Metric.ball (p m : ℂ) (2 * d)) (H₁ ∪ H₂)) (hpinj : Function.Injective p) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam L : ℝ, ∀ [Nonempty Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (rr : Fin n → ℝ)
      (W₂ : ℝ → ℝ) (t₂ : ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ),
      (∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω)) →
      (∀ ω, (S ω : ℝ) ≤ T ω) → (∀ ω, T ω ≤ Tm) → (∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁) →
      Continuous W₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → q < W₂ 0 → 0 < t₂ → t₂ ≤ Tm → fwdHull W₂ t₂ ⊆ H₂ →
      FrzD10Hyp κ B W' a (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) rr (W₂ t₂)
        (fun m => (fwdMap W₂ t₂ (p m)).re + W₂ t₂) S T r a₀ γ Γ lam L Tm := by
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha₀, hγ, hmain⟩ := exists_twoCurveD9 hH₁ hH₂ hδ hsepδ hd hq hqH hpH hpinj Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha₀ hγ Γ lam Tm
  refine ⟨r, a₀, γ, Γ, lam, L, fun κ B W' a rr W₂ t₂ S T hown hST hTm hK₁ hW₂ hW₂H hqW ht₂ ht₂m hK₂ => ?_⟩
  have hD := fun ω => hmain (drive κ B ω) W₂ t₂ (T ω) (a ω) (W' ω) κ rr (hown ω) hW₂ hW₂H hqW ht₂ ht₂m (hTm ω)
    (hK₁ ω) hK₂
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  exact ⟨⟨hown, hST, hTm, fun ω => (hD ω).alive₀, fun ω m => (hD ω).alive m, (hD ω₀).ne, (hD ω₀).inj,
    fun ω => (hD ω).d9, hL⟩, fun ω t ht => (hD ω).drv t ht⟩

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- `|A_{j,0}| ≤ Γ` on `[0, T]`. -/
theorem abs_A0_le (ω : Ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T ω)) : |(frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 t| ≤ Γ := by
  show |frzA (drive κ B ω) (W' ω) (a ω) φ 0 t| ≤ Γ
  rw [(hH.own ω).frzA_zero ht]
  exact hH.drv ω t ht

theorem Γ_nonneg (ω : Ω) : 0 ≤ Γ :=
  (abs_nonneg _).trans (hH.abs_A0_le ω ⟨le_rfl, (hH.own ω).pos.le⟩)

theorem Tmax_pos (ω : Ω) : 0 < Tmax := lt_of_lt_of_le (hH.own ω).pos (hH.leMax ω)

/-- The rate `g` is continuous on `[0, S]`. -/
theorem continuousOn_d10G (ν : ℝ) (ω : Ω) :
    ContinuousOn (d10G κ B W' a φ rr ζ₀ ζ ν ω) (Icc 0 (S ω : ℝ)) := by
  have hJ : Icc (0 : ℝ) (S ω) ⊆ Icc 0 (T ω) := Icc_subset_Icc_right (hH.le ω)
  have h1 := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).continuousOn_d10Rate (hH.own ω) (hH.d9 ω) (hH.alive₀ ω).choose_spec
    (v := fun m => (hH.alive ω m).choose) (fun m => (hH.alive ω m).choose_spec)
  have h2 : ContinuousOn ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 1) (Icc 0 (T ω)) := (hH.own ω).continuousOn_frzA 1
  unfold d10G
  exact ((continuousOn_const.mul (h1.mono hJ)).neg.sub (continuousOn_const.mul ((h2.mono hJ).pow 2)))

/-- `|g| ≤ |ν/√κ| d10Bound + ν²/2` on `[0, S]`. -/
theorem abs_d10G_le (ν : ℝ) (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (S ω : ℝ)) :
    |d10G κ B W' a φ rr ζ₀ ζ ν ω t| ≤ |ν / Real.sqrt κ| * d10Bound κ γ rr + ν ^ 2 / 2 := by
  have htT : t ∈ Icc (0 : ℝ) (T ω) := ⟨ht.1, ht.2.trans (hH.le ω)⟩
  set d := frzDataOf κ B W' a φ rr ζ₀ ζ ω
  have h1 := d.abs_d10Rate_le (hH.own ω) (hH.d9 ω) htT
  obtain ⟨ha1, ha1', -, -⟩ := d.driver_bounds (hH.own ω) (hH.d9 ω) htT
  have ha := (hH.d9 ω).a0
  have hA1sq : d.A 1 t ^ 2 ≤ 1 := by nlinarith
  unfold d10G
  calc _ ≤ |ν / Real.sqrt κ * d.d10Rate t| + |ν ^ 2 / 2 * d.A 1 t ^ 2| :=
        (abs_sub _ _).trans (add_le_add (abs_neg _).le le_rfl)
    _ ≤ |ν / Real.sqrt κ| * d10Bound κ γ rr + ν ^ 2 / 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 2 / 2),
          abs_of_nonneg (sq_nonneg (d.A 1 t))]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          ((mul_le_mul_of_nonneg_left hA1sq (by positivity)).trans (le_of_eq (mul_one _)))

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- The rate `g` is adapted on `{r ≤ S}`. -/
theorem measurable_d10G (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) (rT : ℝ≥0) :
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => d10G κ B W' a φ rr ζ₀ ζ ν ω rT) := by
  obtain ⟨hA, hI0, hIm, -, -, -⟩ := hH.toFrzMartHyp.measurable_parts hBm hBc hS rT
  have hG : MeasurableSet[𝓕 rT] {ω | rT ≤ S ω} := measurableSet_ge_of_isStoppingTime hS rT
  set G := {ω | rT ≤ S ω} with hGdef
  have hA0 := hA 0
  have hA1 := hA 1
  set f0 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 0 rT with hf0
  set f1 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 1 rT with hf1
  set i0 := G.indicator fun ω => frzImg (W' ω) (a ω) ζ₀ rT with hi0
  set im := fun m => G.indicator fun ω => frzImg (W' ω) (a ω) (ζ m) rT with him
  have hmeas : Measurable[𝓕 rT] fun ω => -(ν / Real.sqrt κ * (f1 ω ^ 2 * (-(κ / (2 * (f0 ω - i0 ω))) +
      ∑ m, κ * rr m / (f0 ω - im m ω)))) - ν ^ 2 / 2 * f1 ω ^ 2 := by
    fun_prop
  convert hmeas.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · rw [indicator_of_mem hω, indicator_of_mem hω]
    simp only [hf0, hf1, hi0, him, indicator_of_mem hω]
    rfl
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

/-- **The (D10) field is a regular log-field on every driver piece** in `[0, S]`. -/
theorem isLogField_psi (ν : ℝ) (ω : Ω) {b c y : ℝ} (hb : 0 ≤ b) (hcS : c ≤ S ω)
    (hWy : ∀ t ∈ Icc b c, |Real.sqrt κ * B t.toNNReal ω - y| < cutRad r a₀ γ) :
    IsLogField (d10Psi κ B W' a φ rr ζ₀ ζ ν S ω) (d10PsiX κ B W' a φ rr ζ₀ ζ ν 1 ω)
      (d10PsiX κ B W' a φ rr ζ₀ ζ ν 2 ω) (d10PsiX κ B W' a φ rr ζ₀ ζ ν 3 ω) (d10PsiT κ B W' a φ rr ζ₀ ζ ν ω)
      b c y (cutRad r a₀ γ) (d10K κ ν γ Γ L Tmax rr) := by
  set d := frzDataOf κ B W' a φ rr ζ₀ ζ ω with hd
  have hown : OwnData d.W A d.φ (T ω) d.a d.W' := hH.own ω
  have hJ : Icc b c ⊆ Icc 0 (T ω) := fun _ hx => ⟨hb.trans hx.1, hx.2.trans (hcS.trans (hH.le ω))⟩
  obtain ⟨hdisj, hWm, hq0, h3, hsp⟩ := d.piece_facts hown hJ (hH.d9 ω) (hH.scaleOK ω) hWy
  have hF : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * cutRad r a₀ γ → ∀ k,
      HasDerivAt (d.F k t) (d.F (k + 1) t x) x :=
    fun t ht x hx k => hown.hasDerivAt_re_iterDeriv_box hJ hdisj ht (FrzData.mem_ball_of_near h3 hx) k
  have cF := fun k => d.continuousOn_F hown hJ hdisj h3 k
  set cc := ν / Real.sqrt κ with hcc
  set g := d10G κ B W' a φ rr ζ₀ ζ ν with hg
  set Cg := |cc| * d10Bound κ γ rr + ν ^ 2 / 2 with hCg
  have hgc : ∀ ω', ContinuousOn (g ω') (Icc 0 (S ω' : ℝ)) := fun ω' => hH.continuousOn_d10G ν ω'
  have hβ : ∀ t ∈ Icc b c, HasDerivWithinAt (cutInt S g ω) (g ω t) (Icc b c) t := fun t ht =>
    hasDerivWithinAt_cutInt hgc ω hb hcS ht
  have hβc : ContinuousOn (cutInt S g ω) (Icc b c) := fun t ht => (hβ t ht).continuousWithinAt
  have hgcb : ContinuousOn (g ω) (Icc b c) := (hgc ω).mono (Icc_subset_Icc hb hcS)
  set R := Icc b c ×ˢ {x : ℝ | |x - y| < 3 * cutRad r a₀ γ} with hR
  have hfst : MapsTo Prod.fst R (Icc b c) := fun _p hp => hp.1
  -- nonnegativity of the constants
  have hΓ := hH.Γ_nonneg ω
  have hTm := (hH.Tmax_pos ω).le
  have hL0 : 0 ≤ Real.exp L := (Real.exp_pos _).le
  have hCg0 : 0 ≤ Cg := (abs_nonneg _).trans (hH.abs_d10G_le ν ω ⟨le_rfl, (S ω).coe_nonneg⟩)
  have hcc0 : 0 ≤ |cc| := abs_nonneg _
  have hKe : |cc| * Real.exp L ≤ d10K κ ν γ Γ L Tmax rr := by
    unfold d10K
    rw [← hcc, ← hCg]
    nlinarith [mul_nonneg hcc0 hL0, mul_nonneg hcc0 hΓ, mul_nonneg hCg0 hTm]
  refine ⟨cutRad_pos (hH.d9 ω).r0 (hH.d9 ω).a0 (hH.d9 ω).g0, (mul_nonneg hcc0 hL0).trans hKe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx
    exact ((hF t ht x hx 0).const_mul cc).add_const _
  · intro t ht x hx
    exact (hF t ht x hx 1).const_mul cc
  · intro t ht x hx
    exact (hF t ht x hx 2).const_mul cc
  · intro t ht x hx
    exact ((hown.hasDerivWithinAt_re_ownExt_box hJ hdisj hWm hq0 ht
      (FrzData.mem_ball_of_near h3 hx)).const_mul cc).add ((hβ t ht).const_add _)
  · exact (continuousOn_const.mul (cF 0)).add
      (continuousOn_const.add (hβc.comp continuousOn_fst hfst))
  · exact continuousOn_const.mul (cF 1)
  · exact continuousOn_const.mul (cF 2)
  · have hdf0 := (hown.continuousOn_dHat_box hJ hdisj hWm hq0).comp FrzData.continuous_region.continuousOn
      (FrzData.mapsTo_region (b := b) (c := c) (y := y) h3)
    have hdf := Complex.continuous_re.comp_continuousOn hdf0
    simp only [Function.comp_def] at hdf
    exact (continuousOn_const.mul hdf).add (hgcb.comp continuousOn_fst hfst)
  · intro t ht x hx
    obtain ⟨s1, s0, -, s2, s3, -, sD, -⟩ := hsp t ht x hx
    have htT := hJ ht
    have htS : t ∈ Icc (0 : ℝ) (S ω) := ⟨hb.trans ht.1, ht.2.trans hcS⟩
    have hA0 := hH.abs_A0_le ω htT
    have hA00 := hH.abs_A0_le ω ⟨le_rfl, (hH.own ω).pos.le⟩
    have hE0 := ((hH.d9 ω).E0 t htT).2
    have hF0 : |d.F 0 t x| ≤ Real.exp L + 2 * Γ := by
      have e : d.F 0 t x = (d.F 0 t x - d.A20 t) + (d.A20 t - d.A 0 t) + d.A 0 t := by ring
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add s0.2 hE0)) hA0) |>.trans
        (by linarith)
    have hI : |cutInt S g ω t| ≤ Cg * Tmax :=
      (abs_cutInt_le (fun ω' r hr => hH.abs_d10G_le ν ω' hr) hCg0 ω htS.1).trans
        (mul_le_mul_of_nonneg_left (htT.2.trans (hH.leMax ω)) hCg0)
    have hgt : |g ω t| ≤ Cg := hH.abs_d10G_le ν ω htS
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show |cc * d.F 0 t x + (-(cc * d.A 0 0) + cutInt S g ω t)| ≤ d10K κ ν γ Γ L Tmax rr
      have h1 : |cc * d.F 0 t x| ≤ |cc| * (Real.exp L + 2 * Γ) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hF0 hcc0
      have h2 : |cc * d.A 0 0| ≤ |cc| * Γ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hA00 hcc0
      have h3' : |cc * d.F 0 t x + (-(cc * d.A 0 0) + cutInt S g ω t)| ≤
          |cc| * (Real.exp L + 2 * Γ) + (|cc| * Γ + Cg * Tmax) :=
        (abs_add_le _ _).trans (add_le_add h1 ((abs_add_le _ _).trans (add_le_add ((abs_neg _).le.trans h2) hI)))
      refine h3'.trans ?_
      unfold d10K
      rw [← hcc, ← hCg]
      nlinarith [mul_nonneg hcc0 hL0]
    · show |cc * d.F 1 t x| ≤ _
      rw [abs_mul]; exact (mul_le_mul_of_nonneg_left s1.2 hcc0).trans hKe
    · show |cc * d.F 2 t x| ≤ _
      rw [abs_mul]; exact (mul_le_mul_of_nonneg_left s2 hcc0).trans hKe
    · show |cc * d.F 3 t x| ≤ _
      rw [abs_mul]; exact (mul_le_mul_of_nonneg_left s3 hcc0).trans hKe
    · show |cc * (dHat (ownExt d.W d.W' d.a d.φ t) ((d.W t : ℝ) : ℂ) (x : ℂ)).re + g ω t| ≤ _
      have h1 : |cc * (dHat (ownExt d.W d.W' d.a d.φ t) ((d.W t : ℝ) : ℂ) (x : ℂ)).re| ≤ |cc| * Real.exp L := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left sD hcc0
      refine ((abs_add_le _ _).trans (add_le_add h1 hgt)).trans ?_
      unfold d10K
      rw [← hcc, ← hCg]
      nlinarith [mul_nonneg hcc0 hL0, mul_nonneg hcc0 hΓ, mul_nonneg hCg0 hTm]

/-- **The generator of `ℓ + ψ` vanishes at the driver** ((D10)'s cancellation): `[ℓ_t + κ/2(ℓ_xx + ℓ_x²)] +
(ν/√κ)(Re D̂(W) + κ/2 F''(W) + κ ℓ_x F'(W)) + ν²/2 F'(W)² + g = 0`. -/
theorem gen_d10 (hκ : 0 < κ) (ν : ℝ) (ω : Ω) {u : ℝ} (hu0 : 0 ≤ u) (huS : u ≤ S ω) :
    ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).ellT u (Real.sqrt κ * B u.toNNReal ω) +
        d10PsiT κ B W' a φ rr ζ₀ ζ ν ω u (Real.sqrt κ * B u.toNNReal ω)) +
      Real.sqrt κ ^ 2 / 2 * (((frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXX u (Real.sqrt κ * B u.toNNReal ω) +
          d10PsiX κ B W' a φ rr ζ₀ ζ ν 2 ω u (Real.sqrt κ * B u.toNNReal ω)) +
        ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX u (Real.sqrt κ * B u.toNNReal ω) +
          d10PsiX κ B W' a φ rr ζ₀ ζ ν 1 ω u (Real.sqrt κ * B u.toNNReal ω)) ^ 2) = 0 := by
  set d := frzDataOf κ B W' a φ rr ζ₀ ζ ω with hd
  have hgen := hH.toFrzMartHyp.gen hκ ω hu0 huS
  have huT : u ∈ Icc (0 : ℝ) (T ω) := ⟨hu0, huS.trans (hH.le ω)⟩
  have hρ := hH.toFrzMartHyp.cutRad_pos ω
  have hWy : ∀ t ∈ Icc u u, |d.W t - d.W u| < cutRad r a₀ γ := fun t ht => by
    rw [show t = u from le_antisymm ht.2 ht.1, sub_self, abs_zero]; exact hρ
  have hJ : Icc u u ⊆ Icc 0 (T ω) := fun t ht => by rw [show t = u from le_antisymm ht.2 ht.1]; exact huT
  obtain ⟨hdisj, hWm, hq0, -, -⟩ := d.piece_facts (hH.own ω) hJ (hH.d9 ω) (hH.scaleOK ω) hWy
  have hD := ((hH.own ω).re_dHat_drive hJ hdisj hWm hq0 (t := u) ⟨le_rfl, le_rfl⟩).1
  have hq := d.LSX_driver_eq_dualQ u
  have hA1 : d.A 1 u ≠ 0 := ((hH.own ω).frzA_one_pos huT).ne'
  have hdrift := dualD10_drift (κ := κ) (A1 := d.A 1 u) (A2 := d.A 2 u) (E0 := d.A 0 u - d.A20 u) rr
    (fun m => d.A 0 u - d.B0 u m) hκ.ne' hA1
  have e5 : d.d10Rate u = -3 * d.A 2 u + κ / 2 * d.A 2 u +
      κ * dualQ κ (d.A 1 u) (d.A 2 u) (d.A 0 u - d.A20 u) rr (fun m => d.A 0 u - d.B0 u m) * d.A 1 u := by
    rw [hdrift]; rfl
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hc2 : (ν / Real.sqrt κ) ^ 2 * κ = ν ^ 2 := by
    rw [div_pow, hsq]; field_simp
  have key : ∀ (eT LXX LX F1 F2 ReD R A1 A2 q sq c : ℝ), eT + sq ^ 2 / 2 * (LXX + LX ^ 2) = 0 →
      ReD = -3 * A2 → F1 = A1 → F2 = A2 → LX = q → R = -3 * A2 + κ / 2 * A2 + κ * q * A1 → sq ^ 2 = κ →
      c ^ 2 * κ = ν ^ 2 →
      (eT + (c * ReD + (-(c * R) - ν ^ 2 / 2 * A1 ^ 2))) + sq ^ 2 / 2 * ((LXX + c * F2) + (LX + c * F1) ^ 2) = 0 := by
    intro eT LXX LX F1 F2 ReD R A1 A2 q sq c h1 h2 h3 h4 h5 h6 h7 h8
    subst h2 h3 h4 h5 h6
    rw [h7] at h1 ⊢
    linear_combination h1 + (F1 ^ 2 / 2) * h8
  unfold d10PsiT d10PsiX d10G
  exact key _ _ _ _ _ _ _ _ _ _ _ _ hgen hD rfl rfl hq e5 hsq hc2

variable {𝓕 : Filtration ℝ≥0 mΩ}

omit hH in
theorem measurable_indicator_add_mul {m : MeasurableSpace Ω} {G : Set Ω} {f h : Ω → ℝ}
    (hf : Measurable[m] (G.indicator f)) (hh : Measurable[m] (G.indicator h)) (c : ℝ) :
    Measurable[m] (G.indicator fun ω => f ω + c * h ω) := by
  have e : (G.indicator fun ω => f ω + c * h ω) = fun ω => G.indicator f ω + c * G.indicator h ω := by
    funext ω; by_cases hω : ω ∈ G <;> simp [hω]
  rw [e]; exact hf.add (hh.const_mul c)

/-- `F^{(k)}` at the driver is adapted on `{r ≤ S}`. -/
theorem measurable_d10_F (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (k : ℕ) (rT : ℝ≥0) :
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω =>
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).F k rT (Real.sqrt κ * B rT ω)) := by
  obtain ⟨hA, -, -, -, -, -⟩ := hH.toFrzMartHyp.measurable_parts hBm hBc hS rT
  convert hA k using 2
  funext ω
  rw [← FrzMartHyp.frzDataOf_W (W' := W') (a := a) (φ := φ) (rr := rr) (ζ₀ := ζ₀) (ζ := ζ)]
  rfl

/-- `ℓ + ψ` along the driver is adapted on `{r ≤ S}`. -/
theorem measurable_d10_0 (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) (rT : ℝ≥0) :
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω =>
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell rT (Real.sqrt κ * B rT ω) +
        d10Psi κ B W' a φ rr ζ₀ ζ ν S ω rT (Real.sqrt κ * B rT ω)) := by
  have hG : MeasurableSet[𝓕 rT] {ω | rT ≤ S ω} := measurableSet_ge_of_isStoppingTime hS rT
  have hE := hH.toFrzMartHyp.measurable_ell hBm hBc hS rT
  have hF := hH.measurable_d10_F hBm hBc hS 0 rT
  have hA00 : Measurable[𝓕 rT] fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 0 := by
    have h := (hH.toFrzMartHyp.measurable_parts hBm hBc hS 0).1 0
    have e : ({ω | (0 : ℝ≥0) ≤ S ω}.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 0 ((0 : ℝ≥0) : ℝ)) =
        fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 0 := by
      funext ω; rw [indicator_of_mem (by simp : ω ∈ {ω | (0 : ℝ≥0) ≤ S ω})]; rfl
    rw [e] at h
    exact h.mono (𝓕.mono zero_le) le_rfl
  have hI := measurable_cutInt (hH.continuousOn_d10G ν) hS (hH.measurable_d10G hBm hBc hS ν) rT
  have hsum := measurable_indicator_add_mul hE hF (ν / Real.sqrt κ)
  have hrest : Measurable[𝓕 rT] fun ω => -(ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 0) +
      cutInt S (d10G κ B W' a φ rr ζ₀ ζ ν) ω rT := (hA00.const_mul _).neg.add hI
  have e : ({ω | rT ≤ S ω}.indicator fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell rT (Real.sqrt κ * B rT ω) +
      d10Psi κ B W' a φ rr ζ₀ ζ ν S ω rT (Real.sqrt κ * B rT ω)) = fun ω =>
      ({ω | rT ≤ S ω}.indicator fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell rT (Real.sqrt κ * B rT ω) +
        ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).F 0 rT (Real.sqrt κ * B rT ω)) ω +
      {ω | rT ≤ S ω}.indicator (fun ω => -(ν / Real.sqrt κ * (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 0) +
        cutInt S (d10G κ B W' a φ rr ζ₀ ζ ν) ω rT) ω := by
    funext ω
    by_cases hω : ω ∈ {ω | rT ≤ S ω}
    · simp only [indicator_of_mem hω, d10Psi]; ring
    · simp only [indicator_of_notMem hω, add_zero]
  rw [e]
  exact hsum.add (hrest.indicator hG)

/-- **`log M̃ + ψ` is a driver log-field up to `S`** (the (D10) field added to A8's `log M̃`). -/
theorem isDriverLogField_d10 (hκ : 0 < κ) (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) :
    IsDriverLogField 𝓕 (Real.sqrt κ) (cutRad r a₀ γ) (2 * coefTot κ rr * scaleBound L + d10K κ ν γ Γ L Tmax rr) B S
      (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell t x + d10Psi κ B W' a φ rr ζ₀ ζ ν S ω t x)
      (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX t x + d10PsiX κ B W' a φ rr ζ₀ ζ ν 1 ω t x)
      (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXX t x + d10PsiX κ B W' a φ rr ζ₀ ζ ν 2 ω t x)
      (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXXX t x + d10PsiX κ B W' a φ rr ζ₀ ζ ν 3 ω t x)
      (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ellT t x + d10PsiT κ B W' a φ rr ζ₀ ζ ν ω t x) :=
  ⟨fun ω _ _ _ hb _ hcS hWy => (hH.toFrzMartHyp.isLogField ω hb hcS hWy).add (hH.isLogField_psi ν ω hb hcS hWy),
    fun ω _ hu0 huS => hH.gen_d10 hκ ν ω hu0 huS, hH.measurable_d10_0 hBm hBc hS ν,
    fun rT => measurable_indicator_add_mul (hH.toFrzMartHyp.measurable_LSX hBm hBc hS rT)
      (hH.measurable_d10_F hBm hBc hS 1 rT) _,
    fun rT => measurable_indicator_add_mul (hH.toFrzMartHyp.measurable_LSXX hBm hBc hS rT)
      (hH.measurable_d10_F hBm hBc hS 2 rT) _⟩

/-- **The (D10) exponential along the stopped driver**: `exp ψ(t∧S, W_{t∧S}) = exp((ν/√κ)(W'(a(τ)) − W'(0) − J_τ) −
(ν²/2) a(τ))`, `τ = t∧S`, `J_τ = ∫₀^τ A²_{j,1}(−κ/(2E_{j,0}) + Σ ρ_m/E_{j,m})`. -/
theorem addExp_d10_eq (ν : ℝ) (t : ℝ≥0) (ω : Ω) :
    addExp (Real.sqrt κ) B S (d10Psi κ B W' a φ rr ζ₀ ζ ν S) t ω =
      Real.exp (ν / Real.sqrt κ * (W' ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) - W' ω 0 -
        ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ), (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u) -
        ν ^ 2 / 2 * a ω ((min t (S ω) : ℝ≥0) : ℝ)) := by
  set d := frzDataOf κ B W' a φ rr ζ₀ ζ ω with hd
  have hown : OwnData d.W A d.φ (T ω) d.a d.W' := hH.own ω
  have hτS : ((min t (S ω) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    ⟨(min t (S ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
  have hτT : ((min t (S ω) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (T ω) := ⟨hτS.1, hτS.2.trans (hH.le ω)⟩
  have hW : d.W ((min t (S ω) : ℝ≥0) : ℝ) = Real.sqrt κ * B (min t (S ω)) ω := by
    show Real.sqrt κ * B (((min t (S ω) : ℝ≥0) : ℝ)).toNNReal ω = _
    rw [Real.toNNReal_coe]
  have hA0 : d.A 0 ((min t (S ω) : ℝ≥0) : ℝ) = W' ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) := hown.frzA_zero hτT
  have hA00 : d.A 0 0 = W' ω 0 := by
    rw [show d.A 0 0 = W' ω (a ω 0) from hown.frzA_zero ⟨le_rfl, hown.pos.le⟩]
    rw [show a ω 0 = 0 from hown.a0]
  have h1 : IntervalIntegrable d.d10Rate volume 0 ((min t (S ω) : ℝ≥0) : ℝ) :=
    ((d.continuousOn_d10Rate hown (hH.d9 ω) (hH.alive₀ ω).choose_spec (v := fun m => (hH.alive ω m).choose)
      (fun m => (hH.alive ω m).choose_spec)).mono (Icc_subset_Icc_right hτT.2)).intervalIntegrable_of_Icc hτS.1
  have h2 : IntervalIntegrable (fun u => d.A 1 u ^ 2) volume 0 ((min t (S ω) : ℝ≥0) : ℝ) :=
    ((((hown.continuousOn_frzA 1).pow 2)).mono (Icc_subset_Icc_right hτT.2)).intervalIntegrable_of_Icc hτS.1
  have hI : cutInt S (d10G κ B W' a φ rr ζ₀ ζ ν) ω ((min t (S ω) : ℝ≥0) : ℝ) =
      -(ν / Real.sqrt κ * ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ), d.d10Rate u) -
        ν ^ 2 / 2 * a ω ((min t (S ω) : ℝ≥0) : ℝ) := by
    rw [cutInt_eq ω hτS]
    have e : (fun u => d10G κ B W' a φ rr ζ₀ ζ ν ω u) =
        fun u => -(ν / Real.sqrt κ * d.d10Rate u) - ν ^ 2 / 2 * d.A 1 u ^ 2 := rfl
    have h1' : IntervalIntegrable (fun u => -(ν / Real.sqrt κ * d.d10Rate u)) volume 0
        ((min t (S ω) : ℝ≥0) : ℝ) := (h1.const_mul _).neg
    have h2' : IntervalIntegrable (fun u => ν ^ 2 / 2 * d.A 1 u ^ 2) volume 0 ((min t (S ω) : ℝ≥0) : ℝ) :=
      h2.const_mul _
    rw [e, intervalIntegral.integral_sub h1' h2', intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [show (∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ), d.A 1 u ^ 2) = a ω ((min t (S ω) : ℝ≥0) : ℝ) from
      hown.integral_frzA_one_sq hτT]
  rw [addExp, logFieldExp, ← hW]
  show Real.exp (ν / Real.sqrt κ * d.A 0 ((min t (S ω) : ℝ≥0) : ℝ) + (-(ν / Real.sqrt κ * d.A 0 0) +
    cutInt S (d10G κ B W' a φ rr ζ₀ ζ ν) ω ((min t (S ω) : ℝ≥0) : ℝ))) = _
  rw [hA0, hA00, hI]
  congr 1; ring

/-- **(D10) under the tilted measure** (§A.1.3). For ordinary `SLE_κ` (`W = √κB`) with the other curve frozen and the
(D9) hypotheses up to the stopping time `S` (`FrzD10Hyp`), and `Q = (M̃_S/M̃_0) · P`: for every `ν ∈ ℝ`,
`exp((ν/√κ)(W'(a(t∧S)) − W'(0) − J_{t∧S}) − (ν²/2) a(t∧S))` is a `Q`-martingale of `𝓕`, where `W'(a(·)) = A_{j,0}` is
the mapped driver, `a` the image capacity clock (`a' = A²_{j,1}`) and `J_t = ∫₀ᵗ A²_{j,1}(−κ/(2E_{j,0}) +
Σ ρ_m/E_{j,m})`. That is, `A_{j,0} − J` is a continuous `Q`-martingale with quadratic variation `κ a`: (D10). -/
theorem martingale_d10 {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) :
    Martingale (fun t ω => Real.exp (ν / Real.sqrt κ * (W' ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) - W' ω 0 -
        ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ), (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u) -
        ν ^ 2 / 2 * a ω ((min t (S ω) : ℝ≥0) : ℝ))) 𝓕
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hDL := isDriverLogField_frozen hκ hBm hBc hS hH.toFrzMartHyp
  have hDL' := hH.isDriverLogField_d10 hκ hBm hBc hS ν
  have hSR : ∀ ω, S ω ≤ Tmax.toNNReal := fun ω => by
    rw [← Real.toNNReal_coe (r := S ω)]
    exact Real.toNNReal_le_toNNReal ((hH.le ω).trans (hH.leMax ω))
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hm := hDL.martingale_addExp (ψ := d10Psi κ B W' a φ rr ζ₀ ζ ν S) hDL' hB hBc (Real.sqrt_pos.2 hκ)
    (hH.toFrzMartHyp.cutRad_pos ω₀) hS hSR
  have e : addExp (Real.sqrt κ) B S (d10Psi κ B W' a φ rr ζ₀ ζ ν S) = fun t ω =>
      Real.exp (ν / Real.sqrt κ * (W' ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) - W' ω 0 -
        ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ), (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u) -
        ν ^ 2 / 2 * a ω ((min t (S ω) : ℝ≥0) : ℝ)) :=
    funext fun t => funext fun ω => hH.addExp_d10_eq ν t ω
  rw [e] at hm
  exact hm

end FrzD10Hyp

end InteractingSLE.ZhanGT4
