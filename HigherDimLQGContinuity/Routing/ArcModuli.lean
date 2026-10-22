import HigherDimLQGContinuity.Topology.Junction
import HigherDimLQGMetric.Events.Defs
import HigherDimLQGMetric.Metric.Internal

/-!
# Moduli of favorable arcs and their truncations

Packet Q2 (ruling N9). Sources: planning audit `planning/audits/NA2-section-4.md`, §1.3 and
Details (c) **R2** (arc moduli of internal geodesics) and **R3** (truncated arcs); blueprint Part B,
Lemma `b:lem-arcmod` ([C] p. 11, l. 555–565, 572–574).

* `arcModuli_of_internalGeodesic` (R2, the NA2 probe shape): a constant-speed `A`-minimizing arc in
  `K` (`G(γ s, γ t; A) = ℓ |s - t|`, `ℓ ∈ [ℓ₀, ℓ₁]`) has the moduli (4.1) with `α = 1/β_G`,
  `β = σ` and `A′ = max {(Hℓ₁)^{1/β_G}, 2^σ H/ℓ₀, δ₁^{-σ}}`, from an intrinsic lower Hölder bound
  and internal upper bounds in doubled balls.
* `arcModuli_of_twoSided` (blueprint (a)): the moduli of `m + s₁ η` from the two-sided bounds
  `H⁻¹|η s - η t|^{β₀} ≤ λ|s - t| ≤ H|η s - η t|^σ` of a favorable piece.
* `arcModuli_mono`, `arcModuli_reparam` (affine reparametrization of `γ|[a,b]`: constant
  `A/(b - a)`) and `arcModuli_truncate` (blueprint (b): the truncations `γ(t₀ + ς(1 - t₀))` and
  `γ(ς(1 - t₀))` have the moduli `(2A, α, β)` for `t₀ ≤ 1/2`).
* `arcModuli_le_norm_sub` (inverse modulus `|γ s - γ t| ≥ (|s - t|/A)^{1/β}`) and its consequences
  `arcModuli_endpoint_sep_zero`, `arcModuli_endpoint_sep_one` (blueprint (c)) and
  `arcModuli_tails_sep` (blueprint (d)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric (ContMetric diamIn)
open HigherDimLQGContinuity.Topology (ArcModuli)

namespace HigherDimLQGContinuity.Routing

variable {d : ℕ}

/-! ### Monotonicity and reparametrization -/

/-- The moduli (4.1) persist when the constant is increased. -/
lemma arcModuli_mono {γ : ℝ → Rd d} {A A' α β : ℝ} (hγ : ArcModuli γ A α β) (hAA' : A ≤ A') :
    ArcModuli γ A' α β := by
  intro s hs t ht
  obtain ⟨h1, h2⟩ := hγ s hs t ht
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hAA' (Real.rpow_nonneg (abs_nonneg _) _)),
    h2.trans (mul_le_mul_of_nonneg_right hAA' (Real.rpow_nonneg (norm_nonneg _) _))⟩

/-- **Affine reparametrization** of `γ|[a, b]` to `[0, 1]`: the moduli hold with the constant
`A / (b - a)`. -/
lemma arcModuli_reparam {γ : ℝ → Rd d} {A α β : ℝ} (hγ : ArcModuli γ A α β) (hA : 0 ≤ A)
    (hα : 0 < α) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ArcModuli (fun s => γ (a + (b - a) * s)) (A / (b - a)) α β := by
  intro s hs t ht
  have hba : 0 < b - a := sub_pos.2 hab
  have hba1 : b - a ≤ 1 := by linarith
  have hmem : ∀ x ∈ Icc (0 : ℝ) 1, a + (b - a) * x ∈ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  obtain ⟨h1, h2⟩ := hγ _ (hmem s hs) _ (hmem t ht)
  have hdiff : a + (b - a) * s - (a + (b - a) * t) = (b - a) * (s - t) := by ring
  rw [hdiff, abs_mul, abs_of_pos hba] at h1 h2
  have hAle : A ≤ A / (b - a) := (le_div_iff₀ hba).2 (by nlinarith)
  refine ⟨?_, ?_⟩
  · rw [Real.mul_rpow hba.le (abs_nonneg _)] at h1
    have hpow : (b - a) ^ α ≤ 1 := Real.rpow_le_one hba.le hba1 hα.le
    calc ‖γ (a + (b - a) * s) - γ (a + (b - a) * t)‖
        ≤ A * ((b - a) ^ α * |s - t| ^ α) := h1
      _ ≤ A * |s - t| ^ α := by
          apply mul_le_mul_of_nonneg_left _ hA
          calc (b - a) ^ α * |s - t| ^ α ≤ 1 * |s - t| ^ α :=
                mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (abs_nonneg _) _)
            _ = |s - t| ^ α := one_mul _
      _ ≤ A / (b - a) * |s - t| ^ α :=
          mul_le_mul_of_nonneg_right hAle (Real.rpow_nonneg (abs_nonneg _) _)
  · rw [div_mul_eq_mul_div, le_div_iff₀ hba, mul_comm]
    exact h2

/-- **Truncated arcs** (blueprint `b:lem-arcmod` (b); R2, R3): for `0 < t₀ ≤ 1/2` the
reparametrized truncations `γ₁(ς) = γ(t₀ + ς(1 - t₀))` and `γ₂(ς) = γ(ς(1 - t₀))` have the
moduli `(2A, α, β)`. -/
theorem arcModuli_truncate {γ : ℝ → Rd d} {A α β : ℝ} (hγ : ArcModuli γ A α β) (hA : 0 ≤ A)
    (hα : 0 < α) {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1 / 2) :
    ArcModuli (fun ς => γ (t₀ + ς * (1 - t₀))) (2 * A) α β ∧
      ArcModuli (fun ς => γ (ς * (1 - t₀))) (2 * A) α β := by
  have hle : A / (1 - t₀) ≤ 2 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  constructor
  · have h := arcModuli_mono (arcModuli_reparam hγ hA hα ht₀.le (by linarith) le_rfl) hle
    intro s hs t ht
    have := h s hs t ht
    simpa only [mul_comm s, mul_comm t] using this
  · have h := arcModuli_mono
      (arcModuli_reparam hγ hA hα le_rfl (by linarith) (by linarith : 1 - t₀ ≤ 1))
      (by simpa using hle)
    intro s hs t ht
    have := h s hs t ht
    simpa only [zero_add, sub_zero, mul_comm s, mul_comm t] using this

/-! ### The inverse modulus -/

/-- The inverse modulus as a lower bound: `(|s - t| / A)^{1/β} ≤ |γ s - γ t|`. -/
lemma arcModuli_le_norm_sub {γ : ℝ → Rd d} {A α β : ℝ} (hγ : ArcModuli γ A α β) (hA : 0 < A)
    (hβ : 0 < β) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (|s - t| / A) ^ β⁻¹ ≤ ‖γ s - γ t‖ := by
  have h2 := (hγ s hs t ht).2
  have h3 : |s - t| / A ≤ ‖γ s - γ t‖ ^ β := by
    rw [div_le_iff₀ hA]; linarith [mul_comm A (‖γ s - γ t‖ ^ β)]
  calc (|s - t| / A) ^ β⁻¹ ≤ (‖γ s - γ t‖ ^ β) ^ β⁻¹ :=
        Real.rpow_le_rpow (div_nonneg (abs_nonneg _) hA.le) h3 (inv_nonneg.2 hβ.le)
    _ = ‖γ s - γ t‖ := Real.rpow_rpow_inv (norm_nonneg _) hβ.ne'

/-- Blueprint `b:lem-arcmod` (c), first half: `|γ(0) - γ(t)| ≥ (t₀/A)^{1/β}` for `t ∈ [t₀, 1]`. -/
lemma arcModuli_endpoint_sep_zero {γ : ℝ → Rd d} {A α β : ℝ} (hγ : ArcModuli γ A α β)
    (hA : 0 < A) (hβ : 0 < β) {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t ∈ Icc t₀ 1) :
    (t₀ / A) ^ β⁻¹ ≤ ‖γ 0 - γ t‖ := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht₀.trans ht.1, ht.2⟩
  refine le_trans ?_ (arcModuli_le_norm_sub hγ hA hβ ⟨le_rfl, zero_le_one⟩ ht')
  apply Real.rpow_le_rpow (div_nonneg ht₀ hA.le) _ (inv_nonneg.2 hβ.le)
  apply div_le_div_of_nonneg_right _ hA.le
  rw [zero_sub, abs_neg, abs_of_nonneg ht'.1]
  exact ht.1

/-- Blueprint `b:lem-arcmod` (c), second half: `|γ(1) - γ(t)| ≥ (t₀/A)^{1/β}` for
`t ∈ [0, 1 - t₀]`. -/
lemma arcModuli_endpoint_sep_one {γ : ℝ → Rd d} {A α β : ℝ} (hγ : ArcModuli γ A α β)
    (hA : 0 < A) (hβ : 0 < β) {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t ∈ Icc 0 (1 - t₀)) :
    (t₀ / A) ^ β⁻¹ ≤ ‖γ 1 - γ t‖ := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  refine le_trans ?_ (arcModuli_le_norm_sub hγ hA hβ ⟨zero_le_one, le_rfl⟩ ht')
  apply Real.rpow_le_rpow (div_nonneg ht₀ hA.le) _ (inv_nonneg.2 hβ.le)
  apply div_le_div_of_nonneg_right _ hA.le
  rw [abs_of_nonneg (by linarith [ht.2])]
  linarith [ht.2]

/-- Blueprint `b:lem-arcmod` (d): `|γ(t) - γ(t')| ≥ ((1 - 4t₀)/A)^{1/β}` for `t ≤ 2t₀` and
`t' ≥ 1 - 2t₀` (`t₀ ≤ 1/4`). -/
lemma arcModuli_tails_sep {γ : ℝ → Rd d} {A α β : ℝ} (hγ : ArcModuli γ A α β) (hA : 0 < A)
    (hβ : 0 < β) {t₀ t t' : ℝ} (ht₀ : t₀ ≤ 1 / 4) (ht : t ∈ Icc 0 (2 * t₀))
    (ht' : t' ∈ Icc (1 - 2 * t₀) 1) :
    ((1 - 4 * t₀) / A) ^ β⁻¹ ≤ ‖γ t - γ t'‖ := by
  have h0 : 0 ≤ t₀ := by linarith [ht.1, ht.2]
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have ht'I : t' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.1], ht'.2⟩
  refine le_trans ?_ (arcModuli_le_norm_sub hγ hA hβ htI ht'I)
  apply Real.rpow_le_rpow (div_nonneg (by linarith) hA.le) _ (inv_nonneg.2 hβ.le)
  apply div_le_div_of_nonneg_right _ hA.le
  rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2, ht'.1])]
  linarith [ht.2, ht'.1]

/-! ### Moduli from two-sided bounds (blueprint (a)) -/

/-- **Moduli of a favorable piece** (blueprint `b:lem-arcmod` (a)): if
`H⁻¹|η s - η t|^{β₀} ≤ λ|s - t| ≤ H|η s - η t|^σ` on `[0, 1]` with `λ ∈ [λ₀, λ₁]`, then
`γ = m + s₁ η` (`0 < s₁ ≤ 1`) has the moduli (4.1) with `α = 1/β₀`, `β = σ` and
`A = max {(Hλ₁)^{1/β₀}, H s₁^{-σ}/λ₀, 1}`. -/
theorem arcModuli_of_twoSided {η : ℝ → Rd d} {H σ β₀ lam₀ lam lam₁ s₁ : ℝ} (hH : 1 ≤ H)
    (_hσ : 0 < σ) (_hσ1 : σ ≤ 1) (hβ₀ : 1 ≤ β₀) (hlam₀ : 0 < lam₀) (hlam : lam ∈ Icc lam₀ lam₁)
    (hη : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      H⁻¹ * ‖η s - η t‖ ^ β₀ ≤ lam * |s - t| ∧ lam * |s - t| ≤ H * ‖η s - η t‖ ^ σ)
    (hs₁ : 0 < s₁) (hs₁1 : s₁ ≤ 1) (m : Rd d) :
    ArcModuli (fun t => m + s₁ • η t)
      (max (max ((H * lam₁) ^ β₀⁻¹) (H * s₁ ^ (-σ) / lam₀)) 1) β₀⁻¹ σ := by
  intro s hs t ht
  obtain ⟨h1, h2⟩ := hη s hs t ht
  have hH0 : 0 < H := by linarith
  have hlam0 : 0 < lam := lt_of_lt_of_le hlam₀ hlam.1
  have hβ0 : 0 < β₀ := by linarith
  have hsub : m + s₁ • η s - (m + s₁ • η t) = s₁ • (η s - η t) := by
    rw [smul_sub]; abel
  have hnorm : ‖m + s₁ • η s - (m + s₁ • η t)‖ = s₁ * ‖η s - η t‖ := by
    rw [hsub, norm_smul, Real.norm_of_nonneg hs₁.le]
  set e := ‖η s - η t‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    -- `e^{β₀} ≤ H λ |s - t| ≤ H λ₁ |s - t|`
    have hpow : e ^ β₀ ≤ H * lam₁ * |s - t| := by
      have h1' : e ^ β₀ ≤ H * (lam * |s - t|) := by
        rw [inv_mul_le_iff₀ hH0] at h1; exact h1
      calc e ^ β₀ ≤ H * (lam * |s - t|) := h1'
        _ ≤ H * (lam₁ * |s - t|) := by
            apply mul_le_mul_of_nonneg_left _ hH0.le
            exact mul_le_mul_of_nonneg_right hlam.2 (abs_nonneg _)
        _ = H * lam₁ * |s - t| := by ring
    have hlam₁ : 0 ≤ lam₁ := (hlam0.trans_le hlam.2).le
    have he' : e ≤ (H * lam₁) ^ β₀⁻¹ * |s - t| ^ β₀⁻¹ := by
      calc e = (e ^ β₀) ^ β₀⁻¹ := (Real.rpow_rpow_inv he0 hβ0.ne').symm
        _ ≤ (H * lam₁ * |s - t|) ^ β₀⁻¹ :=
            Real.rpow_le_rpow (Real.rpow_nonneg he0 _) hpow (inv_nonneg.2 hβ0.le)
        _ = (H * lam₁) ^ β₀⁻¹ * |s - t| ^ β₀⁻¹ :=
            Real.mul_rpow (mul_nonneg hH0.le hlam₁) (abs_nonneg _)
    calc s₁ * e ≤ 1 * e := mul_le_mul_of_nonneg_right hs₁1 he0
      _ = e := one_mul e
      _ ≤ (H * lam₁) ^ β₀⁻¹ * |s - t| ^ β₀⁻¹ := he'
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _))
            (Real.rpow_nonneg (abs_nonneg _) _)
  · rw [hnorm]
    -- `|s - t| ≤ (H/λ) e^σ = (H/λ) s₁^{-σ} (s₁ e)^σ`
    have hst : |s - t| ≤ H / lam * e ^ σ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam0]; linarith
    have hes : e ^ σ = s₁ ^ (-σ) * (s₁ * e) ^ σ := by
      rw [Real.mul_rpow hs₁.le he0, ← mul_assoc, ← Real.rpow_add hs₁, neg_add_cancel,
        Real.rpow_zero, one_mul]
    rw [hes] at hst
    have hk : H / lam * s₁ ^ (-σ) ≤ H * s₁ ^ (-σ) / lam₀ := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) hlam₀ hlam.1
    calc |s - t| ≤ H / lam * (s₁ ^ (-σ) * (s₁ * e) ^ σ) := hst
      _ = H / lam * s₁ ^ (-σ) * (s₁ * e) ^ σ := by ring
      _ ≤ H * s₁ ^ (-σ) / lam₀ * (s₁ * e) ^ σ :=
          mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _))
            (Real.rpow_nonneg (by positivity) _)

/-! ### Moduli of internal geodesics (R2) -/

/-- **R2** (NA2 probe shape): the moduli (4.1) of a constant-speed `A`-minimizing arc in `K` from an
intrinsic lower Hölder bound (exponent `βG ≥ 1`) and internal upper bounds in doubled balls
(exponent `σ ≤ 1`): `α = 1/βG`, `β = σ`, `A′ = max {(Hℓ₁)^{1/βG}, 2^σ H/ℓ₀, δ₁^{-σ}}`. -/
theorem arcModuli_of_internalGeodesic {G : ContMetric d} {Asx Kset : Set (Rd d)}
    {H βG σ ℓ₀ ℓ₁ δ₁ : ℝ} (hH : 1 ≤ H) (hβG : 1 ≤ βG) (hσ : 0 < σ) (_hσ1 : σ ≤ 1) (hℓ₀ : 0 < ℓ₀)
    (hδ₁ : 0 < δ₁)
    (hlow : ∀ x ∈ Kset, ∀ y ∈ Kset, ENNReal.ofReal (H⁻¹ * ‖x - y‖ ^ βG) ≤ G.internal Asx x y)
    (hup : ∀ (z : Rd d) (r : ℝ), 0 < r → closedBall z (2 * r) ⊆ Asx →
      diamIn G (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H * r ^ σ))
    (hbuf : ∀ x ∈ Kset, closedBall x (4 * δ₁) ⊆ Asx)
    (γ : ℝ → Rd d) (ℓ : ℝ) (hℓ : ℓ ∈ Icc ℓ₀ ℓ₁) (hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Kset)
    (hgeod : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      G.internal Asx (γ s) (γ t) = ENNReal.ofReal (ℓ * |s - t|)) :
    ArcModuli γ (max (max ((H * ℓ₁) ^ βG⁻¹) (2 ^ σ * H / ℓ₀)) (δ₁ ^ (-σ))) βG⁻¹ σ := by
  intro s hs t ht
  have hH0 : 0 < H := by linarith
  have hβ0 : 0 < βG := by linarith
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hℓ₀ hℓ.1
  have hℓ₁ : 0 ≤ ℓ₁ := (hℓ0.trans_le hℓ.2).le
  set e := ‖γ s - γ t‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hst0 : 0 ≤ ℓ * |s - t| := mul_nonneg hℓ0.le (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · -- the Hölder modulus from the intrinsic lower bound
    have h1 := hlow _ (hγK s hs) _ (hγK t ht)
    rw [hgeod s hs t ht, ENNReal.ofReal_le_ofReal_iff hst0, inv_mul_le_iff₀ hH0] at h1
    have hpow : e ^ βG ≤ H * ℓ₁ * |s - t| := by
      calc e ^ βG ≤ H * (ℓ * |s - t|) := h1
        _ ≤ H * (ℓ₁ * |s - t|) := by
            apply mul_le_mul_of_nonneg_left _ hH0.le
            exact mul_le_mul_of_nonneg_right hℓ.2 (abs_nonneg _)
        _ = H * ℓ₁ * |s - t| := by ring
    have he' : e ≤ (H * ℓ₁) ^ βG⁻¹ * |s - t| ^ βG⁻¹ := by
      calc e = (e ^ βG) ^ βG⁻¹ := (Real.rpow_rpow_inv he0 hβ0.ne').symm
        _ ≤ (H * ℓ₁ * |s - t|) ^ βG⁻¹ :=
            Real.rpow_le_rpow (Real.rpow_nonneg he0 _) hpow (inv_nonneg.2 hβ0.le)
        _ = (H * ℓ₁) ^ βG⁻¹ * |s - t| ^ βG⁻¹ :=
            Real.mul_rpow (mul_nonneg hH0.le hℓ₁) (abs_nonneg _)
    exact he'.trans (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _))
      (Real.rpow_nonneg (abs_nonneg _) _))
  · -- the inverse modulus from the doubled-ball upper bound
    have hA'0 : 0 ≤ max (max ((H * ℓ₁) ^ βG⁻¹) (2 ^ σ * H / ℓ₀)) (δ₁ ^ (-σ)) :=
      le_max_of_le_right (Real.rpow_nonneg hδ₁.le _)
    rcases eq_or_lt_of_le he0 with he00 | hepos
    · -- `γ s = γ t`: the internal distance vanishes, so `s = t`
      have hγeq : γ s = γ t := by
        have : ‖γ s - γ t‖ = 0 := he00.symm
        exact sub_eq_zero.1 (norm_eq_zero.1 this)
      have hmem : γ s ∈ Asx :=
        hbuf _ (hγK s hs) (mem_closedBall_self (by positivity))
      have h0 : G.internal Asx (γ s) (γ t) = 0 := by
        rw [← hγeq]; exact G.internal_self hmem
      rw [hgeod s hs t ht, ENNReal.ofReal_eq_zero] at h0
      have : |s - t| = 0 := by
        have := mul_nonpos_iff.1 h0
        rcases this with ⟨_, h⟩ | ⟨h, _⟩
        · exact le_antisymm h (abs_nonneg _)
        · exact absurd h (not_le.2 hℓ0)
      rw [this]
      exact mul_nonneg hA'0 (Real.rpow_nonneg he0 _)
    rcases lt_or_ge e δ₁ with hed | hed
    · -- close points: the doubled ball `B(γ s, 4e) ⊆ A`
      have hball : closedBall (γ s) (2 * (2 * e)) ⊆ Asx :=
        (closedBall_subset_closedBall (by linarith)).trans (hbuf _ (hγK s hs))
      have hdiam := hup (γ s) (2 * e) (by positivity) hball
      have hs' : γ s ∈ ball (γ s) (2 * e) := mem_ball_self (by positivity)
      have ht' : γ t ∈ ball (γ s) (2 * e) := by
        rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith
      have hint : G.internal (ball (γ s) (2 * (2 * e))) (γ s) (γ t) ≤
          diamIn G (ball (γ s) (2 * (2 * e))) (ball (γ s) (2 * e)) := by
        unfold diamIn
        exact le_iSup₂_of_le (γ s) hs' (le_iSup₂_of_le (γ t) ht' le_rfl)
      have hanti := G.internal_anti (ball_subset_closedBall.trans hball) (γ s) (γ t)
      have hle := (hanti.trans hint).trans hdiam
      rw [hgeod s hs t ht, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
      -- `ℓ |s - t| ≤ H (2e)^σ = 2^σ H e^σ`
      rw [Real.mul_rpow (by norm_num) he0] at hle
      have hst : |s - t| ≤ 2 ^ σ * H / ℓ₀ * e ^ σ := by
        have h2 : ℓ₀ * |s - t| ≤ ℓ * |s - t| :=
          mul_le_mul_of_nonneg_right hℓ.1 (abs_nonneg _)
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ₀]
        nlinarith
      exact hst.trans (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _))
        (Real.rpow_nonneg he0 _))
    · -- far points: `|s - t| ≤ 1 ≤ (e/δ₁)^σ`
      have hst1 : |s - t| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      have h1 : 1 ≤ δ₁ ^ (-σ) * e ^ σ := by
        rw [Real.rpow_neg hδ₁.le, ← div_eq_inv_mul, ← Real.div_rpow he0 hδ₁.le]
        exact Real.one_le_rpow ((one_le_div hδ₁).2 hed) hσ.le
      exact hst1.trans (h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg he0 _)))

end HigherDimLQGContinuity.Routing

end
