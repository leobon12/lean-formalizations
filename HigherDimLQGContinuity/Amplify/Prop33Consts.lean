import HigherDimLQGContinuity.Amplify.Prop33Num

/-!
# The constants of Proposition 3.3 (packet P7)

Blueprint `a:prop33`, "Constants, in this order" (NA1 R9), with the explicit numerics of this packet. From the raw
constants — Lemma 2.1 at the global pin (`p, σ, β, C₁, A`, `p_esc, C_esc`), Lemma 3.2 (`C₀ = C_b`, `C₃₂, c₃₂`),
Lemma 2.2 (`C_cap, C_cp, c_cp`), the covering (`C_c`), the bound `C_b` on `b` and the references `m ≤ M` — we choose

* `c₀ = 1/(8 C₃₂)`, `L = max(5, 8β/σ, 8β/c₀)`, `q_* = 1 - m/(2M)`, `h = min(σ, c₀)/32`,
  `w = min(p h/(2(A + 1)), 1/(4C₃₂), 1/d)`, `h' = A w/p + h`, `κ_H = (|log(C₁ 3^A)| + A)/p`,
* `M₀ = log L / log(1/q_*)`, `K_N = (log(4C₀) + 1)/log(1/q_*) + 1`, `c_a = 1/(4 L (4C₀)^{M₀})`, `K_Γ = C_b + C₀ + 2`,
  `C'_cap = √(2d) + C_cap`, `C'_esc = max(C_esc, 1)`, `c' = min(p_esc w, p h, c₀, 1, c_cp)`,
* `M₃ = d + M₀ + 1`, `C₃ = K_n + K_A/c_a + K_F + 1`, `c₃ = min(c' c_a, c₃₂, 1/(16 C_b C'_cap), 1/(2 C'_cap))`,

and record in the structure `P7Consts33` exactly the inequalities the proof uses (`p7_consts33_nonempty`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- The constants of Proposition 3.3 with the inequalities used by the proof. -/
structure P7Consts33 (d : ℕ) (p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M : ℝ) where
  c₀ : ℝ
  L : ℝ
  qs : ℝ
  h : ℝ
  w : ℝ
  h' : ℝ
  κH : ℝ
  M0 : ℝ
  KN : ℝ
  ca : ℝ
  KΓ : ℝ
  Ccap' : ℝ
  Cesc' : ℝ
  cp : ℝ
  M₃ : ℝ
  C₃ : ℝ
  c₃ : ℝ
  hc₀ : 0 < c₀
  hc₀C : 8 * C32 * c₀ = 1
  hL5 : 5 ≤ L
  hLσ : 8 * β ≤ σ * L
  hLc : 8 * β ≤ c₀ * L
  hqs : qs = 1 - m / (2 * M)
  hqs0 : 0 < qs
  hqs1 : qs < 1
  hh0 : 0 < h
  hhσ : h ≤ σ / 32
  hhc : h ≤ c₀ / 32
  hw0 : 0 < w
  hwC : 4 * C32 * w ≤ 1
  hwd : (d : ℝ) * w ≤ 1
  hh'0 : 0 ≤ h'
  hh' : h' ≤ 3 / 2 * h
  hph' : p * h' = A * w + p * h
  hκH0 : 0 ≤ κH
  hpκH : p * κH = |Real.log (C₁ * 3 ^ A)| + A
  hM0 : M0 = Real.log L / Real.log qs⁻¹
  hM00 : 0 ≤ M0
  hKN : KN = (Real.log (4 * C0) + 1) / Real.log qs⁻¹ + 1
  hKN0 : 0 < KN
  hca : ca = 1 / (4 * L * (4 * C0) ^ M0)
  hca0 : 0 < ca
  hKΓ : KΓ = Cb + C0 + 2
  hKΓ0 : 0 < KΓ
  hCcap' : Ccap' = Real.sqrt (2 * d) + Ccap
  hCcap'0 : 0 < Ccap'
  hCesc' : Cesc ≤ Cesc'
  hCesc'0 : 0 < Cesc'
  hA1 : 3 / w ≤ ca * C₃
  hA2 : 2 ≤ ca * C₃
  hA3 : 2 / σ * (|Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)| + 2 * κH + 3) ≤ ca * C₃
  hA4 : 2 / σ * (|Real.log (16 * KN * KΓ)| + κH + 2) ≤ ca * C₃
  hn1 : 8 * C32 ≤ C₃
  hn2 : 8 / c₀ ≤ C₃
  hn3 : 3 ≤ C₃
  hn4 : 8 / (7 * c₀) * (|Real.log (16 * 4 ^ β * KN)| + κH + 2) ≤ C₃
  hn5 : 2 / c₀ ≤ C₃
  hcp0 : 0 < cp
  hcp1 : cp ≤ pesc * w
  hcp2 : cp ≤ p * h
  hcp3 : cp ≤ c₀
  hcp4 : cp ≤ 1
  hcp5 : cp ≤ ccp
  hKF : Cesc' + 1 + 1 + Ccp + KN * (Cc * 4 ^ d) ≤ C₃
  hM₃d : (d : ℝ) ≤ M₃
  hM₃0' : M0 ≤ M₃
  hM₃1 : 1 ≤ M₃
  hC₃0 : 0 < C₃
  hc₃0 : 0 < c₃
  hc₃1 : c₃ ≤ cp * ca
  hc₃2 : c₃ ≤ c32
  hc₃3 : 16 * Cb * Ccap' * c₃ ≤ 1
  hc₃4 : 2 * Ccap' * c₃ ≤ 1

/-- The constants of Proposition 3.3 exist. -/
theorem p7_consts33_nonempty (d : ℕ) (hd : 2 ≤ d) {p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M : ℝ}
    (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A) (hpesc : 0 < pesc)
    (hC0 : 1 ≤ C0) (hC32 : 0 < C32) (hc32 : 0 < c32) (hCcap : 0 < Ccap) (hCcp : 0 < Ccp) (hccp : 0 < ccp)
    (hCc : 0 < Cc) (hCb : 0 < Cb) (hm : 0 < m) (hmM : m ≤ M) :
    Nonempty (P7Consts33 d p σ β C₁ A pesc Cesc C0 C32 c32 Ccap Ccp ccp Cc Cb m M) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  -- the first constants
  set c₀ : ℝ := 1 / (8 * C32) with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hc₀C : 8 * C32 * c₀ = 1 := by rw [hc₀def]; field_simp
  set L : ℝ := max 5 (max (8 * β / σ) (8 * β / c₀)) with hLdef
  have hL5 : 5 ≤ L := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have hLσ : 8 * β ≤ σ * L := by
    have h1 : 8 * β / σ ≤ L := le_trans (le_max_left _ _) (le_max_right _ _)
    rw [div_le_iff₀ hσ] at h1; linarith
  have hLc : 8 * β ≤ c₀ * L := by
    have h1 : 8 * β / c₀ ≤ L := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [div_le_iff₀ hc₀] at h1; linarith
  set qs : ℝ := 1 - m / (2 * M) with hqsdef
  have hϑ0 : 0 < m / (2 * M) := by positivity
  have hϑ1 : m / (2 * M) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hqs0 : 0 < qs := by linarith
  have hqs1 : qs < 1 := by linarith
  set h : ℝ := min σ c₀ / 32 with hhdef
  have hh0 : 0 < h := by positivity
  have hhσ : h ≤ σ / 32 := by
    have := min_le_left σ c₀; rw [hhdef]; linarith
  have hhc : h ≤ c₀ / 32 := by
    have := min_le_right σ c₀; rw [hhdef]; linarith
  set w : ℝ := min (p * h / (2 * (A + 1))) (min (1 / (4 * C32)) (1 / d)) with hwdef
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ p * h / (2 * (A + 1)) := min_le_left _ _
  have hw2 : w ≤ 1 / (4 * C32) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hw3 : w ≤ 1 / d := le_trans (min_le_right _ _) (min_le_right _ _)
  have hwC : 4 * C32 * w ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hw2; linarith
  have hwd : (d : ℝ) * w ≤ 1 := by
    rw [le_div_iff₀ hd0] at hw3; linarith
  set h' : ℝ := A * w / p + h with hh'def
  have hAw : A * w / p ≤ h / 2 := by
    rw [div_le_iff₀ hp]
    have h1 : A * w ≤ A * (p * h / (2 * (A + 1))) := mul_le_mul_of_nonneg_left hw1 hA
    have h2 : A * (p * h / (2 * (A + 1))) ≤ h / 2 * p := by
      have h3 : A * (p * h / (2 * (A + 1))) = (A / (A + 1)) * (p * h / 2) := by
        field_simp
      have h4 : A / (A + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have h5 : 0 ≤ p * h / 2 := by positivity
      have h6 : (A / (A + 1)) * (p * h / 2) ≤ 1 * (p * h / 2) := mul_le_mul_of_nonneg_right h4 h5
      linarith
    linarith
  have hh'0 : 0 ≤ h' := by positivity
  have hh' : h' ≤ 3 / 2 * h := by rw [hh'def]; linarith
  have hph' : p * h' = A * w + p * h := by rw [hh'def]; field_simp
  set κH : ℝ := (|Real.log (C₁ * 3 ^ A)| + A) / p with hκHdef
  have hκH0 : 0 ≤ κH := by positivity
  have hpκH : p * κH = |Real.log (C₁ * 3 ^ A)| + A := by rw [hκHdef]; field_simp
  have hℓq : 0 < Real.log qs⁻¹ := p7_log_inv_pos hqs0 hqs1
  set M0 : ℝ := Real.log L / Real.log qs⁻¹ with hM0def
  have hM00 : 0 ≤ M0 := div_nonneg (Real.log_nonneg (by linarith)) hℓq.le
  have hlog4C0 : 0 ≤ Real.log (4 * C0) := Real.log_nonneg (by linarith)
  set KN : ℝ := (Real.log (4 * C0) + 1) / Real.log qs⁻¹ + 1 with hKNdef
  have hKN0 : 0 < KN := by positivity
  set ca : ℝ := 1 / (4 * L * (4 * C0) ^ M0) with hcadef
  have hca0 : 0 < ca := by
    have : 0 < (4 * C0) ^ M0 := Real.rpow_pos_of_pos (by linarith) _
    positivity
  set KΓ : ℝ := Cb + C0 + 2 with hKΓdef
  have hKΓ0 : 0 < KΓ := by positivity
  set Ccap' : ℝ := Real.sqrt (2 * d) + Ccap with hCcap'def
  have hCcap'0 : 0 < Ccap' := by positivity
  set Cesc' : ℝ := max Cesc 1 with hCesc'def
  have hCesc' : Cesc ≤ Cesc' := le_max_left _ _
  have hCesc'0 : 0 < Cesc' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set KA : ℝ := 3 / w + 2 + 2 / σ * (|Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)| + 2 * κH + 3) +
    2 / σ * (|Real.log (16 * KN * KΓ)| + κH + 2) with hKAdef
  have hKA1 : 0 ≤ 2 / σ * (|Real.log (128 * 4 ^ β * KN ^ 2 * KΓ)| + 2 * κH + 3) := by positivity
  have hKA2 : 0 ≤ 2 / σ * (|Real.log (16 * KN * KΓ)| + κH + 2) := by positivity
  have hKAw : 0 ≤ 3 / w := by positivity
  set Kn : ℝ := 8 * C32 + 8 / c₀ + 3 + 8 / (7 * c₀) * (|Real.log (16 * 4 ^ β * KN)| + κH + 2) +
    2 / c₀ with hKndef
  have hKn1 : 0 ≤ 8 / (7 * c₀) * (|Real.log (16 * 4 ^ β * KN)| + κH + 2) := by positivity
  have hKn2 : 0 ≤ 8 / c₀ := by positivity
  have hKn3 : 0 ≤ 2 / c₀ := by positivity
  have hKn4 : 0 ≤ 8 * C32 := by positivity
  set cp : ℝ := min (pesc * w) (min (p * h) (min c₀ (min 1 ccp))) with hcpdef
  have hcp0 : 0 < cp := by positivity
  set KF : ℝ := Cesc' + 1 + 1 + Ccp + KN * (Cc * 4 ^ d) with hKFdef
  have hKF0 : 0 ≤ KF := by positivity
  set M₃ : ℝ := d + M0 + 1 with hM₃def
  set C₃ : ℝ := Kn + KA / ca + KF + 1 with hC₃def
  have hKAca : 0 ≤ KA / ca := by positivity
  have hKn0 : 0 ≤ Kn := by positivity
  have hKA0 : 0 ≤ KA := by positivity
  have hKAle : KA ≤ ca * C₃ := by
    have h1 : KA / ca ≤ C₃ := by rw [hC₃def]; linarith
    rw [div_le_iff₀ hca0] at h1; linarith
  have hKnle : Kn ≤ C₃ := by rw [hC₃def]; linarith
  set c₃ : ℝ := min (cp * ca) (min c32 (min (1 / (16 * Cb * Ccap')) (1 / (2 * Ccap')))) with hc₃def
  have hc₃0 : 0 < c₃ := by positivity
  have hc₃3 : c₃ ≤ 1 / (16 * Cb * Ccap') :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc₃4 : c₃ ≤ 1 / (2 * Ccap') :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨{
    c₀ := c₀, L := L, qs := qs, h := h, w := w, h' := h', κH := κH, M0 := M0, KN := KN, ca := ca,
    KΓ := KΓ, Ccap' := Ccap', Cesc' := Cesc', cp := cp, M₃ := M₃, C₃ := C₃, c₃ := c₃,
    hc₀ := hc₀, hc₀C := hc₀C, hL5 := hL5, hLσ := hLσ, hLc := hLc, hqs := rfl, hqs0 := hqs0,
    hqs1 := hqs1, hh0 := hh0, hhσ := hhσ, hhc := hhc, hw0 := hw0, hwC := hwC, hwd := hwd,
    hh'0 := hh'0, hh' := hh', hph' := hph', hκH0 := hκH0, hpκH := hpκH, hM0 := rfl, hM00 := hM00,
    hKN := rfl, hKN0 := hKN0, hca := rfl, hca0 := hca0, hKΓ := rfl, hKΓ0 := hKΓ0, hCcap' := rfl,
    hCcap'0 := hCcap'0, hCesc' := hCesc', hCesc'0 := hCesc'0,
    hA1 := le_trans (by rw [hKAdef]; linarith) hKAle,
    hA2 := le_trans (by rw [hKAdef]; linarith) hKAle,
    hA3 := le_trans (by rw [hKAdef]; linarith) hKAle,
    hA4 := le_trans (by rw [hKAdef]; linarith) hKAle,
    hn1 := le_trans (by rw [hKndef]; linarith) hKnle,
    hn2 := le_trans (by rw [hKndef]; linarith) hKnle,
    hn3 := le_trans (by rw [hKndef]; linarith) hKnle,
    hn4 := le_trans (by rw [hKndef]; linarith) hKnle,
    hn5 := le_trans (by rw [hKndef]; linarith) hKnle,
    hcp0 := hcp0, hcp1 := min_le_left _ _,
    hcp2 := le_trans (min_le_right _ _) (min_le_left _ _),
    hcp3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
    hcp4 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))),
    hcp5 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))),
    hKF := by rw [hC₃def]; linarith,
    hM₃d := by rw [hM₃def]; linarith,
    hM₃0' := by
      have : (0 : ℝ) ≤ d := hd0.le
      rw [hM₃def]; linarith,
    hM₃1 := by
      have : (0 : ℝ) ≤ d := hd0.le
      rw [hM₃def]; linarith,
    hC₃0 := by rw [hC₃def]; linarith,
    hc₃0 := hc₃0, hc₃1 := min_le_left _ _, hc₃2 := le_trans (min_le_right _ _) (min_le_left _ _),
    hc₃3 := by
      rw [le_div_iff₀ (by positivity)] at hc₃3; linarith,
    hc₃4 := by
      rw [le_div_iff₀ (by positivity)] at hc₃4; linarith }⟩

end HigherDimLQGContinuity
