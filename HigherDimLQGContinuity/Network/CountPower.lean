import HigherDimLQGContinuity.Network.Count

/-! # Uniform inverse-power count for the site balls -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

def siteMuCoeff (d : ℕ) : ℝ :=
  siteOmegaCoeff d ^ 2 / (2 * Real.sqrt d)

def siteNetCountCoeff {d : ℕ} (S : SiteData d) : ℝ :=
  (Nat.card S.Edge : ℝ) *
    (3 * (2 * (S.boxHalfSide / siteMuCoeff d + 3) + 1) ^ d +
      (2 + 2 * siteCN d) * (500 / siteOmegaCoeff d + 3))

theorem siteMuCoeff_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < siteMuCoeff d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hω : 0 < siteOmegaCoeff d := siteOmegaCoeff_pos d (by omega)
  unfold siteMuCoeff
  positivity

theorem siteConsts_mu_eq {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).μ =
      siteMuCoeff d * (siteConsts S Cnet v).ν ^ 8 := by
  let C := siteConsts S Cnet v
  change C.μ = siteMuCoeff d * C.ν ^ 8
  change (siteOmegaCoeff d * C.ν ^ 4) ^ 2 / (2 * Real.sqrt d) = _
  unfold siteMuCoeff
  ring

theorem siteConsts_omega_eq {d : ℕ} (S : SiteData d)
    (Cnet v : ℝ) :
    (siteConsts S Cnet v).ω =
      siteOmegaCoeff d * (siteConsts S Cnet v).ν ^ 4 := rfl

theorem siteConsts_N_le_invpow {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) :
    ((siteConsts S Cnet v).N : ℝ) ≤
      siteCN d * ((siteConsts S Cnet v).ν⁻¹) ^ d := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hr1 : C.r ≤ 1 := siteConsts_r_le_one S hd Cnet v hv
  have hνr := siteConsts_ν_le_r_div S hd Cnet v hv hr1
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hνle : C.ν ≤ C.r := by
    have hmul := (le_div_iff₀ (by positivity : 0 < (800 * d : ℝ))).mp hνr
    nlinarith
  have hi : C.r⁻¹ ≤ C.ν⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hν hνle
  have hipow : C.r⁻¹ ^ d ≤ C.ν⁻¹ ^ d :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hi d
  have hN := siteConsts_N_bound S hd Cnet v hv hr1
  have hCN : 0 ≤ siteCN d := (siteCN_pos d).le
  have hN' : (C.N : ℝ) ≤ siteCN d * C.r⁻¹ ^ d := by linarith
  exact hN'.trans (mul_le_mul_of_nonneg_left hipow hCN)

/-- The total number of balls has the exponent `8d` of the order lemma.
The coefficient depends only on fixed site data, not on the tolerance. -/
theorem labelBallSpecs_card_power {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    {Kl : ℕ}
    (ℓ : SiteLabel S (labelCellCutoff S (siteConsts S Cnet v).μ) Kl
      (siteConsts S Cnet v).N (siteConsts S Cnet v).μ
      (siteConsts S Cnet v).ν (siteConsts S Cnet v).r
      (Routing.gpC1 4)) :
    ((labelBallSpecs ℓ (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω).card : ℝ) ≤
      siteNetCountCoeff S *
        (siteConsts S Cnet v).ν ^ (-(8 * d : ℝ)) := by
  let C := siteConsts S Cnet v
  let x := C.ν⁻¹
  let cμ := siteMuCoeff d
  let cω := siteOmegaCoeff d
  let A := 2 * (S.boxHalfSide / cμ + 3) + 1
  let B := 500 / cω + 3
  let T := (max 1 ⌈500 / C.ω⌉₊ + 1 : ℕ)
  let Kc := labelCellCutoff S C.μ
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hx : 1 ≤ x := (one_le_inv₀ hν).2 hν1
  have hx0 : 0 ≤ x := by linarith
  have hcμ : 0 < cμ := siteMuCoeff_pos hd
  have hcω : 0 < cω := siteOmegaCoeff_pos d (by omega)
  have hμ : cμ * C.ν ^ 8 ≤ C.μ :=
    le_of_eq (siteConsts_mu_eq S Cnet v).symm
  have hωeq : C.ω = cω * C.ν ^ 4 := siteConsts_omega_eq S Cnet v
  have hω : 0 < C.ω := by rw [hωeq]; positivity
  have hL : 0 ≤ S.boxHalfSide := (S.boxHalfSide_pos hd).le
  have hK := q4_cutoff_le_invpow hL hcμ hν hν1 hμ
  change (Kc : ℝ) ≤ (S.boxHalfSide / cμ + 3) * x ^ 8 at hK
  have hx8 : 1 ≤ x ^ 8 := one_le_pow₀ hx
  have hbase : ((2 * Kc + 1 : ℕ) : ℝ) ≤ A * x ^ 8 := by
    have hcast : ((2 * Kc + 1 : ℕ) : ℝ) = 2 * (Kc : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    dsimp [A]
    nlinarith
  have hbase0 : (0 : ℝ) ≤ ((2 * Kc + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcell : (((2 * Kc + 1) ^ d : ℕ) : ℝ) ≤ A ^ d * x ^ (8 * d) := by
    have h := pow_le_pow_left₀ hbase0 hbase d
    push_cast at h
    rw [mul_pow, ← pow_mul] at h
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using h
  have hTcut := q4_cutoff_le_invpow
    (B := 500) (a := C.ω) (c := cω) (ν := C.ν) (k := 4)
    (by norm_num) hcω hν hν1 (by rw [hωeq])
  have hTnat : T ≤ ⌈500 / C.ω⌉₊ + 2 := by dsimp [T]; omega
  have hT : (T : ℝ) ≤ B * x ^ 4 := by
    have h : (T : ℝ) ≤ ((⌈500 / C.ω⌉₊ + 2 : ℕ) : ℝ) := by
      exact_mod_cast hTnat
    exact h.trans hTcut
  have hN := siteConsts_N_le_invpow S hd Cnet v hv
  change (C.N : ℝ) ≤ siteCN d * x ^ d at hN
  have hxD : 1 ≤ x ^ d := one_le_pow₀ hx
  have hCN : 0 ≤ siteCN d := (siteCN_pos d).le
  have hNd : (2 : ℝ) + 2 * C.N ≤ (2 + 2 * siteCN d) * x ^ d := by
    nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hprod : ((2 + 2 * C.N : ℕ) : ℝ) * T ≤
      (2 + 2 * siteCN d) * B * x ^ (d + 4) := by
    have hNpos : (0 : ℝ) ≤ 2 + 2 * C.N := by positivity
    have hTpos : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have hmul := mul_le_mul hNd hT hTpos
      (mul_nonneg (by linarith) (pow_nonneg hx0 d))
    push_cast at hmul ⊢
    calc
      (2 + 2 * (C.N : ℝ)) * (T : ℝ) ≤
          ((2 + 2 * siteCN d) * x ^ d) * (B * x ^ 4) := hmul
      _ = (2 + 2 * siteCN d) * B * x ^ (d + 4) := by rw [pow_add]; ring
  have hpow : x ^ (d + 4) ≤ x ^ (8 * d) :=
    pow_le_pow_right₀ hx (by omega)
  have hcoef : 0 ≤ (2 + 2 * siteCN d) * B := by positivity
  have hterm : ((2 + 2 * C.N : ℕ) : ℝ) * T ≤
      (2 + 2 * siteCN d) * B * x ^ (8 * d) :=
    hprod.trans (mul_le_mul_of_nonneg_left hpow hcoef)
  have hcard := labelBallSpecs_card_le (g := C.g) S hd hω ℓ
  have hcardR : ((labelBallSpecs ℓ C.g C.ω).card : ℝ) ≤
      (Nat.card S.Edge : ℝ) *
        (3 * (((2 * Kc + 1) ^ d : ℕ) : ℝ) +
          ((2 + 2 * C.N : ℕ) : ℝ) * T) := by
    exact_mod_cast hcard
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hE0 : (0 : ℝ) ≤ Nat.card S.Edge := Nat.cast_nonneg _
  have hsum : 3 * (((2 * Kc + 1) ^ d : ℕ) : ℝ) +
      ((2 + 2 * C.N : ℕ) : ℝ) * T ≤
      (3 * A ^ d + (2 + 2 * siteCN d) * B) * x ^ (8 * d) := by
    nlinarith [mul_le_mul_of_nonneg_left hcell (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    ((labelBallSpecs ℓ C.g C.ω).card : ℝ) ≤
        (Nat.card S.Edge : ℝ) *
          (3 * (((2 * Kc + 1) ^ d : ℕ) : ℝ) +
            ((2 + 2 * C.N : ℕ) : ℝ) * T) := hcardR
    _ ≤ siteNetCountCoeff S * x ^ (8 * d) := by
      dsimp [siteNetCountCoeff, A, B] at *
      nlinarith [mul_le_mul_of_nonneg_left hsum hE0]
    _ = siteNetCountCoeff S * C.ν ^ (-(8 * d : ℝ)) := by
      rw [show x ^ (8 * d) = C.ν ^ (-(8 * d : ℝ)) by
        dsimp [x]
        have hexp : (8 * d : ℝ) = ((8 * d : ℕ) : ℝ) := by push_cast; ring
        rw [Real.rpow_neg hν.le, hexp, Real.rpow_natCast, ← inv_pow]]

/-- The same coefficient controls the sum of `s`-powers of the ball radii. -/
theorem labelBallSpecs_radius_sum_power {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    {Kl : ℕ}
    (ℓ : SiteLabel S (labelCellCutoff S (siteConsts S Cnet v).μ) Kl
      (siteConsts S Cnet v).N (siteConsts S Cnet v).μ
      (siteConsts S Cnet v).ν (siteConsts S Cnet v).r
      (Routing.gpC1 4)) :
    let C := siteConsts S Cnet v
    ∑ p ∈ labelBallSpecs ℓ C.g C.ω, p.2 ^ S.s ≤
      siteNetCountCoeff S * C.ν ^ (-(8 * d : ℝ)) := by
  let C := siteConsts S Cnet v
  let F := labelBallSpecs ℓ C.g C.ω
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hν1 : C.ν ≤ 1 := siteConsts_ν_le_one S hd Cnet v
  have hr1 := siteConsts_r_le_one S hd Cnet v hv
  have hgr := (siteConsts_lead_short S hd Cnet v hv hr1).2
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    positivity
  have hg1 : C.g ≤ 1 := by
    have hr := siteConsts_r_pos S hd Cnet v hv
    linarith
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega)) (pow_pos hν _)
  have hω1 : C.ω ≤ 1 :=
    (siteConsts_omega_le_nu S hd Cnet v).trans hν1
  have hsum : ∑ p ∈ F, p.2 ^ S.s ≤ (F.card : ℝ) := by
    calc
      ∑ p ∈ F, p.2 ^ S.s ≤ ∑ _p ∈ F, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p.2 = C.g ∨ p.2 = C.ω := by
          simp only [F, labelBallSpecs, Finset.mem_biUnion] at hp
          obtain ⟨e, _, hpe⟩ := hp
          exact edgeBallSpecs_radius ℓ e hpe
        rcases hp' with h | h
        · rw [h]; exact Real.rpow_le_one hg.le hg1 S.s_pos.le
        · rw [h]; exact Real.rpow_le_one hω.le hω1 S.s_pos.le
      _ = F.card := by simp
  exact hsum.trans (labelBallSpecs_card_power S hd Cnet v hv ℓ)

end HigherDimLQGContinuity
