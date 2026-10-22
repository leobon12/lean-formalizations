import HigherDimLQGContinuity.MomentsW1.Normalize

/-! Transfer of normalized per-scale costs to a box diameter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLQGMetric.DGZ

/-- Constant in the finite normalized chain sum. -/
def wnScaleSumConst (d : ℕ) (a b : ℝ) : ℝ :=
  2^(a-b) * ((2*d).factorial : ℝ) / (Real.log 2 * (a-b))^(2*d+1) +
    2^(a-b) * ((2 : ℕ).factorial : ℝ) / (Real.log 2 * (a-b))^3

theorem wnScaleSumConst_nonneg (d : ℕ) {a b : ℝ} (hab : b < a) :
    0 ≤ wnScaleSumConst d a b := by
  unfold wnScaleSumConst
  positivity

theorem wnScale_sum {d j n : ℕ} {a b G e : ℝ} {c : ℕ → ℝ}
    (hb : 0 < b) (hab : b < a) (hG : 0 ≤ G) (hjn : j ≤ n)
    (hc : ∀ k, j ≤ k → k < n → c k ≤ G * (2 : ℝ)^(-(a*k)))
    (he : (n : ℝ)^2 * (2 : ℝ)⁻¹ ^ n * e ≤
      G * ((n : ℝ)^2 * (2 : ℝ)^(-(a*n)))) :
    wnLocalChain_sum d j n c e ≤
      G * wnScaleSumConst d a b * (2 : ℝ)^(-(b*j)) := by
  simpa only [wnScaleSumConst] using wnLocalChain_sum_bound hb hab hG hjn hc he

def wnScaleStartConst (b σ : ℝ) : ℝ :=
  (2*((2 : ℝ)^110+200000)+2) *
    (2^(b-σ) * ((2 : ℕ).factorial : ℝ) /
      (Real.log 2 * (b-σ))^3)

theorem wnScaleStartConst_nonneg {b σ : ℝ} (hσb : σ < b) :
    0 ≤ wnScaleStartConst b σ := by
  unfold wnScaleStartConst
  positivity

theorem wnScale_chain_start {d n : ℕ} {ρ σ a b D G e S : ℝ} {c : ℕ → ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : 0 < σ) (hσb : σ < b)
    (hba : b < a) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hn : wnStartScale ρ hρ ≤ n)
    (hS : S ≤ (2*ρ*(2 : ℝ)^wnStartScale ρ hρ+2)*D*
      wnLocalChain_sum d (wnStartScale ρ hρ) n c e)
    (hc : ∀ k, wnStartScale ρ hρ ≤ k → k < n →
      c k ≤ G * (2 : ℝ)^(-(a*k)))
    (he : (n : ℝ)^2 * (2 : ℝ)⁻¹ ^ n * e ≤
      G * ((n : ℝ)^2 * (2 : ℝ)^(-(a*n)))) :
    S ≤ D * G * wnScaleSumConst d a b * wnScaleStartConst b σ * ρ^σ := by
  let j := wnStartScale ρ hρ
  let F : ℝ := 2*ρ*(2 : ℝ)^j+2
  let K : ℝ := wnScaleSumConst d a b
  let L : ℝ := wnScaleStartConst b σ
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hK : 0 ≤ K := wnScaleSumConst_nonneg d hba
  have hL : 0 ≤ L := wnScaleStartConst_nonneg hσb
  have hsum : wnLocalChain_sum d j n c e ≤ G*K*(2 : ℝ)^(-(b*j)) :=
    wnScale_sum (hσ.trans hσb) hba hG hn hc he
  have hfac : F*(2 : ℝ)^(-(b*j)) ≤ L*ρ^σ := by
    simpa only [F, L, j, wnScaleStartConst] using
      wnStartScale_chain_factor hρ hρ1 hσ hσb
  have hbound : F*D*wnLocalChain_sum d j n c e ≤
      F*D*(G*K*(2 : ℝ)^(-(b*j))) :=
    mul_le_mul_of_nonneg_left hsum (mul_nonneg hF hD)
  have hbound' : F*D*(G*K*(2 : ℝ)^(-(b*j))) ≤ D*G*K*(L*ρ^σ) := by
    have hgk : 0 ≤ D*G*K := by positivity
    nlinarith [mul_nonneg hgk (sub_nonneg.mpr hfac)]
  change S ≤ D*G*K*L*ρ^σ
  calc
    S ≤ F*D*wnLocalChain_sum d j n c e := hS
    _ ≤ F*D*(G*K*(2 : ℝ)^(-(b*j))) := hbound
    _ ≤ D*G*K*(L*ρ^σ) := hbound'
    _ = D*G*K*L*ρ^σ := by ring

theorem wnScale_chain_bad {d n M : ℕ} {ρ σ a b D G e S : ℝ} {c : ℕ → ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσb : σ < b) (hba : b < a) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hM : wnStartScale ρ hρ ≤ M) (hn : M ≤ n)
    (hS : S ≤ (2*ρ*(2 : ℝ)^M+2)*D*wnLocalChain_sum d M n c e)
    (hc : ∀ k, M ≤ k → k < n → c k ≤ G * (2 : ℝ)^(-(a*k)))
    (he : (n : ℝ)^2 * (2 : ℝ)⁻¹ ^ n * e ≤
      G * ((n : ℝ)^2 * (2 : ℝ)^(-(a*n)))) :
    S ≤ 4*D*G*wnScaleSumConst d a b*((2 : ℝ)^M)^4*ρ^σ := by
  let F : ℝ := 2*ρ*(2 : ℝ)^M+2
  let K : ℝ := wnScaleSumConst d a b
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hK : 0 ≤ K := wnScaleSumConst_nonneg d hba
  have hsum : wnLocalChain_sum d M n c e ≤ G*K*(2 : ℝ)^(-(b*(M:ℝ))) :=
    wnScale_sum (hσ.trans hσb) hba hG hn hc he
  have hfac : F*(2 : ℝ)^(-(b*(M:ℝ))) ≤ 4*((2 : ℝ)^M)^4*ρ^σ := by
    simpa only [F] using wnBadScale_chain_factor hρ hρ1 hσ hσ1 (hσ.trans hσb) hM
  have hbound : F*D*wnLocalChain_sum d M n c e ≤
      F*D*(G*K*(2 : ℝ)^(-(b*(M:ℝ)))) :=
    mul_le_mul_of_nonneg_left hsum (mul_nonneg hF hD)
  have hbound' : F*D*(G*K*(2 : ℝ)^(-(b*(M:ℝ)))) ≤
      D*G*K*(4*((2 : ℝ)^M)^4*ρ^σ) := by
    have hgk : 0 ≤ D*G*K := by positivity
    nlinarith [mul_nonneg hgk (sub_nonneg.mpr hfac)]
  change S ≤ 4*D*G*K*((2 : ℝ)^M)^4*ρ^σ
  calc
    S ≤ F*D*wnLocalChain_sum d M n c e := hS
    _ ≤ F*D*(G*K*(2 : ℝ)^(-(b*(M:ℝ)))) := hbound
    _ ≤ D*G*K*(4*((2 : ℝ)^M)^4*ρ^σ) := hbound'
    _ = 4*D*G*K*((2 : ℝ)^M)^4*ρ^σ := by ring

def wnScaleTerminalConst (a σ : ℝ) : ℝ :=
  ((2 : ℝ)^110+200000) *
    (2^(a-σ) * ((2 : ℕ).factorial : ℝ) /
      (Real.log 2 * (a-σ))^3)

theorem wnScaleTerminalConst_nonneg {a σ : ℝ} (hσa : σ < a) :
    0 ≤ wnScaleTerminalConst a σ := by
  unfold wnScaleTerminalConst
  positivity

theorem wnScale_terminal_start {d n : ℕ} {ρ σ a G e S : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : 0 < σ)
    (hσa : σ < a) (ha1 : a ≤ 1) (hG : 0 ≤ G)
    (hn : n < wnStartScale ρ hρ)
    (hS : S ≤ 2*Real.sqrt (d:ℝ)*ρ*e)
    (he : e ≤ G*(2 : ℝ)^((1-a)*(n:ℝ))) :
    S ≤ 2*Real.sqrt (d:ℝ)*G*wnScaleTerminalConst a σ*ρ^σ := by
  let L : ℝ := wnScaleTerminalConst a σ
  have hfac : ρ*(2 : ℝ)^((1-a)*(n:ℝ)) ≤ L*ρ^σ := by
    simpa only [L, wnScaleTerminalConst] using
      wnStartScale_terminal_factor hρ hρ1 hσ hσa ha1 hn
  have hcoef : 0 ≤ 2*Real.sqrt (d:ℝ)*ρ := by positivity
  have hbound : 2*Real.sqrt (d:ℝ)*ρ*e ≤
      2*Real.sqrt (d:ℝ)*ρ*(G*(2 : ℝ)^((1-a)*(n:ℝ))) :=
    mul_le_mul_of_nonneg_left he hcoef
  have hg : 0 ≤ 2*Real.sqrt (d:ℝ)*G := by positivity
  change S ≤ 2*Real.sqrt (d:ℝ)*G*L*ρ^σ
  calc
    S ≤ 2*Real.sqrt (d:ℝ)*ρ*e := hS
    _ ≤ 2*Real.sqrt (d:ℝ)*ρ*(G*(2 : ℝ)^((1-a)*(n:ℝ))) := hbound
    _ = (2*Real.sqrt (d:ℝ)*G)*(ρ*(2 : ℝ)^((1-a)*(n:ℝ))) := by ring
    _ ≤ (2*Real.sqrt (d:ℝ)*G)*(L*ρ^σ) := mul_le_mul_of_nonneg_left hfac hg
    _ = 2*Real.sqrt (d:ℝ)*G*L*ρ^σ := by ring

theorem wnScale_terminal_bad {d n M : ℕ} {ρ σ a G e S : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (ha : 0 ≤ a) (hG : 0 ≤ G)
    (hM : wnStartScale ρ hρ ≤ M) (hn : n < M)
    (hS : S ≤ 2*Real.sqrt (d:ℝ)*ρ*e)
    (he : e ≤ G*(2 : ℝ)^((1-a)*(n:ℝ))) :
    S ≤ 2*Real.sqrt (d:ℝ)*G*((2 : ℝ)^M)^4*ρ^σ := by
  have hfac : ρ*(2 : ℝ)^((1-a)*(n:ℝ)) ≤ ((2 : ℝ)^M)^4*ρ^σ :=
    wnBadScale_terminal_factor hρ hρ1 hσ hσ1 ha hM hn
  have hcoef : 0 ≤ 2*Real.sqrt (d:ℝ)*ρ := by positivity
  have hbound : 2*Real.sqrt (d:ℝ)*ρ*e ≤
      2*Real.sqrt (d:ℝ)*ρ*(G*(2 : ℝ)^((1-a)*(n:ℝ))) :=
    mul_le_mul_of_nonneg_left he hcoef
  have hg : 0 ≤ 2*Real.sqrt (d:ℝ)*G := by positivity
  calc
    S ≤ 2*Real.sqrt (d:ℝ)*ρ*e := hS
    _ ≤ 2*Real.sqrt (d:ℝ)*ρ*(G*(2 : ℝ)^((1-a)*(n:ℝ))) := hbound
    _ = (2*Real.sqrt (d:ℝ)*G)*(ρ*(2 : ℝ)^((1-a)*(n:ℝ))) := by ring
    _ ≤ (2*Real.sqrt (d:ℝ)*G)*(((2 : ℝ)^M)^4*ρ^σ) :=
      mul_le_mul_of_nonneg_left hfac hg
    _ = 2*Real.sqrt (d:ℝ)*G*((2 : ℝ)^M)^4*ρ^σ := by ring

/-- Uniform box modulus from the four starting-scale cases. -/
theorem wnScale_diameter_bound (d : ℕ) {σ a b D : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσb : σ < b) (hba : b < a)
    (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ρ G e S : ℝ} {M n : ℕ} {c : ℕ → ℝ},
      (hρ : 0 < ρ) → ρ ≤ 1 → 0 ≤ G →
      (∀ j, M ≤ j → wnStartScale ρ hρ ≤ j → j ≤ n →
        S ≤ (2*ρ*(2 : ℝ)^j+2)*D*wnLocalChain_sum d j n c e) →
      S ≤ 2*Real.sqrt (d:ℝ)*ρ*e →
      (∀ k, M ≤ k → k < n → c k ≤ G*(2 : ℝ)^(-(a*k))) →
      (n : ℝ)^2*(2 : ℝ)⁻¹ ^ n*e ≤
        G*((n : ℝ)^2*(2 : ℝ)^(-(a*n))) →
      e ≤ G*(2 : ℝ)^((1-a)*(n:ℝ)) →
      S ≤ K*G*((2 : ℝ)^M)^4*ρ^σ := by
  let K₁ : ℝ := D*wnScaleSumConst d a b*wnScaleStartConst b σ
  let K₂ : ℝ := 4*D*wnScaleSumConst d a b
  let K₃ : ℝ := 2*Real.sqrt (d:ℝ)*wnScaleTerminalConst a σ
  let K₄ : ℝ := 2*Real.sqrt (d:ℝ)
  let K : ℝ := K₁+K₂+K₃+K₄+1
  have hK₁ : 0 ≤ K₁ := by
    dsimp [K₁]
    exact mul_nonneg (mul_nonneg hD (wnScaleSumConst_nonneg d hba))
      (wnScaleStartConst_nonneg hσb)
  have hK₂ : 0 ≤ K₂ := by
    dsimp [K₂]
    exact mul_nonneg (mul_nonneg (by norm_num) hD) (wnScaleSumConst_nonneg d hba)
  have hK₃ : 0 ≤ K₃ := by
    dsimp [K₃]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (wnScaleTerminalConst_nonneg (hσb.trans hba))
  have hK₄ : 0 ≤ K₄ := by dsimp [K₄]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro ρ G e S M n c hρ hρ1 hG hchain hseg hc hterm he
  let j₀ := wnStartScale ρ hρ
  let T : ℝ := ((2 : ℝ)^M)^4
  have hT : 1 ≤ T := by
    dsimp [T]
    exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hρσ : 0 ≤ ρ^σ := by positivity
  have hprod : 0 ≤ G*T*ρ^σ := by positivity
  have hK₁le : K₁ ≤ K := by dsimp [K]; linarith
  have hK₂le : K₂ ≤ K := by dsimp [K]; linarith
  have hK₃le : K₃ ≤ K := by dsimp [K]; linarith
  have hK₄le : K₄ ≤ K := by dsimp [K]; linarith
  have hlift (A : ℝ) (hA : 0 ≤ A) (hAK : A ≤ K)
      (hS : S ≤ A*G*T*ρ^σ) : S ≤ K*G*T*ρ^σ := by
    have hmul := mul_le_mul_of_nonneg_right hAK hprod
    nlinarith
  have hlift0 (A : ℝ) (hA : 0 ≤ A) (hAK : A ≤ K)
      (hS : S ≤ A*G*ρ^σ) : S ≤ K*G*T*ρ^σ := by
    have hAT : A*G*ρ^σ ≤ A*G*T*ρ^σ := by
      have hprod0 : 0 ≤ A*G*ρ^σ := by positivity
      nlinarith [mul_nonneg hprod0 (sub_nonneg.mpr hT)]
    exact hlift A hA hAK (hS.trans hAT)
  rcases le_total M j₀ with hMj | hjM
  · rcases le_or_gt j₀ n with h0n | hn
    · have hS := wnScale_chain_start hρ hρ1 hσ hσb hba hD hG h0n
        (hchain j₀ hMj le_rfl h0n)
        (fun k h1 h2 => hc k (hMj.trans h1) h2) hterm
      exact hlift0 K₁ hK₁ hK₁le (by
        convert hS using 1
        ring)
    ·
      have hS := wnScale_terminal_start hρ hρ1 hσ (hσb.trans hba) ha1 hG hn hseg he
      exact hlift0 K₃ hK₃ hK₃le (by
        convert hS using 1
        ring)
  · rcases le_or_gt M n with hMn | hn
    · have hS := wnScale_chain_bad hρ hρ1 hσ hσ1 hσb hba hD hG hjM hMn
        (hchain M le_rfl hjM hMn) hc hterm
      exact hlift K₂ hK₂ hK₂le (by
        convert hS using 1
        ring)
    ·
      have hS := wnScale_terminal_bad hρ hρ1 hσ hσ1 (hσ.trans (hσb.trans hba)).le
        hG hjM hn hseg he
      exact hlift K₄ hK₄ hK₄le (by
        convert hS using 1)

end HigherDimLQGContinuity
