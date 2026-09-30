import QuantumZipper.Proofs.Thm18.LWFarSideMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGETOP (partial): both end points of `Z_t ηⱼ` lie on one side of `0`

Task FL-IMAGETOP (helper of FL-THM, D75). Field–Lawler, EJP 20 (2015), proof of Prop. 3.4
(p. 9): the crosscuts `Z_t ηⱼ` have both end points on one side of `0`, because the tip (sent to
`0`) and `∞` lie outside `B̄(0, ε)` and are joined in `H_t \ B̄(0, ε)` (FL leave this implicit).

`fl_endpoints_sameSide`: a curve in `ℍ` from a real `a` to a real `b` whose `F`-image lies in
`B̄(0, ε)` has `0 < a b`. Own argument (the one of `lwfSide_sign`): otherwise the curve and the
`Z_t`-image of the radial segment `λ · η(t)`, `λ ∈ [λ₀, λ₁]`, `λ₀ ↓ 1` (whose `Z_t`-image starts
near `0`, by `lwfSide_limit` and `SideCtx.Ftip`, and ends far away, by `norm_fwdMap_ge`) must
cross (`lwfSide_crossing`, winding number), but the segment lies outside `B̄(0, R)`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- No path in `ℍ̄` from `u₁ < 0` to `u₂ > 0` has its `F`-image in `B̄(0, ε)`. -/
theorem fl_no_sep_path (hc : SideCtx W t F) {R ε : ℝ} (hεR : ε < R) (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {u₁ u₂ : ℝ} (hu₁ : u₁ < 0)
    (hu₂ : 0 < u₂) (σ : Path (u₁ : ℂ) (u₂ : ℂ)) (hσ : ∀ s, 0 ≤ (σ s).im)
    (hσF : ∀ s, ‖F (σ s)‖ ≤ ε) : False := by
  set tp := trace W t with htp
  have hR : 0 < R := hnorm ▸ norm_pos_iff.2 (fun h => by
    have : (0 : ℝ) < tp.im := hH
    rw [h] at this; simp at this)
  -- `σ` avoids `0`
  have hσ0 : ∀ s, σ s ≠ 0 := fun s h => by
    have := hσF s
    rw [h, hc.F0, ← htp, hnorm] at this
    linarith
  obtain ⟨z₀, ⟨s₀', rfl⟩, hs₀⟩ := (isCompact_range σ.continuous).exists_isMinOn
    (range_nonempty σ) continuous_norm.continuousOn
  set m := ‖σ s₀'‖ with hm
  have hmpos : 0 < m := norm_pos_iff.2 (hσ0 s₀')
  have hmle : ∀ s, m ≤ ‖σ s‖ := fun s => hs₀ (mem_range_self s)
  obtain ⟨M, hM⟩ := (isCompact_range σ.continuous).isBounded.subset_closedBall 0
  have hMle : ∀ s, ‖σ s‖ ≤ M := fun s => by
    simpa using hM (mem_range_self s)
  -- the radial ray beyond the tip
  set r : ℝ → ℂ := fun l => (l : ℂ) * tp with hrdef
  have hrD : ∀ l : ℝ, 1 < l → r l ∈ H \ fwdHull W t := by
    intro l hl
    have hnr : ‖r l‖ = l * R := by
      simp [hrdef, abs_of_pos (zero_lt_one.trans hl), hnorm]
    refine ⟨?_, fun hK => ?_⟩
    · show 0 < (r l).im
      simp only [hrdef, Complex.im_ofReal_mul]
      exact mul_pos (zero_lt_one.trans hl) hH
    · have := hle _ hK
      rw [hnr] at this
      nlinarith
  have hrnorm : ∀ l : ℝ, 1 < l → R < ‖r l‖ := fun l hl => by
    simp only [hrdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hl), hnorm]
    nlinarith
  -- a point of the ray whose image is near `0`
  obtain ⟨l₀, hl₀, hp⟩ : ∃ l₀ : ℝ, 1 < l₀ ∧ ‖fwdMap W t (r l₀)‖ < m := by
    set x : ℕ → ℂ := fun n => r (1 + 1 / ((n : ℝ) + 1)) with hxdef
    have hl : ∀ n : ℕ, 1 < 1 + 1 / ((n : ℝ) + 1) := fun n => by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hx : ∀ n, x n ∈ H \ fwdHull W t := fun n => hrD _ (hl n)
    have hlim : Tendsto x atTop (𝓝 tp) := by
      have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const tp
      simpa [hxdef, hrdef, Function.comp_def] using h2
    obtain ⟨φ, -, a, ha, hla⟩ := lwfSide_limit hc hx hc.tip_not_mem hlim
    have ha0 : a = 0 := hc.Ftip a ha
    subst ha0
    have hev := hla.eventually (Metric.ball_mem_nhds _ hmpos)
    obtain ⟨n, hn⟩ := hev.exists
    refine ⟨1 + 1 / ((φ n : ℝ) + 1), hl (φ n), ?_⟩
    have hn' : ‖fwdMap W t (x (φ n))‖ < m := by simpa using hn
    exact hn'
  -- a far point of the ray
  obtain ⟨C, hC⟩ := hc.bound
  set l₁ : ℝ := l₀ + (M + |C| + 1) / R with hl₁
  have hl₀₁ : l₀ < l₁ := by
    have : 0 < (M + |C| + 1) / R := by
      have : 0 ≤ M := (norm_nonneg _).trans (hMle 0)
      positivity
    linarith
  have hq : M < ‖fwdMap W t (r l₁)‖ := by
    have h1 := hc.norm_fwdMap_ge hC (hrD l₁ (hl₀.trans hl₀₁))
    have h2 : ‖r l₁‖ = l₁ * R := by
      simp [hrdef, abs_of_pos (zero_lt_one.trans (hl₀.trans hl₀₁)), hnorm]
    have h3 : l₁ * R ≥ M + |C| + 1 := by
      have : l₁ * R = l₀ * R + (M + |C| + 1) := by
        rw [hl₁, add_mul, div_mul_cancel₀ _ hR.ne']
      nlinarith
    have := le_abs_self C
    linarith
  -- the path `τ`
  set ρ : ℝ → ℝ := fun s => l₀ + s * (l₁ - l₀) with hρ
  have hρ1 : ∀ s : unitInterval, 1 < ρ s := fun s => by
    have := s.2.1
    have : 0 ≤ (s : ℝ) * (l₁ - l₀) := mul_nonneg this (sub_nonneg.2 hl₀₁.le)
    simp only [hρ]; linarith
  let τ : Path (fwdMap W t (r l₀)) (fwdMap W t (r l₁)) :=
    { toFun := fun s => fwdMap W t (r (ρ s))
      continuous_toFun := by
        refine hc.continuousOn_fwdMap.comp_continuous ?_ fun s => hrD _ (hρ1 s)
        simp only [hrdef, hρ]; fun_prop
      source' := by simp [hρ]
      target' := by simp [hρ] }
  obtain ⟨s, s', he⟩ := lwfSide_crossing hu₁ hu₂ σ hσ τ
    (fun s => (hc.mapsTo (hrD _ (hρ1 s))).out) (fun s => hp.trans_le (hmle s))
    (fun s => (hMle s).trans_lt hq)
  have h1 := hσF s
  have h2 : F (τ s') = r (ρ s') := hc.F_fwdMap (hrD _ (hρ1 s'))
  rw [he, h2] at h1
  have := hrnorm _ (hρ1 s')
  linarith

/-- **Same side.** A curve in `ℍ` from a real `a` to a real `b` with `F`-image in `B̄(0, ε)` has
`0 < a b`. -/
theorem fl_endpoints_sameSide (hc : SideCtx W t F) {R ε : ℝ} (hεR : ε < R)
    (hH : trace W t ∈ H) (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R)
    {η : ℝ → ℂ} {a b : ℝ} (hη : ContinuousOn η (Ioo 0 1)) (hηH : MapsTo η (Ioo 0 1) H)
    (hηF : ∀ s ∈ Ioo (0 : ℝ) 1, ‖F (η s)‖ ≤ ε) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) (hFa : ‖F a‖ ≤ ε) (hFb : ‖F b‖ ≤ ε) :
    0 < a * b := by
  set e := extendFrom (Ioo (0 : ℝ) 1) η with hedef
  have hec : ContinuousOn e (Icc 0 1) := continuousOn_Icc_extendFrom_Ioo hη ha hb
  have he0 : e 0 = a := eq_lim_at_left_extendFrom_Ioo zero_lt_one ha
  have he1 : e 1 = b := eq_lim_at_right_extendFrom_Ioo zero_lt_one hb
  have hein : ∀ s ∈ Ioo (0 : ℝ) 1, e s = η s := extendFrom_extends hη
  let σ : Path (a : ℂ) (b : ℂ) :=
    { toFun := fun s => e s
      continuous_toFun := hec.comp_continuous continuous_subtype_val fun s => s.2
      source' := by simp [he0]
      target' := by simp [he1] }
  have hσ : ∀ s, 0 ≤ (σ s).im ∧ ‖F (σ s)‖ ≤ ε := by
    intro s
    show 0 ≤ (e s).im ∧ ‖F (e s)‖ ≤ ε
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc s.2 with h | h | h
    · rw [h, he0]; exact ⟨by simp, hFa⟩
    · rw [h, he1]; exact ⟨by simp, hFb⟩
    · rw [hein _ h]; exact ⟨(hηH h).out.le, hηF _ h⟩
  have hR : 0 < R := hnorm ▸ norm_pos_iff.2 (fun h => by
    have : (0 : ℝ) < (trace W t).im := hH
    rw [h] at this; simp at this)
  have hne : ∀ x : ℝ, ‖F x‖ ≤ ε → x ≠ 0 := fun x hx h => by
    rw [h, Complex.ofReal_zero, hc.F0, hnorm] at hx
    linarith
  have ha0 := hne a hFa
  have hb0 := hne b hFb
  rcases ha0.lt_or_gt with ha' | ha' <;> rcases hb0.lt_or_gt with hb' | hb'
  · nlinarith
  · exact (fl_no_sep_path hc hεR hH hnorm hle ha' hb' σ (fun s => (hσ s).1)
      fun s => (hσ s).2).elim
  · exact (fl_no_sep_path hc hεR hH hnorm hle hb' ha' σ.symm (fun s => (hσ _).1)
      fun s => (hσ _).2).elim
  · nlinarith

end FieldLawler
end QuantumZipper
