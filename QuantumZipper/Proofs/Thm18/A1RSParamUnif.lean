import QuantumZipper.Proofs.Thm18.A1RSParamBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (16): the uniform parameter modulus of the smeared-loop family

**`a1rfNu_param_unif`**: for a good driver which is `a_H`-Hölder on `[0, T]`, on the box
`t, t + h ∈ (0, T]`, `‖d‖, ‖d'‖ ≤ 2R`, `s, s' ∈ [e^{-R}, e^R]`, uniformly in the smoothing radius
`ρ ∈ [0, 1]`,

`|E(ν_{t,d,s,ρ} − ν_{t+h,d',s',ρ})| ≤ C₂ (h + ‖d − d'‖ + |s − s'|)^{b₂}`.

From `abs_kernelCov2_smear_param_le` (A1RSParamE.lean) with the strip levels `τ₁ = x^{1/2}`,
`τ = x^{e/2}`, `x = Δ/D_m`, `e = min(a_H, 1/2)`: every term is a constant times a power of `x`.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- **Uniform parameter modulus of the smeared-loop family.** -/
theorem a1rfNu_param_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ} (hT : 0 < T)
    (R : ℕ) {CH aH : ℝ} (hCH : 0 ≤ CH) (haH : 0 < aH) (haH1 : aH ≤ 1)
    (hHol : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, |W a - W b| ≤ CH * |a - b| ^ aH) :
    ∃ C₂ b₂ : ℝ, 0 ≤ C₂ ∧ 0 < b₂ ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ h : ℝ, 0 ≤ h → t + h ≤ T →
      ∀ d d' : ℂ, ‖d‖ ≤ 2 * R → ‖d'‖ ≤ 2 * R → ∀ s s' : ℝ, Real.exp (-R) ≤ s →
        s ≤ Real.exp R → Real.exp (-R) ≤ s' → s' ≤ Real.exp R → ∀ ρ ∈ Icc (0 : ℝ) 1,
          |kernelCov2 neumannH (a1rfNu W t left d s ρ, a1rfNu W (t + h) left d' s' ρ)
            (a1rfNu W t left d s ρ, a1rfNu W (t + h) left d' s' ρ)| ≤
            C₂ * (h + ‖d - d'‖ + |s - s'|) ^ b₂ := by
  -- constants
  set Rb : ℝ := 2 * R + Real.exp R with hRb
  have hRb0 : 0 ≤ Rb := by positivity
  obtain ⟨R₁, hR₁0, hR₁⟩ := norm_sidePush_le_unif hG left hT (Rb + 1)
  obtain ⟨α, CF, hα, hα1, hCF, hFr⟩ := isFrostman_a1rfNu_unif hG left hT R
  obtain ⟨Ci, hCi, hinv⟩ := norm_fwdMapInv_le_unif hG.1 hG.2.1 hT
  obtain ⟨R₁', Cm, hR₁', hCm, hbox⟩ := a1rMu_box_facts hG left hT R
  set Rh : ℝ := R₁ + 1 with hRh
  set Bf : ℝ := Rh + Ci with hBf
  set Dm : ℝ := T + 4 * R + Real.exp R + 1 with hDm
  have hDm1 : 1 ≤ Dm := by
    have := Real.exp_pos (R : ℝ); have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    rw [hDm]; linarith
  set e : ℝ := min aH (1 / 2) with he
  have he0 : 0 < e := lt_min haH (by norm_num)
  have heH : e ≤ aH := min_le_left _ _
  have he12 : e ≤ 1 / 2 := min_le_right _ _
  set cD : ℝ := (3 * CH + 6) * Dm with hcD
  set S1 : ℝ := Real.sqrt (Rh ^ 2 + 4 * T) with hS1
  set S2 : ℝ := Real.sqrt ((Rh + cD) ^ 2 + 4 * T) with hS2
  set K₀ : ℝ := S1 * ((2 * R₁ + 24 * CH + 8) * Dm) + S2 * cD with hK₀
  set KH := holderKα α CF Bf with hKH
  set Pm := potMaxα α CF Bf with hPm
  have hKH0 : 0 ≤ KH := holderKα_nonneg hα hCF (by positivity)
  have hPm0 : 0 ≤ Pm := potMaxα_nonneg hα hCF (by positivity)
  set b : ℝ := e * α / 8 with hb
  have hb0 : 0 < b := by positivity
  set Cw : ℝ := 3 / 2 * Real.sqrt (Real.exp R) with hCw
  refine ⟨2 * (KH * K₀ ^ (α / 2) + 2 * Pm * (2 * Cw + 2 * (2 * Cm + 2))), b, by positivity, hb0,
    ?_⟩
  intro t ht h hh htT d d' hd hd' s s' hs1 hs2 hs1' hs2' ρ hρ
  have hs : 0 < s := (Real.exp_pos _).trans_le hs1
  have hs' : 0 < s' := (Real.exp_pos _).trans_le hs1'
  have htT' : t + h ∈ Ioc (0 : ℝ) T := ⟨by linarith [ht.1], htT⟩
  set Δ : ℝ := h + ‖d - d'‖ + |s - s'| with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hCnn : 0 ≤ 2 * (KH * K₀ ^ (α / 2) + 2 * Pm * (2 * Cw + 2 * (2 * Cm + 2))) := by
    have : 0 ≤ K₀ ^ (α / 2) := Real.rpow_nonneg (by positivity) _
    positivity
  rcases eq_or_lt_of_le hΔ0 with hΔz | hΔpos
  · -- equal parameters
    have hh0 : h = 0 := by linarith [norm_nonneg (d - d'), abs_nonneg (s - s')]
    have hdd : ‖d - d'‖ = 0 := by linarith [abs_nonneg (s - s'), norm_nonneg (d - d')]
    have hss : |s - s'| = 0 := by linarith [norm_nonneg (d - d'), abs_nonneg (s - s')]
    have e1 : d' = d := (sub_eq_zero.1 (norm_eq_zero.1 hdd)).symm
    have e2 : s' = s := by linarith [abs_eq_zero.1 hss]
    have hmeq : a1rfNu W (t + h) left d' s' ρ = a1rfNu W t left d s ρ := by
      rw [hh0, add_zero, e1, e2]
    have hz : ∀ a b : Measure ℂ, b = a → kernelCov2 neumannH (a, b) (a, b) = 0 := fun a b hab => by
      subst hab; unfold kernelCov2; ring
    rw [hz _ _ hmeq, abs_zero]
    exact mul_nonneg hCnn (Real.rpow_nonneg hΔ0 _)
  -- the scale `x = Δ / Dm ∈ (0, 1]`
  have hΔDm : Δ ≤ Dm := by
    have h1 : ‖d - d'‖ ≤ 4 * R := (norm_sub_le _ _).trans (by linarith)
    have h2 : |s - s'| ≤ Real.exp R := by
      rw [abs_le]; constructor <;> linarith [Real.exp_pos (-(R : ℝ))]
    have h3 : h ≤ T := by linarith [ht.1]
    linarith [hΔ, hDm]
  set x : ℝ := Δ / Dm with hx
  have hx0 : 0 < x := div_pos hΔpos (by linarith)
  have hx1 : x ≤ 1 := (div_le_one (by linarith)).2 hΔDm
  have hΔx : Δ = Dm * x := by rw [hx]; field_simp
  set τ₁ : ℝ := x ^ (1 / 2 : ℝ) with hτ₁
  set τ : ℝ := x ^ (e / 2) with hτ
  have hτ₁0 : 0 < τ₁ := Real.rpow_pos_of_pos hx0 _
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hx0 _
  have hτ₁1 : τ₁ ≤ 1 := Real.rpow_le_one hx0.le hx1 (by norm_num)
  have hτ1 : τ ≤ 1 := Real.rpow_le_one hx0.le hx1 (by positivity)
  -- measurable versions of the pushing maps and the angle representation
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht.1 left
  obtain ⟨-, -, g', hgm', hEq'⟩ := A1R.sidePush_props hG htT'.1 left
  rw [a1rfNu_eq_map_angles' hG ht.1 hgm hEq d hs ρ,
    a1rfNu_eq_map_angles' hG htT'.1 hgm' hEq' d' hs' ρ]
  -- oscillation of the driver
  set ε : ℝ := CH * h ^ aH with hε
  have hosc1 : ∀ r ∈ Icc (0 : ℝ) h, |W (t + r) - W t| ≤ ε := fun r hr => by
    refine (hHol _ ⟨by linarith [ht.1, hr.1], by linarith [hr.2]⟩ _ ⟨ht.1.le, by linarith⟩).trans ?_
    rw [show t + r - t = r by ring, abs_of_nonneg hr.1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.1 hr.2 haH.le) hCH
  have hosc2 : ∀ q ∈ Icc (0 : ℝ) h, |W (t + h - q) - W (t + h)| ≤ ε := fun q hq => by
    refine (hHol _ ⟨by linarith [ht.1, hq.2], by linarith [hq.1]⟩ _ ⟨by linarith [ht.1], htT⟩).trans ?_
    rw [show t + h - q - (t + h) = -q by ring, abs_neg, abs_of_nonneg hq.1]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.1 hq.2 haH.le) hCH
  have hB : ∀ z ∈ H, ‖z‖ < Rb + 1 → ‖fwdMap W t (g1zSideMap left W z)‖ ≤ R₁ :=
    fun z hz hzn => hR₁ t ht z hz hzn.le
  have hdR : ‖d‖ + s ≤ Rb := by rw [hRb]; linarith
  have hdR' : ‖d'‖ + s' ≤ Rb := by rw [hRb]; linarith
  have hRhw : ∀ w ∈ H, ‖w‖ ≤ Rb → ‖g w‖ + 1 ≤ Rh ∧ ‖g' w‖ + 1 ≤ Rh := fun w hw hwn => by
    have a1 := hR₁ t ht w hw (by linarith)
    have a2 := hR₁ (t + h) htT' w hw (by linarith)
    rw [← hEq hw, ← hEq' hw]
    exact ⟨by linarith, by linarith⟩
  have hBf0 : 0 ≤ Bf := by rw [hBf, hRh]; linarith
  -- a.e. the side-circle points lie in `ℍ`
  have hwH : ∀ᵐ q ∂(G1RC.circM.prod E6.XAreaPC.angMeas), foldH (circleMap d s q.1) ∈ H :=
    Measure.quasiMeasurePreserving_fst.ae (ae_circM_mem_H d hs)
  have hwH' : ∀ᵐ q ∂(G1RC.circM.prod E6.XAreaPC.angMeas), foldH (circleMap d' s' q.1) ∈ H :=
    Measure.quasiMeasurePreserving_fst.ae (ae_circM_mem_H d' hs')
  have hsupp : ∀ (c : ℂ) (σ : ℝ) (tt : ℝ) (gg : ℂ → ℂ), tt ∈ Ioc (0 : ℝ) T → ‖c‖ + σ ≤ Rb →
      0 ≤ σ → (∀ w ∈ H, ‖w‖ ≤ Rb → ‖gg w‖ + 1 ≤ Rh) → ∀ θ₁ θ₂ : ℝ,
      foldH (circleMap c σ θ₁) ∈ H →
      ‖fwdMapInv W tt (foldH (circleMap (gg (foldH (circleMap c σ θ₁))) ρ θ₂))‖ ≤ Bf := by
    intro c σ tt gg htt hcR hσ hgg θ₁ θ₂ hmem
    refine (hinv tt htt _).trans ?_
    have hwn : ‖foldH (circleMap c σ θ₁)‖ ≤ Rb := by
      rw [norm_foldH]; exact (norm_circleMap_le_add c hσ θ₁).trans hcR
    have := hgg _ hmem hwn
    rw [norm_foldH]
    have := norm_circleMap_le_add (gg (foldH (circleMap c σ θ₁))) hρ.1 θ₂
    rw [hBf]; linarith [hρ.2]
  have hb1 : ∀ᵐ q ∂(G1RC.circM.prod E6.XAreaPC.angMeas),
      ‖fwdMapInv W t (foldH (circleMap (g (foldH (circleMap d s q.1))) ρ q.2))‖ ≤ Bf := by
    filter_upwards [hwH] with q hq
    exact hsupp d s t g ht hdR hs.le (fun w hw hwn => (hRhw w hw hwn).1) q.1 q.2 hq
  have hb2 : ∀ᵐ q ∂(G1RC.circM.prod E6.XAreaPC.angMeas),
      ‖fwdMapInv W (t + h) (foldH (circleMap (g' (foldH (circleMap d' s' q.1))) ρ q.2))‖ ≤ Bf := by
    filter_upwards [hwH'] with q hq
    exact hsupp d' s' (t + h) g' htT' hdR' hs'.le (fun w hw hwn => (hRhw w hw hwn).2) q.1 q.2 hq
  -- Frostman bounds in the angle representation
  have hF1 := hFr t ht d hd s hs1 hs2 ρ hρ
  rw [a1rfNu_eq_map_angles' hG ht.1 hgm hEq d hs ρ] at hF1
  have hF2 := hFr (t + h) htT' d' hd' s' hs1' hs2' ρ hρ
  rw [a1rfNu_eq_map_angles' hG htT'.1 hgm' hEq' d' hs' ρ] at hF2
  -- strip masses
  set εw : ℝ := Cw * x ^ (1 / 4 : ℝ) with hεw
  have hstripw : ∀ (c : ℂ) (σ : ℝ), 0 < σ → Real.exp (-R) ≤ σ →
      (G1RC.circM.prod E6.XAreaPC.angMeas).real
        {q : ℝ × ℝ | (foldH (circleMap c σ q.1)).im ≤ τ₁} ≤ εw := by
    intro c σ hσ hσ1
    refine (circM_strip_le c hσ hτ₁0.le).trans ?_
    have h1 : τ₁ / σ ≤ τ₁ * Real.exp R := by
      rw [div_le_iff₀ hσ]
      have h0 : 1 ≤ Real.exp R * σ := by
        calc (1 : ℝ) = Real.exp R * Real.exp (-R) := by rw [← Real.exp_add]; simp
          _ ≤ Real.exp R * σ := mul_le_mul_of_nonneg_left hσ1 (Real.exp_pos _).le
      calc τ₁ = τ₁ * 1 := by ring
        _ ≤ τ₁ * (Real.exp R * σ) := mul_le_mul_of_nonneg_left h0 hτ₁0.le
        _ = τ₁ * Real.exp R * σ := by ring
    have h2 : Real.sqrt (τ₁ * Real.exp R) = Real.sqrt (Real.exp R) * x ^ (1 / 4 : ℝ) := by
      rw [mul_comm, Real.sqrt_mul (Real.exp_pos _).le, hτ₁, Real.sqrt_eq_rpow (x ^ _),
        ← Real.rpow_mul hx0.le]
      norm_num
    rw [hεw, hCw, mul_assoc, ← h2]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (by norm_num)
  set εU : ℝ := (2 * Cm + 2) * τ ^ (1 / 4 : ℝ) with hεU
  have hstripU : ∀ (tt : ℝ) (gg : ℂ → ℂ) (c : ℂ) (σ : ℝ), tt ∈ Ioc (0 : ℝ) T → Measurable gg →
      EqOn (fun w => fwdMap W tt (g1zSideMap left W w)) gg H → ‖c‖ ≤ 2 * R →
      Real.exp (-R) ≤ σ → σ ≤ Real.exp R →
      (G1RC.circM.prod E6.XAreaPC.angMeas).real
        {q : ℝ × ℝ | (foldH (circleMap (gg (foldH (circleMap c σ q.1))) ρ q.2)).im ≤ τ} ≤ εU := by
    intro tt gg c σ htt hggm hggE hc hσ1 hσ2
    have hσ : 0 < σ := (Real.exp_pos _).trans_le hσ1
    obtain ⟨hP, hsp, hms⟩ := hbox tt htt c hc σ hσ1 hσ2
    rw [angles_stripU_eq hggm hggE c hσ ρ τ]
    exact prod_strip_le (hsp.mono fun z hz => hz.1) hCm hms hρ.1 hτ0 hτ1
  have hgen := abs_kernelCov2_smear_param_le hG left ht.1 hh hosc1 hosc2 hB hτ0 hτ₁0 hτ₁1 hρ.1
    hρ.2 hα hα1 hCF hBf0 hgm hgm' hEq hEq' hdR hdR' hs.le hs'.le hRhw hF1 hF2 hb1 hb2
    (hstripw d s hs hs1) (hstripw d' s' hs' hs1') (hstripU t g d s ht hgm hEq hd hs1 hs2)
    (hstripU (t + h) g' d' s' htT' hgm' hEq' hd' hs1' hs2')
  refine hgen.trans ?_
  -- exponent bookkeeping
  have hxe : x ^ e ≤ 1 := Real.rpow_le_one hx0.le hx1 he0.le
  have hxe0 : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have hDmx : Δ = Dm * x := hΔx
  have hε1 : ε ≤ CH * Dm * x ^ e := by
    have hhΔ : h ≤ Dm * x := by
      rw [← hDmx]; linarith [hΔ, norm_nonneg (d - d'), abs_nonneg (s - s')]
    have a1 : h ^ aH ≤ (Dm * x) ^ aH := Real.rpow_le_rpow hh hhΔ haH.le
    have a2 : (Dm * x) ^ aH = Dm ^ aH * x ^ aH := Real.mul_rpow (by linarith) hx0.le
    have a3 : Dm ^ aH ≤ Dm := by
      calc Dm ^ aH ≤ Dm ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hDm1 haH1
        _ = Dm := Real.rpow_one Dm
    have a4 : x ^ aH ≤ x ^ e := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 heH
    have a5 : Dm ^ aH * x ^ aH ≤ Dm * x ^ e :=
      mul_le_mul a3 a4 (Real.rpow_nonneg hx0.le _) (by linarith)
    rw [hε]
    have := mul_le_mul_of_nonneg_left (a1.trans (a2 ▸ a5)) hCH
    linarith
  have hsq1 : Real.sqrt h ≤ Dm * x ^ e := by
    have hhΔ : h ≤ Dm * x := by
      rw [← hDmx]; linarith [hΔ, norm_nonneg (d - d'), abs_nonneg (s - s')]
    have a1 : Real.sqrt h ≤ Real.sqrt (Dm * x) := Real.sqrt_le_sqrt hhΔ
    have a2 : Real.sqrt (Dm * x) = Real.sqrt Dm * x ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by linarith), Real.sqrt_eq_rpow x]
    have a3 : Real.sqrt Dm ≤ Dm := by
      calc Real.sqrt Dm ≤ Real.sqrt (Dm * Dm) :=
            Real.sqrt_le_sqrt (le_mul_of_one_le_right (by linarith) hDm1)
        _ = Dm := Real.sqrt_mul_self (by linarith)
    have a4 : x ^ (1 / 2 : ℝ) ≤ x ^ e := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 he12
    rw [a2] at a1
    exact a1.trans (mul_le_mul a3 a4 (Real.rpow_nonneg hx0.le _) (by linarith))
  have hcD0 : 0 ≤ cD := by rw [hcD]; positivity
  have hD1 : 3 * ε + 6 * Real.sqrt h ≤ cD * x ^ e := by
    have : 3 * ε + 6 * Real.sqrt h ≤ 3 * (CH * Dm * x ^ e) + 6 * (Dm * x ^ e) := by linarith
    refine this.trans (le_of_eq ?_)
    rw [hcD]; ring
  have hD2 : 3 * ε + 6 * Real.sqrt h ≤ cD := hD1.trans (mul_le_of_le_one_right hcD0 hxe)
  have hε0 : 0 ≤ ε := by rw [hε]; exact mul_nonneg hCH (Real.rpow_nonneg hh _)
  have hD0 : 0 ≤ 3 * ε + 6 * Real.sqrt h := by
    have := Real.sqrt_nonneg h
    linarith
  have i0 : 0 ≤ 2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h) := by
    have := Real.sqrt_nonneg h
    have := mul_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ 2 * R₁) hτ₁0.le)
      (add_nonneg (norm_nonneg (d - d')) (abs_nonneg (s - s')))
    linarith
  have hspace : 2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) ≤ 2 * R₁ * Dm * x ^ e := by
    have a1 : ‖d - d'‖ + |s - s'| ≤ Dm * x := by rw [← hDmx]; linarith [hΔ]
    have a2 : x / τ₁ = x ^ (1 / 2 : ℝ) := by
      rw [hτ₁, div_eq_iff (Real.rpow_pos_of_pos hx0 _).ne', ← Real.rpow_add hx0]
      norm_num
    have a3 : x ^ (1 / 2 : ℝ) ≤ x ^ e := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 he12
    calc 2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) ≤ 2 * R₁ / τ₁ * (Dm * x) :=
          mul_le_mul_of_nonneg_left a1 (div_nonneg (by linarith) hτ₁0.le)
      _ = 2 * R₁ * Dm * (x / τ₁) := by field_simp
      _ ≤ 2 * R₁ * Dm * x ^ e := by
          rw [a2]; exact mul_le_mul_of_nonneg_left a3 (mul_nonneg (by linarith) (by linarith))
  have hS1t : Real.sqrt (Rh ^ 2 + 4 * t) ≤ S1 := Real.sqrt_le_sqrt (by linarith [ht.2])
  have hS2t : Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) ≤ S2 := by
    apply Real.sqrt_le_sqrt
    have hRh0 : 0 ≤ Rh := by positivity
    have : (Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 ≤ (Rh + cD) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith [ht.2]
  have hnum : Real.sqrt (Rh ^ 2 + 4 * t) *
        (2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h)) +
      Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h) ≤
      K₀ * x ^ e := by
    have i1 : 2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h) ≤
        (2 * R₁ + 24 * CH + 8) * Dm * x ^ e := by
      have : 2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h) ≤
          2 * R₁ * Dm * x ^ e + 24 * (CH * Dm * x ^ e) + 8 * (Dm * x ^ e) := by linarith
      refine this.trans (le_of_eq ?_)
      ring
    have j1 := mul_le_mul hS1t i1 i0 (Real.sqrt_nonneg _)
    have j2 := mul_le_mul hS2t hD1 hD0 (Real.sqrt_nonneg _)
    calc _ ≤ S1 * ((2 * R₁ + 24 * CH + 8) * Dm * x ^ e) + S2 * (cD * x ^ e) := add_le_add j1 j2
      _ = K₀ * x ^ e := by rw [hK₀]; ring
  have hδ : (Real.sqrt (Rh ^ 2 + 4 * t) *
        (2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h)) +
      Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h)) / τ ≤
      K₀ * x ^ (e / 2) := by
    rw [div_le_iff₀ hτ0, hτ, mul_assoc, ← Real.rpow_add hx0]
    rw [show e / 2 + e / 2 = e by ring]
    exact hnum
  have hδ0 : 0 ≤ (Real.sqrt (Rh ^ 2 + 4 * t) *
        (2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h)) +
      Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h)) / τ :=
    div_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) i0)
      (mul_nonneg (Real.sqrt_nonneg _) hD0)) hτ0.le
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    refine add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg ?_ (by linarith)))
      (mul_nonneg (Real.sqrt_nonneg _) hcD0)
    linarith
  have hpow : ((Real.sqrt (Rh ^ 2 + 4 * t) *
        (2 * R₁ / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h)) +
      Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h)) / τ) ^
        (α / 2) ≤ K₀ ^ (α / 2) * x ^ b := by
    refine (Real.rpow_le_rpow hδ0 hδ (by positivity)).trans ?_
    rw [Real.mul_rpow hK₀0 (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ?_)
      (Real.rpow_nonneg hK₀0 _)
    have : e / 2 * (α / 2) = 2 * b := by rw [hb]; ring
    linarith only [this, hb0]
  have hw' : εw ≤ Cw * x ^ b := by
    rw [hεw]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ?_)
      (by rw [hCw]; positivity)
    have : e * α ≤ 1 := mul_le_one₀ (by linarith only [he12]) hα.le hα1
    rw [hb]; linarith only [this]
  have hU' : εU ≤ (2 * Cm + 2) * x ^ b := by
    rw [hεU, hτ, ← Real.rpow_mul hx0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 ?_)
      (by linarith only [hCm])
    have h1 : e * α ≤ e * 1 := mul_le_mul_of_nonneg_left hα1 he0.le
    have h2 : e / 2 * (1 / 4) = e * 1 / 8 := by ring
    rw [hb, h2]; linarith only [h1]
  have hxΔ : x ^ b ≤ Δ ^ b := by
    refine Real.rpow_le_rpow hx0.le ?_ hb0.le
    rw [hx]; exact div_le_self hΔ0 hDm1
  have hxb0 : 0 ≤ x ^ b := Real.rpow_nonneg hx0.le _
  have f1 := mul_le_mul_of_nonneg_left hpow hKH0
  have f4 := mul_le_mul_of_nonneg_left hxΔ hCnn
  have g2 : 2 * Pm * (2 * εw + 2 * εU) ≤
      2 * Pm * (2 * (Cw * x ^ b) + 2 * ((2 * Cm + 2) * x ^ b)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hw', hU']) (by linarith only [hPm0])
  calc _ ≤ 2 * (KH * (K₀ ^ (α / 2) * x ^ b) +
        2 * Pm * (2 * (Cw * x ^ b) + 2 * ((2 * Cm + 2) * x ^ b))) := by linarith only [f1, g2]
    _ = 2 * (KH * K₀ ^ (α / 2) + 2 * Pm * (2 * Cw + 2 * (2 * Cm + 2))) * x ^ b := by ring
    _ ≤ _ := f4

end A1RS
end R18
end QuantumZipper
