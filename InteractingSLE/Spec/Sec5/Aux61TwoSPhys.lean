/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61TwoSSide
import InteractingSLE.Spec.Sec5.MarkovFlow
import InteractingSLE.GFF.Pushforward
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit

/-!
# Aux. 61, the two new sides: the physical form of (D1), and (D2)

Packet PROVE-AUX61-TWOSIDES. The objects of `Aux61SlitV.ae_tendsto_chart_sub_flowMean` / `tendsto_slit_of_chart`
(PROVE-AUX61-SLIT): a physical driver `W_ph`, the restart time `r`, the comparison time `ρ = r + σ`, the physical flow
line's mean `M₂ = couplingMean κ W_ph ρ u_ph`, a restart chart `c` (inverse `inv = c.2.1`, lift `c.2.2 = Im Lc`), its
chart reading `w₂ = M₂ ∘ inv + a + χ · lift ∘ inv`, and the chart driver `w` at time `t` with `F_t = fwdMapInv w t`.

* **`chartReading_sub_couplingMean_eq`** (exact identity): on `ℍ`,
  `w₂(F_t y) − couplingMean κ w t u_c (F_t y) = u_ph(Θ y) + a − u_c(y) − χ · Im thetaLog(y)`, where `Θ`, `thetaLog` are
  the configuration's transition and its logarithm with `Ψ⁻¹ = f_r ∘ inv` and `LΨ = (Lc − L_r) ∘ F_r` (the chain rule of
  the Loewner flow `couplingMean_add`; no branch is reset);
* **`tendsto_chartReading_sub_couplingMean_of_neg`**, **`…_of_pos`** — **(D1)**: at a real point `x′` of the slit image
  (`F_t(y) → Ψ(β′(s′))`, `0 < s′ < σ`), `w₂ ∘ F_t − couplingMean κ w t u_c ∘ F_t → b_ph + a − b_c`, where `b_ph` is the
  boundary value of `u_ph` on the corresponding side of the flow slit and `b_c` that of `u_c` at `x′` (both `∓λ` for
  flow-line words, so the limit is `a`, which is `0` for the seed-normalized chart);
* **(D2)** `tendsto_inv_comp_of_tendsto` (the boundary correspondence `inv ∘ F_t → z₀`) and
  `exists_ball_inter_subset_of_open` / `exists_ball_inter_subset_curve` (`A ∩ B(z₀, r) ⊆ L` near a slit point).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.Aux61TwoS

open WangWu (IsProperArc chartAL chartAR)

/-! ### The exact identity -/

section Identity

variable {Wph : ℝ → ℝ} {r σ : ℝ} {c : Chart} {Lc : ℂ → ℂ} {w : ℝ → ℝ} {t : ℝ}

/-- The inverse transition in physical form, `Ψ⁻¹ = f_r ∘ inv`. -/
def physInv (Wph : ℝ → ℝ) (r : ℝ) (c : Chart) (y : ℂ) : ℂ := fwdMap Wph r (c.2.1 y)

/-- The seed logarithm in physical form, `LΨ = (Lc − L_r) ∘ F_r`. -/
def physLog (Wph : ℝ → ℝ) (r : ℝ) (Lc : ℂ → ℂ) (z : ℂ) : ℂ :=
  Lc (fwdMapInv Wph r z) - logDerivFwd Wph r (fwdMapInv Wph r z)

/-- **The exact identity** behind (D1): the chart reading of the physical flow mean at the time `r + σ` minus the
chart coupling mean, at `F_t(y)`, is `u_ph(Θ y) + a − u_c(y) − χ · Im thetaLog(y)`. Hypotheses: `inv` maps `ℍ` off the
physical hull at time `r` (the chart domain is a component of the complement of the old prefix), `Ψ⁻¹ ∘ F_t` maps `ℍ`
off the shifted hull at time `σ` (`IsTwoSideConfig.inv_fwdMapInv_mem`), and the lift is `Im Lc`. -/
theorem chartReading_sub_couplingMean_eq (κ : ℝ) (hWph : Continuous Wph) (hWph0 : Wph 0 = 0) (hr : 0 ≤ r)
    (hσ : 0 ≤ σ) (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t)
    (hinvD : ∀ y ∈ H, c.2.1 y ∈ H \ fwdHull Wph r)
    (hΘ : ∀ y ∈ H, physInv Wph r c (fwdMapInv w t y) ∈ H \ fwdHull (fun s => Wph (r + s) - Wph r) σ)
    (hlift : ∀ y ∈ H, c.2.2 (c.2.1 y) = (Lc (c.2.1 y)).im) (uph uc : ℂ → ℝ) (a : ℝ) {y : ℂ} (hy : y ∈ H) :
    couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) + a + chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) -
        couplingMean κ w t uc (fwdMapInv w t y) =
      uph (thetaMap (fun s => Wph (r + s) - Wph r) σ (physInv Wph r c) w t y) + a - uc y -
        chiC κ * (thetaLog (fun s => Wph (r + s) - Wph r) σ (physInv Wph r c) (physLog Wph r Lc) w t y).im := by
  set z := c.2.1 (fwdMapInv w t y) with hzdef
  have hFy : fwdMapInv w t y ∈ H := (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hy).1
  have hzr : z ∈ H \ fwdHull Wph r := hinvD _ hFy
  have hFf : fwdMapInv Wph r (fwdMap Wph r z) = z := QuantumZipper.RS.fwdMapInv_fwdMap hWph hWph0 hr hzr
  -- `z` is not swallowed at time `r + σ`
  have hzrσ : z ∈ H \ fwdHull Wph (r + σ) := by
    rw [← Markov.image_fwdMapInv_diff_fwdHull hWph hWph0 hr hσ]
    exact ⟨_, hΘ y hy, hFf⟩
  rw [Markov.couplingMean_add κ uph hWph hr hσ hzrσ]
  have hct : couplingMean κ w t uc (fwdMapInv w t y) =
      uc y - chiC κ * (logDerivFwd w t (fwdMapInv w t y)).im := by
    rw [couplingMean, QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 ht hy]
  rw [hct, couplingMean, hlift _ hFy]
  simp only [thetaMap, thetaLog, physInv, physLog, ← hzdef, hFf, sub_im]
  ring

end Identity

/-! ### (D1) -/

section D1

variable {Wph : ℝ → ℝ} {r : ℝ} {c : Chart} {Lc : ℂ → ℂ} {β β' : ℝ → ℂ} {σ τ : ℝ} {Ω : Set ℂ}
  {Ψ : ℂ → ℂ} {δ : ℝ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {t : ℝ}

/-- **(D1), left side of the new slit.** In the two-sides configuration of the restart (flow coordinates at the restart
time `r`, `Ψ⁻¹ = f_r ∘ inv`, `LΨ = (Lc − L_r) ∘ F_r`), at a real point `x′ < 0` of the chart whose inverse Loewner image
is the slit point `Ψ(β′(s′))`, `0 < s′ < σ`: the chart reading of the physical flow mean at time `r + σ` minus the chart
coupling mean tends to `b_ph + a − b_c`. -/
theorem tendsto_chartReading_sub_couplingMean_of_neg (κ : ℝ)
    (hc : IsTwoSideConfig (fun s => Wph (r + s) - Wph r) β β' σ τ Ω Ψ (physInv Wph r c) (physLog Wph r Lc) δ
      w γ t)
    (hWph : Continuous Wph) (hWph0 : Wph 0 = 0) (hr : 0 ≤ r) (hinvD : ∀ y ∈ H, c.2.1 y ∈ H \ fwdHull Wph r)
    (hlift : ∀ y ∈ H, c.2.2 (c.2.1 y) = (Lc (c.2.1 y)).im) {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : x' < 0) {uph uc : ℂ → ℝ}
    {bph bc : ℝ}
    (huph : ∀ p : ℝ, chartAL (fun s => Wph (r + s) - Wph r) σ < p → p < 0 → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bph))
    (huc : Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bc)) (a : ℝ) :
    Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) + a +
        chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) - couplingMean κ w t uc (fwdMapInv w t y))
      (𝓝[H] (x' : ℂ)) (𝓝 (bph + a - bc)) := by
  refine (hc.tendsto_slitMean_of_neg hs' hs'σ hx' hx'0 huph huc a (chiC κ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (chartReading_sub_couplingMean_eq κ hWph hWph0 hr hc.σ_nonneg hc.hw hc.hw0 hc.t_nonneg hinvD
    (fun y hy => hc.inv_fwdMapInv_mem hy) hlift uph uc a hy).symm

/-- **(D1), right side of the new slit** (mirror). -/
theorem tendsto_chartReading_sub_couplingMean_of_pos (κ : ℝ)
    (hc : IsTwoSideConfig (fun s => Wph (r + s) - Wph r) β β' σ τ Ω Ψ (physInv Wph r c) (physLog Wph r Lc) δ
      w γ t)
    (hWph : Continuous Wph) (hWph0 : Wph 0 = 0) (hr : 0 ≤ r) (hinvD : ∀ y ∈ H, c.2.1 y ∈ H \ fwdHull Wph r)
    (hlift : ∀ y ∈ H, c.2.2 (c.2.1 y) = (Lc (c.2.1 y)).im) {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : 0 < x') {uph uc : ℂ → ℝ}
    {bph bc : ℝ}
    (huph : ∀ p : ℝ, 0 < p → p < chartAR (fun s => Wph (r + s) - Wph r) σ → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bph))
    (huc : Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bc)) (a : ℝ) :
    Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) + a +
        chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) - couplingMean κ w t uc (fwdMapInv w t y))
      (𝓝[H] (x' : ℂ)) (𝓝 (bph + a - bc)) := by
  refine (hc.tendsto_slitMean_of_pos hs' hs'σ hx' hx'0 huph huc a (chiC κ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (chartReading_sub_couplingMean_eq κ hWph hWph0 hr hc.σ_nonneg hc.hw hc.hw0 hc.t_nonneg hinvD
    (fun y hy => hc.inv_fwdMapInv_mem hy) hlift uph uc a hy).symm

end D1

/-! ### (D1) with a driver agreeing with the restarted driver up to the comparison time -/

section D1Frozen

variable {Wph : ℝ → ℝ} {r : ℝ} {c : Chart} {Lc : ℂ → ℂ} {W' : ℝ → ℝ} {β β' : ℝ → ℂ} {σ τ : ℝ} {Ω : Set ℂ}
  {Ψ : ℂ → ℂ} {δ : ℝ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {t : ℝ}

/-- The transition only sees the flow driver on `[0, σ]`. -/
theorem thetaMap_congr {V V' : ℝ → ℝ} (h : EqOn V V' (Icc 0 σ)) (Ψi : ℂ → ℂ) (w : ℝ → ℝ) (t : ℝ) (y : ℂ) :
    thetaMap V σ Ψi w t y = thetaMap V' σ Ψi w t y :=
  Ito.fwdMap_congr_of_eqOn_of_le h le_rfl

/-- The transition logarithm only sees the flow driver on `[0, σ]`. -/
theorem thetaLog_congr {V V' : ℝ → ℝ} (h : EqOn V V' (Icc 0 σ)) (hσ : 0 ≤ σ) (Ψi LΨ : ℂ → ℂ) (w : ℝ → ℝ)
    (t : ℝ) (y : ℂ) : thetaLog V σ Ψi LΨ w t y = thetaLog V' σ Ψi LΨ w t y := by
  simp only [thetaLog, Ito.logDerivFwd_congr_of_eqOn h hσ le_rfl]

/-- **(D1), left side, for a configuration driver `W′` that agrees with the restarted driver on `[0, σ]`** (e.g. the
restarted driver frozen after a time in `(σ, τ)`, whose trace is a simple proper arc:
`IsLoewnerTraceLT.isLoewnerTrace_ext`, `isProperArc_extTrace`). -/
theorem tendsto_chartReading_sub_couplingMean_of_neg' (κ : ℝ)
    (hc : IsTwoSideConfig W' β β' σ τ Ω Ψ (physInv Wph r c) (physLog Wph r Lc) δ w γ t)
    (hW'eq : EqOn W' (fun s => Wph (r + s) - Wph r) (Icc 0 σ))
    (hWph : Continuous Wph) (hWph0 : Wph 0 = 0) (hr : 0 ≤ r) (hinvD : ∀ y ∈ H, c.2.1 y ∈ H \ fwdHull Wph r)
    (hlift : ∀ y ∈ H, c.2.2 (c.2.1 y) = (Lc (c.2.1 y)).im) {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : x' < 0) {uph uc : ℂ → ℝ}
    {bph bc : ℝ} (huph : ∀ p : ℝ, chartAL W' σ < p → p < 0 → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bph))
    (huc : Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bc)) (a : ℝ) :
    Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) + a +
        chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) - couplingMean κ w t uc (fwdMapInv w t y))
      (𝓝[H] (x' : ℂ)) (𝓝 (bph + a - bc)) := by
  have hsh : Continuous fun s => Wph (r + s) - Wph r := by fun_prop
  have hK : fwdHull W' σ = fwdHull (fun s => Wph (r + s) - Wph r) σ :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hc.hW hsh hc.σ_nonneg fun s hs => hW'eq hs
  refine (hc.tendsto_slitMean_of_neg hs' hs'σ hx' hx'0 huph huc a (chiC κ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [chartReading_sub_couplingMean_eq κ hWph hWph0 hr hc.σ_nonneg hc.hw hc.hw0 hc.t_nonneg hinvD
    (fun y hy => hK ▸ hc.inv_fwdMapInv_mem hy) hlift uph uc a hy, thetaMap_congr hW'eq.symm,
    thetaLog_congr hW'eq.symm hc.σ_nonneg]

/-- **(D1), right side, for a configuration driver agreeing with the restarted driver on `[0, σ]`** (mirror). -/
theorem tendsto_chartReading_sub_couplingMean_of_pos' (κ : ℝ)
    (hc : IsTwoSideConfig W' β β' σ τ Ω Ψ (physInv Wph r c) (physLog Wph r Lc) δ w γ t)
    (hW'eq : EqOn W' (fun s => Wph (r + s) - Wph r) (Icc 0 σ))
    (hWph : Continuous Wph) (hWph0 : Wph 0 = 0) (hr : 0 ≤ r) (hinvD : ∀ y ∈ H, c.2.1 y ∈ H \ fwdHull Wph r)
    (hlift : ∀ y ∈ H, c.2.2 (c.2.1 y) = (Lc (c.2.1 y)).im) {x' s' : ℝ} (hs' : 0 < s') (hs'σ : s' < σ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (Ψ (β' s')))) (hx'0 : 0 < x') {uph uc : ℂ → ℝ}
    {bph bc : ℝ} (huph : ∀ p : ℝ, 0 < p → p < chartAR W' σ → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bph))
    (huc : Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bc)) (a : ℝ) :
    Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) + a +
        chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) - couplingMean κ w t uc (fwdMapInv w t y))
      (𝓝[H] (x' : ℂ)) (𝓝 (bph + a - bc)) := by
  have hsh : Continuous fun s => Wph (r + s) - Wph r := by fun_prop
  have hK : fwdHull W' σ = fwdHull (fun s => Wph (r + s) - Wph r) σ :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hc.hW hsh hc.σ_nonneg fun s hs => hW'eq hs
  refine (hc.tendsto_slitMean_of_pos hs' hs'σ hx' hx'0 huph huc a (chiC κ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [chartReading_sub_couplingMean_eq κ hWph hWph0 hr hc.σ_nonneg hc.hw hc.hw0 hc.t_nonneg hinvD
    (fun y hy => hK ▸ hc.inv_fwdMapInv_mem hy) hlift uph uc a hy, thetaMap_congr hW'eq.symm,
    thetaLog_congr hW'eq.symm hc.σ_nonneg]

end D1Frozen

/-! ### (D2) -/

/-- **(D2), the boundary correspondence**: if `F(y) → c.1(z₀)` along `l` (e.g. `F = F_t`, `l = 𝓝[ℍ] x′`),
`c.1(z₀) ∈ ℍ` and `c.2.1 (c.1 z₀) = z₀`, then `inv(F(y)) → z₀`. -/
theorem tendsto_inv_comp_of_tendsto {c : Chart} (hc : c.IsConformal) {F : ℂ → ℂ} {z₀ : ℂ} {l : Filter ℂ}
    (hF : Tendsto F l (𝓝 (c.1 z₀))) (hH : c.1 z₀ ∈ H) (hinv : c.2.1 (c.1 z₀) = z₀) :
    Tendsto (fun y => c.2.1 (F y)) l (𝓝 z₀) := by
  have hcont : ContinuousAt c.2.1 (c.1 z₀) :=
    (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hH)).continuousAt
  have := hcont.tendsto.comp hF
  rwa [hinv] at this

/-- **(D2), the local inclusion**: if `z₀` lies in an open set `D` off a closed set `E`, and `A ∩ D ⊆ L ∪ E`, then
`A ∩ B(z₀, ε) ⊆ L` for some `ε > 0`. -/
theorem exists_ball_inter_subset_of_open {A L D E : Set ℂ} {z₀ : ℂ} (hD : IsOpen D) (hz₀D : z₀ ∈ D)
    (hE : IsClosed E) (hz₀E : z₀ ∉ E) (hA : A ∩ D ⊆ L ∪ E) : ∃ ε > 0, A ∩ ball z₀ ε ⊆ L := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 hD z₀ hz₀D
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.1 hE.isOpen_compl z₀ hz₀E
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz => ?_⟩
  rcases hA ⟨hz.1, h₁ (ball_subset_ball (min_le_left _ _) hz.2)⟩ with h | h
  · exact h
  · exact absurd h (h₂ (ball_subset_ball (min_le_right _ _) hz.2))

/-- **(D2) for a slit point**: a point `η(s)` of a curve injective on `[a, T]` and continuous on `[ρ, T]`, with
`a ≤ s < ρ ≤ T`, inside an open set `D` in which the union `A` is contained in the curve `η([a, T])`, has a ball in
which `A` is contained in `η([a, ρ])`. -/
theorem exists_ball_inter_subset_curve {A D : Set ℂ} {η : ℝ → ℂ} {a s ρ T : ℝ} (hD : IsOpen D) (hsD : η s ∈ D)
    (hcont : ContinuousOn η (Icc ρ T)) (hinj : InjOn η (Icc a T)) (has : a ≤ s) (hsρ : s < ρ) (hρT : ρ ≤ T)
    (hA : A ∩ D ⊆ η '' Icc a T) : ∃ ε > 0, A ∩ ball (η s) ε ⊆ η '' Icc a ρ := by
  have hE : IsClosed (η '' Icc ρ T) := (isCompact_Icc.image_of_continuousOn hcont).isClosed
  refine exists_ball_inter_subset_of_open hD hsD hE ?_ fun z hz => ?_
  · rintro ⟨u, hu, he⟩
    have := hinj ⟨(has.trans hsρ.le).trans hu.1, hu.2⟩ ⟨has, hsρ.le.trans hρT⟩ he
    linarith [hu.1]
  · obtain ⟨u, hu, rfl⟩ := hA hz
    rcases le_or_gt u ρ with h | h
    · exact Or.inl ⟨u, ⟨hu.1, h⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨h.le, hu.2⟩, rfl⟩

end InteractingSLE.Sec5.Aux61TwoS
