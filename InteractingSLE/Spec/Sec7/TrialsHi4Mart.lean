/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi4Gen

/-!
# The critical side oscillation: spreads, the localized martingale, and the exit after a time `q`

Packet PROVE-TRIALS-HI4. Tools for the Lyapunov argument of `TrialsHi4Osc`:

* the right spread `V^{R,j} − V^{R,0}` is nonincreasing in time (`vR_sub_vR_antitone`) and stays positive while the
  nearest right mark is not hit (`vR_lt_vR_of_pos`: `d(Δ e^{Kt}) ≥ 0` with `K = 2/m²`, `m` the minimum of the nearest
  gap);
* the localized Itô martingale `Φ(Λ_{t∧σ_n}) − ∫₀^{t∧σ_n} itoGen Φ` of an arbitrary `C³` function `Φ` of the
  coordinates (`genMart`, `martingale_genMart`, `continuous_genMart`, `genMart_eq`);
* the first time after `q` at which the right spread reaches the nearest right gap or falls to a level `e`
  (`critExit`, a stopping time), with its attainment properties.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi4

open Zhan Clock ZhanGT4 TrialsHi3

/-! ### Right spreads -/

section Spread

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Right spreads are nonincreasing in time**: for `i ≤ j` and `t₁ ≤ t₂ < ζ`,
`V^{R,j}_{t₂} − V^{R,i}_{t₂} ≤ V^{R,j}_{t₁} − V^{R,i}_{t₁}`. -/
theorem vR_sub_vR_antitone (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {i j : Fin (nR + 1)}
    (hij : i ≤ j) {t₁ t₂ : ℝ≥0} (h12 : t₁ ≤ t₂) (ht₂ : (t₂ : ℝ≥0∞) < ζ) :
    vR j t₂ - vR i t₂ ≤ vR j t₁ - vR i t₁ := by
  have hf := hp.isForcePath
  have ht₁ : (t₁ : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast h12) ht₂
  have hj := hf.intervalIntegrable_forceR ht₂ j
  have hi := hf.intervalIntegrable_forceR ht₂ i
  have hj1 := hf.intervalIntegrable_forceR ht₁ j
  have hi1 := hf.intervalIntegrable_forceR ht₁ i
  have hsub : ∀ {f : ℝ → ℝ}, IntervalIntegrable f volume 0 t₂ → IntervalIntegrable f volume t₁ t₂ := fun hf' =>
    hf'.mono_set (by
      rw [uIcc_of_le (by exact_mod_cast h12 : (t₁ : ℝ) ≤ t₂), uIcc_of_le t₂.coe_nonneg]
      exact Icc_subset_Icc_left t₁.coe_nonneg)
  have key : (vR j t₂ - vR i t₂) - (vR j t₁ - vR i t₁) = ∫ s in (t₁ : ℝ)..t₂,
      (2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i s.toNNReal - w s.toNNReal)) := by
    rw [intervalIntegral.integral_sub (hsub hj) (hsub hi), hf.vR_eq ht₂ i, hf.vR_eq ht₂ j, hf.vR_eq ht₁ i,
      hf.vR_eq ht₁ j, ← intervalIntegral.integral_interval_sub_left hj hj1,
      ← intervalIntegral.integral_interval_sub_left hi hi1]
    ring
  have hae : (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i s.toNNReal - w s.toNNReal)) ≤ᵐ[
      volume.restrict (Icc (t₁ : ℝ) t₂)] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hf.volume_collisionR i)] with s hs hsI
    have hs0 : 0 ≤ s := t₁.coe_nonneg.trans hsI.1
    have hlt : (s.toNNReal : ℝ≥0∞) < ζ :=
      lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hsI.2) ht₂
    have hne : w s.toNNReal ≠ vR i s.toNNReal := fun he => hs ⟨hs0, hlt, he⟩
    have hpos : 0 < vR i s.toNNReal - w s.toNNReal := sub_pos.2 (lt_of_le_of_ne (hf.w_le_vR hlt i) hne)
    have hpq : vR i s.toNNReal - w s.toNNReal ≤ vR j s.toNNReal - w s.toNNReal :=
      sub_le_sub_right (hf.monotone_vR hlt hij) _
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hpos hpq
    linarith
  have hle := intervalIntegral.integral_mono_ae_restrict (by exact_mod_cast h12) ((hsub hj).sub (hsub hi))
    intervalIntegrable_const hae
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hle
  linarith

/-- **Distinct right marks stay distinct while the nearest one is not hit**: if `x^{R,0} < x^{R,j}` and the nearest
right gap is positive on `[0, t]`, `t < ζ`, then `V^{R,0}_t < V^{R,j}_t`. -/
theorem vR_lt_vR_of_pos (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {j : Fin (nR + 1)}
    (h0j : xR 0 < xR j) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hpos : ∀ s ≤ t, w s < vR 0 s) :
    vR 0 t < vR j t := by
  have hf := hp.isForcePath
  have hlt : ∀ s : ℝ≥0, s ≤ t → (s : ℝ≥0∞) < ζ := fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) ht
  -- the minimum of the nearest gap on `[0, t]`
  have hc0 : ContinuousOn (fun s => vR 0 s - w s) (Icc 0 t) :=
    ((hf.continuousOn_vR 0).sub hf.continuousOn_w).mono fun s hs => hlt s hs.2
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_continuousOn_Icc hc0 fun s hs => sub_pos.2 (hpos s hs.2)
  set K : ℝ := 2 / m ^ 2 with hK
  -- real-time functions
  set Δr : ℝ → ℝ := fun u => vR j u.toNNReal - vR 0 u.toNNReal with hΔr
  set φ : ℝ → ℝ := fun u => 2 / (vR j u.toNNReal - w u.toNNReal) - 2 / (vR 0 u.toNNReal - w u.toNNReal)
    with hφ
  have hR0 : ∀ u ∈ Icc (0 : ℝ) t, m ≤ vR 0 u.toNNReal - w u.toNNReal := fun u hu =>
    hmle u.toNNReal ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hu.2⟩
  have hX : ∀ u ∈ Icc (0 : ℝ) t, vR 0 u.toNNReal - w u.toNNReal ≤ vR j u.toNNReal - w u.toNNReal := fun u hu =>
    sub_le_sub_right (hf.monotone_vR (hlt _ (Real.toNNReal_le_iff_le_coe.2 hu.2)) (Fin.zero_le j)) _
  have hΔ0 : ∀ u ∈ Icc (0 : ℝ) t, 0 ≤ Δr u := fun u hu => sub_nonneg.2
    (hf.monotone_vR (hlt _ (Real.toNNReal_le_iff_le_coe.2 hu.2)) (Fin.zero_le j))
  -- continuity on `[0, t]`
  have hmaps : MapsTo (fun u : ℝ => u.toNNReal) (Icc (0 : ℝ) t) (Icc 0 t) := fun u hu =>
    ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hu.2⟩
  have hcR : ∀ i, ContinuousOn (fun u : ℝ => vR i u.toNNReal) (Icc (0 : ℝ) t) := fun i =>
    (((hf.continuousOn_vR i).mono fun s hs => hlt s hs.2)).comp continuous_real_toNNReal.continuousOn hmaps
  have hcW : ContinuousOn (fun u : ℝ => w u.toNNReal) (Icc (0 : ℝ) t) :=
    ((hf.continuousOn_w.mono fun s hs => hlt s hs.2)).comp continuous_real_toNNReal.continuousOn hmaps
  have hcΔ : ContinuousOn Δr (Icc (0 : ℝ) t) := (hcR j).sub (hcR 0)
  have hcφ : ContinuousOn φ (Icc (0 : ℝ) t) := by
    refine ((continuousOn_const.div ((hcR j).sub hcW) fun u hu => ?_).sub
      (continuousOn_const.div ((hcR 0).sub hcW) fun u hu => ?_))
    · have h1 := hR0 u hu; have h2 := hX u hu
      exact ne_of_gt (by simp only [Pi.sub_apply]; linarith)
    · have h1 := hR0 u hu
      exact ne_of_gt (by linarith)
  -- the integral identity
  have hint : ∀ u ∈ Icc (0 : ℝ) t, Δr u = (xR j - xR 0) + ∫ v in (0 : ℝ)..u, φ v := by
    intro u hu
    have hut := hlt _ (Real.toNNReal_le_iff_le_coe.2 hu.2)
    have hu' : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu.1
    have hj := hf.intervalIntegrable_forceR hut j
    have hi := hf.intervalIntegrable_forceR hut 0
    rw [hu'] at hj hi
    simp only [hΔr, hφ]
    rw [intervalIntegral.integral_sub hj hi, hf.vR_eq hut j, hf.vR_eq hut 0, hu']
    ring
  -- `g = Δ e^{Ku}` is monotone on `[0, t]`
  set g : ℝ → ℝ := fun u => Δr u * Real.exp (K * u) with hg
  have hgc : ContinuousOn g (Icc (0 : ℝ) t) := hcΔ.mul (Real.continuous_exp.comp (continuous_const.mul
    continuous_id)).continuousOn
  have hderiv : ∀ u ∈ interior (Icc (0 : ℝ) t), HasDerivWithinAt g
      (φ u * Real.exp (K * u) + Δr u * (Real.exp (K * u) * K)) (interior (Icc (0 : ℝ) t)) u := by
    intro u hu
    rw [interior_Icc] at hu
    have hIcc : Icc (0 : ℝ) t ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have hφu : ContinuousAt φ u := hcφ.continuousAt hIcc
    have hφi : IntervalIntegrable φ volume 0 u :=
      (hcφ.mono (by rw [uIcc_of_le hu.1.le]; exact Icc_subset_Icc_right hu.2.le)).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter φ (𝓝 u) :=
      (hcφ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu
    have hF : HasDerivAt (fun v => (xR j - xR 0) + ∫ x in (0 : ℝ)..v, φ x) (φ u) u :=
      (intervalIntegral.integral_hasDerivAt_right hφi hmeas hφu).const_add _
    have hΔd : HasDerivAt Δr (φ u) u := hF.congr_of_eventuallyEq
      (Filter.eventually_of_mem hIcc fun v hv => hint v hv)
    have hE : HasDerivAt (fun v : ℝ => Real.exp (K * v)) (Real.exp (K * u) * K) u := by
      simpa using ((hasDerivAt_id u).const_mul K).exp
    exact (hΔd.mul hE).hasDerivWithinAt
  have hnn : ∀ u ∈ interior (Icc (0 : ℝ) t), 0 ≤ φ u * Real.exp (K * u) + Δr u * (Real.exp (K * u) * K) := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) t := interior_subset hu
    have hE : 0 < Real.exp (K * u) := Real.exp_pos _
    have hR := hR0 u hu'
    have hXu := hX u hu'
    have hΔu := hΔ0 u hu'
    -- `φ = −2Δ/(R₀ X) ≥ −K Δ`
    have hm0 : 0 < m := hm
    have hR0p : 0 < vR 0 u.toNNReal - w u.toNNReal := hm0.trans_le hR
    have hXp : 0 < vR j u.toNNReal - w u.toNNReal := hR0p.trans_le hXu
    have hφe : φ u = -(2 * Δr u / ((vR 0 u.toNNReal - w u.toNNReal) * (vR j u.toNNReal - w u.toNNReal))) := by
      simp only [hφ, hΔr]
      field_simp
      ring
    have hprod : m ^ 2 ≤ (vR 0 u.toNNReal - w u.toNNReal) * (vR j u.toNNReal - w u.toNNReal) := by
      rw [sq]; exact mul_le_mul hR (hR.trans hXu) hm0.le hR0p.le
    have hbound : 2 * Δr u / ((vR 0 u.toNNReal - w u.toNNReal) * (vR j u.toNNReal - w u.toNNReal)) ≤
        K * Δr u := by
      rw [hK, div_le_iff₀ (by positivity)]
      have : 2 * Δr u * m ^ 2 ≤ 2 * Δr u * ((vR 0 u.toNNReal - w u.toNNReal) * (vR j u.toNNReal - w u.toNNReal)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      calc 2 * Δr u = 2 / m ^ 2 * Δr u * m ^ 2 := by field_simp
        _ ≤ 2 / m ^ 2 * Δr u * ((vR 0 u.toNNReal - w u.toNNReal) * (vR j u.toNNReal - w u.toNNReal)) := by
            have h2 : 0 ≤ 2 / m ^ 2 * Δr u := by positivity
            exact mul_le_mul_of_nonneg_left hprod h2
    rw [hφe]
    have : 0 ≤ (K * Δr u - 2 * Δr u / ((vR 0 u.toNNReal - w u.toNNReal) * (vR j u.toNNReal - w u.toNNReal))) *
        Real.exp (K * u) := mul_nonneg (by linarith) hE.le
    linarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) t) hgc hderiv hnn
  have h0t := hmono ⟨le_rfl, t.coe_nonneg⟩ ⟨t.coe_nonneg, le_rfl⟩ t.coe_nonneg
  have hg0 : g 0 = xR j - xR 0 := by
    simp only [hg, hΔr, mul_zero, Real.exp_zero, mul_one, Real.toNNReal_zero, hf.vR_zero]
  rw [hg0] at h0t
  have hgt : g t = (vR j t - vR 0 t) * Real.exp (K * t) := by simp [hg, hΔr]
  rw [hgt] at h0t
  have hpos' : 0 < (vR j t - vR 0 t) * Real.exp (K * t) := lt_of_lt_of_le (sub_pos.2 h0j) h0t
  have := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 hpos'
  linarith

end Spread

/-! ### The localized Itô martingale of a `C³` function of the coordinates -/

section Mart

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The localized Itô martingale** of a function `Φ` of the coordinates (no extra coordinate). -/
def genMart (Φ : SCoord nL (nR + 1) × ℝ → ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω)
    (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Φ (coordA xL xR G VL VR (fun _ _ => 0) (min t (angLoc G T W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
      Ito.itoGen Φ (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hE hGm hGc hgood hT hx in
theorem martingale_genMart {Φ : SCoord nL (nR + 1) × ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (n : ℕ) :
    Martingale (genMart Φ xL xR G T W VL VR B ζ n) (usualAugmentation 𝓕 P) P :=
  martingale_angLoc hE hGm hGc hgood hT hx hΦ.contDiffOn n
    (I := fun _ _ => 0) (c := fun _ _ => 0) (KI := 0) (Kc := 0) (fun _ _ _ _ => by simp)
    (fun _ _ => intervalIntegrable_const) (fun _ _ => by simp) (fun _ _ _ _ => by simp)
    ⟨fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ => rfl⟩ (fun _ _ => continuousOn_const)

omit hE hGm hGc hT hx in
theorem genMart_min (Φ : SCoord nL (nR + 1) × ℝ → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    genMart Φ xL xR G T W VL VR B ζ n t ω =
      genMart Φ xL xR G T W VL VR B ζ n (min t (angLoc G T W VL VR B ζ n ω)) ω := by
  simp only [genMart, min_assoc, min_self]

include hgood in
omit hE hGm hGc hT hx in
theorem intervalIntegrable_genMart {Φ : SCoord nL (nR + 1) × ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (n : ℕ) {ω : Ω}
    (hω : ω ∈ G) :
    IntervalIntegrable (fun s : ℝ => Ito.itoGen Φ
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)) volume 0 (angLoc G T W VL VR B ζ n ω) := by
  have hω' := hgood ω hω
  have hF := hω'.1.isForcePath
  set σ := angLoc G T W VL VR B ζ n ω
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hpath : ContinuousOn (fun s : ℝ => pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
      s.toNNReal) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]
    have hm := mapsTo_toNNReal (ζ := ζ ω) hσζ
    refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ continuousOn_const)) ?_
    · exact continuousOn_pi.2 fun i =>
        (hF.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn hm
    · exact continuousOn_pi.2 fun j =>
        (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hm
    · exact (hω'.2.1.comp continuous_real_toNNReal).continuousOn
  have hPFc : Continuous (Ito.partialFst Φ) := (hΦ.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hF1 : ContDiff ℝ 2 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hPSSc : Continuous (Ito.partialSndSnd Φ) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hlam : IntervalIntegrable (fun s : ℝ => angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω)
      (fun j => VR j s.toNNReal ω) (0 : ℝ)) volume 0 σ :=
    intervalIntegrable_scoord (fun i => hF.intervalIntegrable_forceL hσζ i)
      (fun j => hF.intervalIntegrable_forceR hσζ j) intervalIntegrable_const
  have h := (Ito.intervalIntegrable_clm_apply (hPFc.comp_continuousOn hpath) hlam).add
    ((hPSSc.comp_continuousOn hpath).intervalIntegrable.const_mul (1 / 2))
  refine h.congr fun s _ => ?_
  simp only [Function.comp_apply, coord_eq_pathCoord hω, densA_eq_angDens hω, Ito.itoGen]

include hgood in
omit hE hGm hGc hT hx in
/-- **The martingale is continuous in time.** -/
theorem continuous_genMart {Φ : SCoord nL (nR + 1) × ℝ → ℝ} (hΦ : ContDiff ℝ 3 Φ) (n : ℕ) (ω : Ω) :
    Continuous fun t => genMart Φ xL xR G T W VL VR B ζ n t ω := by
  by_cases hω : ω ∈ G
  · have hω' := hgood ω hω
    have hF := hω'.1.isForcePath
    set σ := angLoc G T W VL VR B ζ n ω with hσdef
    have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
    have hgi := intervalIntegrable_genMart hgood hΦ n hω (κ := κ) (xL := xL) (xR := xR)
      (ρL := ρL) (ρR := ρR) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ)
    have hinner : Continuous fun t : ℝ≥0 => ((min t σ : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_id.min continuous_const)
    have hmaps : ∀ t : ℝ≥0, ((min t σ : ℝ≥0) : ℝ) ∈ Icc 0 (σ : ℝ) := fun t =>
      ⟨(min t σ).coe_nonneg, by exact_mod_cast min_le_right t σ⟩
    have hpath : ContinuousOn (fun s : ℝ => pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
        s.toNNReal) (Icc 0 (σ : ℝ)) := by
      have hm := mapsTo_toNNReal (ζ := ζ ω) hσζ
      refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ continuousOn_const)) ?_
      · exact continuousOn_pi.2 fun i =>
          (hF.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn hm
      · exact continuousOn_pi.2 fun j =>
          (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hm
      · exact (hω'.2.1.comp continuous_real_toNNReal).continuousOn
    have hA : ContinuousOn (fun s : ℝ => Φ
        (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 s.toNNReal)) (Icc 0 (σ : ℝ)) :=
      hΦ.continuous.comp_continuousOn hpath
    have hI : ContinuousOn (fun x : ℝ => ∫ s in (0 : ℝ)..x, Ito.itoGen Φ
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)) (Icc 0 (σ : ℝ)) := by
      have h := intervalIntegral.continuousOn_primitive_interval ((intervalIntegrable_iff').1 hgi)
      rwa [uIcc_of_le σ.coe_nonneg] at h
    have hcomp := (hA.sub hI).comp_continuous hinner hmaps
    refine hcomp.congr fun t => ?_
    simp only [genMart, Function.comp_apply, Pi.sub_apply, Real.toNNReal_coe, ← hσdef, coord_eq_pathCoord hω]
  · have h0 : angLoc G T W VL VR B ζ n ω = 0 := angLoc_of_not_mem hω n
    simp only [genMart, h0, min_zero]
    exact continuous_const

omit hE hGm hGc hT hx in
/-- **The martingale along a good path** at a time `r ≤ σ_n`. -/
theorem genMart_eq (Φ : SCoord nL (nR + 1) × ℝ → ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ G) (r : ℝ≥0)
    (hr : r ≤ angLoc G T W VL VR B ζ n ω) :
    genMart Φ xL xR G T W VL VR B ζ n r ω =
      Φ (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 r) -
        ∫ s in (0 : ℝ)..(r : ℝ), Ito.itoGen Φ
          (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 s.toNNReal)
          (angDens (W s.toNNReal ω) (fun i => VL i s.toNNReal ω) (fun j => VR j s.toNNReal ω) 0) := by
  simp only [genMart, min_eq_left hr, coord_eq_pathCoord hω, densA_eq_angDens hω]

end Mart

/-! ### The exit after `q` from the region `{e < Δ < R₀}` -/

section Exit

variable {nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The level of `(W, V^{R,0}, V^{R,last})`: positive iff `e < Δ < R₀` (`Δ = V^{R,last} − V^{R,0}`,
`R₀ = V^{R,0} − W`). -/
def critLev (e : ℝ) (p : ℝ × ℝ × ℝ) : ℝ := min ((p.2.1 - p.1) - (p.2.2 - p.2.1)) ((p.2.2 - p.2.1) - e)

theorem continuous_critLev (e : ℝ) : Continuous (critLev e) := by unfold critLev; fun_prop

theorem critLev_pos_iff {e : ℝ} {p : ℝ × ℝ × ℝ} :
    0 < critLev e p ↔ p.2.2 - p.2.1 < p.2.1 - p.1 ∧ e < p.2.2 - p.2.1 := by
  simp only [critLev, lt_min_iff, sub_pos]

/-- **The test after `q`**: `max(critLev e (W, V^{R,0}, V^{R,last}), q − t)`. -/
def critTest (e : ℝ) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => max (critLev e (W t ω, VR 0 t ω, VR (Fin.last nR) t ω)) ((q : ℝ) - t)

/-- **The first exit after `q`** from `{e < Δ < R₀}` before the lifetime (`0` on `N`). -/
def critExit (N : Set Ω) (ζ : Ω → ℝ≥0∞) (e : ℝ) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  zeroOn N (firstMeet zeroProc (critTest e q W VR) ζ) ω

variable {N : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {e : ℝ} {q : ℝ≥0}

theorem continuousOn_critTest {ω : Ω} (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (h0 : ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (h1 : ContinuousOn (fun t => VR (Fin.last nR) t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    ContinuousOn (fun t => critTest e q W VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  simp only [critTest, zeroProc, sub_zero]
  exact continuous_max.comp_continuousOn (((continuous_critLev e).comp_continuousOn
    (hW.prodMk (h0.prodMk h1))).prodMk (continuousOn_const.sub NNReal.continuous_coe.continuousOn))

/-- **The exit is a stopping time.** -/
theorem isStoppingTime_critExit {𝓖 : Filtration ℝ≥0 mΩ} (hW : AdaptedBefore 𝓖 ζ W)
    (h0 : AdaptedBefore 𝓖 ζ (VR 0)) (h1 : AdaptedBefore 𝓖 ζ (VR (Fin.last nR)))
    (hN : ∀ t, MeasurableSet[𝓖 t] N)
    (hc : ∀ ω ∉ N, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR (Fin.last nR) t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsStoppingTime 𝓖 fun ω => (critExit N ζ e q W VR ω : WithTop ℝ≥0) := by
  have hYa : AdaptedBefore 𝓖 ζ (critTest e q W VR) :=
    adaptedBefore_of_eq (fun t p => max (critLev e p) ((q : ℝ) - t))
      (fun t => ((continuous_critLev e).max continuous_const).measurable) hW h0 h1 fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hW h0 h1 fun _ _ => rfl
  exact isStoppingTime_firstMeet_off hZa hYa hN fun ω hω =>
    continuousOn_critTest (hc ω hω).1 (hc ω hω).2.1 (hc ω hω).2.2

/-- Before the exit and after `q`, the level is positive. -/
theorem pos_of_lt_critExit {ω : Ω} (hω : ω ∉ N) {t : ℝ≥0} (hqt : q ≤ t)
    (ht : (t : ℝ≥0∞) < critExit N ζ e q W VR ω) :
    (t : ℝ≥0∞) < ζ ω ∧ 0 < critLev e (W t ω, VR 0 t ω, VR (Fin.last nR) t ω) := by
  rw [critExit, zeroOn_of_notMem hω] at ht
  have h := lt_of_lt_firstMeet ht
  simp only [critTest, zeroProc, lt_max_iff] at h
  rcases h.2 with h' | h'
  · exact ⟨h.1, h'⟩
  · exact absurd h' (not_lt.2 (sub_nonpos.2 (NNReal.coe_le_coe.2 hqt)))

/-- The exit is not before `q`, nor after the lifetime. -/
theorem le_critExit {ω : Ω} (hω : ω ∉ N) (hq : (q : ℝ≥0∞) < ζ ω) : (q : ℝ≥0∞) ≤ critExit N ζ e q W VR ω := by
  rw [critExit, zeroOn_of_notMem hω]
  refine le_inf hq.le (le_iInf₂ fun t ht => ?_)
  by_contra hlt
  push Not at hlt
  have hlt' : (t : ℝ) < q := by exact_mod_cast hlt
  have := ht.2
  simp only [critTest, zeroProc, max_le_iff] at this
  linarith [this.2]

theorem critExit_le_lifetime {ω : Ω} (hω : ω ∉ N) : critExit N ζ e q W VR ω ≤ ζ ω := by
  rw [critExit, zeroOn_of_notMem hω]; exact firstMeet_le_lifetime

/-- If the level is positive on `[q, t]`, `t < ζ`, the exit is after `t`. -/
theorem lt_critExit_of_forall {ω : Ω} (hω : ω ∉ N)
    (hc : ContinuousOn (fun t => critTest e q W VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ ω)
    (h : ∀ s, q ≤ s → s ≤ t → 0 < critLev e (W s ω, VR 0 s ω, VR (Fin.last nR) s ω)) :
    (t : ℝ≥0∞) < critExit N ζ e q W VR ω := by
  rw [critExit, zeroOn_of_notMem hω]
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨m, hm, -, hmle⟩ := exists_eq_firstMeet hc (hle.trans_lt htζ)
  have hmt : m ≤ t := by rw [hm] at hle; exact_mod_cast hle
  simp only [critTest, zeroProc, max_le_iff] at hmle
  have hqm : q ≤ m := by
    have : (q : ℝ) ≤ m := by linarith [hmle.2]
    exact_mod_cast this
  have := h m hqm hmt
  linarith [hmle.1]

/-- **At a finite exit before `ζ`**, the exit time `m` has `q ≤ m`, level `≤ 0`, and level `≥ 0` if `q < m`. -/
theorem critLev_critExit {ω : Ω} (hω : ω ∉ N)
    (hc : ContinuousOn (fun t => critTest e q W VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hlev : ContinuousOn (fun t => critLev e (W t ω, VR 0 t ω, VR (Fin.last nR) t ω)) {t | (t : ℝ≥0∞) < ζ ω})
    (hlt : critExit N ζ e q W VR ω < ζ ω) :
    ∃ m : ℝ≥0, critExit N ζ e q W VR ω = m ∧ (m : ℝ≥0∞) < ζ ω ∧ q ≤ m ∧
      critLev e (W m ω, VR 0 m ω, VR (Fin.last nR) m ω) ≤ 0 ∧
      (q < m → 0 ≤ critLev e (W m ω, VR 0 m ω, VR (Fin.last nR) m ω)) := by
  have hlt' := hlt
  rw [critExit, zeroOn_of_notMem hω] at hlt'
  obtain ⟨m, hm, hmζ, hmle⟩ := exists_eq_firstMeet hc hlt'
  simp only [critTest, zeroProc, max_le_iff] at hmle
  have hqm : q ≤ m := by
    have : (q : ℝ) ≤ m := by linarith [hmle.2]
    exact_mod_cast this
  have hex : critExit N ζ e q W VR ω = m := by rw [critExit, zeroOn_of_notMem hω, hm]
  refine ⟨m, hex, hmζ, hqm, hmle.1, fun hqm' => ?_⟩
  -- left limit of positive values
  have hca : ContinuousWithinAt (fun t => critLev e (W t ω, VR 0 t ω, VR (Fin.last nR) t ω)) (Ioo q m) m :=
    ((hlev.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hmζ)).continuousWithinAt)
  have hne : (𝓝[Ioo q m] m).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hqm'.ne]
    exact ⟨hqm'.le, le_rfl⟩
  refine ge_of_tendsto hca (eventually_nhdsWithin_of_forall fun t ht => ?_)
  have htm : (t : ℝ≥0∞) < critExit N ζ e q W VR ω := by rw [hex]; exact_mod_cast ht.2
  exact (pos_of_lt_critExit hω ht.1.le htm).2.le

end Exit

end TrialsHi4

end Sec7

end InteractingSLE
