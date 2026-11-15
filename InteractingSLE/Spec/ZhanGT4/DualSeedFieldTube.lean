/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldBound

/-!
# Zhan's A.1.6, the seeded field VI: the tube around the driver, the generator and the drift

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38). PROVE-ZHAN-GT4-A19's Itô theorem for a drifted driver
(`IsDriftLogField.integral_mul_stopped_sub_eq_zero`, `DualSeedDrift`) asks for the regularity of the log-field on a
**tube** `{(t, x) : t ∈ [ε, S], |x − W_t| < 4ρ}` around the driver, a bounded continuous drift and the vanishing
drifted generator. This file derives these per path for the seeded density of `DualSeedField`:

* `tube_of_isLogField` (generic): log-fields on boxes centred at the driver around every time give the tube properties
  (derivatives, one-sided time derivative within `[ε, S]`, continuity on the tube, bounds);
* **`SeedData.tube_facts`**: on a cut-off piece `[ε, T]` (`SeedConst`, `SeedScaleOK`) the seeded log-density has the
  tube properties with radius `3 · cutRad r a₀ γ` and bound `4 · coefTot κ r · scaleBound L`;
* **`SeedData.gen_eq_zero_of_const`**: the drifted generator `∂_tℓ + b ∂_xℓ + (κ/2)(∂²_xℓ + (∂_xℓ)²)` vanishes at the
  driver (`b = drift`, the force-point drift);
* `SeedData.abs_drift_le`, `SeedData.continuousOn_drift`: the drift is bounded by `|κ| · coefTot κ r · scaleBound L`
  and continuous on `[ε, T]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- **Local log-fields give the tube properties.** If around every time `t ∈ [ε, S]` there is a neighbourhood
`[b, c]` (within `[ε, S]`) on which `ℓ` is a log-field centred at `W_t` with half-width `3ρ`, then on the tube of
radius `R₀ ≤ 3ρ` around `W` the field has its space derivatives, its time derivative within `[ε, S]`, the bounds, and
is continuous together with `ℓ_x`, `ℓ_xx`, `ℓ_t`. -/
theorem tube_of_isLogField {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {W : ℝ → ℝ} {ε S ρ K R₀ : ℝ} (hR₀ : R₀ ≤ 3 * ρ)
    (hloc : ∀ t ∈ Icc ε S, ∃ b c : ℝ, Icc b c ∈ 𝓝[Icc ε S] t ∧ t ∈ Icc b c ∧
      IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c (W t) ρ K) :
    (∀ p ∈ {p : ℝ × ℝ | p.1 ∈ Icc ε S ∧ |p.2 - W p.1| < R₀},
      HasDerivAt (ℓ p.1) (ℓx p.1 p.2) p.2 ∧ HasDerivAt (ℓx p.1) (ℓxx p.1 p.2) p.2 ∧
        HasDerivAt (ℓxx p.1) (ℓxxx p.1 p.2) p.2 ∧
        HasDerivWithinAt (fun s => ℓ s p.2) (ℓt p.1 p.2) (Icc ε S) p.1 ∧
        (|ℓ p.1 p.2| ≤ K ∧ |ℓx p.1 p.2| ≤ K ∧ |ℓxx p.1 p.2| ≤ K ∧ |ℓxxx p.1 p.2| ≤ K ∧ |ℓt p.1 p.2| ≤ K)) ∧
    ContinuousOn (fun p : ℝ × ℝ => ℓ p.1 p.2) {p : ℝ × ℝ | p.1 ∈ Icc ε S ∧ |p.2 - W p.1| < R₀} ∧
    ContinuousOn (fun p : ℝ × ℝ => ℓx p.1 p.2) {p : ℝ × ℝ | p.1 ∈ Icc ε S ∧ |p.2 - W p.1| < R₀} ∧
    ContinuousOn (fun p : ℝ × ℝ => ℓxx p.1 p.2) {p : ℝ × ℝ | p.1 ∈ Icc ε S ∧ |p.2 - W p.1| < R₀} ∧
    ContinuousOn (fun p : ℝ × ℝ => ℓt p.1 p.2) {p : ℝ × ℝ | p.1 ∈ Icc ε S ∧ |p.2 - W p.1| < R₀} := by
  set tube := {p : ℝ × ℝ | p.1 ∈ Icc ε S ∧ |p.2 - W p.1| < R₀} with htube
  -- the box around a tube point is a neighbourhood within the tube
  have hnb : ∀ p ∈ tube, ∀ b c : ℝ, Icc b c ∈ 𝓝[Icc ε S] p.1 →
      Icc b c ×ˢ {x : ℝ | |x - W p.1| < 3 * ρ} ∈ 𝓝[tube] p := fun p hp b c hbc => by
    have hsub : tube ⊆ Icc ε S ×ˢ univ := fun q hq => ⟨hq.1, mem_univ _⟩
    refine nhdsWithin_mono p hsub ?_
    rw [show p = (p.1, p.2) from rfl, nhdsWithin_prod_eq, nhdsWithin_univ]
    refine prod_mem_prod hbc ?_
    have ho : IsOpen {x : ℝ | |x - W p.1| < 3 * ρ} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    exact ho.mem_nhds (lt_of_lt_of_le hp.2 hR₀)
  have hcont : ∀ f : (ℝ → ℝ → ℝ), (∀ b c t, IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c (W t) ρ K →
      ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc b c ×ˢ {x | |x - W t| < 3 * ρ})) →
      ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) tube := fun f hf p hp => by
    obtain ⟨b, c, hbc, htb, hLF⟩ := hloc p.1 hp.1
    exact (hf b c p.1 hLF p ⟨htb, lt_of_lt_of_le hp.2 hR₀⟩).mono_of_mem_nhdsWithin (hnb p hp b c hbc)
  refine ⟨fun p hp => ?_, hcont ℓ fun b c t hLF => hLF.cont, hcont ℓx fun b c t hLF => hLF.contX,
    hcont ℓxx fun b c t hLF => hLF.contXX, hcont ℓt fun b c t hLF => hLF.contT⟩
  obtain ⟨b, c, hbc, htb, hLF⟩ := hloc p.1 hp.1
  have hx3 : |p.2 - W p.1| < 3 * ρ := lt_of_lt_of_le hp.2 hR₀
  exact ⟨hLF.dx p.1 htb p.2 hx3, hLF.dxx p.1 htb p.2 hx3, hLF.dxxx p.1 htb p.2 hx3,
    (hLF.dt p.1 htb p.2 hx3).mono_of_mem_nhdsWithin hbc, hLF.bound p.1 htb p.2 hx3⟩

/-- A time box `[max ε (t − η), min S (t + η)]` is a neighbourhood of `t` within `[ε, S]`. -/
theorem box_mem_nhdsWithin_Icc {ε S t η : ℝ} (hη : 0 < η) :
    Icc (max ε (t - η)) (min S (t + η)) ∈ 𝓝[Icc ε S] t :=
  mem_nhdsWithin.2 ⟨Ioo (t - η) (t + η), isOpen_Ioo, ⟨by linarith, by linarith⟩,
    fun x hx => ⟨max_le hx.2.1 hx.1.1.le, le_min hx.2.2 hx.1.2.le⟩⟩

namespace SeedData

variable {n : ℕ} (d : SeedData n) {A : Set ℂ} {ε T r a₀ γ Γ lam ρm L : ℝ}

/-- **The tube properties of the seeded log-density** on a cut-off piece `[ε, T]`: radius `3 · cutRad r a₀ γ`, bound
`4 · coefTot κ r · scaleBound L` (the deterministic inputs of `IsDriftLogField` along one path). -/
theorem tube_facts (h : OwnData d.W A d.φ T d.a d.W') {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀)
    (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam T L) (hε : 0 ≤ ε)
    (hV₀ : ∀ t ∈ Icc ε T, HasDerivWithinAt d.V₀ (2 / (d.V₀ t - d.W t)) (Icc ε T) t)
    (hG₀ : ∀ t ∈ Icc ε T, HasDerivWithinAt d.G₀ (-2 * d.G₀ t / (d.V₀ t - d.W t) ^ 2) (Icc ε T) t)
    (hV : ∀ m, ∀ t ∈ Icc ε T, HasDerivWithinAt (d.V m) (2 / (d.V m t - d.W t)) (Icc ε T) t)
    (hVc : ∀ m, ContinuousOn (d.V m) (Icc 0 T)) :
    (∀ p ∈ {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ},
      HasDerivAt (d.ell p.1) (d.ellX p.1 p.2) p.2 ∧ HasDerivAt (d.ellX p.1) (d.ellXX p.1 p.2) p.2 ∧
        HasDerivAt (d.ellXX p.1) (d.ellXXX p.1 p.2) p.2 ∧
        HasDerivWithinAt (fun s => d.ell s p.2) (d.ellT p.1 p.2) (Icc ε T) p.1 ∧
        (|d.ell p.1 p.2| ≤ 4 * (coefTot d.κ d.r * scaleBound L) ∧
          |d.ellX p.1 p.2| ≤ 4 * (coefTot d.κ d.r * scaleBound L) ∧
          |d.ellXX p.1 p.2| ≤ 4 * (coefTot d.κ d.r * scaleBound L) ∧
          |d.ellXXX p.1 p.2| ≤ 4 * (coefTot d.κ d.r * scaleBound L) ∧
          |d.ellT p.1 p.2| ≤ 4 * (coefTot d.κ d.r * scaleBound L))) ∧
    ContinuousOn (fun p : ℝ × ℝ => d.ell p.1 p.2) {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} ∧
    ContinuousOn (fun p : ℝ × ℝ => d.ellX p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} ∧
    ContinuousOn (fun p : ℝ × ℝ => d.ellXX p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} ∧
    ContinuousOn (fun p : ℝ × ℝ => d.ellT p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} := by
  have hρc := cutRad_pos hc.r0 hc.a0 hc.g0
  refine tube_of_isLogField le_rfl fun t ht => ?_
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuous_iff.1 h.cont t (cutRad r a₀ γ) hρc
  refine ⟨max ε (t - δ / 2), min T (t + δ / 2), box_mem_nhdsWithin_Icc (by positivity),
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩, ?_⟩
  have hJ : Icc (max ε (t - δ / 2)) (min T (t + δ / 2)) ⊆ Icc ε T := fun s hs =>
    ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
  refine d.isLogField_of_const h hv₀ hc hL hε hV₀ hG₀ hV hVc hJ fun s hs => ?_
  have h1 : t - δ / 2 ≤ s := (le_max_right _ _).trans hs.1
  have h2 : s ≤ t + δ / 2 := hs.2.trans (min_le_right _ _)
  have := hδW s (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rwa [Real.dist_eq] at this

/-- **The drifted generator of the seeded density vanishes at the driver** on `[ε, T]`. -/
theorem gen_eq_zero_of_const (h : OwnData d.W A d.φ T d.a d.W') (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hε : 0 ≤ ε)
    (hκ : d.κ ≠ 0) {t : ℝ} (ht : t ∈ Icc ε T) :
    d.ellT t (d.W t) + d.drift t * d.ellX t (d.W t) + d.κ / 2 * (d.ellXX t (d.W t) + d.ellX t (d.W t) ^ 2) = 0 := by
  have ht0 : t ∈ Icc (0 : ℝ) T := ⟨hε.trans ht.1, ht.2⟩
  have hJ : Icc t t ⊆ Icc 0 T := fun s hs => by rw [Icc_self, mem_singleton_iff] at hs; rw [hs]; exact ht0
  have hWy : ∀ s ∈ Icc t t, |d.W s - d.W t| < clrRad r a₀ / 24 := fun s hs => by
    rw [Icc_self, mem_singleton_iff] at hs
    rw [hs, sub_self, abs_zero]
    have := clrRad_pos hc.r0 hc.a0
    positivity
  obtain ⟨hdisj, hWm, hq0, -⟩ := h.box_of_clearance hc.r0 hc.a0 hc.clr hc.A1 hJ hWy
  have htt : t ∈ Icc t t := left_mem_Icc.2 le_rfl
  have hD2 := h.re_dHat_drive hJ hdisj hWm hq0 htt
  have hnt := d.timeNd_of_const hc ht
  have hA1 : d.A 1 t ≠ 0 := (h.frzA_one_pos ht0).ne'
  have h21 : d.A21 t ≠ 0 := ne_zero_of_inScale (hc.A21 t ht)
  have hE0 : d.A 0 t - d.A20 t ≠ 0 := ne_zero_of_le_abs hc.g0 (by rw [abs_sub_comm]; exact (hc.E0 t ht).1)
  have hE : ∀ m, d.A 0 t - d.B0 t m ≠ 0 := fun m =>
    ne_zero_of_le_abs hc.g0 (by rw [abs_sub_comm]; exact (hc.Em t ht m).1)
  have hE0' : d.W t - d.V₀ t ≠ 0 := ne_zero_of_le_abs hc.g0 (by rw [abs_sub_comm]; exact (hc.O0 t ht).1)
  have hE' : ∀ m, d.W t - d.V m t ≠ 0 := fun m =>
    ne_zero_of_le_abs hc.g0 (by rw [abs_sub_comm]; exact (hc.Om t ht m).1)
  exact d.gen_eq_zero_of_D2 hκ hD2 hA1 h21 hnt.B1 hE0 hE hnt.A2B hnt.BB hE0' hE' hnt.V₀V hnt.VV

/-- **The drift is bounded** on `[ε, T]`: `|b_t| ≤ |κ| · coefTot κ r · scaleBound L`. -/
theorem abs_drift_le (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam T L) {t : ℝ}
    (ht : t ∈ Icc ε T) : |d.drift t| ≤ |d.κ| * (coefTot d.κ d.r * scaleBound L) := by
  have hγ := hc.g0
  have hB := hL.base
  have hL0 := hB.L0
  have hlo : Real.exp (-L) ≤ γ := hB.g.trans (by linarith)
  have hhi : Γ ≤ Real.exp L := le_trans (by linarith) hB.G
  have h0 : |(0 : ℝ)| ≤ Real.exp L := by rw [abs_zero]; exact (Real.exp_pos _).le
  have sV₀ : InScale L (d.W t - d.V₀ t) := by
    refine FrzData.inScale_of_le hlo hhi ?_
    rw [abs_sub_comm]; exact hc.O0 t ht
  have sV : ∀ m, InScale L (d.W t - d.Vv t m) := fun m => by
    refine FrzData.inScale_of_le hlo hhi ?_
    rw [abs_sub_comm]; exact hc.Om t ht m
  obtain ⟨-, z1, -, -, -⟩ := abs_dualLogSpace_le (κ := d.κ) (r := d.r) (f := d.W t) (f1 := 1) (f2 := 0) (f3 := 0)
    (f4 := 0) (A0 := d.V₀ t) (B0 := d.Vv t) (df := 0) (df1 := 0) (dA0 := 0) (dB0 := fun _ => 0) hL0
    (inScale_one hL0) sV₀ sV h0 h0 h0 h0 h0 h0 fun _ => h0
  rw [drift, abs_mul]
  exact mul_le_mul_of_nonneg_left z1 (abs_nonneg _)

/-- **The drift is continuous** on `[ε, T]` (given the force ODE of the marks there). -/
theorem continuousOn_drift (h : OwnData d.W A d.φ T d.a d.W') (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hV₀ : ∀ t ∈ Icc ε T, HasDerivWithinAt d.V₀ (2 / (d.V₀ t - d.W t)) (Icc ε T) t)
    (hV : ∀ m, ∀ t ∈ Icc ε T, HasDerivWithinAt (d.V m) (2 / (d.V m t - d.W t)) (Icc ε T) t) :
    ContinuousOn d.drift (Icc ε T) := by
  have cV₀ : ContinuousOn d.V₀ (Icc ε T) := fun t ht => (hV₀ t ht).continuousWithinAt
  have cV : ∀ m, ContinuousOn (fun t => d.Vv t m) (Icc ε T) := fun m t ht => (hV m t ht).continuousWithinAt
  have hx : ContinuousOn d.W (Icc ε T) := h.cont.continuousOn
  exact continuousOn_const.mul (continuousOn_dualLogSpaceX (f := d.W) (f1 := fun _ => (1 : ℝ))
    (f2 := fun _ => (0 : ℝ)) (A0 := d.V₀) (B0 := d.Vv) hx continuousOn_const continuousOn_const cV₀ cV
    (fun _ _ => one_ne_zero)
    (fun t ht => ne_zero_of_le_abs hc.g0 (by rw [abs_sub_comm]; exact (hc.O0 t ht).1))
    (fun t ht m => ne_zero_of_le_abs hc.g0 (by rw [abs_sub_comm]; exact (hc.Om t ht m).1)))

end SeedData

end InteractingSLE.ZhanGT4
