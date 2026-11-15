/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcAssembly

/-!
# Zhan's A.1, G3: the pathwise half of a G3 source column

Packet PROVE-A1-G3CALC (R48). A1-EIGHTSEED's `IsColumnStoch` asks, besides Brownian, adaptedness and measurability
clauses, for two pathwise clauses: the record's driver is `√κ̂ B + D`, and `D` has the record's force-point drift as
derivative on `(0, S]`. For the G3 records with `B = B₁` (the small marginal's Brownian motion) and
`D = W^{stop} − √κ̂ B₁` both follow from the path relation of the small marginal: on `(0, S]`, `D` is the sum of the
drift integrals `∫ ρ/(w − v)` (`w_eq`), whose derivative is the path drift (fundamental theorem of calculus at
positive times), and the path drift is the record's drift (`drift_fromSource_eq_three`; the other source's force
point is its real flow, `fwdMap_add_eq_force`).

## Main results

* `hasDerivWithinAt_integral_gap`, **`hasDerivWithinAt_pathDrift`**: for an integrated `SLE_a(ρ)` path, `w − √a b` has
  derivative `Σ ρ_L/(w − v_L) + Σ ρ_R/(w − v_R)` within `(0, S]` at every positive time when no force point meets the
  driver on `(0, S]`;
* `eightDrv_toNNReal`, **`g3Rec_W_eq_driftDriver`**: the record's driver is `driftDriver √κ̂ B₁ D`;
* **`hasDerivWithinAt_g3Rec_drift`**: `D` has the G3 record's drift as derivative on `(0, S]`;
* **`isColumnStoch_g3Rec`**: A1-EIGHTSEED's `IsColumnStoch` for the G3 records from the Brownian and measurability
  inputs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (fwdMap fwdHull)
open InteractingSLE.ZhanGT4 A1SeedField A1EightSeed A2X

/-! ### The drift of an integrated path -/

/-- **A drift integral has its integrand as derivative at positive times**: for `w`, `v` continuous before the
lifetime, `(w − v)⁻¹` integrable, and `v ≠ w` on `(0, S]`, `u ↦ ∫₀ᵘ ρ/(w − v)` has derivative `ρ/(w t − v t)` within
`(0, S]` at every `t ∈ (0, S]`. -/
theorem hasDerivWithinAt_integral_gap {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) (ρ : ℝ)
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t)
    {S : ℝ≥0} (hS : (S : ℝ≥0∞) < ζ) (hne : ∀ s : ℝ≥0, 0 < s → s ≤ S → v s ≠ w s) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) S) :
    HasDerivWithinAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, ρ / (w s.toNNReal - v s.toNNReal))
      (ρ / (w t.toNNReal - v t.toNNReal)) (Ioc 0 S) t := by
  have hwc : ContinuousOn (Strip.extPath w) (Icc 0 (S : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hw (by rw [ENNReal.ofReal_coe_nnreal]; exact hS)
  have hvc : ContinuousOn (Strip.extPath v) (Icc 0 (S : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hv (by rw [ENNReal.ofReal_coe_nnreal]; exact hS)
  have hc : ContinuousOn (fun s : ℝ => ρ / (w s.toNNReal - v s.toNNReal)) (Ioc 0 (S : ℝ)) :=
    continuousOn_const.div ((hwc.mono Ioc_subset_Icc_self).sub (hvc.mono Ioc_subset_Icc_self)) fun u hu =>
      sub_ne_zero.2 (hne u.toNNReal (Real.toNNReal_pos.2 hu.1) (Real.toNNReal_le_iff_le_coe.2 hu.2)).symm
  have : Fact (t ∈ Icc (0 : ℝ) S) := ⟨Ioc_subset_Icc_self ht⟩
  have he : Ioi (0 : ℝ) ∩ Icc 0 (S : ℝ) = Ioc 0 (S : ℝ) := by
    ext u
    exact ⟨fun hu => ⟨hu.1, hu.2.2⟩, fun hu => ⟨hu.1, hu.1.le, hu.2⟩⟩
  have hEq := nhdsWithin_inter_of_mem
    (nhdsWithin_le_nhds (Ioi_mem_nhds ht.1) : Ioi (0 : ℝ) ∈ 𝓝[Icc 0 (S : ℝ)] t)
  rw [he] at hEq
  have hct := hc t ht
  change Tendsto (fun s : ℝ => ρ / (w s.toNNReal - v s.toNNReal)) (𝓝[Ioc 0 (S : ℝ)] t)
    (𝓝 (ρ / (w t.toNNReal - v t.toNNReal))) at hct
  have hmeas := hc.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Ioc t
  rw [hEq] at hct hmeas
  have hi : IntervalIntegrable (fun s : ℝ => ρ / (w s.toNNReal - v s.toNNReal)) volume 0 t := by
    have h := (hint t.toNNReal (toNNReal_lt_of_mem_Icc hS (Ioc_subset_Icc_self ht))).const_mul ρ
    rw [Real.coe_toNNReal t ht.1.le] at h
    exact h.congr fun r _ => by simp only [div_eq_mul_inv]
  exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 (S : ℝ)) hi hmeas hct).mono
    Ioc_subset_Icc_self

/-- **The drift of an integrated `SLE_a(ρ)` path**: if `D = w − √a b` on `[0, S]` (`S` before the lifetime) and no
force point meets the driver on `(0, S]`, then `D` has derivative `Σ ρ_L/(w − v_L) + Σ ρ_R/(w − v_R)` within `(0, S]`
at every `t ∈ (0, S]` (`w_eq` and `hasDerivWithinAt_integral_gap`). -/
theorem hasDerivWithinAt_pathDrift {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {S : ℝ≥0} (hS : (S : ℝ≥0∞) < ζ)
    (hneL : ∀ i (s : ℝ≥0), 0 < s → s ≤ S → vL i s ≠ w s) (hneR : ∀ j (s : ℝ≥0), 0 < s → s ≤ S → vR j s ≠ w s)
    {D : ℝ → ℝ} (hD : ∀ u ∈ Icc (0 : ℝ) S, D u = w u.toNNReal - Real.sqrt a * b u.toNNReal) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) S) :
    HasDerivWithinAt D ((∑ i, ρL i / (w t.toNNReal - vL i t.toNNReal))
      + ∑ j, ρR j / (w t.toNNReal - vR j t.toNNReal)) (Ioc 0 S) t := by
  obtain ⟨-, -, -, hcw, hcL, hcR, -, -, -, -, hiL, hiR, hweq, -⟩ := hP
  have hF := (HasDerivWithinAt.sum (u := Finset.univ) fun i _ =>
      hasDerivWithinAt_integral_gap hcw (hcL i) (ρL i) (fun t ht => hiL t ht i) hS (hneL i) ht).add
    (HasDerivWithinAt.sum (u := Finset.univ) fun j _ =>
      hasDerivWithinAt_integral_gap hcw (hcR j) (ρR j) (fun t ht => hiR t ht j) hS (hneR j) ht)
  have hDF : ∀ u ∈ Icc (0 : ℝ) S, D u = (∑ i, ∫ s in (0 : ℝ)..u, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + ∑ j, ∫ s in (0 : ℝ)..u, ρR j / (w s.toNNReal - vR j s.toNNReal) := by
    intro u hu
    have h := hweq u.toNNReal (toNNReal_lt_of_mem_Icc hS hu)
    rw [Real.coe_toNNReal u hu.1] at h
    rw [hD u hu, h]
    ring
  refine hF.congr (fun u hu => ?_) ?_
  · rw [hDF u (Ioc_subset_Icc_self hu)]
    simp only [Pi.add_apply, Finset.sum_apply]
  · rw [hDF t (Ioc_subset_Icc_self ht)]
    simp only [Pi.add_apply, Finset.sum_apply]

/-! ### The G3 column -/

section G3

variable {X Y : Type*}

/-- The stopped driver reads only nonnegative times: its value at `t` is its value at `t⁺`. -/
theorem eightDrv_toNNReal (W₁ : ℝ≥0 → X → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) (t : ℝ) :
    eightDrv W₁ S₁ m x (t.toNNReal : ℝ) = eightDrv W₁ S₁ m x t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [Real.coe_toNNReal t ht]
  · rw [Real.toNNReal_of_nonpos ht.le]
    simp only [eightDrv, A1Ref.stopDrv, NNReal.coe_zero, min_eq_left (S₁ m x).coe_nonneg, max_self]
    rw [max_eq_left ((min_le_left _ _).trans ht.le)]

/-- **The drift part of a G3 column**: `D = W^{stop} − √κ̂ B₁` (the small curve's driver stopped at the rectangle's
exit, minus its Brownian part). -/
def g3ColD (κ : ℝ) (W₁ B₁ : ℝ≥0 → X → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) : ℝ≥0 → X → ℝ :=
  fun u x => eightDrv W₁ S₁ m x u - Real.sqrt (kh κ) * B₁ u x

/-- **The G3 record's driver is `√κ̂ B₁ + D`** (`IsColumnStoch`'s driver clause, `D = g3ColD`). -/
theorem g3Rec_W_eq_driftDriver (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ)
    (VR₁ : Fin 3 → ℝ≥0 → X → ℝ) (W₂ : ℝ≥0 → Y → ℝ) (B₁ : ℝ≥0 → X → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (t₂ : ℝ) (x : X)
    (y : Y) :
    (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).W = driftDriver (Real.sqrt (kh κ)) B₁ (g3ColD κ W₁ B₁ S₁ m) x := by
  funext t
  show eightDrv W₁ S₁ m x t = driftDriver (Real.sqrt (kh κ)) B₁ (g3ColD κ W₁ B₁ S₁ m) x t
  simp only [driftDriver, g3ColD]
  rw [eightDrv_toNNReal]
  ring

/-- The drift part of a G3 column is continuous along a sample whose Brownian path is continuous and whose small curve
is continuous before its lifetime, with the exit before the lifetime. -/
theorem continuous_g3ColD {κ : ℝ} {W₁ B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X}
    (hc : ContinuousOn (W₁ · x) {t | (t : ℝ≥0∞) < ζ₁ x}) (hT : (S₁ m x : ℝ≥0∞) < ζ₁ x)
    (hB : Continuous (B₁ · x)) : Continuous (g3ColD κ W₁ B₁ S₁ m · x) :=
  ((continuous_eightDrv hc hT).comp NNReal.continuous_coe).sub (continuous_const.mul hB)

/-- **`D` has the G3 record's drift as derivative on `(0, S]`** (`IsColumnStoch`'s drift clause): at a sample where
the small curve's path relation holds (parameter `κ̂`, the G3 weights `smallG3RhoL`, `smallG3RhoR`, the other source at
`x_R(2) = p`), the exit is before the lifetime, every force point is off the driver at positive times up to the exit,
and the other source is off the driver up to the exit. The path drift `Σ ρ/(w − v)` (`hasDerivWithinAt_pathDrift`) is
the record's drift (`drift_fromSource_eq_three`; the other source's own-chart coordinate is its force point,
`fwdMap_add_eq_force`). -/
theorem hasDerivWithinAt_g3Rec_drift {κ p : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {t₂ : ℝ} {x : X} {y : Y}
    (hP : IsIntegratedSLEPath (kh κ) xL xR (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · x) (fun i s => VL₁ i s x)
      (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hk : kh κ ≠ 0) (hxp : xR 2 = p) (hT : (S₁ m x : ℝ≥0∞) < ζ₁ x)
    (hneL : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x)
    (hneR : ∀ j (s : ℝ≥0), 0 < s → s ≤ S₁ m x → VR₁ j s x ≠ W₁ s x)
    (hneP : ∀ s : ℝ≥0, s ≤ S₁ m x → VR₁ 2 s x ≠ W₁ s x) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (S₁ m x)) :
    HasDerivWithinAt (fun u : ℝ => g3ColD κ W₁ B₁ S₁ m u.toNNReal x)
      ((g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).drift t) (Ioc 0 (S₁ m x : ℝ)) t := by
  have hWc := continuous_eightDrv (S₁ := S₁) (m := m) hP.2.2.2.1 hT
  have hEq := eightDrv_eqOn W₁ S₁ m x
  have hD : ∀ u ∈ Icc (0 : ℝ) (S₁ m x), g3ColD κ W₁ B₁ S₁ m u.toNNReal x =
      W₁ u.toNNReal x - Real.sqrt (kh κ) * B₁ u.toNNReal x := by
    intro u hu
    simp only [g3ColD]
    rw [eightDrv_toNNReal, hEq hu]
    rfl
  have hd := hasDerivWithinAt_pathDrift hP hT
    (fun i s hs hsS => by fin_cases i; exact hneL s hs hsS) (fun j s hs hsS => hneR j s hs hsS)
    (D := fun u : ℝ => g3ColD κ W₁ B₁ S₁ m u.toNNReal x) hD ht
  refine hd.congr_deriv ?_
  obtain ⟨-, -, -, -, -, hcR, -, -, -, -, -, -, -, -, hReq, -⟩ := id hP
  have hV0 : (fwdMap (eightDrv W₁ S₁ m x) t p).re + eightDrv W₁ S₁ m x t = VR₁ 2 t.toNNReal x := by
    have h := fwdMap_add_eq_force (hcR 2) (fun s hs => hReq s hs 2) hT hneP hWc.continuousOn hEq
      (Ioc_subset_Icc_self ht)
    rw [hxp] at h
    exact h
  have hWt : eightDrv W₁ S₁ m x t = W₁ t.toNNReal x := hEq (Ioc_subset_Icc_self ht)
  have hdr : (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).drift t =
      smallG3RhoL κ 0 / (eightDrv W₁ S₁ m x t - Strip.extPath (VL₁ 0 · x) t)
        + smallG3RhoR κ 0 / (eightDrv W₁ S₁ m x t - Strip.extPath (VR₁ 0 · x) t)
        + smallG3RhoR κ 1 / (eightDrv W₁ S₁ m x t - Strip.extPath (VR₁ 1 · x) t)
        + -(kh κ / 2) / (eightDrv W₁ S₁ m x t - ((fwdMap (eightDrv W₁ S₁ m x) t p).re + eightDrv W₁ S₁ m x t)) :=
    drift_fromSource_eq_three (eightDrv W₁ S₁ m x) _ _ _ hk (smallG3RhoL κ 0) (smallG3RhoR κ 0) (smallG3RhoR κ 1) _ p
      (Strip.extPath (VL₁ 0 · x)) (Strip.extPath (VR₁ 0 · x)) (Strip.extPath (VR₁ 1 · x)) t
  rw [hdr, hV0, hWt]
  have h2 : smallG3RhoR κ 2 = -(kh κ / 2) := rfl
  simp only [Fin.sum_univ_one, Fin.sum_univ_three, Strip.extPath, h2]
  ring

/-- **The stochastic half of a G3 column from its Brownian and measurability inputs**: with `B = B₁` and
`D = g3ColD`, A1-EIGHTSEED's `IsColumnStoch` holds once `B₁` is an `𝓕`-Brownian motion with continuous paths, `D` is
adapted, the masked force coordinates are adapted, and at every sample the pathwise conditions of
`hasDerivWithinAt_g3Rec_drift` hold; the driver clause, the continuity of `D` and the drift clause are proved here. -/
theorem isColumnStoch_g3Rec {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {P : Measure X} {κ p : ℝ}
    {xL : Fin 1 → ℝ} {xR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0}
    {m : ℕ} {t₂ : ℝ} {y : Y}
    (hB : IsFilteredBrownianReal 𝓕 B₁ P) (hBc : ∀ x, Continuous (B₁ · x))
    (hDm : ∀ u, Measurable[𝓕 u] (g3ColD κ W₁ B₁ S₁ m u))
    (hP : ∀ x, IsIntegratedSLEPath (kh κ) xL xR (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · x) (fun i s => VL₁ i s x)
      (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hk : kh κ ≠ 0) (hxp : xR 2 = p) (hT : ∀ x, (S₁ m x : ℝ≥0∞) < ζ₁ x)
    (hneL : ∀ x (s : ℝ≥0), 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x)
    (hneR : ∀ x j (s : ℝ≥0), 0 < s → s ≤ S₁ m x → VR₁ j s x ≠ W₁ s x)
    (hneP : ∀ x (s : ℝ≥0), s ≤ S₁ m x → VR₁ 2 s x ≠ W₁ s x)
    (hVm : ∀ (u : ℝ≥0) k, Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x =>
      (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).V k u))
    (hV₀m : ∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x =>
      (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).V₀ u))
    (hG₀m : ∀ u : ℝ≥0, Measurable[𝓕 u] ({x | u ≤ S₁ m x}.indicator fun x =>
      (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)).G₀ u)) :
    IsColumnStoch 𝓕 P (kh κ) (fun x => g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t₂ (x, y)) (S₁ m) B₁
      (g3ColD κ W₁ B₁ S₁ m) :=
  ⟨hB, hBc, hDm, fun x => continuous_g3ColD (hP x).2.2.2.1 (hT x) (hBc x),
    fun x => g3Rec_W_eq_driftDriver κ p W₁ VL₁ VR₁ W₂ B₁ S₁ m t₂ x y,
    fun x _ ht => hasDerivWithinAt_g3Rec_drift (hP x) hk hxp (hT x) (hneL x) (hneR x) (hneP x) ht,
    hVm, hV₀m, hG₀m⟩

end G3

end InteractingSLE.ZhanGT4.A1G3Calc
