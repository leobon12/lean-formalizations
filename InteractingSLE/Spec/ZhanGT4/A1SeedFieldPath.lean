/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldStatement
import InteractingSLE.Spec.ZhanGT4.A1RefReg
import QuantumZipper.Proofs.Zipper.F1Side

/-!
# Zhan's A.1 (R80): the seed coordinates of a source record from the marginal path relation

Packet PROVE-A1-SEEDFIELD. The source records of `A1SeedFieldCol` (`IsSourceRecord`) ask for the growing curve's seeds
as integrated seed coordinates (`IsSeedCoordinate`), the driver between the two outermost seeds, distinct seeds at
positive times, and the other source's own-chart coordinate `V⁰ = g_t(p)` (`SeedData.fromSource`). For a regular
marginal these come from its pathwise integrated relation `IsIntegratedSLEPath` (every sample), read on `ℝ`
(`Strip.extPath`), once the seeds do not collide with the driver at positive times (an almost-sure property of the
marginal, not part of the path relation: the relation only gives collision sets of measure zero).

## Main results

* **`isSeedCoordinate_of_force`**: a force process started at the driver, continuous before the lifetime, with its
  integrated equation and integrable reciprocal gap, separated from the driver at positive times up to `T` before the
  lifetime, is an integrated seed coordinate of every driver agreeing with the path on `[0, T]`;
* `isSeedCoordinate_vL_of_path`, `isSeedCoordinate_vR_of_path`: the left and right seeds of an integrated `SLE_a(ρ)`
  path;
* `seedPair_between`, `seedPair_marks`, `seedPair_injective`: the driver lies between a left and a right seed, the two
  seeds lie between themselves, and they are distinct at positive times (`IsSourceRecord.drv`, `.marks`, `.inj` for the
  seed vector `![vL, vR]`);
* **`fwdMap_add_eq_force`**: the other source's own-chart coordinate `g_t(p) = fwdMap W t p + W t` is the integrated
  force process from `p` (`SeedData.fromSource`'s `V₀`), when it stays separated from the driver;
* `drift_fromSource_eq`: the force-point drift of a source record with seeds `![vL, vR]` and reduced charges
  `![ρL/κ, ρR/κ]` is the path drift `ρL/(W − vL) + ρR/(W − vR) − (κ/2)/(W − V⁰)` (Eight: the other source carries
  `−κ̂/2`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1SeedField

open QuantumZipper (H fwdMap fwdHull IsForwardSol)

/-- Real times in `[0, T]` are before the lifetime when `T` is. -/
theorem toNNReal_lt_of_mem_Icc {ζ : ℝ≥0∞} {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hT

/-- **A force process started at the driver is an integrated seed coordinate** (read on `ℝ`): continuity before the
lifetime, the integrated equation `v t = v 0 + ∫₀ᵗ 2/(v − w)`, integrability of `(w − v)⁻¹`, and separation from the
driver at positive times up to `T` (before the lifetime) give `IsSeedCoordinate W (extPath v) T` for every driver `W`
agreeing with `extPath w` on `[0, T]`. -/
theorem isSeedCoordinate_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hv0 : v 0 = w 0)
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = v 0 + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hne : ∀ s : ℝ≥0, 0 < s → s ≤ T → v s ≠ w s)
    {W : ℝ → ℝ} (hW : EqOn W (Strip.extPath w) (Icc 0 T)) :
    IsSeedCoordinate W (Strip.extPath v) T := by
  have hWs : ∀ s ∈ Icc (0 : ℝ) T, W s = w s.toNNReal := fun s hs => hW hs
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, T.coe_nonneg⟩
  have hint' : ∀ s ∈ Icc (0 : ℝ) T,
      EqOn (fun r : ℝ => 2 / (Strip.extPath v r - W r)) (fun r => -2 * (w r.toNNReal - v r.toNNReal)⁻¹)
        (uIcc 0 s) := by
    intro s hs r hr
    rw [uIcc_of_le hs.1] at hr
    simp only [Strip.extPath, hWs r ⟨hr.1, hr.2.trans hs.2⟩]
    rw [show w r.toNNReal - v r.toNNReal = -(v r.toNNReal - w r.toNNReal) by ring, inv_neg]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact A1Ref.continuousOn_extPath_Icc hv (by rw [ENNReal.ofReal_coe_nnreal]; exact hT)
  · rw [hWs 0 h0]
    simp only [Strip.extPath, Real.toNNReal_zero, hv0]
  · intro s hs
    rw [hWs s (Ioc_subset_Icc_self hs)]
    exact hne s.toNNReal (Real.toNNReal_pos.2 hs.1) (Real.toNNReal_le_iff_le_coe.2 hs.2)
  · intro s hs
    have h := (hint s.toNNReal (toNNReal_lt_of_mem_Icc hT hs)).const_mul (-2)
    rw [Real.coe_toNNReal s hs.1] at h
    exact h.congr fun r hr => (hint' s hs (uIoc_subset_uIcc hr)).symm
  · intro s hs
    have h := hveq s.toNNReal (toNNReal_lt_of_mem_Icc hT hs)
    rw [Real.coe_toNNReal s hs.1] at h
    have hI : (∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal)) =
        ∫ r in (0 : ℝ)..s, 2 / (Strip.extPath v r - W r) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [Strip.extPath, hWs r ⟨hr.1, hr.2.trans hs.2⟩]
    rw [hI] at h
    have e0 : Strip.extPath v 0 = v 0 := by simp [Strip.extPath]
    rw [e0]
    exact h

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A left seed of an integrated `SLE_a(ρ)` path is an integrated seed coordinate** up to `T` before the lifetime,
when it does not meet the driver at positive times. -/
theorem isSeedCoordinate_vL_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nL)
    (hi : xL i = 0) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hne : ∀ s : ℝ≥0, 0 < s → s ≤ T → vL i s ≠ w s)
    {W : ℝ → ℝ} (hW : EqOn W (Strip.extPath w) (Icc 0 T)) : IsSeedCoordinate W (Strip.extPath (vL i)) T := by
  obtain ⟨hw0, hL0, -, -, hcL, -, -, -, -, -, hiL, -, -, hLeq, -⟩ := hP
  refine isSeedCoordinate_of_force (hcL i) (by rw [hL0 i, hi, hw0]) (fun t ht => ?_) (fun t ht => hiL t ht i) hT
    hne hW
  rw [hL0 i]
  exact hLeq t ht i

/-- **A right seed of an integrated `SLE_a(ρ)` path is an integrated seed coordinate** up to `T` before the lifetime,
when it does not meet the driver at positive times. -/
theorem isSeedCoordinate_vR_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (j : Fin nR)
    (hj : xR j = 0) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hne : ∀ s : ℝ≥0, 0 < s → s ≤ T → vR j s ≠ w s)
    {W : ℝ → ℝ} (hW : EqOn W (Strip.extPath w) (Icc 0 T)) : IsSeedCoordinate W (Strip.extPath (vR j)) T := by
  obtain ⟨hw0, -, hR0, -, -, hcR, -, -, -, -, -, hiR, -, -, hReq, -⟩ := hP
  refine isSeedCoordinate_of_force (hcR j) (by rw [hR0 j, hj, hw0]) (fun t ht => ?_) (fun t ht => hiR t ht j) hT
    hne hW
  rw [hR0 j]
  exact hReq t ht j

/-- **The driver lies between a left and a right force point** (`IsSourceRecord.drv`), read on `ℝ`, up to `T` before
the lifetime. -/
theorem seedPair_between (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nL) (j : Fin nR)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) {W : ℝ → ℝ} (hW : EqOn W (Strip.extPath w) (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Strip.extPath (vL i) t) (Strip.extPath (vR j) t) := by
  obtain ⟨-, -, -, -, -, -, -, hLw, hwR, -⟩ := hP
  intro t ht
  rw [hW ht]
  have hlt := toNNReal_lt_of_mem_Icc hT ht
  exact Icc_subset_uIcc ⟨hLw _ hlt i, hwR _ hlt j⟩

/-- The two seeds lie between themselves (`IsSourceRecord.marks` for the seed vector `![vL, vR]`). -/
theorem seedPair_marks (Vlo Vhi : ℝ → ℝ) (t : ℝ) (m : Fin 2) : ![Vlo, Vhi] m t ∈ uIcc (Vlo t) (Vhi t) := by
  fin_cases m
  · exact left_mem_uIcc
  · exact right_mem_uIcc

/-- **The two seeds are distinct at positive times** (`IsSourceRecord.inj`): a left seed below the driver and a right
seed above it, each separated from it, are different. -/
theorem seedPair_injective (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nL) (j : Fin nR)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hneL : ∀ s : ℝ≥0, 0 < s → s ≤ T → vL i s ≠ w s)
    (hneR : ∀ s : ℝ≥0, 0 < s → s ≤ T → vR j s ≠ w s) :
    ∀ t ∈ Ioc (0 : ℝ) T, Function.Injective fun m : Fin 2 => ![Strip.extPath (vL i), Strip.extPath (vR j)] m t := by
  obtain ⟨-, -, -, -, -, -, -, hLw, hwR, -⟩ := hP
  intro t ht
  have hlt := toNNReal_lt_of_mem_Icc hT (Ioc_subset_Icc_self ht)
  have hpos : 0 < t.toNNReal := Real.toNNReal_pos.2 ht.1
  have hle : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
  have hL : vL i t.toNNReal < w t.toNNReal := lt_of_le_of_ne (hLw _ hlt i) (hneL _ hpos hle)
  have hR : w t.toNNReal < vR j t.toNNReal := lt_of_le_of_ne (hwR _ hlt j) (hneR _ hpos hle).symm
  have hne : Strip.extPath (vL i) t ≠ Strip.extPath (vR j) t := by
    simp only [Strip.extPath]
    exact (hL.trans hR).ne
  intro m m' hmm'
  fin_cases m <;> fin_cases m'
  · rfl
  · exact absurd hmm' hne
  · exact absurd hmm'.symm hne
  · rfl

end Path

/-- **The other source's own-chart coordinate is its integrated force process** (`SeedData.fromSource`'s `V⁰`): for a
driver `W` agreeing with `extPath w` on `[0, T]` and a force process `v` of `w` from `p` (continuous before the
lifetime, integrated equation) separated from the driver on `[0, T]`, `fwdMap W t p + W t = v t` for `t ≤ T`. -/
theorem fwdMap_add_eq_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ T, v r ≠ w r) {W : ℝ → ℝ} (hWc : ContinuousOn W (Icc 0 T))
    (hW : EqOn W (Strip.extPath w) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fwdMap W t p).re + W t = Strip.extPath v t := by
  have hWt : ∀ s ∈ Icc (0 : ℝ) T, W s = w s.toNNReal := fun s hs => hW hs
  set u : ℝ → ℂ := fun s => ((Strip.extPath v s - W s : ℝ) : ℂ) with hudef
  have hvc : ContinuousOn (Strip.extPath v) (Icc 0 (T : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hv (by rw [ENNReal.ofReal_coe_nnreal]; exact hT)
  have hu : IsForwardSol W (p : ℂ) T u := by
    refine ⟨continuous_ofReal.comp_continuousOn (hvc.sub hWc), fun s hs => ⟨?_, ?_⟩⟩
    · simp only [hudef, ne_eq, ofReal_eq_zero, hWt s hs, sub_eq_zero, Strip.extPath]
      exact hsep _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
    · have hint : ∫ r in (0 : ℝ)..s, (2 : ℂ) / u r =
          ((∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hs.1] at hr
        simp only [hudef, hWt r ⟨hr.1, hr.2.trans hs.2⟩, Strip.extPath]
        push_cast
        rfl
      have hve := hveq s.toNNReal (toNNReal_lt_of_mem_Icc hT hs)
      rw [Real.coe_toNNReal s hs.1] at hve
      rw [hint, hudef]
      simp only [hWt s hs, Strip.extPath]
      rw [hve]
      push_cast
      ring
  rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu ht, hudef]
  simp only [ofReal_re]
  ring

/-- **The drift of a two-seed source record is the path drift**: with seeds `V = ![vL, vR]`, reduced charges
`![ρL/κ, ρR/κ]` (`κ ≠ 0`) and the other source carrying `−κ/2`, `drift = ρL/(W − vL) + ρR/(W − vR) + (−κ/2)/(W − V⁰)`
(the Eight small curve's drift: `ρL = −κ̂/2`, `ρR = κ̂/2 − 2`, other source `−κ̂/2`). -/
theorem drift_fromSource_eq (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) {κ : ℝ} (hκ : κ ≠ 0) (ρL ρR ζ₀ p : ℝ)
    (Vlo Vhi : ℝ → ℝ) (t : ℝ) :
    (SeedData.fromSource W W' a φ κ ![ρL / κ, ρR / κ] ζ₀ p ![Vlo, Vhi]).drift t =
      ρL / (W t - Vlo t) + ρR / (W t - Vhi t) + -(κ / 2) / (W t - ((fwdMap W t p).re + W t)) := by
  rw [SeedData.drift_eq]
  simp only [SeedData.fromSource, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

end InteractingSLE.ZhanGT4.A1SeedField
