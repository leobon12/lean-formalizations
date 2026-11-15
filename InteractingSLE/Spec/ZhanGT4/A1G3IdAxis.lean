/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdView
import InteractingSLE.Spec.ZhanGT4.A1G3CalcG3Rec
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkCap

/-!
# Zhan's A.1 (G3): the own-time-`0` value of the seeded logarithm with an ordinary mark

Packet PROVE-A1-G3ROW2. Source: Astra, *Follow-up proofs*, §A.1.6 (`ig1_followup_proofs.txt` L426–L500: (D13)–(D15),
the divided differences at coincident seeds) and the specification's one-force-point martingale (proof of Theorem 2.2,
L488; Lemma 2.1's `SLE_κ(ρ)` density `∏|W − V_i|^{ρ_i/κ} g'(x_i)^{ρ_i(ρ_i+4−κ)/(4κ)} ∏|V_i − V_j|^{ρ_iρ_j/(2κ)}`).

At own time `0` the two seeds of the small curve coincide with its driver while the ordinary mark keeps its own
coordinate. A22's fused-axis formula (`normEll_zero_eq_fused_axis`) treats all marks as seeds; here:

* `pairSum_fin3`, **`SeedData.normEll_eq_mixed_axis`**: for three marks, two of them at the driver, the normalized
  logarithm is an explicit combination of `log A₁`, `log B₁₂`, the source gap, the mark's gap and its divided
  difference;
* `normEll_zero_eq_mixed_axis`: the same at the entrance of an `OwnData` record;
* `g3_coeff_*`: with the G3 charges the coefficients are `1`, `0`, `−κ̂/4`, `1 − κ̂/4`, `(κ̂ − 4)/2` — the exponents
  of the `SLE_κ(κ − 4, −4)` density relative to `SLE_κ` (`κ̂ = 16/κ`);
* **`normEll_srcRec_g3_own_zero`**: for a `G3Setup` with the G3 charges, the record at height `t` has
  `d_t.normEll 0 = log A₂₁ + (−κ̂/4) log((A₂₀ + p − V₂ t)/(−p)) + (1 − κ̂/4) log((V₂ t − p − B₀)/(p − x₀))
  + ((κ̂ − 4)/2) log((A₂₀ − B₀)/(−x₀))`, all read from the opposite view `e⁰` frozen at own time `0` (its image of the
  small source, its derivative there, and its image of the ordinary mark `x₀`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

/-- The sum over ordered pairs of `Fin 3`. -/
theorem pairSum_fin3 (f : Fin 3 → Fin 3 → ℝ) : pairSum f = f 0 1 + f 0 2 + f 1 2 := by
  unfold pairSum
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  simp only [Fin.isValue, lt_self_iff_false, ite_false, Fin.reduceLT, ite_true, zero_add, add_zero]

namespace SeedData

/-- **The mixed axis**: if the first two marks of a three-mark record sit at the driver (`A₂₁ = 1`, `L = 0`), the
normalized logarithm is
`(γ₀ + γ₁ + δ₀₁ + α + r₀ + r₁) log A₁ + γ₂ log B₁₂ + (−(κ/4)(r₀ + r₁) − ½) log((A₀ − A₂₀)/(W − V⁰))
 + (−(κ/4) r₂) log((A₂₀ − B₀₂)/(V⁰ − V₂)) + (δ₀₂ + δ₁₂ + r₂) log dslope(F, V₂, W)`. -/
theorem normEll_eq_mixed_axis (d : SeedData 3) {t : ℝ}
    (hd : DifferentiableAt ℂ (ownExt d.W d.W' d.a d.φ t) (d.W t)) (hV0 : d.V 0 t = d.W t) (hV1 : d.V 1 t = d.W t)
    (h21 : d.A21 t = 1) (hL : d.L t = 0) :
    d.normEll t =
      (dualGamma d.κ (d.r 0) + dualGamma d.κ (d.r 1) + dualDelta d.κ (d.r 0) (d.r 1) + dualAlpha d.κ + d.r 0 +
          d.r 1) * Real.log (d.A 1 t) +
        dualGamma d.κ (d.r 2) * Real.log (d.B1 t 2) +
        (-(d.κ / 4) * d.r 0 + -(d.κ / 4) * d.r 1 - 1 / 2) *
          Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t)) +
        (-(d.κ / 4) * d.r 2) * Real.log ((d.A20 t - d.B0 t 2) / (d.V₀ t - d.V 2 t)) +
        (dualDelta d.κ (d.r 0) (d.r 2) + dualDelta d.κ (d.r 1) (d.r 2) + d.r 2) *
          Real.log (dslope (d.F 0 t) (d.V 2 t) (d.W t)) := by
  have hB00 : d.B0 t 0 = d.A 0 t := by
    change d.F 0 t (d.V 0 t) = _
    rw [hV0, d.F_driver]
  have hB01 : d.B0 t 1 = d.A 0 t := by
    change d.F 0 t (d.V 1 t) = _
    rw [hV1, d.F_driver]
  have hB10 : d.B1 t 0 = d.A 1 t := by
    change d.F 1 t (d.V 0 t) = _
    rw [hV0, d.F_driver]
  have hB11 : d.B1 t 1 = d.A 1 t := by
    change d.F 1 t (d.V 1 t) = _
    rw [hV1, d.F_driver]
  have hds : dslope (d.F 0 t) (d.W t) (d.W t) = d.A 1 t := by
    rw [dslope_same, d.deriv_F_zero hd, d.F_driver]
  have hratio : (d.A20 t - d.A 0 t) / (d.V₀ t - d.W t) =
      (d.A 0 t - d.A20 t) / (d.W t - d.V₀ t) := by
    rw [← neg_sub (d.A 0 t) (d.A20 t), ← neg_sub (d.W t) (d.V₀ t), neg_div_neg_eq]
  simp only [normEll, pairSum_fin3, Fin.sum_univ_three, h21, hL, hB00, hB01, hB10, hB11, hV0, hV1, hds, hratio,
    Real.log_one, mul_zero, sub_zero]
  ring

/-- **The mixed axis at the entrance of a record**: an `OwnData` record whose first two marks start at the driver
(and whose other tip is alive for the image chain) has the mixed-axis normalized logarithm at own time `0`. -/
theorem normEll_zero_eq_mixed_axis (d : SeedData 3) {A : Set ℂ} {T : ℝ} (h : OwnData d.W A d.φ T d.a d.W')
    {q : ℝ → ℂ} (hq : QuantumZipper.IsForwardSol d.W' d.ζ₀ (d.a T) q) (hV0 : d.V 0 0 = d.W 0)
    (hV1 : d.V 1 0 = d.W 0) (hG : d.G₀ 0 = 1) :
    d.normEll 0 =
      (dualGamma d.κ (d.r 0) + dualGamma d.κ (d.r 1) + dualDelta d.κ (d.r 0) (d.r 1) + dualAlpha d.κ + d.r 0 +
          d.r 1) * Real.log (d.A 1 0) +
        dualGamma d.κ (d.r 2) * Real.log (d.B1 0 2) +
        (-(d.κ / 4) * d.r 0 + -(d.κ / 4) * d.r 1 - 1 / 2) *
          Real.log ((d.A 0 0 - d.A20 0) / (d.W 0 - d.V₀ 0)) +
        (-(d.κ / 4) * d.r 2) * Real.log ((d.A20 0 - d.B0 0 2) / (d.V₀ 0 - d.V 2 0)) +
        (dualDelta d.κ (d.r 0) (d.r 2) + dualDelta d.κ (d.r 1) (d.r 2) + d.r 2) *
          Real.log (dslope (d.F 0 0) (d.V 2 0) (d.W 0)) := by
  have ht : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, h.pos.le⟩
  obtain ⟨ρ, _, hc⟩ := h.exists_clearance
  have hd := (h.ownExt_props ht (hc 0 ht)).1
  have hdr := hd.differentiableAt (ball_mem_nhds (d.W 0 : ℂ) (by positivity : 0 < ρ / 2))
  have hbT : 0 ≤ d.a T := (h.mapsTo_clock ⟨h.pos.le, le_rfl⟩).1
  obtain ⟨δ, hδ, hl, hv⟩ := exists_aliveDisc_self hq hbT
  have hder := deriv_fwdMap_aliveDisc h.contW' hq hδ hl hv ⟨(le_rfl : (0 : ℝ) ≤ 0), hbT⟩
  have h21 : d.A21 0 = 1 := by
    simp only [A21, frzImgD, h.a0, hG, hder, QuantumZipper.logDerivFwd, intervalIntegral.integral_same,
      neg_zero, Complex.exp_zero, Complex.one_re, div_one]
  have hL : d.L 0 = 0 := by simp only [L, frzLogF, intervalIntegral.integral_same]
  exact d.normEll_eq_mixed_axis hdr hV0 hV1 h21 hL

end SeedData

namespace A1G3Id

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed A1EightFin A1G3Calc A2X

/-! ### The G3 coefficients -/

section Coeff

variable {k : ℝ}

theorem g3_coeff_log_deriv (hk : k ≠ 0) :
    dualGamma k ((3 * k / 2 - 4) / k) + dualGamma k ((2 - k / 2) / k) +
        dualDelta k ((3 * k / 2 - 4) / k) ((2 - k / 2) / k) + dualAlpha k + (3 * k / 2 - 4) / k +
        (2 - k / 2) / k = 1 := by
  unfold dualGamma dualDelta dualAlpha
  field_simp
  ring

theorem g3_coeff_mark_deriv (hk : k ≠ 0) : dualGamma k ((k - 4) / k) = 0 := by
  unfold dualGamma
  field_simp
  ring

theorem g3_coeff_src (hk : k ≠ 0) :
    -(k / 4) * ((3 * k / 2 - 4) / k) + -(k / 4) * ((2 - k / 2) / k) - 1 / 2 = -(k / 4) := by
  field_simp
  ring

theorem g3_coeff_mark (hk : k ≠ 0) : -(k / 4) * ((k - 4) / k) = 1 - k / 4 := by
  field_simp
  ring

theorem g3_coeff_pair (hk : k ≠ 0) :
    dualDelta k ((3 * k / 2 - 4) / k) ((k - 4) / k) + dualDelta k ((2 - k / 2) / k) ((k - 4) / k) + (k - 4) / k =
      (k - 4) / 2 := by
  unfold dualDelta
  field_simp
  ring

theorem g3RR_eq (κ : ℝ) :
    g3RR κ = ![(3 * kh κ / 2 - 4) / kh κ, (2 - kh κ / 2) / kh κ, (kh κ - 4) / kh κ] := by
  funext m
  fin_cases m <;> rfl

end Coeff

/-! ### The G3 records at own time `0` -/

variable {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}

/-- **The G3 record at own time `0`, read from the opposite view frozen at own time `0`.** For a `G3Setup` whose first
two marks are the seeds (starting at the driver `W₁ 0 = 0`) and whose third mark starts at `x₀ ≠ 0`, with the G3
charges, at every height `t ≤ Y` at which the large tip is not the image `A₂₀ + p` of the small source:
`d_t.normEll 0 = log A₂₁ + (−κ̂/4) log((A₂₀ + p − V₂ t)/(−p)) + (1 − κ̂/4) log((V₂ t − (B₀ + p))/(p − x₀))
 + ((κ̂ − 4)/2) log((A₂₀ − B₀)/(−x₀))`, with `A₂₀ = e⁰.A20 t`, `A₂₁ = e⁰.A21 t`, `B₀ = e⁰.B0 t 2`. -/
theorem normEll_srcRec_g3_own_zero {κ : ℝ} (hk : kh κ ≠ 0) {V : Fin 3 → ℝ → ℝ}
    (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V) (hV0 : V 0 0 = W₁ 0) (hV1 : V 1 0 = W₁ 0)
    (hV2 : V 2 0 ≠ W₁ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y)
    (htip : (eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A20 t + p ≠ V₂ t) :
    (srcRec W₁ S V₂ t (kh κ) (g3RR κ) p V).normEll 0 =
      Real.log ((eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A21 t) +
        -(kh κ / 4) * Real.log (((eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A20 t + p - V₂ t) / (-p)) +
        (1 - kh κ / 4) * Real.log ((V₂ t - ((eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).B0 t 2 + p)) / (p - V 2 0)) +
        (kh κ - 4) / 2 * Real.log (((eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A20 t -
          (eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).B0 t 2) / (-V 2 0)) := by
  have hv := h.view
  have h0S : (0 : ℝ) ∈ Icc (0 : ℝ) S := ⟨le_rfl, hv.pos₁.le⟩
  have hz₁ : W₁ 0 = 0 := hv.zero₁
  have hz₂ : V₂ 0 = p := hv.zero₂
  obtain ⟨-, -, h20, h21, hB0, -, -, -⟩ := eView_factors_of_clear hv (κ := kh κ) (g3RR κ) h0S ht (mark_clear h h0S)
  set e := eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0 with he
  set d := srcRec W₁ S V₂ t (kh κ) (g3RR κ) p V with hd
  -- the record is an `OwnData` record at height `t`
  obtain ⟨hown, v, hvv⟩ := hv.sOwn ht
  have hdeq : d = SeedData.fromSource W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
      (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) (kh κ) (g3RR κ) (V₂ t) p V :=
    srcRec_eq_sSel W₁ V₂ hv.pos₁.le ht.2 (kh κ) (g3RR κ) p V
  have hown' : OwnData d.W (fwdHull V₂ t) d.φ S d.a d.W' := by rw [hdeq]; exact hown
  have hq' : IsForwardSol d.W' d.ζ₀ (d.a S) v := by rw [hdeq]; exact hvv
  have hG : d.G₀ 0 = 1 := by
    rw [hdeq]
    change (deriv (fwdMap W₁ 0) p).re = 1
    have e0 : fwdMap W₁ 0 = fun z : ℂ => z - (W₁ 0 : ℂ) := funext (fwdMap_zero_eq_sub W₁)
    rw [e0, deriv_sub_const, deriv_id'', Complex.one_re]
  have hdW : d.W = W₁ := by rw [hdeq]; rfl
  have hdV : d.V = V := by rw [hdeq]; rfl
  have hdκ : d.κ = kh κ := by rw [hdeq]; rfl
  have hdr : d.r = g3RR κ := by rw [hdeq]; rfl
  have hdV₀ : d.V₀ 0 = p := by
    rw [hdeq]
    change (fwdMap W₁ 0 p).re + W₁ 0 = p
    rw [fwdMap_zero_eq_sub W₁, hz₁]
    simp
  have hA00 : d.A 0 0 = e.A20 t + p := by rw [h20, hz₂]; ring
  have hB02 : d.B0 0 2 = e.B0 t 2 + p := by rw [hB0 2, hz₂]; ring
  have hA20 : d.A20 0 = V₂ t := by
    have hW'0 : d.W' 0 = d.A 0 0 := (A1MultiMark.A_zero_zero d hown').symm
    have hζ : d.ζ₀ ≠ d.W' 0 := by
      rw [hW'0, hA00]
      have : d.ζ₀ = V₂ t := by rw [hdeq]; rfl
      rw [this]
      exact fun he' => htip he'.symm
    have hfz := A1MultiMark.frzImg_zero d hown' hζ
    have : d.ζ₀ = V₂ t := by rw [hdeq]; rfl
    rw [← this]
    exact hfz
  have hax := d.normEll_zero_eq_mixed_axis hown' hq' (by rw [hdV, hdW]; exact hV0) (by rw [hdV, hdW]; exact hV1) hG
  have hF00 : d.F 0 0 (d.W 0) = d.A 0 0 := d.F_driver 0 0
  have hF02 : d.F 0 0 (d.V 2 0) = d.B0 0 2 := rfl
  have hdsl : dslope (d.F 0 0) (d.V 2 0) (d.W 0) = (e.A20 t - e.B0 t 2) / (-V 2 0) := by
    rw [dslope_of_ne _ (by rw [hdV, hdW]; exact fun he' => hV2 he'.symm), slope_def_field, hF00, hF02, hA00, hB02,
      hdV, hdW, hz₁]
    congr 1
    · ring
    · ring
  rw [hax, hdκ, hdr, g3RR_eq, hA00, hA20, hB02, hdV₀, hdsl, hdW, hdV, hz₁]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [g3_coeff_log_deriv hk, g3_coeff_mark_deriv hk, g3_coeff_src hk, g3_coeff_mark hk, g3_coeff_pair hk, h21]
  have hA1 : d.A 1 0 = e.A21 t := h21.symm
  rw [hA1]
  ring_nf

end A1G3Id

end InteractingSLE.ZhanGT4
