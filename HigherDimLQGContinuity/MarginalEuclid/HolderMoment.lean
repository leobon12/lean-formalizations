import HigherDimLQGContinuity.MarginalEuclid.Chain
import HigherDimLQGContinuity.MarginalEuclid.PairBound
import HigherDimLFPP.Exist.SupBound

/-! Moments of the dyadic edge envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open QuantumZipper.KolmD (InRangeD lptD)

private theorem n5_norm_toLp_of_box {d R : ℕ} (q : Fin d → ℝ)
    (hq : q ∈ QuantumZipper.KolmD.boxD (R + 1)) :
    ‖(WithLp.toLp 2 q : Rd d)‖ ≤ ((d + 1 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ) := by
  have hqnorm : ‖q‖ ≤ ((R + 1 : ℕ) : ℝ) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      simpa only [Real.norm_eq_abs] using hq i
  have hs := HigherDimLFPP.Conc.norm_sub_le_sqrt_dim_mul
    (WithLp.toLp 2 q : Rd d) (0 : Rd d)
  have hs' : ‖(WithLp.toLp 2 q : Rd d)‖ ≤ Real.sqrt d * ‖q‖ := by
    simpa using hs
  have hd : Real.sqrt (d : ℝ) ≤ (d + 1 : ℕ) := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg d)
    have h0 := Real.sqrt_nonneg (d : ℝ)
    push_cast
    nlinarith
  calc ‖(WithLp.toLp 2 q : Rd d)‖ ≤ Real.sqrt d * ‖q‖ := hs'
    _ ≤ ((d + 1 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ) := by gcongr

private theorem n5_dist_lptD_step_eq {d : ℕ} (j : ℕ) (a : Fin d → ℤ) (i : Fin d) :
    dist (WithLp.toLp 2 (lptD j (a + Pi.single i 1)))
      (WithLp.toLp 2 (lptD j a)) = 1 / 2 ^ j := by
  have he : lptD j (a + Pi.single i 1) - lptD j a =
      Pi.single i (1 / (2 : ℝ) ^ j) := by
    funext i'
    simp only [Pi.sub_apply, lptD, Pi.add_apply, Pi.single_apply]
    by_cases h : i' = i
    · subst i'
      simp
      ring
    · simp [h]
  rw [dist_eq_norm, ← WithLp.toLp_sub, he]
  change ‖PiLp.single 2 (β := fun _ : Fin d => ℝ) i (1 / (2 : ℝ) ^ j)‖ = _
  rw [PiLp.norm_single 2 (fun _ : Fin d => ℝ)]
  simp

private theorem n5_rpow_iSup_le_tsum {ι : Type*} (f : ι → ℝ≥0∞) {q : ℝ}
    (hq : 0 < q) : (⨆ i, f i) ^ q ≤ ∑' i, f i ^ q := by
  let S := ∑' i, f i ^ q
  have hqi : 0 < 1 / q := by positivity
  have hbound : (⨆ i, f i) ≤ S ^ (1 / q) := by
    refine iSup_le fun i => ?_
    have hle : f i ^ q ≤ S := ENNReal.le_tsum (f := fun i => f i ^ q) i
    have hi := ENNReal.rpow_le_rpow hle hqi.le
    calc f i = (f i ^ q) ^ (1 / q) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
      _ ≤ S ^ (1 / q) := hi
  calc (⨆ i, f i) ^ q ≤ (S ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow hbound hq.le
    _ = S := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

abbrev N5EdgeIndex (d : ℕ) := ℕ × (Fin d → ℤ) × Fin d

/-- A normalized coordinate edge, with zero outside the box index set. -/
def metricEdgeVal {d : ℕ} (D : ContMetric d) (R : ℕ) (β : ℝ)
    (e : N5EdgeIndex d) : ℝ≥0∞ := by
  classical
  exact if InRangeD R e.1 e.2.1 then
    ENNReal.ofReal (D.1 (WithLp.toLp 2 (lptD e.1 (e.2.1 + Pi.single e.2.2 1)),
      WithLp.toLp 2 (lptD e.1 e.2.1)) / (((1 / 2 : ℝ) ^ β) ^ e.1))
  else 0

theorem metricEdgeAmp_le_iSup_edgeVal {d : ℕ} (D : ContMetric d) (R : ℕ)
    (β : ℝ) : metricEdgeAmp D R β ≤ ⨆ e : N5EdgeIndex d, metricEdgeVal D R β e := by
  unfold metricEdgeAmp
  refine iSup_le fun j => iSup_le fun a => iSup_le fun ha => iSup_le fun i => ?_
  exact le_iSup_of_le (j, a, i) (by simp [metricEdgeVal, ha])

theorem measurable_metricEdgeVal_rho {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (R : ℕ) (β : ℝ) (e : N5EdgeIndex d) :
    Measurable fun g => metricEdgeVal (rho D g) R β e := by
  unfold metricEdgeVal
  split_ifs
  · exact ENNReal.measurable_ofReal.comp
      ((p2_measurable_contMetric_apply (measurable_rho hD) _).div_const _)
  · exact measurable_const

theorem lintegral_metricEdgeAmp_rpow_le_tsum {d : ℕ}
    {D : DistRd d → ContMetric d} (hD : Measurable D) (R : ℕ) (β : ℝ)
    {q : ℝ} (hq : 0 < q) :
    ∫⁻ g, metricEdgeAmp (rho D g) R β ^ q ∂(normLGFLaw d) ≤
      ∑' e : N5EdgeIndex d,
        ∫⁻ g, metricEdgeVal (rho D g) R β e ^ q ∂(normLGFLaw d) := by
  calc
    ∫⁻ g, metricEdgeAmp (rho D g) R β ^ q ∂(normLGFLaw d)
        ≤ ∫⁻ g, (∑' e : N5EdgeIndex d,
            metricEdgeVal (rho D g) R β e ^ q) ∂(normLGFLaw d) := by
          apply lintegral_mono
          intro g
          exact (ENNReal.rpow_le_rpow
            (metricEdgeAmp_le_iSup_edgeVal (rho D g) R β) hq.le).trans
              (n5_rpow_iSup_le_tsum _ hq)
    _ = ∑' e : N5EdgeIndex d,
        ∫⁻ g, metricEdgeVal (rho D g) R β e ^ q ∂(normLGFLaw d) := by
          rw [lintegral_tsum]
          exact fun e => ((measurable_metricEdgeVal_rho hD R β e).pow_const q).aemeasurable

private theorem n5_lintegral_normalized_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) {r β q B : ℝ}
    (hr : 0 < r) (hX : ∀ ω, 0 ≤ X ω) (hq : 0 ≤ q)
    (hpair : ∫⁻ ω, ENNReal.ofReal ((X ω) ^ q) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (X ω / r ^ β) ^ q ∂μ ≤
      ENNReal.ofReal (B / (r ^ β) ^ q) := by
  have hden : 0 < r ^ β := Real.rpow_pos_of_pos hr _
  have hdenq : 0 < (r ^ β) ^ q := Real.rpow_pos_of_pos hden _
  have hpoint (ω : Ω) : ENNReal.ofReal (X ω / r ^ β) ^ q =
      ENNReal.ofReal ((X ω) ^ q) / ENNReal.ofReal ((r ^ β) ^ q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hX ω) hden.le) hq,
      Real.div_rpow (hX ω) hden.le, ENNReal.ofReal_div_of_pos hdenq]
  simp_rw [hpoint]
  have hden_ne : ENNReal.ofReal ((r ^ β) ^ q) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hdenq
  calc
    ∫⁻ ω, ENNReal.ofReal ((X ω) ^ q) / ENNReal.ofReal ((r ^ β) ^ q) ∂μ
        = (ENNReal.ofReal ((r ^ β) ^ q))⁻¹ *
            ∫⁻ ω, ENNReal.ofReal ((X ω) ^ q) ∂μ := by
          simp_rw [div_eq_mul_inv, mul_comm _ (ENNReal.ofReal ((r ^ β) ^ q))⁻¹]
          exact lintegral_const_mul' _ _ (by finiteness)
    _ ≤ (ENNReal.ofReal ((r ^ β) ^ q))⁻¹ * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal (B / (r ^ β) ^ q) := by
          rw [ENNReal.ofReal_div_of_pos hdenq, div_eq_mul_inv, mul_comm]

private theorem n5_lintegral_edge_le_geom {d R : ℕ} (_hd : 3 ≤ d)
    {D : DistRd d → ContMetric d} {β q C₅ : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hq : 1 ≤ q) (hC₅ : 0 ≤ C₅)
    (hgap : ((d + 1 : ℕ) : ℝ) ≤ q * ((1 - (1 - β) / 4) - β))
    (hpair : ∀ x y : Rd d,
      ‖x‖ ≤ ((d + 1 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ) → dist x y ≤ 1 →
        ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
          ENNReal.ofReal (C₅ * (dist x y) ^ (q * (1 - (1 - β) / 4))))
    (e : N5EdgeIndex d) :
    ∫⁻ g, metricEdgeVal (rho D g) R β e ^ q ∂(normLGFLaw d) ≤
      ⨆ (_ : InRangeD R e.1 e.2.1),
        ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ e.1) ^ ((d + 1 : ℕ) : ℝ)) := by
  let r : ℝ := (1 / 2 : ℝ) ^ e.1
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hC : 0 ≤ C₅ * r ^ (((d + 1 : ℕ) : ℝ)) := by positivity
  by_cases ha : InRangeD R e.1 e.2.1
  · simp only [iSup_pos ha]
    let x : Rd d := WithLp.toLp 2 (lptD e.1 (e.2.1 + Pi.single e.2.2 1))
    let y : Rd d := WithLp.toLp 2 (lptD e.1 e.2.1)
    have hbox := (QuantumZipper.KolmD.lptD_mem_boxD ha e.2.2).1
    have hx : ‖x‖ ≤ ((d + 1 : ℕ) : ℝ) * ((R + 1 : ℕ) : ℝ) :=
      n5_norm_toLp_of_box _ hbox
    have hdist : dist x y = r := by
      simpa [x, y, r, one_div, inv_pow] using
        n5_dist_lptD_step_eq e.1 e.2.1 e.2.2
    have hpair' := hpair x y hx (by rw [hdist]; exact hr1)
    have hden : ((1 / 2 : ℝ) ^ β) ^ e.1 = r ^ β := by
      dsimp [r]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2) β e.1,
        mul_comm β, Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hnorm := n5_lintegral_normalized_le (β := β) (q := q)
      (B := C₅ * r ^ (q * (1 - (1 - β) / 4))) (normLGFLaw d)
      (fun g => (rho D g).1 (x, y)) hr (fun g => (rho D g).nonneg _ _)
      (by linarith : 0 ≤ q)
      (by simpa only [hdist] using hpair')
    have hscalar : (C₅ * r ^ (q * (1 - (1 - β) / 4))) / (r ^ β) ^ q =
        C₅ * r ^ (q * ((1 - (1 - β) / 4) - β)) := by
      have hdenq : (r ^ β) ^ q = r ^ (β * q) :=
        (Real.rpow_mul hr.le β q).symm
      calc
        (C₅ * r ^ (q * (1 - (1 - β) / 4))) / (r ^ β) ^ q
            = C₅ * (r ^ (q * (1 - (1 - β) / 4)) / r ^ (β * q)) := by
                rw [hdenq]
                ring
        _ = C₅ * r ^ (q * (1 - (1 - β) / 4) - β * q) := by
              rw [Real.rpow_sub hr]
        _ = C₅ * r ^ (q * ((1 - (1 - β) / 4) - β)) := by congr 1; ring_nf
    have hpow : r ^ (q * ((1 - (1 - β) / 4) - β)) ≤
        r ^ (((d + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 hgap
    calc
      ∫⁻ g, metricEdgeVal (rho D g) R β e ^ q ∂(normLGFLaw d)
          = ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) / r ^ β) ^ q
              ∂(normLGFLaw d) := by
            simp [metricEdgeVal, ha, x, y]
            have hden' : (((2 : ℝ)⁻¹) ^ β) ^ e.1 = r ^ β := by
              simpa only [one_div] using hden
            rw [hden']
      _ ≤ ENNReal.ofReal ((C₅ * r ^ (q * (1 - (1 - β) / 4))) / (r ^ β) ^ q) := hnorm
      _ = ENNReal.ofReal (C₅ * r ^ (q * ((1 - (1 - β) / 4) - β))) := by rw [hscalar]
      _ ≤ ENNReal.ofReal (C₅ * r ^ (((d + 1 : ℕ) : ℝ))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hC₅)
      _ = ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ e.1) ^ ((d + 1 : ℕ) : ℝ)) := rfl
  · simp [metricEdgeVal, ha, ENNReal.zero_rpow_of_pos (by linarith : 0 < q)]

/-- The finite coordinate lattice in the box at level `j`. -/
private def n5_edgeGrid {d : ℕ} (R j : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-((R : ℤ) * 2 ^ j)) ((R : ℤ) * 2 ^ j)

private theorem n5_mem_edgeGrid_iff {d R j : ℕ} (a : Fin d → ℤ) :
    a ∈ n5_edgeGrid R j ↔ InRangeD R j a := by
  simp only [n5_edgeGrid, Fintype.mem_piFinset, Finset.mem_Icc]
  exact forall_congr' fun i => by rw [abs_le]

private theorem n5_edgeGrid_card {d R j : ℕ} :
    ((n5_edgeGrid (d := d) R j).card : ℝ) =
      (2 * (R : ℝ) * 2 ^ j + 1) ^ d := by
  let A : ℤ := (R : ℤ) * 2 ^ j
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h1 : (0 : ℤ) ≤ A + 1 - -A := by omega
  rw [n5_edgeGrid, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Int.card_Icc]
  push_cast
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
  push_cast
  dsimp [A]
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow]
  ring

private theorem n5_edgeGrid_card_le {d R j : ℕ} :
    ((n5_edgeGrid (d := d) R j).card : ℝ) ≤
      (2 * (R : ℝ) + 1) ^ d * ((2 : ℝ) ^ j) ^ d := by
  rw [n5_edgeGrid_card, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  nlinarith

private theorem n5_tsum_edge_level {d R j : ℕ} (K : ℝ≥0∞) :
    ∑' p : (Fin d → ℤ) × Fin d, (⨆ (_ : InRangeD R j p.1), K) =
      ((n5_edgeGrid (d := d) R j).card : ℝ≥0∞) * d * K := by
  classical
  let S := n5_edgeGrid (d := d) R j
  rw [ENNReal.tsum_prod']
  have hi (a : Fin d → ℤ) :
      (∑' i : Fin d, (⨆ (_ : InRangeD R j a), K)) =
        (d : ℝ≥0∞) * (⨆ (_ : InRangeD R j a), K) := by
    rw [tsum_fintype]
    simp [Finset.sum_const, nsmul_eq_mul]
  simp_rw [hi]
  have hout (a : Fin d → ℤ) (ha : a ∉ S) :
      (d : ℝ≥0∞) * (⨆ (_ : InRangeD R j a), K) = 0 := by
    have hn : ¬InRangeD R j a := fun h => ha ((n5_mem_edgeGrid_iff a).2 h)
    simp [hn]
  rw [tsum_eq_sum (s := S) hout]
  have hin (a : Fin d → ℤ) (ha : a ∈ S) :
      (⨆ (_ : InRangeD R j a), K) = K := by
    exact iSup_pos ((n5_mem_edgeGrid_iff a).mp ha)
  have hsum : (∑ a ∈ S, (d : ℝ≥0∞) * (⨆ (_ : InRangeD R j a), K)) =
      ∑ a ∈ S, (d : ℝ≥0∞) * K := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hin a ha]
  rw [hsum]
  simp [Finset.sum_const, nsmul_eq_mul, S, mul_assoc]

private theorem n5_level_sum_le {d R j : ℕ} {C₅ : ℝ} (hC₅ : 0 ≤ C₅) :
    (∑' p : (Fin d → ℤ) × Fin d,
      (⨆ (_ : InRangeD R j p.1),
        ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ j) ^ (((d + 1 : ℕ) : ℝ))))) ≤
      ENNReal.ofReal (C₅ * d * (2 * (R : ℝ) + 1) ^ d * ((1 / 2 : ℝ) ^ j)) := by
  let r : ℝ := (1 / 2 : ℝ) ^ j
  let L : ℝ := (2 : ℝ) ^ j
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hrel : r = L⁻¹ := by dsimp [r, L]; rw [one_div, inv_pow]
  have he : L ^ d * r ^ (((d + 1 : ℕ) : ℝ)) = r := by
    rw [Real.rpow_natCast, pow_succ, hrel, inv_pow]
    calc L ^ d * ((L ^ d)⁻¹ * L⁻¹) = (L ^ d * (L ^ d)⁻¹) * L⁻¹ := by ring
      _ = L⁻¹ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hL.ne'), one_mul]
  have hscalar : ((n5_edgeGrid (d := d) R j).card : ℝ) * d *
      (C₅ * r ^ (((d + 1 : ℕ) : ℝ))) ≤
        C₅ * d * (2 * (R : ℝ) + 1) ^ d * r := by
    have hfac : 0 ≤ (d : ℝ) * (C₅ * r ^ (((d + 1 : ℕ) : ℝ))) := by positivity
    calc
      ((n5_edgeGrid (d := d) R j).card : ℝ) * d *
          (C₅ * r ^ (((d + 1 : ℕ) : ℝ)))
          = ((n5_edgeGrid (d := d) R j).card : ℝ) *
              (d * (C₅ * r ^ (((d + 1 : ℕ) : ℝ)))) := by ring
      _ ≤ ((2 * (R : ℝ) + 1) ^ d * L ^ d) *
            (d * (C₅ * r ^ (((d + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_right n5_edgeGrid_card_le hfac
      _ = C₅ * d * (2 * (R : ℝ) + 1) ^ d *
            (L ^ d * r ^ (((d + 1 : ℕ) : ℝ))) := by ring
      _ = C₅ * d * (2 * (R : ℝ) + 1) ^ d * r := by rw [he]
  rw [n5_tsum_edge_level]
  have hleft : ((n5_edgeGrid (d := d) R j).card : ℝ≥0∞) * d *
      ENNReal.ofReal (C₅ * r ^ (((d + 1 : ℕ) : ℝ))) =
      ENNReal.ofReal (((n5_edgeGrid (d := d) R j).card : ℝ) * d *
        (C₅ * r ^ (((d + 1 : ℕ) : ℝ)))) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((n5_edgeGrid (d := d) R j).card : ℝ) * d),
      ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp [mul_assoc]
  rw [hleft]
  exact ENNReal.ofReal_le_ofReal hscalar

private theorem n5_tsum_edge_geom_le {d R : ℕ} {C₅ : ℝ} (hC₅ : 0 ≤ C₅) :
    (∑' e : N5EdgeIndex d,
      (⨆ (_ : InRangeD R e.1 e.2.1),
        ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ e.1) ^ (((d + 1 : ℕ) : ℝ))))) ≤
      ENNReal.ofReal (2 * C₅ * d * (2 * (R : ℝ) + 1) ^ d) := by
  let K : ℝ := C₅ * d * (2 * (R : ℝ) + 1) ^ d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hhalf : (∑' j : ℕ, (ENNReal.ofReal (1 / 2 : ℝ)) ^ j) = 2 := by
    rw [ENNReal.tsum_geometric]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : 0 ≤ (1 / 2 : ℝ)),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (1 - 1 / 2 : ℝ))]
    norm_num
  calc
    (∑' e : N5EdgeIndex d,
      (⨆ (_ : InRangeD R e.1 e.2.1),
        ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ e.1) ^ (((d + 1 : ℕ) : ℝ)))))
        = ∑' j : ℕ, ∑' p : (Fin d → ℤ) × Fin d,
            (⨆ (_ : InRangeD R j p.1),
              ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ j) ^ (((d + 1 : ℕ) : ℝ)))) :=
          ENNReal.tsum_prod'
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (K * ((1 / 2 : ℝ) ^ j)) := by
          apply ENNReal.tsum_le_tsum
          intro j
          simpa only [K, mul_assoc] using n5_level_sum_le (d := d) (R := R) (j := j) hC₅
    _ = ENNReal.ofReal K * ∑' j : ℕ, (ENNReal.ofReal (1 / 2 : ℝ)) ^ j := by
          have ht (j : ℕ) : ENNReal.ofReal (K * ((1 / 2 : ℝ) ^ j)) =
              ENNReal.ofReal K * (ENNReal.ofReal (1 / 2 : ℝ)) ^ j := by
            rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_pow (by norm_num)]
          simp_rw [ht]
          exact ENNReal.tsum_mul_left
    _ = ENNReal.ofReal K * 2 := by rw [hhalf]
    _ = ENNReal.ofReal (2 * C₅ * d * (2 * (R : ℝ) + 1) ^ d) := by
          rw [show (2 * C₅ * d * (2 * (R : ℝ) + 1) ^ d) = 2 * K by dsimp [K]; ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num [mul_comm]

private theorem n5_lintegral_of_amp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H A : Ω → ℝ≥0∞)
    {p q C K : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (_hC : 0 ≤ C)
    (hH : ∀ ω, H ω ≤ ENNReal.ofReal C * (1 + A ω))
    (hA : ∫⁻ ω, A ω ^ q ∂μ ≤ ENNReal.ofReal K) :
    ∫⁻ ω, H ω ^ p ∂μ ≤
      ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p * (2 + ENNReal.ofReal K) := by
  have hp0 : 0 ≤ p := by linarith
  have hAp (ω : Ω) : A ω ^ p ≤ 1 + A ω ^ q := by
    by_cases h : A ω ≤ 1
    · exact (ENNReal.rpow_le_rpow h hp0).trans (by simp)
    · have h1 : 1 ≤ A ω := le_of_not_ge h
      exact (ENNReal.rpow_le_rpow_of_exponent_le h1 hpq).trans le_add_self
  have hpoint (ω : Ω) : H ω ^ p ≤
      ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p * (2 + A ω ^ q) := by
    calc H ω ^ p ≤ (ENNReal.ofReal C * (1 + A ω)) ^ p :=
          ENNReal.rpow_le_rpow (hH ω) hp0
      _ = ENNReal.ofReal C ^ p * (1 + A ω) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0
      _ ≤ ENNReal.ofReal C ^ p * ((2 : ℝ≥0∞) ^ p * (1 + A ω ^ p)) := by
            gcongr
            simpa using ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
              (1 : ℝ≥0∞) (A ω) hp0
      _ ≤ ENNReal.ofReal C ^ p * ((2 : ℝ≥0∞) ^ p * (2 + A ω ^ q)) := by
            have hadd : (1 : ℝ≥0∞) + A ω ^ p ≤ 2 + A ω ^ q := by
              calc (1 : ℝ≥0∞) + A ω ^ p ≤ 1 + (1 + A ω ^ q) :=
                    add_le_add le_rfl (hAp ω)
                _ = 2 + A ω ^ q := by rw [← add_assoc]; norm_num
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hadd (by positivity)) (by positivity)
      _ = ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p * (2 + A ω ^ q) := by
            rw [mul_assoc]
  have hconst : ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p ≠ ⊤ := by finiteness
  calc
    ∫⁻ ω, H ω ^ p ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p) *
            (2 + A ω ^ q) ∂μ := lintegral_mono hpoint
    _ = (ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p) *
          ∫⁻ ω, (2 + A ω ^ q) ∂μ := lintegral_const_mul' _ _ hconst
    _ = (ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p) *
          (2 + ∫⁻ ω, A ω ^ q ∂μ) := by
            rw [lintegral_add_left (f := fun _ : Ω => 2) measurable_const]
            simp [lintegral_const, measure_univ]
    _ ≤ (ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p) *
          (2 + ENNReal.ofReal K) := by gcongr
    _ = ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p * (2 + ENNReal.ofReal K) := by
          rw [mul_assoc]

private theorem n5_lintegral_edgeAmp_le {d N : ℕ} (hd : 3 ≤ d)
    {D : DistRd d → ContMetric d} (hD : Measurable D)
    {β q C₅ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hq : 1 ≤ q)
    (hC₅ : 0 ≤ C₅)
    (hgap : ((d + 1 : ℕ) : ℝ) ≤ q * ((1 - (1 - β) / 4) - β))
    (hpair : ∀ x y : Rd d,
      ‖x‖ ≤ ((d + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) → dist x y ≤ 1 →
        ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
          ENNReal.ofReal (C₅ * (dist x y) ^ (q * (1 - (1 - β) / 4)))) :
    ∫⁻ g, metricEdgeAmp (rho D g) N β ^ q ∂(normLGFLaw d) ≤
      ENNReal.ofReal (2 * C₅ * d * (2 * (N : ℝ) + 1) ^ d) := by
  calc
    ∫⁻ g, metricEdgeAmp (rho D g) N β ^ q ∂(normLGFLaw d)
        ≤ ∑' e : N5EdgeIndex d,
            ∫⁻ g, metricEdgeVal (rho D g) N β e ^ q ∂(normLGFLaw d) :=
          lintegral_metricEdgeAmp_rpow_le_tsum hD N β (by linarith)
    _ ≤ ∑' e : N5EdgeIndex d,
          (⨆ (_ : InRangeD N e.1 e.2.1),
            ENNReal.ofReal (C₅ * ((1 / 2 : ℝ) ^ e.1) ^ (((d + 1 : ℕ) : ℝ)))) := by
          apply ENNReal.tsum_le_tsum
          exact n5_lintegral_edge_le_geom hd hβ hβ1 hq hC₅ hgap hpair
    _ ≤ ENNReal.ofReal (2 * C₅ * d * (2 * (N : ℝ) + 1) ^ d) :=
      n5_tsum_edge_geom_le hC₅

/-- Uniform Hölder moments on a ball of integer radius. -/
theorem holderMoments_nat {d N : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hConc : ConcentrationStmt d)
    {β p : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hp : 1 ≤ p) :
    ∃ ξ₅ C₆ : ℝ, 0 < ξ₅ ∧ 0 ≤ C₆ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₅,
        ∀ D : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
            ∫⁻ g, holderConstRd (rho D g).1
              (Metric.closedBall 0 (N : ℝ)) β ^ p ∂(normLGFLaw d) ≤
                ENNReal.ofReal C₆ := by
  let δ : ℝ := (1 - (1 - β) / 4) - β
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let q : ℝ := p + ((d + 1 : ℕ) : ℝ) / δ
  have hpq : p ≤ q := by
    dsimp [q]
    have : 0 ≤ (((d + 1 : ℕ) : ℝ) / δ) := by positivity
    linarith
  have hq : 1 ≤ q := hp.trans hpq
  have hgap : ((d + 1 : ℕ) : ℝ) ≤ q * δ := by
    dsimp [q]
    rw [add_mul, div_mul_cancel₀ _ hδ.ne']
    have : 0 ≤ p * δ := mul_nonneg (by linarith) hδ.le
    linarith
  have hRbig : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hd1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d + 1)
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1)
    nlinarith
  obtain ⟨ξ₄, C₅, hξ₄, hC₅, hpair⟩ :=
    lintegral_rho_rpow_le_pair_radius hd hφ hRot hConc hRbig
      (by norm_num : (1 : ℝ) ≤ 1) hβ hβ1 hq
  let C : ℝ := (2 * (d / (1 - (1 / 2 : ℝ) ^ β)) + d) *
    (4 ^ β + (2 * N + 2 : ℝ) / ((1 / 2 : ℝ) ^ β))
  have hC : 0 ≤ C := by
    have hθ : (1 / 2 : ℝ) ^ β < 1 :=
      Real.rpow_lt_one (by norm_num) (by norm_num) hβ
    dsimp [C]
    positivity
  let K : ℝ := 2 * C₅ * d * (2 * (N : ℝ) + 1) ^ d
  let E : ℝ≥0∞ := ENNReal.ofReal C ^ p * (2 : ℝ≥0∞) ^ p * (2 + ENNReal.ofReal K)
  have hE : E ≠ ⊤ := by dsimp [E]; finiteness
  refine ⟨ξ₄, E.toReal, hξ₄, ENNReal.toReal_nonneg, ?_⟩
  intro ξ hξ D hD
  let _ : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  have hpair' : ∀ x y : Rd d,
      ‖x‖ ≤ ((d + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) → dist x y ≤ 1 →
      ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
        ENNReal.ofReal (C₅ * (dist x y) ^ (q * (1 - (1 - β) / 4))) :=
    hpair ξ hξ D hD
  have hAmp := n5_lintegral_edgeAmp_le hd hD.measurable hβ hβ1 hq hC₅
    (by simpa only [δ] using hgap) hpair'
  have hPath (g : DistRd d) :
      holderConstRd (rho D g).1 (Metric.closedBall 0 (N : ℝ)) β ≤
        ENNReal.ofReal C * (1 + metricEdgeAmp (rho D g) N β) := by
    simpa only [C] using
      holderConstRd_le_chain (by omega : 0 < d) hβ hβ1 (rho D g)
  have hh := n5_lintegral_of_amp (normLGFLaw d)
    (fun g => holderConstRd (rho D g).1 (Metric.closedBall 0 (N : ℝ)) β)
    (fun g => metricEdgeAmp (rho D g) N β) hp hpq hC hPath
    (by simpa only [K] using hAmp)
  calc
    ∫⁻ g, holderConstRd (rho D g).1 (Metric.closedBall 0 (N : ℝ)) β ^ p
        ∂(normLGFLaw d) ≤ E := hh
    _ = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hE).symm

private theorem n5_holderConstRd_mono {d : ℕ} (F : Rd d × Rd d → ℝ)
    {K L : Set (Rd d)} (hKL : K ⊆ L) (β : ℝ) :
    holderConstRd F K β ≤ holderConstRd F L β := by
  unfold holderConstRd
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
    le_iSup₂_of_le x (hKL hx) (le_iSup₂_of_le y (hKL hy)
      (le_iSup_of_le hxy le_rfl))

/-- Uniform moments of the Hölder constant on the requested real-radius ball. -/
theorem holderMoments {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hConc : ConcentrationStmt d)
    {R β p : ℝ} (_hR : 1 ≤ R) (hβ : 0 < β) (hβ1 : β < 1) (hp : 1 ≤ p) :
    ∃ ξ₅ C₆ : ℝ, 0 < ξ₅ ∧ 0 ≤ C₆ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₅,
        ∀ D : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
            ∫⁻ g, holderConstRd (rho D g).1
              (Metric.closedBall 0 (R + 1)) β ^ p ∂(normLGFLaw d) ≤
                ENNReal.ofReal C₆ := by
  let N : ℕ := ⌈R + 1⌉₊ + 1
  have hN : R + 1 ≤ (N : ℝ) := by
    have hh := Nat.le_ceil (R + 1)
    dsimp [N]
    push_cast
    linarith
  have hsub : Metric.closedBall (0 : Rd d) (R + 1) ⊆
      Metric.closedBall 0 (N : ℝ) := by
    intro x hx
    exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hx).trans hN)
  obtain ⟨ξ₅, C₆, hξ₅, hC₆, hmom⟩ :=
    holderMoments_nat (N := N) hd hφ hRot hConc hβ hβ1 hp
  refine ⟨ξ₅, C₆, hξ₅, hC₆, ?_⟩
  intro ξ hξ D hD
  calc
    ∫⁻ g, holderConstRd (rho D g).1 (Metric.closedBall 0 (R + 1)) β ^ p
        ∂(normLGFLaw d)
        ≤ ∫⁻ g, holderConstRd (rho D g).1 (Metric.closedBall 0 (N : ℝ)) β ^ p
            ∂(normLGFLaw d) := by
          apply lintegral_mono
          intro g
          exact ENNReal.rpow_le_rpow (n5_holderConstRd_mono _ hsub β) (by linarith)
    _ ≤ ENNReal.ofReal C₆ := hmom ξ hξ D hD

end HigherDimLQGContinuity
