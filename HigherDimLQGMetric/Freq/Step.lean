import HigherDimLQGMetric.Freq.ExitTimes

/-!
# One annular replacement step

This is the deterministic step in Proposition 5.4. The previous outer hit
can be any hit: geodesicity and (R1) bound the distance to the next outer hit
without requiring the intermediate path to stay in the annulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A good shell gives a positive time step with improved `B/A` ratio. -/
theorem s4c_frequency_step
    (A B : DistRd d → ContMetric d) (ξ Q U a₀ A₀ ℓ β₀ t r : ℝ)
    (z : Rd d) (g : DistRd d) (hr : 0 < r) (hℓ : 0 < ℓ)
    (hℓa : ℓ < a₀ / 100) (hA₀ : 0 < A₀)
    (ht : 0 ≤ t) (htU : t ≤ U) (hA : (A g).IsLength)
    (hreg : g ∈ RegEvent A B ξ Q U a₀ A₀ ℓ β₀ r z)
    (hno : g ∉ WitEvent A B ξ Q U a₀ A₀ ℓ β₀ t r z)
    (hratio : ∀ x y : Rd d, (B g).1 (x, y) ≤ U * (A g).1 (x, y))
    (P : ℝ → Rd d) {L a : ℝ} (ha : a ∈ Icc 0 L)
    (hPc : ContinuousOn P (Icc 0 L))
    (hunit : ∀ s ∈ Icc 0 L, ∀ v ∈ Icc 0 L, s ≤ v →
      (A g).len P s v = ENNReal.ofReal (v - s) ∧
      (A g).1 (P s, P v) = v - s)
    (hstart : 2 * r ≤ ‖P 0 - z‖) (hend : 2 * r ≤ ‖P L - z‖)
    (hnear : ‖P a - z‖ < r / 2) :
    ∃ e ∈ Ioc a L,
      ‖P e - z‖ = 2 * r ∧
      r / 2 ≤ ‖P e - P a‖ ∧
      (B g).1 (P a, P e) ≤ (U - a₀ / A₀ * (U - t)) * (e - a) := by
  let D := A g
  let E := B g
  let s := sNorm ξ Q g r z
  let S := annCl z r (2 * r)
  let V := ann z (3 * r / 4) (3 * r)
  have hs : 0 < s := sNorm_pos ξ Q g hr z
  have ha₀ : 0 < a₀ := by nlinarith
  have hfa : ‖P a - z‖ < r := by linarith
  have hfc : ContinuousOn (fun u => ‖P u - z‖) (Icc 0 L) :=
    continuous_norm.comp_continuousOn (hPc.sub continuousOn_const)
  obtain ⟨b, c, e, hb0, hba, hac, hce, heL, hPb, hPcIn, hPe, hShell⟩ :=
    s4c_shell_times hfc ha hstart hend hfa (by linarith : r < 2 * r)
  have hcI : c ∈ Icc 0 L := ⟨ha.1.trans hac, hce.le.trans heL⟩
  have heI : e ∈ Icc 0 L := ⟨ha.1.trans (hac.trans hce.le), heL⟩
  have hbI : b ∈ Icc 0 L := ⟨hb0, hba.trans ha.2⟩
  have hPeuc : r / 2 ≤ ‖P e - P a‖ := by
    have hnorm := norm_sub_norm_le (P e - z) (P a - z)
    have hdiff : P e - z - (P a - z) = P e - P a := by abel
    rw [hdiff, hPe] at hnorm
    linarith
  have hcross : ENNReal.ofReal (a₀ * s) ≤
      setDistG D (Metric.sphere z r) (Metric.sphere z (2 * r)) := hreg.1
  have hdiam : diamIn D V S ≤ ENNReal.ofReal (A₀ * s) := hreg.2.1
  have hPbS : P b ∈ S := by
    change r ≤ ‖P b - z‖ ∧ ‖P b - z‖ ≤ 2 * r
    rw [hPb]; constructor <;> linarith
  have hPeS : P e ∈ S := by
    change r ≤ ‖P e - z‖ ∧ ‖P e - z‖ ≤ 2 * r
    rw [hPe]; constructor <;> linarith
  have hDbe : e - b ≤ A₀ * s := by
    have hDdist : ENNReal.ofReal (e - b) = ENNReal.ofReal (D.1 (P b, P e)) := by
      rw [(hunit b hbI e heI (hba.trans (hac.trans hce.le))).2]
    have hle : ENNReal.ofReal (D.1 (P b, P e)) ≤ ENNReal.ofReal (A₀ * s) := by
      calc
        ENNReal.ofReal (D.1 (P b, P e)) ≤ D.internal V (P b) (P e) := D.ofReal_le_internal V _ _
        _ ≤ diamIn D V S := by
          unfold diamIn
          exact le_iSup_of_le (P b) <| le_iSup_of_le hPbS <|
            le_iSup_of_le (P e) <| le_iSup_of_le hPeS le_rfl
        _ ≤ ENNReal.ofReal (A₀ * s) := hdiam
    have hEbe : ENNReal.ofReal (e - b) ≤ ENNReal.ofReal (A₀ * s) := by
      rw [hDdist]
      exact hle
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA₀.le hs.le)).1 hEbe
  have hDea : e - a ≤ A₀ * s := by linarith
  have hPcS : P c ∈ S := by
    change r ≤ ‖P c - z‖ ∧ ‖P c - z‖ ≤ 2 * r
    rw [hPcIn]; constructor <;> linarith
  have hPcsph : P c ∈ Metric.sphere z r := by
    simp only [Metric.mem_sphere, dist_eq_norm]
    simpa only [norm_sub_rev] using hPcIn
  have hPesph : P e ∈ Metric.sphere z (2 * r) := by
    simp only [Metric.mem_sphere, dist_eq_norm]
    simpa only [norm_sub_rev] using hPe
  have hset : setDistG D (Metric.sphere z r) (Metric.sphere z (2 * r)) ≤
      ENNReal.ofReal (D.1 (P c, P e)) := by
    unfold setDistG
    exact iInf_le_of_le (P c) <| iInf_le_of_le hPcsph <|
      iInf_le_of_le (P e) <| iInf_le_of_le hPesph le_rfl
  have hDce : a₀ * s ≤ e - c := by
    rw [← (hunit c hcI e heI hce.le).2]
    exact (ENNReal.ofReal_le_ofReal_iff (D.nonneg _ _)).1 (hcross.trans hset)
  have hSV : S ⊆ V := by
    intro x hx
    change r ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 2 * r at hx
    change 3 * r / 4 < ‖x - z‖ ∧ ‖x - z‖ < 3 * r
    constructor <;> linarith
  have hsubS : ∀ τ ∈ Icc c e, P τ ∈ S := by
    intro τ hτ
    exact hShell τ hτ
  obtain ⟨R, hRint, hRS, hR0, hR1, hRlen⟩ :=
    s4c_affinePiece D P S V hcI.1 hce.le heL hPc hsubS
      hSV (hunit c hcI e heI hce.le).1
      (by rw [(hunit c hcI e heI hce.le).2])
  have hRgeo : IsGeod D R := by
    refine ⟨hRint.1, ?_⟩
    rw [hRlen, hR0, hR1, (hunit c hcI e heI hce.le).2]
  have hBceE := lemma51 (d := d) A B ξ Q U a₀ A₀ ℓ β₀ t r z g hr hℓ hℓa ht
    hA hreg hno R hRgeo (by rw [hR0]; exact hPcsph)
      (by rw [hR1]; exact hPesph) hRS
  have hBce : E.1 (P c, P e) ≤ t * (e - c) := by
    have hcle : 0 ≤ e - c := sub_nonneg.mpr hce.le
    have htr : 0 ≤ t * (e - c) := mul_nonneg ht hcle
    have hBceE' : ENNReal.ofReal (E.1 (P c, P e)) ≤
        ENNReal.ofReal (t * (e - c)) := by
      calc
        ENNReal.ofReal (E.1 (P c, P e)) =
            ENNReal.ofReal ((B g).1 (R 0, R 1)) := by rw [hR0, hR1]
        _ ≤ ENNReal.ofReal t * (A g).len R 0 1 := hBceE
        _ = ENNReal.ofReal (t * (e - c)) := by rw [hRlen, ENNReal.ofReal_mul ht]
    exact (ENNReal.ofReal_le_ofReal_iff htr).1 hBceE'
  have hBac : E.1 (P a, P c) ≤ U * (c - a) := by
    rw [← (hunit a ha c hcI hac).2]
    exact hratio _ _
  have hfrac : a₀ / A₀ * (e - a) ≤ e - c := by
    have hmul := mul_le_mul_of_nonneg_left hDea ha₀.le
    have hmul' := mul_le_mul_of_nonneg_left hDce hA₀.le
    have : a₀ * (e - a) ≤ A₀ * (e - c) := by nlinarith only [hmul, hmul']
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hA₀).2 (by simpa only [mul_comm] using this)
  have hstep := s4c_step_ratio htU hfrac
  refine ⟨e, ⟨hac.trans_lt hce, heL⟩,
    hPe, hPeuc, ?_⟩
  have htri := E.2.triangle (P a) (P c) (P e)
  linarith only [htri, hBac, hBce, hstep]

end HigherDimLQGMetric
