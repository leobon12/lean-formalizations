import HigherDimLQGMetric.Freq.GeodesicPieces
import HigherDimLQGMetric.Events.ScaledEvent
import HigherDimLQGMetric.Metric.WeightedLength

/-!
# Lemma 5.1: crossings without a witness

Divide a crossing geodesic into equal arc length pieces. Each piece is an
internal geodesic of the buffered annulus, so absence of the witness bounds
the second metric on each piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The deterministic crossing improvement of [S] Lemma 5.1. -/
theorem lemma51 : Lemma51 d := by
  intro A B ξ Q U a A₀ ℓ β₀ t r z h hr hℓ hℓa ht hlength hreg hno P hP hP0 hP1 hPS
  let D := A h
  let E := B h
  let S := annCl z r (2 * r)
  let V := ann z (3 * r / 4) (3 * r)
  let s := sNorm ξ Q h r z
  let L := D.1 (P 0, P 1)
  have hs : 0 < s := sNorm_pos ξ Q h hr z
  have hδ : 0 < ℓ * s := mul_pos hℓ hs
  have ha : 0 < a := by nlinarith
  have hcross : ENNReal.ofReal (a * s) ≤
      setDistG D (Metric.sphere z r) (Metric.sphere z (2 * r)) := hreg.1
  have hdiam : diamIn D V S ≤ ENNReal.ofReal (A₀ * s) := hreg.2.1
  have hset : setDistG D (Metric.sphere z r) (Metric.sphere z (2 * r)) ≤
      ENNReal.ofReal L := by
    unfold setDistG
    exact iInf_le_of_le (P 0) <| iInf_le_of_le hP0 <|
      iInf_le_of_le (P 1) <| iInf_le_of_le hP1 le_rfl
  have hLlow : a * s ≤ L :=
    (ENNReal.ofReal_le_ofReal_iff (D.nonneg _ _)).1 (hcross.trans hset)
  have hLδ : ℓ * s ≤ L := by
    have : ℓ ≤ a := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hs.le]
  have hLpos : 0 < L := lt_of_lt_of_le hδ hLδ
  have hupper : ENNReal.ofReal L ≤ ENNReal.ofReal (A₀ * s) := by
    calc
      ENNReal.ofReal L ≤ D.internal V (P 0) (P 1) := D.ofReal_le_internal V _ _
      _ ≤ diamIn D V S := by
        unfold diamIn
        exact le_iSup_of_le (P 0) <| le_iSup_of_le (hPS 0 ⟨le_rfl, zero_le_one⟩) <|
          le_iSup_of_le (P 1) <| le_iSup_of_le (hPS 1 ⟨zero_le_one, le_rfl⟩) le_rfl
      _ ≤ ENNReal.ofReal (A₀ * s) := hdiam
  have hSV : S ⊆ V := by
    intro x hx
    change r ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 2 * r at hx
    change 3 * r / 4 < ‖x - z‖ ∧ ‖x - z‖ < 3 * r
    constructor <;> linarith
  obtain ⟨P', hPc, hP'0, hP'1, hP'S, hPlen⟩ :=
    s4c_geodesic_arclength D P hP S hPS
  let N : ℕ := ⌈L / (ℓ * s)⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (div_pos hLpos hδ)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let part := IccPartition.uniform (a := 0) (b := L) hLpos.le N hN
  have hstep (i : ℕ) : part.t (i + 1) - part.t i = L / N := by
    simpa only [part, sub_zero] using IccPartition.uniform_step hLpos.le N hN i
  have hbds := s4c_piece_bounds hδ hLδ
  have hstepPos : 0 ≤ L / N := (div_pos hLpos hN0).le
  have hBstep : ∀ i < N,
      edist (E.pt (P' (part.t i))) (E.pt (P' (part.t (i + 1)))) ≤
        ENNReal.ofReal (t * (L / N)) := by
    intro i hi
    have hia : part.t i ∈ Icc 0 L := part.mem_Icc hi.le
    have hib : part.t (i + 1) ∈ Icc 0 L := part.mem_Icc (Nat.succ_le_of_lt hi)
    have hiab : part.t i ≤ part.t (i + 1) := (part.step hi).2.1
    have hQlen : D.len P' (part.t i) (part.t (i + 1)) =
        ENNReal.ofReal (L / N) := by
      rw [← hstep]
      exact (hPlen _ hia _ hib hiab).1
    have hQdist : ENNReal.ofReal (D.1 (P' (part.t i), P' (part.t (i + 1)))) =
        ENNReal.ofReal (part.t (i + 1) - part.t i) :=
      (hPlen _ hia _ hib hiab).2
    obtain ⟨R, hRgeo, hRS, hR0, hR1, hRlen⟩ :=
      s4c_affinePiece D P' S V hia.1 hiab hib.2 hPc
        (fun u hu => hP'S u ⟨hia.1.trans hu.1, hu.2.trans hib.2⟩) hSV
        (by rw [hstep]; exact hQlen) hQdist
    have hBle : E.internal V (R 0) (R 1) ≤ ENNReal.ofReal t * D.len R 0 1 := by
      by_contra hbad
      have hbad' : ENNReal.ofReal t * D.len R 0 1 < E.internal V (R 0) (R 1) :=
        lt_of_not_ge hbad
      apply hno
      refine ⟨hreg, R, hRS, hRgeo, ?_, ?_, hbad'⟩
      · change ENNReal.ofReal (ℓ / 2 * s) ≤ D.len R 0 1
        rw [hRlen, hstep]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [hbds.1])
      · change D.len R 0 1 ≤ ENNReal.ofReal (ℓ * s)
        rw [hRlen, hstep]
        exact ENNReal.ofReal_le_ofReal hbds.2
    calc
      edist (E.pt (P' (part.t i))) (E.pt (P' (part.t (i + 1))))
          = ENNReal.ofReal (E.1 (R 0, R 1)) := by rw [hR0, hR1, E.edist_pt]
      _ ≤ E.internal V (R 0) (R 1) := E.ofReal_le_internal V _ _
      _ ≤ ENNReal.ofReal t * D.len R 0 1 := hBle
      _ = ENNReal.ofReal (t * (L / N)) := by rw [hRlen, hstep, ENNReal.ofReal_mul ht]
  have hchain := edist_le_range_sum_of_edist_le N (fun {i} hi => hBstep i hi)
  have hsum : (∑ i ∈ Finset.range N, ENNReal.ofReal (t * (L / N))) =
      ENNReal.ofReal (t * L) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro i hi; exact mul_nonneg ht hstepPos)]
    congr 1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hp0 : part.t 0 = 0 := part.zero
  have hpN : part.t N = L := part.last
  have hgoal : ENNReal.ofReal (E.1 (P 0, P 1)) ≤ ENNReal.ofReal (t * L) := by
    calc
      ENNReal.ofReal (E.1 (P 0, P 1)) = edist (E.pt (P' 0)) (E.pt (P' L)) := by
        rw [hP'0, hP'1, E.edist_pt]
      _ = edist (E.pt (P' (part.t 0))) (E.pt (P' (part.t N))) := by
        rw [hp0, hpN]
      _ ≤ ENNReal.ofReal (t * L) := hchain.trans_eq hsum
  change ENNReal.ofReal (E.1 (P 0, P 1)) ≤ ENNReal.ofReal t * D.len P 0 1
  calc
    ENNReal.ofReal (E.1 (P 0, P 1)) ≤ ENNReal.ofReal (t * L) := hgoal
    _ = ENNReal.ofReal t * D.len P 0 1 := by rw [hP.2, ENNReal.ofReal_mul ht]

end HigherDimLQGMetric
