import QuantumZipper.Proofs.Section5.Prop16ShiftGoodBasic

/-!
# Proposition 1.6, node C′: compact pieces with the M6 local hypothesis

K3 node M6 (`K3.mixedLocalKernel`) represents the mixed covariance by `neumannH + k` on measures
carried by a *compact* `K` with `K3.MixedLocalHyp D S K R`, which also has to contain the free-arc
point `x` and the small folded circles around `x` used by the Palm formula. This file proves the
geometric input of the gluing of the Palm circle representation (`Prop16ShiftGood.lean`): every
compact `L ⊆ D` (in particular a folded circle inside `D`, or a small ball around a point of `D`)
is contained in the *interior* of such a compact `K`.

The construction is the union of two pieces: a small closed thickening of `L` (well inside `D`) and
a half-disc collar around `x` (inside the half-disc that `K3.Prop16Geometry` provides at the
free-arc point `x`). `K3.LocalBall` is checked pointwise: on the thickening of `L` the disc of
radius `2R` stays in `D` (so its frontier part is empty), and on the collar a frontier point of `D`
at distance `< 2R` from the collar point is in the half-disc around `x`, hence in `D` when its
imaginary part is positive; thus it lies on the real axis and in the free arc
`[c,d] = frontier D ∩ ℝ`.

Source: Sheffield, arXiv:1012.4797, Prop. 1.6 (p. 25) and the M6 node of the project's K3
blueprint; the geometry here is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G

/-- The closure of `D` stays in the closed upper half-plane. -/
theorem closure_subset_Hbar {D : Set ℂ} (hDH : D ⊆ H) : closure D ⊆ Hbar :=
  closure_minimal (hDH.trans H_subset_Hbar) isClosed_Hbar

/-- A point of `ℍ̄` close to a half-disc of `D` centred at the real point `x` is in `closure D`. -/
theorem mem_closure_of_ball_inter {D : Set ℂ} {x r : ℝ} (hr : 0 < r)
    (hD : ball (x : ℂ) r ∩ H ⊆ D) {w : ℂ} (hwH : w ∈ Hbar) (hw : dist w (x : ℂ) < r) :
    w ∈ closure D := by
  refine closure_mono hD (Metric.mem_closure_iff.2 fun ε hε => ?_)
  set s : ℝ := min (ε / 2) ((r - dist w (x : ℂ)) / 2) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by linarith)
  have hsw : dist w (x : ℂ) + s < r := by
    have := min_le_right (ε / 2) ((r - dist w (x : ℂ)) / 2)
    linarith
  have hnorm : ‖Complex.I * (s : ℂ)‖ = s := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg hs0.le]
  have hdw : dist (w + Complex.I * (s : ℂ)) w = s := by
    rw [dist_eq_norm]
    calc ‖(w + Complex.I * (s : ℂ)) - w‖ = ‖Complex.I * (s : ℂ)‖ := by ring_nf
      _ = s := hnorm
  refine ⟨w + Complex.I * (s : ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball]
    calc dist (w + Complex.I * (s : ℂ)) (x : ℂ)
        ≤ dist (w + Complex.I * (s : ℂ)) w + dist w (x : ℂ) := dist_triangle _ _ _
      _ = s + dist w (x : ℂ) := by rw [hdw]
      _ < r := by linarith [hsw]
  · show 0 < (w + Complex.I * (s : ℂ)).im
    have him : (w + Complex.I * (s : ℂ)).im = w.im + s := by simp
    have : (0 : ℝ) ≤ w.im := hwH
    rw [him]; linarith
  · rw [dist_eq_norm, show w - (w + Complex.I * (s : ℂ)) = -(Complex.I * (s : ℂ)) from by ring,
      norm_neg, hnorm]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- A frontier point of `D` close to the free arc around `x` lies on the real axis, hence in the
free arc. -/
theorem frontier_subset_of_ball_inter {D : Set ℂ} {x r : ℝ} {S : Set ℂ} (hDo : IsOpen D)
    (hDH : D ⊆ H) {c d : ℝ} (hfront : frontier D ∩ {z : ℂ | z.im = 0} = realSet (Icc c d))
    (hS : S = realSet (Icc c d)) (hr : 0 < r) (hD : ball (x : ℂ) r ∩ H ⊆ D) {w : ℂ}
    (hwf : w ∈ frontier D) (hw : dist w (x : ℂ) < r) : w ∈ S := by
  have hwH : w ∈ Hbar := closure_subset_Hbar hDH (frontier_subset_closure hwf)
  have hw0 : w.im = 0 := by
    by_contra hne
    have hpos : 0 < w.im := lt_of_le_of_ne hwH (Ne.symm hne)
    have hwD : w ∈ D := hD ⟨by rwa [mem_ball], hpos⟩
    have hfr : w ∈ frontier D := hwf
    rw [hDo.frontier_eq] at hfr
    exact hfr.2 hwD
  rw [hS, ← hfront]
  exact ⟨hwf, hw0⟩

/-- A point of the closed `ρ`-thickening of `L` is within `2ρ` of a point of `L`. -/
theorem exists_dist_lt_of_mem_cthickening {L : Set ℂ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hz : z ∈ cthickening ρ L) : ∃ l ∈ L, dist z l < 2 * ρ :=
  Metric.mem_thickening_iff.1
    (Metric.cthickening_subset_thickening' (by linarith) (by linarith) L hz)

/-- **Compact pieces with the M6 local hypothesis.** Every compact `L ⊆ D` is contained in the
interior of a compact `K` with `K3.MixedLocalHyp D (realSet (Icc c d)) K R`, which also contains
`x` and the folded circles of small radius around `x`. -/
theorem exists_compact_mixedLocalHyp {D : Set ℂ} {c d x : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hx : x ∈ Ioo c d) {L : Set ℂ} (hLc : IsCompact L) (hLD : L ⊆ D) :
    ∃ (K : Set ℂ) (R : ℝ), 0 < R ∧ K3.MixedLocalHyp D (realSet (Icc c d)) K R ∧
      (x : ℂ) ∈ K ∧ L ⊆ interior K ∧ ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0 := by
  obtain ⟨hDo, -, hDb, hDH, -, hfront, hdisc⟩ := hgeo
  obtain ⟨rx, hrx, hballx⟩ := hdisc x hx
  obtain ⟨δ, hδ, hδD⟩ := hLc.exists_cthickening_subset_open hDo hLD
  set R : ℝ := min δ rx / 8 with hRdef
  have hR0 : 0 < R := by
    have : 0 < min δ rx := lt_min hδ hrx
    rw [hRdef]; positivity
  have hRδ : 4 * R < δ := by
    have h1 : min δ rx ≤ δ := min_le_left _ _
    rw [hRdef]; linarith
  have hRx : 4 * R < rx := by
    have h1 : min δ rx ≤ rx := min_le_right _ _
    rw [hRdef]; linarith
  set K : Set ℂ := cthickening R L ∪ (closedBall (x : ℂ) (2 * R) ∩ Hbar) with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact hLc.cthickening.union
      ((isCompact_closedBall (x : ℂ) (2 * R)).inter_right isClosed_Hbar)
  have hKsub : K ⊆ closure D := by
    rintro z (hz | hz)
    · obtain ⟨l, hlL, hzl⟩ := exists_dist_lt_of_mem_cthickening hR0 hz
      exact subset_closure (hδD (Metric.mem_cthickening_of_dist_le z l δ L hlL (by linarith)))
    · refine mem_closure_of_ball_inter hrx hballx hz.2 ?_
      have h1 := Metric.mem_closedBall.1 hz.1
      linarith
  have hlocal : ∀ z ∈ K, K3.LocalBall D (realSet (Icc c d)) z (2 * R) := by
    intro z hz
    have hzH : z ∈ Hbar := closure_subset_Hbar hDH (hKsub hz)
    refine ⟨hzH, by positivity, hDH, ?_, ?_⟩
    · -- `closedBall z (2R) ∩ ℍ̄ ⊆ closure D`
      rintro w ⟨hwz, hwH⟩
      rcases hz with hz | hz
      · obtain ⟨l, hlL, hzl⟩ := exists_dist_lt_of_mem_cthickening hR0 hz
        have hwl : dist w l ≤ δ := by
          have h1 := Metric.mem_closedBall.1 hwz
          linarith [dist_triangle w z l]
        exact subset_closure (hδD (Metric.mem_cthickening_of_dist_le w l δ L hlL hwl))
      · refine mem_closure_of_ball_inter hrx hballx hwH ?_
        have h1 := Metric.mem_closedBall.1 hz.1
        have h2 := Metric.mem_closedBall.1 hwz
        linarith [dist_triangle w z (x : ℂ)]
    · -- `closedBall z (2R) ∩ frontier D ⊆ S`
      rintro w ⟨hwz, hwf⟩
      have hwz' := Metric.mem_closedBall.1 hwz
      rcases hz with hz | hz
      · obtain ⟨l, hlL, hzl⟩ := exists_dist_lt_of_mem_cthickening hR0 hz
        have hwl : dist w l ≤ δ := by
          linarith [dist_triangle w z l]
        have hwD : w ∈ D := hδD (Metric.mem_cthickening_of_dist_le w l δ L hlL hwl)
        have hfr : w ∈ frontier D := hwf
        rw [hDo.frontier_eq] at hfr
        exact absurd hwD hfr.2
      · have h1 := Metric.mem_closedBall.1 hz.1
        refine frontier_subset_of_ball_inter hDo hDH hfront rfl hrx hballx hwf ?_
        linarith [dist_triangle w z (x : ℂ)]
  have hxK : (x : ℂ) ∈ K := by
    refine Or.inr ⟨Metric.mem_closedBall.2 (by rw [dist_self]; linarith [hR0]), ?_⟩
    show (0 : ℝ) ≤ ((x : ℂ)).im
    simp
  have hLint : L ⊆ interior K := by
    have h1 : L ⊆ thickening R L := fun l hl =>
      Metric.mem_thickening_iff.2 ⟨l, hl, by simpa using hR0⟩
    refine (h1.trans (Metric.thickening_subset_interior_cthickening R L)).trans
      (interior_mono ?_)
    rw [hKdef]
    exact subset_union_left
  have hS0 : realSet (Icc c d) ⊆ {z : ℂ | z.im = 0} := by
    rintro z ⟨t, -, rfl⟩
    simp
  have hevK : ∀ᶠ n in atTop, Palm.fcK x n Kᶜ = 0 := by
    filter_upwards [tendsto_radius_zero_nodeB.eventually
      (gt_mem_nhds (by linarith : (0 : ℝ) < 2 * R))] with n hn
    refine (mem_ae_iff (μ := Palm.fcK x n) (s := K)).1 ?_
    refine (ae_fc_mem_ball_inter (d := (x : ℂ))
      (by show (0 : ℝ) ≤ ((x : ℂ)).im; simp) (radius_pos n)).mono fun w hw => ?_
    refine Or.inr ⟨?_, hw.2⟩
    have h1 := Metric.mem_closedBall.1 hw.1
    rw [Metric.mem_closedBall]
    linarith
  exact ⟨K, R, hR0, ⟨hDo, hDH, hDb, hS0, hKc, hR0, hlocal⟩, hxK, hLint, hevK⟩

end Prop16Asm

end QuantumZipper
