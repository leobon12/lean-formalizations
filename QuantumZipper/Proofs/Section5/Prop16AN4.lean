import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnNodes
import QuantumZipper.Proofs.GFF.K3.MixedM7A1

/-!
# Prop 1.6, node AN4: a uniform local radius on compact subsets of `D ∪ (c,d)`

`Prop16UnifLocalStmt` (`Prop16LocCoupleAnnNodes.lean`): for `(D, c, d)` with
`Prop16Geometry D c d` and `K ⊆ D ∪ realSet (Ioo c d)` compact, there is `R > 0` with
`MixedLocalHyp D (realSet (Icc c d)) K R`.

Proof (own elementary argument; standard compactness / Lebesgue-number reasoning, no literature
needed under the cost rule of `AGENT_GUIDE.md` §"Sources first"). Write `Ω = D ∪ (c,d)` and
`Bad = Hbar \ Ω`, and put `f z = infDist z Bad`.

* **`Ω ⊆ closure D`** (`unifCore_subset_closure`): `D ⊆ closure D`, and a point `(t : ℂ)` with
  `t ∈ (c,d)` is in `closure D` because the half-disc `ball t r ∩ H` lies in `D` for some `r > 0`
  (`halfDisc_subset_closure_m7a`, node M7-a1). (`Bad` is nonempty: `(d+1 : ℂ) ∈ Bad`.)
* **`f > 0` on `Ω`** (`unif_pos`): if `z ∈ D`, some ball around `z` is inside `D` (openness); if
  `z = (t : ℂ)` with `t ∈ (c,d)`, with `r` from the geometry and `δ = min (t - c) (d - t) > 0`,
  every `w ∈ Hbar` at distance `< min r δ` from `z` satisfies: `w.im > 0` gives
  `w ∈ H ∩ ball z r ⊆ D`, and `w.im = 0` gives `|w.re - t| < δ`, so `w.re ∈ (c,d)`. Hence no
  point of `Bad` is closer than `min r δ`.
* **Compactness** (`prop16UnifLocal_holds`): `z ↦ infDist z Bad` is 1-Lipschitz, so
  `IsCompact.exists_forall_le'` gives `a > 0` with `a ≤ f z` for `z ∈ K`; `R = a/4` then has
  `2R < f z` on `K`.
* **Conclusion**: for `z ∈ K`, a point `w ∈ Hbar` with `dist w z ≤ 2R < f z` cannot lie in `Bad`,
  hence lies in `Ω ⊆ closure D`; if moreover `w ∈ frontier D`, then `w ∈ Ω` and `w ∉ D`
  (`D` is open), so `w ∈ realSet (Ioo c d) ⊆ realSet (Icc c d)`.

`Prop16Geometry` is used through `IsOpen D`, `Bornology.IsBounded D`, `D ⊆ H` and the half-disc
condition `∀ t ∈ Ioo c d, ∃ r > 0, ball (t : ℂ) r ∩ H ⊆ D`; the remaining conjuncts
(`IsConnected`, `c < d`, `frontier D ∩ ℝ = realSet (Icc c d)`) are not needed for the radius
(the last one is used elsewhere, e.g. `frontier_inter_ball_subset_m7a`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3

/-- The set covered by the local condition: `D ∪ (c,d)`. -/
def unifCore (D : Set ℂ) (c d : ℝ) : Set ℂ := D ∪ realSet (Ioo c d)

/-- The points of `Hbar` outside `unifCore D c d`: a local ball around `z ∈ unifCore` must avoid
`unifBad` within its radius, and `infDist z (unifBad D c d)` is such a radius. -/
def unifBad (D : Set ℂ) (c d : ℝ) : Set ℂ := Hbar \ unifCore D c d

variable {D : Set ℂ} {c d : ℝ}

/-- `unifBad` is nonempty, so that `infDist` into it is not trivially `0`: the real number
`d + 1` lies in `Hbar` but neither in `D ⊆ H` nor in `realSet (Ioo c d)`. -/
theorem unifBad_nonempty (hDH : D ⊆ H) : (unifBad D c d).Nonempty := by
  refine ⟨((d + 1 : ℝ) : ℂ), show 0 ≤ (((d + 1 : ℝ) : ℂ)).im from by simp, ?_⟩
  rintro (hDmem | ⟨t, ht, hte⟩)
  · have h : 0 < (((d + 1 : ℝ) : ℂ)).im := hDH hDmem
    simp at h
  · have ht' : t = d + 1 := Complex.ofReal_inj.1 hte
    linarith [ht.2]

theorem unifCore_subset_Hbar (hDH : D ⊆ H) : unifCore D c d ⊆ Hbar := by
  rintro z (hz | ⟨t, -, rfl⟩)
  · exact H_subset_Hbar (hDH hz)
  · show 0 ≤ (((t : ℝ) : ℂ)).im
    simp

/-- `D ∪ (c,d) ⊆ closure D`: on the open real part this is the half-disc condition of
`Prop16Geometry` (`halfDisc_subset_closure_m7a`). -/
theorem unifCore_subset_closure (hgeom : Prop16Geometry D c d) :
    unifCore D c d ⊆ closure D := by
  rintro z (hz | ⟨t, ht, rfl⟩)
  · exact subset_closure hz
  · obtain ⟨r, hr, hsub⟩ := hgeom.2.2.2.2.2.2 t ht
    exact halfDisc_subset_closure_m7a hr hsub
      ⟨mem_closedBall_self hr.le, show 0 ≤ (((t : ℝ) : ℂ)).im from by simp⟩

/-- The distance between two points of the real axis in `ℂ`. -/
theorem dist_ofReal_ofReal (s t : ℝ) : dist ((s : ℂ)) ((t : ℝ) : ℂ) = |t - s| := by
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_sub_comm s t

/-- **`infDist` is positive at points of `D`**: a ball inside the open set `D` avoids `unifBad`,
which is contained in `Dᶜ`. -/
theorem unif_pos_of_mem_open (hD : IsOpen D) (hDH : D ⊆ H) {z : ℂ} (hz : z ∈ D) :
    0 < infDist z (unifBad D c d) := by
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 (hD.mem_nhds hz)
  refine lt_of_lt_of_le hη ((le_infDist (unifBad_nonempty hDH)).2 fun y hy => ?_)
  by_contra hcon
  rw [not_le] at hcon
  exact hy.2 (Or.inl (hball (by rwa [mem_ball, dist_comm])))

/-- **`infDist` is positive at points of the open real arc `(c,d)`**: the half-disc of the
geometry at `t` covers all of `Hbar` close to `(t : ℂ)` except the real points, and those stay
inside `(c,d)` within `min (t - c) (d - t)`. -/
theorem unif_pos_of_mem_realSet (hgeom : Prop16Geometry D c d) {t : ℝ} (ht : t ∈ Ioo c d) :
    0 < infDist ((t : ℂ)) (unifBad D c d) := by
  obtain ⟨r, hr, hsub⟩ := hgeom.2.2.2.2.2.2 t ht
  have htc : 0 < t - c := sub_pos.2 ht.1
  have hdt : 0 < d - t := sub_pos.2 ht.2
  have hη : 0 < min r (min (t - c) (d - t)) := lt_min hr (lt_min htc hdt)
  refine lt_of_lt_of_le hη ((le_infDist (unifBad_nonempty hgeom.2.2.2.1)).2 fun y hy => ?_)
  by_contra hcon
  rw [not_le] at hcon
  have hconr : dist ((t : ℂ)) y < r := lt_of_lt_of_le hcon (min_le_left _ _)
  have hconc : dist ((t : ℂ)) y < t - c :=
    lt_of_lt_of_le hcon ((min_le_right _ _).trans (min_le_left _ _))
  have hcond : dist ((t : ℂ)) y < d - t :=
    lt_of_lt_of_le hcon ((min_le_right _ _).trans (min_le_right _ _))
  have hyim : 0 ≤ y.im := hy.1
  rcases lt_or_eq_of_le hyim with hpos | hzero
  · exact hy.2 (Or.inl (hsub ⟨by rwa [mem_ball, dist_comm], hpos⟩))
  · have hyc : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzero])
    have hltc : |y.re - t| < t - c := by
      rw [hyc, dist_ofReal_ofReal] at hconc
      exact hconc
    have hltd : |y.re - t| < d - t := by
      rw [hyc, dist_ofReal_ofReal] at hcond
      exact hcond
    refine hy.2 (Or.inr ⟨y.re, ⟨?_, ?_⟩, hyc.symm⟩)
    · have := (abs_lt.1 hltc).1
      linarith
    · have := (abs_lt.1 hltd).2
      linarith

/-- **`infDist` into `unifBad` is positive on the whole core `D ∪ (c,d)`.** -/
theorem unif_pos (hgeom : Prop16Geometry D c d) {z : ℂ} (hz : z ∈ unifCore D c d) :
    0 < infDist z (unifBad D c d) := by
  rcases hz with hzD | ⟨t, ht, rfl⟩
  · exact unif_pos_of_mem_open hgeom.1 hgeom.2.2.2.1 hzD
  · exact unif_pos_of_mem_realSet hgeom ht

/-- **AN4: every compact subset of `D ∪ (c,d)` carries a uniform local radius.** -/
theorem prop16UnifLocal_holds : Prop16UnifLocalStmt := by
  intro D c d hgeom K hK hKΩ
  have hD : IsOpen D := hgeom.1
  have hb : Bornology.IsBounded D := hgeom.2.2.1
  have hDH : D ⊆ H := hgeom.2.2.2.1
  obtain ⟨a, ha0, ha⟩ := hK.exists_forall_le'
    (f := fun z : ℂ => infDist z (unifBad D c d)) (continuous_infDist_pt _).continuousOn
    (a := 0) fun z hz => unif_pos hgeom (hKΩ hz)
  have hS : realSet (Icc c d) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨s, -, rfl⟩
    simp
  refine ⟨a / 4, by linarith, hD, hDH, hb, hS, hK, by linarith, fun z hz => ?_⟩
  have hclHbar : closure D ⊆ Hbar := closure_minimal (hDH.trans H_subset_Hbar) isClosed_Hbar
  have hzε : 2 * (a / 4) < infDist z (unifBad D c d) := by
    have := ha z hz
    linarith
  have hcore : ∀ w ∈ closedBall z (2 * (a / 4)) ∩ Hbar, w ∈ unifCore D c d := by
    rintro w ⟨hw1, hw2⟩
    by_contra hwc
    have h1 : infDist z (unifBad D c d) ≤ dist z w :=
      infDist_le_dist_of_mem (show w ∈ unifBad D c d from ⟨hw2, hwc⟩)
    have h2 : dist z w ≤ 2 * (a / 4) := by
      rw [dist_comm]
      exact mem_closedBall.1 hw1
    linarith
  refine ⟨unifCore_subset_Hbar hDH (hKΩ hz), by linarith, hDH, fun w hw => ?_, fun w hw => ?_⟩
  · exact unifCore_subset_closure hgeom (hcore w hw)
  · have hnD : w ∉ D := by
      have h := hw.2
      rw [hD.frontier_eq] at h
      exact h.2
    have hwbar : w ∈ Hbar := hclHbar (frontier_subset_closure hw.2)
    have hcore' : w ∈ unifCore D c d := by
      by_contra hwc
      have h1 : infDist z (unifBad D c d) ≤ dist z w :=
        infDist_le_dist_of_mem (show w ∈ unifBad D c d from ⟨hwbar, hwc⟩)
      have h2 : dist z w ≤ 2 * (a / 4) := by
        rw [dist_comm]
        exact mem_closedBall.1 hw.1
      linarith
    rcases hcore' with hwD | hwR
    · exact absurd hwD hnD
    · obtain ⟨u, hu, rfl⟩ := hwR
      exact ⟨u, Ioo_subset_Icc_self hu, rfl⟩

end Prop16Asm

end QuantumZipper
