import QuantumZipper.Proofs.Thm18.D74Basic
import QuantumZipper.Proofs.Thm18.MatchPaperOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T9b infrastructure: fields equal off the curve have equal regularized values at off-curve circles

For the raw masked round trip `R18.G4RoundRawAStmt` (clause (3) of the paper-form Theorem 1.8,
`t > 0`), the off-curve comparison `RegEqOff K x y` (equal regularized circle averages at dyadic
circles that avoid `K`, D74) must give equal regularized evaluations `evalReg` at every folded
circle that stays off `K`: `evalReg` reads `avgReg · k` on the circle only for large `k`, and for
`2^{-k}` below half the gap, every small circle centred on the folded circle avoids `K`.
Own elementary argument (a property of the regularized encoding; Sheffield compares the
restrictions `h|_{D_i}`, arXiv:1012.4797 p. 26).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace R18

/-- Folding is invariant under conjugation. -/
theorem foldH_conj (p : ℂ) : foldH ((starRingEnd ℂ) p) = foldH p := by
  unfold foldH
  simp only [Complex.conj_im, Complex.conj_conj]
  rcases lt_trichotomy p.im 0 with h | h | h
  · rw [if_pos (by linarith), if_neg (by linarith)]
  · have hp : (starRingEnd ℂ) p = p := Complex.conj_eq_iff_im.2 h
    rw [if_pos (by linarith), if_pos (by linarith), hp]
  · rw [if_neg (by linarith), if_pos h.le]

/-- A small circle centred at a point of the folded image of an off-`K` circle is off `K`. -/
theorem circleOff_foldH_of_sphere {K : Set ℂ} {z : ℂ} {r δ ρ : ℝ}
    (hδ : ∀ w : ℂ, |dist w z - r| < δ → foldH w ∉ K) {w : ℂ} (hw : w ∈ Metric.sphere z r)
    (hρ : ρ < δ / 2) (hδ0 : 0 < δ) : CircleOff K (foldH w) ρ := by
  refine ⟨δ / 2, by linarith, fun p hp => ?_⟩
  have hd : dist p (foldH w) < δ := by
    have := (abs_lt.1 hp).2
    linarith
  have hwz : dist w z = r := hw
  by_cases hw0 : 0 ≤ w.im
  · have hfw : foldH w = w := by simp [foldH, hw0]
    rw [hfw] at hd
    refine hδ p ?_
    rw [← hwz]
    exact lt_of_le_of_lt (abs_dist_sub_le p w z) hd
  · have hfw : foldH w = (starRingEnd ℂ) w := by simp [foldH, hw0]
    rw [hfw] at hd
    have hd' : dist ((starRingEnd ℂ) p) w < δ := by
      rw [← Complex.dist_conj_conj, Complex.conj_conj]
      exact hd
    have := hδ ((starRingEnd ℂ) p) (by
      rw [← hwz]
      exact lt_of_le_of_lt (abs_dist_sub_le _ w z) hd')
    rwa [foldH_conj] at this

/-- **Off-`K` equal fields have equal regularized values at off-`K` folded circles.** -/
theorem evalReg_foldedCircle_congr_of_regEqOff {K : Set ℂ} {x y : FieldSample}
    (h : RegEqOff K x y) {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hc : CircleOff K z r) :
    evalReg x (foldedCircle z r) = evalReg y (foldedCircle z r) := by
  obtain ⟨δ, hδ0, hδ⟩ := hc
  obtain ⟨N, hN⟩ := ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
    (gt_mem_nhds (half_pos hδ0))).exists_forall_of_atTop
  have hev : (fun k => ∫ w, avgReg x k w ∂foldedCircle z r) =ᶠ[atTop]
      fun k => ∫ w, avgReg y k w ∂foldedCircle z r := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hmx : Measurable fun w : ℂ => avgReg x k w :=
      (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
    have hmy : Measurable fun w : ℂ => avgReg y k w :=
      (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
    have hU : MeasurableSet {u : ℂ | avgReg x k u = avgReg y k u} :=
      measurableSet_eq_fun hmx hmy
    have hae := Thm18Asm.MatchPaper.ae_mem_of_sphere hU hr fun w hw =>
      h k (foldH w) (circleOff_foldH_of_sphere hδ hw (hN k hk) hδ0)
    exact integral_congr_ae hae
  unfold evalReg
  rw [limUnder, limUnder, Filter.map_congr hev]

/-- Reflecting a lower point to the upper half-plane brings it closer to an upper point. -/
theorem dist_conj_le_of_im {p w : ℂ} (hp : p.im ≤ 0) (hw : 0 ≤ w.im) :
    dist ((starRingEnd ℂ) p) w ≤ dist p w := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im, Complex.conj_re, Complex.conj_im]
  refine Real.sqrt_le_sqrt ?_
  nlinarith

/-- A small circle centred at an upper point at distance `≥ d` from `K` is off `K`. -/
theorem circleOff_of_far {K : Set ℂ} {w : ℂ} (hw : 0 ≤ w.im) {d ρ : ℝ}
    (hK : ∀ p ∈ K, d ≤ dist w p) (hρ : ρ < d / 2) (hd : 0 < d) : CircleOff K w ρ := by
  refine ⟨d / 2, by linarith, fun q hq hqK => ?_⟩
  have hqw : dist q w < d := by
    have := (abs_lt.1 hq).2
    linarith
  by_cases hq0 : 0 ≤ q.im
  · have hf : foldH q = q := by simp [foldH, hq0]
    rw [hf] at hqK
    have := hK q hqK
    rw [dist_comm] at this
    linarith
  · have hf : foldH q = (starRingEnd ℂ) q := by simp [foldH, hq0]
    rw [hf] at hqK
    have h1 := hK _ hqK
    have h2 := dist_conj_le_of_im (le_of_lt (not_le.1 hq0)) hw
    rw [dist_comm] at h1
    linarith

/-- **Off-`K` equal fields have equal regularized evaluations** at every measure carried by upper
points at distance `≥ d > 0` from `K`. -/
theorem evalReg_congr_of_regEqOff_far {K : Set ℂ} {x y : FieldSample} (h : RegEqOff K x y)
    {ν : Measure ℂ} {d : ℝ} (hd : 0 < d)
    (hν : ∀ᵐ w ∂ν, 0 ≤ w.im ∧ ∀ p ∈ K, d ≤ dist w p) : evalReg x ν = evalReg y ν := by
  obtain ⟨N, hN⟩ := ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
    (gt_mem_nhds (half_pos hd))).exists_forall_of_atTop
  have hev : (fun k => ∫ w, avgReg x k w ∂ν) =ᶠ[atTop] fun k => ∫ w, avgReg y k w ∂ν := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    refine integral_congr_ae (hν.mono fun w hw => ?_)
    exact h k w (circleOff_of_far hw.1 hw.2 (hN k hk) hd)
  unfold evalReg
  rw [limUnder, limUnder, Filter.map_congr hev]

/-- **Off-`K` equal fields have equal regularized pairings** with every test function whose
support avoids the closed set `K`. -/
theorem pairTest_congr_of_regEqOff {K : Set ℂ} (hK : IsClosed K) {x y : FieldSample}
    (h : RegEqOff K x y) (ρ : TestFun H) (hρ : Disjoint (tsupport ρ.1) K) :
    pairTest x ρ.1 = pairTest y ρ.1 := by
  obtain ⟨r, hr0, hr⟩ := Metric.exists_pos_forall_lt_edist ρ.2.2.1 hK hρ
  have hd : (0 : ℝ) < r := hr0
  have hfar : ∀ w ∈ tsupport ρ.1, 0 ≤ w.im ∧ ∀ p ∈ K, (r : ℝ) ≤ dist w p := fun w hw =>
    ⟨le_of_lt (ρ.2.2.2 hw), fun p hp => by
      have := hr w hw p hp
      rw [edist_dist] at this
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1
        (by simpa using this))⟩
  have hae : ∀ f : ℂ → ℝ, (∀ z, z ∉ tsupport ρ.1 → f z = 0) →
      ∀ᵐ w ∂(volume.withDensity fun z => ENNReal.ofReal (f z)), w ∈ tsupport ρ.1 := by
    intro f hf
    rw [ae_iff]
    have hm : MeasurableSet {a : ℂ | a ∉ tsupport ρ.1} :=
      (isClosed_tsupport ρ.1).isOpen_compl.measurableSet
    rw [withDensity_apply _ hm, setLIntegral_congr_fun hm (g := fun _ => 0) (fun z hz => by
      show ENNReal.ofReal (f z) = 0
      rw [hf z hz, ENNReal.ofReal_zero]), lintegral_zero]
  unfold pairTest
  rw [evalReg_congr_of_regEqOff_far h hd ((hae ρ.1 fun z hz =>
      image_eq_zero_of_notMem_tsupport hz).mono fun w hw => hfar w hw),
    evalReg_congr_of_regEqOff_far h hd ((hae (fun z => -ρ.1 z) fun z hz => by
      simp [image_eq_zero_of_notMem_tsupport hz]).mono fun w hw => hfar w hw)]

end R18
end QuantumZipper
