import QuantumZipper.Proofs.Zipper.Cor15PosRezip
import QuantumZipper.Proofs.RS.TipB
import QuantumZipper.Proofs.RS.OnePointFinal
import QuantumZipper.Proofs.Thm11.AddendumArea
import QuantumZipper.Proofs.Thm11.CharFunRhs
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# Corollary 1.5, positive times: input K0 (the folded circles do not charge the hull)

Proves `Cor15Group.Cor15HullNullStmt` (`cor15HullNullStmt`): for `0 < κ < 4`, `t > 0` and each
dyadic folded circle `σ_i`, almost surely `σ_i(revHull (vrev W t) t) = 0`, `W = √κ B`.

Route.
1. `revHull (vrev W t) t = fwdHull W t` (`revHull_vrev_eq_fwdHull`): Sheffield's A1(c)
   (`LoewnerAlgebra.revHull_eq_fwdHull_timeRev`) plus the hull depending only on the driver on
   `[0,t]` (`CharFunRhs.fwdHull_eq_of_eqOn`).
2. For `κ ≤ 4` the forward hull is `η(0,t]` (Rohde–Schramm, *Basic properties of SLE*,
   Ann. Math. 161 (2005), Thm 6.1, p. 23; `RS.ae_fwdHull_eq_sleTrace_image_of_le_four`).
3. A fixed `a ∈ ℍ` is a.s. not on `η[0,∞)`: the one-point estimate (Beffara, *The dimension of
   the SLE curves*, Ann. Probab. 36 (2008), Prop. 4, p. 6; `RS.sleOnePointBound`) gives
   `P(dist(a, η) < ε) ≤ C (ε / Im a)^{1-κ/8} (...) → 0` (`ae_notMem_sleTrace_lt_four`). This is
   the standard deduction (RS 2005, proof of Thm 6.1 uses the same fact for κ ≤ 4).
4. Fubini–Tonelli over `P ⊗ σ_i` with the jointly measurable trace version
   (`RS.exists_measurable_sleTrace`), following `Thm11Area.ae_volume_sleTrace_eq_zero`. No
   absolute continuity of `σ_i` is needed: every section at a point of `ℍ` is `P`-null, and the
   set is intersected with `ℍ` (the hull lies in `ℍ`).
**Own elementary argument** for steps 3–4 (limit ε → 0 and Fubini).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-- The reverse hull of the time-reversed driver is the forward hull. -/
theorem revHull_vrev_eq_fwdHull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 < t) : revHull (B2.vrev W t) t = fwdHull W t := by
  have hVc : Continuous (B2.vrev W t) := by
    unfold B2.vrev; fun_prop
  have hV0 : B2.vrev W t 0 = 0 := by
    simp [B2.vrev, ht.le]
  rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev _ hVc hV0 ht]
  refine CharFunRhs.fwdHull_eq_of_eqOn (by unfold B2.vrev; fun_prop) hW ht.le ?_
  intro r hr
  have h1 : min (max (t - r) 0) t = t - r := by
    rw [max_eq_left (by linarith [hr.2]), min_eq_left (by linarith [hr.1])]
  simp only [B2.vrev, h1, max_eq_left ht.le, min_self, sub_self, hW0]
  ring_nf

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- For `0 < κ < 4` a fixed point of `ℍ` is a.s. not on the SLE trace (from the one-point
estimate). -/
theorem ae_notMem_sleTrace_lt_four (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {a : ℂ} (ha : a ∈ H) : ∀ᵐ ω ∂P, a ∉ sleTrace κ B ω '' Ici 0 := by
  have ha0 : 0 < a.im := ha
  obtain ⟨C, hC⟩ := RS.sleOnePointBound κ hκ hκ4
  set K : ℝ := C * (a.im / ‖a‖) ^ (8 / κ - 1)
  set p : ℝ := 1 - κ / 8
  have hp : 0 < p := by simp only [p]; linarith
  rw [ae_iff]
  simp only [not_not]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) bot_le
  rw [zero_add]
  -- choose `x ∈ (0,1]` with `K x^p < δ`
  have htend : Tendsto (fun x : ℝ => K * x ^ p) (𝓝 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).const_mul K
    simpa [Real.zero_rpow hp.ne'] using this
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), K * x ^ p < δ ∧ x ∈ Ioc 0 1 :=
    (tendsto_nhdsWithin_of_tendsto_nhds htend |>.eventually (gt_mem_nhds (NNReal.coe_pos.2 hδ))).and
      (Ioc_mem_nhdsGT zero_lt_one)
  obtain ⟨x, hxδ, hx0, hx1⟩ := hev.exists
  have hε : 0 < x * a.im := mul_pos hx0 ha0
  have hεim : x * a.im ≤ a.im := by nlinarith
  have hsub : {ω | a ∈ sleTrace κ B ω '' Ici 0} ⊆
      {ω | Metric.infDist a (sleTrace κ B ω '' Ici 0) < x * a.im} := by
    intro ω hω
    show Metric.infDist a _ < _
    have hω' : a ∈ sleTrace κ B ω '' Ici 0 := hω
    rw [Metric.infDist_zero_of_mem hω']; exact hε
  refine (measure_mono hsub).trans ((hC P B hB a ha _ hε hεim).trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : x * a.im / a.im = x := by field_simp
  rw [e]
  have : C * x ^ (1 - κ / 8) * (a.im / ‖a‖) ^ (8 / κ - 1) = K * x ^ p := by
    simp only [K, p]; ring
  rw [this]; exact hxδ.le

/-- **Input K0 of Corollary 1.5 (positive times).** -/
theorem cor15HullNullStmt : Cor15HullNullStmt := by
  intro κ hκ hκ4 t ht Ω _ P _ B hB i
  set ν := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := RS.exists_measurable_sleTrace hB hκ (by linarith)
  set S : Set (Ω × ℂ) := {p | p.2 ∈ η p.1 '' Ici 0} ∩ Prod.snd ⁻¹' H with hSdef
  have hS : MeasurableSet S := (Thm11Area.measurableSet_mem_image_Ici hηm hηc).inter
    (measurable_snd isOpen_H.measurableSet)
  have himg : ∀ᵐ ω ∂P, η ω '' Ici 0 = sleTrace κ B ω '' Ici 0 :=
    hηeq.mono fun ω h => h.image_eq
  have hpt : ∀ z : ℂ, P ((fun ω => (ω, z)) ⁻¹' S) = 0 := by
    intro z
    by_cases hz : z ∈ H
    · have hae : ∀ᵐ ω ∂P, z ∉ η ω '' Ici 0 := by
        filter_upwards [himg, ae_notMem_sleTrace_lt_four hB hκ hκ4 hz] with ω hi h
        rwa [hi]
      exact measure_mono_null (fun ω hω => not_not.2 hω.1) (ae_iff.1 hae)
    · have : (fun ω => (ω, z)) ⁻¹' S = ∅ := by
        ext ω; simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact fun h => hz h.2
      rw [this, measure_empty]
  have hprod : (P.prod ν) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    simp [hpt]
  rw [Measure.prod_apply hS] at hprod
  have hzero := (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).1 hprod
  filter_upwards [hzero, himg, RS.ae_fwdHull_eq_sleTrace_image_of_le_four hB hκ hκ4.le,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω h hi hh hc h0
  refine measure_mono_null (fun w hw => ?_) h
  rw [revHull_vrev_eq_fwdHull (drive_continuous hc) (drive_zero h0) ht] at hw
  have hwH : w ∈ H := hw.1
  rw [hh t ht.le] at hw
  refine ⟨?_, hwH⟩
  show w ∈ η ω '' Ici 0
  rw [hi]
  exact image_mono (fun s hs => le_of_lt hs.1) hw

end Cor15Group
end QuantumZipper
