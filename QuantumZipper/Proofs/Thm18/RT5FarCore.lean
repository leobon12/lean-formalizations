import QuantumZipper.Proofs.Thm18.ASepModA
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.Zipper.Cor15RezipRegDist
import QuantumZipper.Statements.Thm18Off

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT5 FarPull, deterministic core: pulled-back folded circles stay off the old curve

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, p. 26: `Z_ℓ` welds the two
pieces conformally, so the pulled-back circles live in the pieces. Here: if the Carathéodory
extension `E` of the reverse map `revMap W' T` is continuous on `ℍ̄`, maps the old curve `K`
into a set `Z`, and the reverse hull lies in `Z`, then every compact set `S` disjoint from `Z`
pulls back by `revMapInv W' T` to a set at positive distance from `K`. Own elementary
compactness argument (sequences in `S × closedBall 0 M`).
-/

noncomputable section

open MeasureTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- **Compactness core.** -/
theorem rt5far_pointwise {W' : ℝ → ℝ} {T : ℝ} {E : ℂ → ℂ} (hE : EqOn E (revMap W' T) H)
    (hEc : ContinuousOn E Hbar) {K Z S : Set ℂ} (hK : IsClosed K) (hEK : ∀ q ∈ K, E q ∈ Z)
    (hhull : H \ revMap W' T '' H ⊆ Z) (hS : IsCompact S) (hSZ : ∀ w ∈ S, w ∉ Z)
    (hbd : ∃ M : ℝ, ∀ w ∈ S, w ∈ H → ‖revMapInv W' T w‖ ≤ M)
    (hinv : ∀ w ∈ revMap W' T '' H, revMapInv W' T w ∈ H ∧ revMap W' T (revMapInv W' T w) = w) :
    ∃ δ > 0, ∀ w ∈ S, w ∈ H → ∀ q ∈ K, δ ≤ dist (revMapInv W' T w) q := by
  obtain ⟨M, hM⟩ := hbd
  by_contra hcon
  push Not at hcon
  have hn : ∀ n : ℕ, ∃ w ∈ S, w ∈ H ∧ ∃ q ∈ K,
      dist (revMapInv W' T w) q < 1 / ((n : ℝ) + 1) := fun n => hcon _ (by positivity)
  choose w hwS hwH q hqK hdist using hn
  have himg : ∀ n, w n ∈ revMap W' T '' H := fun n => by
    by_contra h
    exact hSZ _ (hwS n) (hhull ⟨hwH n, h⟩)
  set u : ℕ → ℂ := fun n => revMapInv W' T (w n) with hudef
  have huH : ∀ n, u n ∈ H := fun n => (hinv _ (himg n)).1
  have hEu : ∀ n, E (u n) = w n := fun n => by
    rw [hE (huH n)]; exact (hinv _ (himg n)).2
  have hcpt : IsCompact (S ×ˢ closedBall (0 : ℂ) M) := hS.prod (isCompact_closedBall _ _)
  have hmem : ∀ n, (w n, u n) ∈ S ×ˢ closedBall (0 : ℂ) M := fun n =>
    ⟨hwS n, by rw [mem_closedBall, dist_zero_right]; exact hM _ (hwS n) (hwH n)⟩
  obtain ⟨⟨w₀, u₀⟩, hmem₀, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  have hw : Tendsto (fun n => w (φ n)) atTop (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hu : Tendsto (fun n => u (φ n)) atTop (𝓝 u₀) := (continuous_snd.tendsto _).comp hlim
  -- the curve points converge to `u₀` as well
  have hsmall : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
  have hq : Tendsto (fun n => q (φ n)) atTop (𝓝 u₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h1 : Tendsto (fun n => dist (u (φ n)) u₀) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero.1 hu)
    have h3 := h1.add hsmall
    rw [add_zero] at h3
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h3
    have h4 := dist_triangle (q (φ n)) (u (φ n)) u₀
    have h2 : dist (u (φ n)) (q (φ n)) < 1 / ((φ n : ℝ) + 1) := hdist (φ n)
    rw [dist_comm (q (φ n)) (u (φ n))] at h4
    show dist (q (φ n)) u₀ ≤ dist (u (φ n)) u₀ + 1 / ((φ n : ℝ) + 1)
    linarith
  have hu₀K : u₀ ∈ K := hK.mem_of_tendsto hq (Eventually.of_forall fun n => hqK _)
  have hHb : ∀ n, u n ∈ Hbar := fun n => show (0 : ℝ) ≤ (u n).im from le_of_lt (huH n)
  have hu₀H : u₀ ∈ Hbar := isClosed_Hbar.mem_of_tendsto hu
    (Eventually.of_forall fun n => hHb _)
  have hEt : Tendsto (fun n => E (u (φ n))) atTop (𝓝 (E u₀)) :=
    (hEc u₀ hu₀H).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hu, Eventually.of_forall fun n => hHb _⟩)
  simp only [hEu] at hEt
  have heq : w₀ = E u₀ := tendsto_nhds_unique hw hEt
  exact hSZ _ hmem₀.1 (heq ▸ hEK _ hu₀K)

/-- A `CircleOff` circle, folded, avoids `Z`. -/
theorem rt5far_foldSph_notMem {Z : Set ℂ} {d : ℂ} {r : ℝ} (h : CircleOff Z d r) :
    ∀ w ∈ ASep.foldSph d r, w ∉ Z := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨δ, hδ, hoff⟩ := h
  refine hoff x ?_
  rw [mem_sphere.1 hx, sub_self, abs_zero]
  exact hδ

/-- **Measure form.** -/
theorem rt5far_ae {W' : ℝ → ℝ} {T : ℝ} (hW' : Continuous W') (hT : 0 ≤ T) {K : Set ℂ}
    {d : ℂ} {r : ℝ} (hr : 0 < r) {δ : ℝ}
    (hpt : ∀ w ∈ ASep.foldSph d r, w ∈ H → ∀ q ∈ K, δ ≤ dist (revMapInv W' T w) q) :
    ∀ᵐ w ∂((foldedCircle d r).map (revMapInv W' T)),
      0 ≤ w.im ∧ ∀ q ∈ K, δ ≤ dist w q := by
  have hm := Cor15Group.measurable_revMapInv hW' hT
  have hP : IsClosed {w : ℂ | 0 ≤ w.im ∧ ∀ q ∈ K, δ ≤ dist w q} := by
    have e : {w : ℂ | 0 ≤ w.im ∧ ∀ q ∈ K, δ ≤ dist w q} =
        {w : ℂ | 0 ≤ w.im} ∩ ⋂ q ∈ K, {w : ℂ | δ ≤ dist w q} := by
      ext w; simp
    rw [e]
    refine (isClosed_le continuous_const Complex.continuous_im).inter ?_
    exact isClosed_biInter fun q _ => isClosed_le continuous_const (continuous_id.dist
      continuous_const)
  rw [ae_map_iff hm.aemeasurable hP.measurableSet]
  filter_upwards [ASep.ae_mem_foldSph d hr.le, TwoPoint.foldedCircle_ae_mem_H d hr]
    with w hwS hwH
  refine ⟨?_, hpt w hwS hwH⟩
  by_cases hw : w ∈ revMap W' T '' H
  · exact le_of_lt (Cor15Group.revMapInv_mem_H hW' hT hw).1
  · rw [Cor15Group.revMapInv_eq_zero_of_notMem hw]; simp

end R18
end QuantumZipper
