import QuantumZipper.Proofs.Thm18.LWFarDefs
import QuantumZipper.Proofs.RS.OnePointFinalKoebe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LWF-5 (side bound): the deterministic context and boundary limits

For a driver `W` and a time `t > 0` we collect in `SideCtx W t F` the deterministic facts used by
the side bound (LW eq. (2), p. 6; Beffara Lemma 6, p. 13): `K_t = η(0,t]` for a continuous trace,
and a continuous extension `F` of `g_t⁻¹ = fwdMapInv W t` to `ℍ̄` (the Carathéodory extension,
Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1/2.6, via `CaraR.extExists`) that is
bounded-distance from the identity and takes the value `η(t)` only at `0` on `ℝ` (the tip is not
a cut point of the arc: `RevExt.inj_tip`).

Main result: `lwfSide_limit` (the boundary behaviour of `Z_t = g_t − W_t` at a point of `∂H_t`:
along any sequence of `H_t` converging to a point `x₀ ∉ H_t`, a subsequence of `Z_t` converges to a
real `a` with `F a = x₀`). Own elementary argument (compactness and continuity of `F`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Deterministic context of the side bound at time `t > 0`. -/
structure SideCtx (W : ℝ → ℝ) (t : ℝ) (F : ℂ → ℂ) : Prop where
  cont : Continuous W
  zero : W 0 = 0
  tpos : 0 < t
  Fcont : ContinuousOn F Hbar
  Feq : EqOn F (fwdMapInv W t) H
  Ftip : ∀ x : ℝ, F x = trace W t → x = 0
  F0 : F 0 = trace W t
  bound : ∃ C : ℝ, ∀ u ∈ H, ‖F u - u‖ ≤ C
  hull : fwdHull W t = trace W '' Ioc 0 t
  trCont : ContinuousOn (trace W) (Icc 0 t)
  tr0 : trace W 0 = 0

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

namespace SideCtx

theorem isOpen_dom (hc : SideCtx W t F) : IsOpen (H \ fwdHull W t) :=
  FwdHolo.isOpen_compl_fwdHull hc.cont hc.tpos.le

theorem mapsTo (hc : SideCtx W t F) {x : ℂ} (hx : x ∈ H \ fwdHull W t) : fwdMap W t x ∈ H :=
  FwdHolo.mapsTo_fwdMap hc.cont hc.tpos.le hx

theorem F_fwdMap (hc : SideCtx W t F) {x : ℂ} (hx : x ∈ H \ fwdHull W t) :
    F (fwdMap W t x) = x := by
  rw [hc.Feq (hc.mapsTo hx)]
  exact RS.fwdMapInv_fwdMap hc.cont hc.zero hc.tpos.le hx

theorem F_mem_dom (hc : SideCtx W t F) {u : ℂ} (hu : u ∈ H) : F u ∈ H \ fwdHull W t := by
  rw [hc.Feq hu]
  exact RS.fwdMapInv_mem_compl_fwdHull hc.cont hc.zero hc.tpos.le hu

theorem fwdMap_F (hc : SideCtx W t F) {u : ℂ} (hu : u ∈ H) : fwdMap W t (F u) = u := by
  rw [hc.Feq hu]
  exact RS.fwdMap_fwdMapInv hc.cont hc.zero hc.tpos.le hu

theorem tip_not_mem (hc : SideCtx W t F) : trace W t ∉ H \ fwdHull W t := fun h =>
  h.2 (by rw [hc.hull]; exact ⟨t, ⟨hc.tpos, le_rfl⟩, rfl⟩)

theorem continuousOn_fwdMap (hc : SideCtx W t F) : ContinuousOn (fwdMap W t) (H \ fwdHull W t) :=
  (FwdHolo.differentiableOn_fwdMap hc.cont hc.tpos.le).continuousOn

/-- `‖x‖ - C ≤ ‖Z_t(x)‖`. -/
theorem norm_fwdMap_ge (hc : SideCtx W t F) {C : ℝ} (hC : ∀ u ∈ H, ‖F u - u‖ ≤ C) {x : ℂ}
    (hx : x ∈ H \ fwdHull W t) : ‖x‖ - C ≤ ‖fwdMap W t x‖ := by
  have h := hC _ (hc.mapsTo hx)
  rw [hc.F_fwdMap hx] at h
  have := norm_sub_norm_le x (fwdMap W t x)
  linarith

end SideCtx

/-- **Boundary limits of `Z_t`.** Along a sequence of `H_t` converging to `x₀ ∉ H_t`, a
subsequence of `Z_t` converges to a real point `a` with `F a = x₀`. -/
theorem lwfSide_limit (hc : SideCtx W t F) {x : ℕ → ℂ} (hx : ∀ n, x n ∈ H \ fwdHull W t)
    {x₀ : ℂ} (hx₀ : x₀ ∉ H \ fwdHull W t) (hlim : Tendsto x atTop (𝓝 x₀)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a : ℝ, F a = x₀ ∧
      Tendsto (fun n => fwdMap W t (x (φ n))) atTop (𝓝 (a : ℂ)) := by
  obtain ⟨C, hC⟩ := hc.bound
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto x hlim).subset_closedBall 0
  set u : ℕ → ℂ := fun n => fwdMap W t (x n) with hudef
  have huH : ∀ n, u n ∈ H := fun n => hc.mapsTo (hx n)
  have hub : ∀ n, u n ∈ closedBall (0 : ℂ) (R + C) := fun n => by
    have h1 := hc.norm_fwdMap_ge hC (hx n)
    have h2 := hC _ (huH n)
    rw [show F (u n) = x n from hc.F_fwdMap (hx n)] at h2
    have h3 : ‖x n‖ ≤ R := by simpa using hR ⟨n, rfl⟩
    have h4 := norm_sub_norm_le (u n) (x n)
    rw [mem_closedBall, dist_zero_right]
    rw [norm_sub_rev] at h2
    linarith
  obtain ⟨b, -, φ, hφ, hb⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hub
  have hbH : b ∈ Hbar := isClosed_Hbar.mem_of_tendsto hb
    (Eventually.of_forall fun n => H_subset_Hbar (huH (φ n)))
  have hbW : Tendsto (u ∘ φ) atTop (𝓝[Hbar] b) :=
    tendsto_nhdsWithin_iff.2 ⟨hb, Eventually.of_forall fun n => H_subset_Hbar (huH (φ n))⟩
  have hFb : Tendsto (F ∘ (u ∘ φ)) atTop (𝓝 (F b)) := (hc.Fcont b hbH).tendsto.comp hbW
  have hFx : F ∘ (u ∘ φ) = x ∘ φ := funext fun n => hc.F_fwdMap (hx (φ n))
  rw [hFx] at hFb
  have hFb0 : F b = x₀ := tendsto_nhds_unique hFb (hlim.comp hφ.tendsto_atTop)
  have hbnot : b ∉ H := fun hbH' => hx₀ (hFb0 ▸ hc.F_mem_dom hbH')
  have hbim : b.im = 0 := le_antisymm (not_lt.1 hbnot) hbH
  have hbre : ((b.re : ℝ) : ℂ) = b := Complex.ext (by simp) (by simp [hbim])
  exact ⟨φ, hφ, b.re, by rw [hbre]; exact hFb0, by rw [hbre]; exact hb⟩

end LWFar
end Thm18Asm
end QuantumZipper
