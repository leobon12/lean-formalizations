import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpreadMeas
import QuantumZipper.Proofs.LQG.ZoomRadialBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD4 (`HitPathIndStmt`), part 1: deterministic splitting at an intermediate level

For a path `W` and a time `τ` at which the drift path `Y t = √2 W t + (α − Q) t` first reaches the
level `a = M − L < 0`, the first passage of `Xc_L = L + Y` below `0` is `τ` plus the first passage
of `Xc_M` below `0` along the restarted path `W' s = W (τ + s) − W τ`, and the re-centred
truncated path at the passage is the one of `W'` (as soon as that passage takes at least `S`).
This is the pathwise content of the strong Markov step in Duplantier–Miller–Sheffield
arXiv:1409.7055, proof of Prop. 4.7 (p. 78). Own elementary arguments (intermediate value theorem,
`sInf` bookkeeping), and the joint measurability of the pair
`(trunc S (zoomRadial ..), Tc ..)` for continuous paths.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace QuantumZipper
namespace T13Path

/-- Before the first visit to `a`, a continuous path started above `a` stays above `a`. -/
theorem lt_of_lt_first_visit {Y : ℝ≥0 → ℝ} (hY : Continuous Y) {a : ℝ} (h0 : a < Y 0)
    {τ : ℝ≥0} (hne : ∀ t < τ, Y t ≠ a) : ∀ t < τ, a < Y t := by
  intro t ht
  by_contra hle
  push Not at hle
  have hsub := intermediate_value_Icc' (zero_le (a := t)) hY.continuousOn
  obtain ⟨s, hs, hsa⟩ := hsub ⟨hle, h0.le⟩
  exact hne s (lt_of_le_of_lt hs.2 ht) hsa

variable {Ω : Type*}

/-- The drift path `Xc` after an intermediate time `τ` is the drift path of the restarted path,
started at the intermediate level `M = L + Y τ`. -/
theorem Xc_split {α Q L M : ℝ} {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} {τ : ℝ≥0}
    (hW' : ∀ s, W' s ω = W (τ + s) ω - W τ ω)
    (hM : M = L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ))) {v : ℝ} (hv : 0 ≤ v) :
    ZoomRadial.Xc α Q L W ω ((τ : ℝ) + v) = ZoomRadial.Xc α Q M W' ω v := by
  have ht : ((τ : ℝ) + v).toNNReal = τ + v.toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_add, Real.coe_toNNReal _ hv]
  simp only [ZoomRadial.Xc, ht, hW', hM]
  ring

/-- **First passage splitting.** -/
theorem Tc_split {α Q L M : ℝ} {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} {τ : ℝ≥0}
    (hW' : ∀ s, W' s ω = W (τ + s) ω - W τ ω) (hW'c : Continuous fun s => W' s ω)
    (hM : M = L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ))) (hM0 : 0 < M)
    (habove : ∀ t < τ, M - L < Real.sqrt 2 * W t ω + (α - Q) * (t : ℝ))
    (hhit : ∃ v, 0 ≤ v ∧ ZoomRadial.Xc α Q M W' ω v ≤ 0) :
    ZoomRadial.Tc α Q L W ω = τ + ZoomRadial.Tc α Q M W' ω := by
  set SL : Set ℝ := {t | 0 ≤ t ∧ ZoomRadial.Xc α Q L W ω t ≤ 0} with hSL
  set SM : Set ℝ := {v | 0 ≤ v ∧ ZoomRadial.Xc α Q M W' ω v ≤ 0} with hSM
  have hcM : Continuous fun v : ℝ => ZoomRadial.Xc α Q M W' ω v := by
    have h1 : Continuous fun v : ℝ => W' v.toNNReal ω := hW'c.comp continuous_real_toNNReal
    simp only [ZoomRadial.Xc]
    fun_prop
  have hSMc : IsClosed SM := isClosed_Ici.inter (isClosed_le hcM continuous_const)
  have hSMne : SM.Nonempty := hhit
  have hmem := hSMc.csInf_mem hSMne ⟨0, fun s hs => hs.1⟩
  have hTcM : ZoomRadial.Tc α Q M W' ω = sInf SM := rfl
  have hTcL : ZoomRadial.Tc α Q L W ω = sInf SL := rfl
  -- before `τ`, `Xc_L > 0`
  have hpos : ∀ t : ℝ, 0 ≤ t → t < τ → 0 < ZoomRadial.Xc α Q L W ω t := by
    intro t ht0 htτ
    have hlt : t.toNNReal < τ := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht0]; exact htτ
    have h := habove _ hlt
    rw [Real.coe_toNNReal t ht0] at h
    simp only [ZoomRadial.Xc]
    linarith
  have hin : (τ : ℝ) + sInf SM ∈ SL := by
    refine ⟨add_nonneg τ.2 hmem.1, ?_⟩
    · rw [Xc_split hW' hM hmem.1]; exact hmem.2
  refine le_antisymm ?_ ?_
  · rw [hTcL, hTcM]; exact csInf_le ⟨0, fun s hs => hs.1⟩ hin
  · rw [hTcL, hTcM]
    refine le_csInf ⟨_, hin⟩ fun t ht => ?_
    have htτ : (τ : ℝ) ≤ t := by
      by_contra h
      push Not at h
      exact absurd ht.2 (not_le.2 (hpos t ht.1 h))
    have hv : 0 ≤ t - τ := by linarith
    have hmemv : t - τ ∈ SM := by
      refine ⟨hv, ?_⟩
      have h := Xc_split (α := α) (Q := Q) hW' hM hv
      rw [add_sub_cancel] at h
      rw [← h]; exact ht.2
    have := csInf_le ⟨0, fun s hs => hs.1⟩ hmemv
    linarith

/-- **Splitting of the re-centred truncated path.** -/
theorem trunc_split {α Q L M S : ℝ} {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} {τ : ℝ≥0}
    (hW' : ∀ s, W' s ω = W (τ + s) ω - W τ ω)
    (hM : M = L + (Real.sqrt 2 * W τ ω + (α - Q) * (τ : ℝ)))
    (hT : ZoomRadial.Tc α Q L W ω = τ + ZoomRadial.Tc α Q M W' ω)
    (hS : S ≤ ZoomRadial.Tc α Q M W' ω) :
    ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω) =
      ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W' M ω) := by
  funext s
  simp only [ZoomRadial.trunc, ZoomRadial.zoomRadial]
  have hv : 0 ≤ ZoomRadial.Tc α Q M W' ω + max s (-S) := by
    have := le_max_right s (-S); linarith
  rw [hT, add_assoc, Xc_split hW' hM hv]

variable [MeasurableSpace Ω]

/-- **Joint measurability** of the re-centred truncated path and the first passage time, for a
path family with continuous sections and measurable evaluations. -/
theorem measurable_truncTc {b : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun t : ℝ≥0 => b t ω)
    (hm : ∀ t : ℝ≥0, Measurable (b t)) (α Q c S : ℝ) :
    Measurable fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q b c ω),
      ZoomRadial.Tc α Q c b ω) := by
  have hTc := D3Plus.measurable_Tc_of_cont hc (fun t => hm _) α Q c
  have hJ : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => ZoomRadial.Xc α Q c b ω t) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => D3Plus.continuous_Xc hc ω α Q c)
      (fun t => D3Plus.measurable_Xc (fun t => hm _) α Q c t)
  refine Measurable.prodMk (Measurable.of_eval fun s => ?_) hTc
  exact hJ.comp ((hTc.add_const (max s (-S))).prodMk measurable_id)

end T13Path
end QuantumZipper
