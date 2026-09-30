import QuantumZipper.Proofs.Thm18.LWExc3Circle
import QuantumZipper.Proofs.Thm18.LWExc2Refl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: the lower half of LW's key estimate, and Lemma 4.3

`lw43KeyLower_holds : LW43KeyLowerStmt` — the lower half of the key estimate
`h_η(z) ≍ Im z · diam η/(|z| + 1)²` for `Re z ≥ 0` (G. F. Lawler, B. M. Werness, *Multi-point
Green's functions for SLE and an estimate of Beffara*, Ann. Probab. 41 (2013), sketch of proof of
Lemma 4.3, p. 24, `literature/1011.3551.pdf`), with `c = c₀/40`.
Consequently `lw43Lower_holds : LW43LowerStmt` (via `lw43Lower_of_keyLower`) and
`lw43_holds : LW43Stmt` (LW Lemma 4.3, via `lw43Stmt_of_lower`).

Proof (LW state the key estimate without proof; own elementary argument, route of `LWExc43.lean`):
with `d = diam η`, pick `r ∈ {d/5, d/40}` so that the second endpoint `a` of `η` is off the
closed annulus `r/2 ≤ |z + 1| ≤ 2r`; `η` reaches beyond `|z + 1| = 2r` (`diam η = d > 4r`).
`lw3_circle` gives `h ≥ c₀ Im q/r` on `|q + 1| = r`; the harmonic function
`u = c₀ r Im z/|z + 1|²` equals `c₀ Im q / r` there, is `≤ c₀ ≤ 1` outside `B(−1, r)` and
vanishes on `ℝ` and at `∞`, so `u ≤ h` on `H_η \ B̄(−1, r)` by the weak maximum principle
`lwExc_harm_le_zero` (Ahlfors, *Complex Analysis*, Ch. 4 §6.2, Thm 21). For `Re z ≥ 0`,
`|z + 1| ≥ 1 > r` and `r ≥ d/40`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

lemma lw3Out_le {c r : ℝ} (hc : 0 ≤ c) (hr : 0 < r) {y : ℂ} (hy : 0 ≤ y.im) (hne : y + 1 ≠ 0) :
    lw3Out c r y ≤ c * r / ‖y + 1‖ := by
  have hn : 0 < ‖y + 1‖ := norm_pos_iff.2 hne
  have him : y.im ≤ ‖y + 1‖ := by
    have := Complex.abs_im_le_norm (y + 1); simp at this; linarith [le_abs_self y.im]
  rw [lw3Out_eq, div_le_div_iff₀ (by positivity) hn]
  have : c * r * y.im * ‖y + 1‖ ≤ c * r * ‖y + 1‖ * ‖y + 1‖ := by gcongr
  nlinarith

/-- **Comparison outside `B̄(−1, r)`.** -/
theorem lw3_outer {η : ℝ → ℂ} {h : ℂ → ℝ} (hη : IsCrosscutH η)
    (hm : IsHarmMeas (hullComp η) (arcH η) h) {r : ℝ} (hr : 0 < r)
    (hcirc : ∀ q ∈ hullComp η, ‖q + 1‖ = r → lw3c0 * (q.im / r) ≤ h q) :
    ∀ z ∈ hullComp η, r < ‖z + 1‖ → lw3c0 * r * z.im / ‖z + 1‖ ^ 2 ≤ h z := by
  set U := hullComp η ∩ {z : ℂ | r < ‖z + 1‖} with hUdef
  have hUo : IsOpen U := (lwExc_hullComp_isOpen hη).inter (isOpen_lt continuous_const (by fun_prop))
  have hUH : U ⊆ H := fun z hz => lwExc_hullComp_subset_H η hz.1
  have hUU : U ⊆ hullComp η := fun z hz => hz.1
  have hc0 := lw3c0_pos
  have hc1 := lw3c0_le_one
  have hUne : ∀ y ∈ U, y + 1 ≠ 0 := fun y hy he => by
    have := hy.2; rw [mem_setOf_eq, he, norm_zero] at this; linarith
  have hUle : ∀ y ∈ U, lw3Out lw3c0 r y ≤ lw3c0 := by
    intro y hy
    have h1 := lw3Out_le hc0.le hr (le_of_lt (hUH hy)) (hUne y hy)
    have h2 : lw3c0 * r / ‖y + 1‖ ≤ lw3c0 := by
      rw [div_le_iff₀ (norm_pos_iff.2 (hUne y hy))]
      have : r < ‖y + 1‖ := hy.2
      nlinarith
    linarith
  have key := lwExc_harm_le_zero (U := U) (f := fun w => lw3Out lw3c0 r w - h w) hUo
    (((lw3Out_harm _ _).mono hUH).sub (hm.harm.mono hUU)) ?_ ?_
  · intro z hz hzr
    have hk : lw3Out lw3c0 r z - h z ≤ 0 := key z ⟨hz, hzr⟩
    rw [lw3Out_eq] at hk
    linarith
  · intro x₀ hx₀ ε hε
    have hx₀cl : x₀ ∈ closure U := frontier_subset_closure hx₀
    have hclH : x₀ ∈ closure (hullComp η) := closure_mono hUU hx₀cl
    have hCr : IsClosed {z : ℂ | r ≤ ‖z + 1‖} := isClosed_le continuous_const (by fun_prop)
    have hr0 : r ≤ ‖x₀ + 1‖ :=
      closure_minimal (s := U) (t := {z : ℂ | r ≤ ‖z + 1‖})
        (fun z hz => le_of_lt (show r < ‖z + 1‖ from hz.2)) hCr hx₀cl
    have hCi : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    have hi0 : 0 ≤ x₀.im :=
      closure_minimal (s := U) (t := {z : ℂ | 0 ≤ z.im})
        (fun z hz => le_of_lt (show 0 < z.im from hUH hz)) hCi hx₀cl
    have hx₀ne : x₀ + 1 ≠ 0 := fun he => by rw [he, norm_zero] at hr0; linarith
    rcases hi0.eq_or_lt with him | him
    · -- real frontier point: `u → 0`
      have hcont : ContinuousAt (lw3Out lw3c0 r) x₀ := by
        have h1 : ContinuousAt (fun z : ℂ => (((-(lw3c0 * r)) : ℝ) : ℂ) * (z + 1)⁻¹) x₀ := by
          fun_prop (disch := exact hx₀ne)
        exact ContinuousAt.comp (g := Complex.im) Complex.continuous_im.continuousAt h1
      have hv : lw3Out lw3c0 r x₀ = 0 := by rw [lw3Out_eq, ← him]; simp
      obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hcont ε hε
      refine ⟨δ, hδ, fun y hy hdy => ?_⟩
      have h1 := hδs hdy
      rw [hv, Real.dist_eq, sub_zero] at h1
      have h3 := (hm.mem01 y (hUU hy)).1
      show lw3Out lw3c0 r y - h y ≤ ε
      linarith [le_abs_self (lw3Out lw3c0 r y)]
    by_cases hx₀a : x₀ ∈ arcH η
    · -- a point of `η`: `h → 1`
      have hx₀U : x₀ ∉ closure (frontier (hullComp η) \ arcH η) := by
        intro hc
        have hC : IsClosed {z : ℂ | z.im ≤ 0} := isClosed_le Complex.continuous_im continuous_const
        have h4 : x₀.im ≤ 0 :=
          closure_minimal (fun z hz => lw3_frontier_hull_im hη hz.1 hz.2) hC hc
        linarith
      have ht := hm.one x₀ hx₀a hx₀U
      have hev : ∀ᶠ y in 𝓝[hullComp η] x₀, 1 - ε < h y :=
        ht.eventually (lt_mem_nhds (by linarith))
      obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
      refine ⟨δ, hδ, fun y hy hdy => ?_⟩
      have h1 : 1 - ε < h y := hδs ⟨hdy, hUU hy⟩
      have h2 := hUle y hy
      show lw3Out lw3c0 r y - h y ≤ ε
      linarith
    · -- a point of the circle `|z + 1| = r` inside `H_η`
      have hx₀H : x₀ ∈ hullComp η := lw3_mem_hull_of_closure hη ⟨him, hx₀a⟩ hclH
      have hx₀nU : x₀ ∉ U := by rw [hUo.frontier_eq] at hx₀; exact hx₀.2
      have hx₀r : ‖x₀ + 1‖ = r := by
        by_contra hne
        exact hx₀nU ⟨hx₀H, lt_of_le_of_ne hr0 (Ne.symm hne)⟩
      have hval : lw3Out lw3c0 r x₀ - h x₀ ≤ 0 := by
        have := hcirc x₀ hx₀H hx₀r
        rw [lw3Out_eq, hx₀r]
        have : lw3c0 * r * x₀.im / r ^ 2 = lw3c0 * (x₀.im / r) := by field_simp
        linarith
      have hcont : ContinuousAt (fun w => lw3Out lw3c0 r w - h w) x₀ :=
        ((lw3Out_harm lw3c0 r x₀ him).1.continuousAt).sub (hm.harm x₀ hx₀H).1.continuousAt
      obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hcont ε hε
      refine ⟨δ, hδ, fun y hy hdy => ?_⟩
      have h1 := hδs hdy
      rw [Real.dist_eq] at h1
      have := le_abs_self (lw3Out lw3c0 r y - h y - (lw3Out lw3c0 r x₀ - h x₀))
      show lw3Out lw3c0 r y - h y ≤ ε
      linarith
  · intro ε hε
    refine ⟨lw3c0 * r / ε + 1, fun y hy hRy => ?_⟩
    have hn : ‖y‖ ≤ ‖y + 1‖ + 1 := by
      calc ‖y‖ = ‖(y + 1) + (-1)‖ := by ring_nf
        _ ≤ ‖y + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
        _ = ‖y + 1‖ + 1 := by simp
    have hpos : 0 < ‖y + 1‖ := norm_pos_iff.2 (hUne y hy)
    have h1 := lw3Out_le hc0.le hr (le_of_lt (hUH hy)) (hUne y hy)
    have h2 : lw3c0 * r / ‖y + 1‖ ≤ ε := by
      rw [div_le_iff₀ hpos]
      have : lw3c0 * r / ε ≤ ‖y + 1‖ := by linarith
      rw [div_le_iff₀ hε] at this
      linarith
    have h3 := (hm.mem01 y (hUU hy)).1
    show lw3Out lw3c0 r y - h y ≤ ε
    linarith

end LWFar
end Thm18Asm
end QuantumZipper
