import QuantumZipper.Proofs.Thm18.LWExc3Sep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: `h_η ≥ c₀ Im z / r` on the semicircle `|z + 1| = r`

`lw3_circle`: under the hypotheses of Lawler–Werness Lemma 4.3 (Ann. Probab. 41 (2013), p. 23),
if the crosscut `η` reaches beyond `|z + 1| = 2r` and its second endpoint `a` is off the closed
annulus `r/2 ≤ |z + 1| ≤ 2r`, then the harmonic measure `h` of `η` in `H_η` satisfies
`h(q) ≥ c₀ Im q / r` for `q ∈ H_η` with `|q + 1| = r` (`c₀ = k/sinh(kπ)`, `k = π/(2 log 2)`).

Proof (LW's sketch p. 24 leaves the key estimate unproved; route recorded in `LWExc43.lean`):
`W` = the component of `q` in (upper half-annulus) `\ η`. By `lw3_sep`, `closure W` misses one of
the two open real sides; the log-polar minorant `lw3Min s r` (`s = ±1` chosen accordingly),
which vanishes on both semicircles and on the real side that `W` may touch and is `≤ 1` on `η`, is `≤ h` on `W` by the weak maximum principle `lwExc_harm_le_zero` (Ahlfors, Ch. 4 §6.2,
Thm 21); its value at `q` is `≥ c₀ Im q / r` (`lw3Min_circle`). Own elementary argument.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- A point of an open set `S` in the closure of a component of `S` lies in that component. -/
lemma lw3_mem_comp_of_closure {S : Set ℂ} (hS : IsOpen S) {q z : ℂ} (hz : z ∈ S)
    (hcl : z ∈ closure (connectedComponentIn S q)) : z ∈ connectedComponentIn S q := by
  obtain ⟨y, hyz, hyq⟩ := mem_closure_iff.1 hcl _ hS.connectedComponentIn
    (mem_connectedComponentIn hz)
  rw [connectedComponentIn_eq hyq, ← connectedComponentIn_eq hyz]
  exact mem_connectedComponentIn hz

/-- A point of `ℍ \ η` in the closure of `H_η` lies in `H_η`. -/
lemma lw3_mem_hull_of_closure {η : ℝ → ℂ} (hη : IsCrosscutH η) {z : ℂ} (hz : z ∈ H \ arcH η)
    (hcl : z ∈ closure (hullComp η)) : z ∈ hullComp η := by
  have hS := lwExc_isOpen_H_diff_arc hη
  obtain ⟨y, hyz, hyU⟩ := mem_closure_iff.1 hcl _ hS.connectedComponentIn
    (mem_connectedComponentIn hz)
  refine ⟨hz, ?_⟩
  rw [connectedComponentIn_eq hyz]
  exact hyU.2

/-- The frontier of `H_η` off `η` is real. -/
lemma lw3_frontier_hull_im {η : ℝ → ℂ} (hη : IsCrosscutH η) {z : ℂ}
    (hz : z ∈ frontier (hullComp η)) (hza : z ∉ arcH η) : z.im ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hU := lwExc_hullComp_isOpen hη
  rw [hU.frontier_eq] at hz
  exact hz.2 (lw3_mem_hull_of_closure hη ⟨hpos, hza⟩ hz.1)

/-- Real points other than the endpoints are off `closure η`. -/
lemma lw3_real_not_mem_closure {η : ℝ → ℂ} (hη : IsCrosscutH η) {a0 b1 : ℂ}
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 a0)) (h1 : Tendsto η (𝓝[<] 1) (𝓝 b1)) {x : ℂ}
    (hx : x.im = 0) (hx0 : x ≠ a0) (hx1 : x ≠ b1) : x ∉ closure (arcH η) := by
  intro hxc
  set ρ := min (dist x a0) (dist x b1) / 2 with hρ
  have hρ0 : 0 < ρ := by
    have := dist_pos.2 hx0; have := dist_pos.2 hx1; rw [hρ]; positivity
  obtain ⟨δ₀, δ₁, hδ₀, hδ₁, hK, hcov⟩ := lwExc_arc_cover hη.1 h0 h1 hρ0
  have hcl := closure_mono hcov hxc
  rw [closure_union, closure_union, hK.isClosed.closure_eq] at hcl
  rcases hcl with (h | h) | h
  · have := closure_ball_subset_closedBall h
    rw [mem_closedBall] at this
    have : ρ < dist x a0 := by
      rw [hρ]; have := min_le_left (dist x a0) (dist x b1); have := dist_pos.2 hx0; linarith
    linarith
  · have := closure_ball_subset_closedBall h
    rw [mem_closedBall] at this
    have : ρ < dist x b1 := by
      rw [hρ]; have := min_le_right (dist x a0) (dist x b1); have := dist_pos.2 hx1; linarith
    linarith
  · obtain ⟨s, hs, hse⟩ := h
    have : 0 < (η s).im := hη.2.2.1 ⟨lt_of_lt_of_le hδ₀ hs.1, lt_of_le_of_lt hs.2 hδ₁⟩
    rw [hse, hx] at this
    exact lt_irrefl _ this

lemma lw3Ann_isOpen (r : ℝ) : IsOpen (lw3Ann r) := by
  have : lw3Ann r = {z : ℂ | 0 < z.im} ∩ ({z : ℂ | r / 2 < ‖z + 1‖} ∩ {z : ℂ | ‖z + 1‖ < 2 * r}) :=
    rfl
  rw [this]
  exact (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const))

lemma lw3_closure_ann {r : ℝ} {W : Set ℂ} (hW : W ⊆ lw3Ann r) {z : ℂ} (hz : z ∈ closure W) :
    0 ≤ z.im ∧ r / 2 ≤ ‖z + 1‖ ∧ ‖z + 1‖ ≤ 2 * r := by
  have hC : IsClosed ({z : ℂ | 0 ≤ z.im} ∩ ({z : ℂ | r / 2 ≤ ‖z + 1‖} ∩
      {z : ℂ | ‖z + 1‖ ≤ 2 * r})) :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      ((isClosed_le continuous_const (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const))
  refine closure_minimal (fun w hw => ?_) hC hz
  obtain ⟨a1, a2, a3⟩ := hW hw
  exact ⟨a1.le, a2.le, a3.le⟩

/-- **`h_η ≥ c₀ Im q / r` on `|q + 1| = r`** (see the module docstring). -/
theorem lw3_circle {η : ℝ → ℂ} {a : ℝ} {h : ℂ → ℝ} (hη : IsCrosscutH η)
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 (-1 : ℂ))) (h1 : Tendsto η (𝓝[<] 1) (𝓝 (a : ℂ)))
    (hm : IsHarmMeas (hullComp η) (arcH η) h) {r : ℝ} (hr : 0 < r)
    (hfar : ∃ p ∈ arcH η, 2 * r < ‖p + 1‖)
    (ha : ‖(a : ℂ) + 1‖ < r / 2 ∨ 2 * r < ‖(a : ℂ) + 1‖)
    {q : ℂ} (hq : q ∈ hullComp η) (hqr : ‖q + 1‖ = r) : lw3c0 * (q.im / r) ≤ h q := by
  have hSo : IsOpen (lw3Ann r \ arcH η) := by
    have : lw3Ann r \ arcH η = lw3Ann r ∩ (H \ arcH η) := by
      ext z; constructor
      · rintro ⟨hz, hza⟩; exact ⟨hz, hz.1, hza⟩
      · rintro ⟨hz, -, hza⟩; exact ⟨hz, hza⟩
    rw [this]; exact (lw3Ann_isOpen r).inter (lwExc_isOpen_H_diff_arc hη)
  have hqim : 0 < q.im := lwExc_hullComp_subset_H η hq
  have hqA : q ∈ lw3Ann r := by
    show 0 < q.im ∧ r / 2 < ‖q + 1‖ ∧ ‖q + 1‖ < 2 * r
    rw [hqr]; exact ⟨hqim, by linarith, by linarith⟩
  have hqS : q ∈ lw3Ann r \ arcH η := ⟨hqA, hq.1.2⟩
  set W := connectedComponentIn (lw3Ann r \ arcH η) q with hWdef
  have hWo : IsOpen W := hSo.connectedComponentIn
  have hWc : IsConnected W := isConnected_connectedComponentIn_iff.2 hqS
  have hWS : W ⊆ lw3Ann r \ arcH η := connectedComponentIn_subset _ _
  have hWA : W ⊆ lw3Ann r := fun z hz => (hWS hz).1
  have hWη : Disjoint W (arcH η) := Set.disjoint_left.2 fun z hz => (hWS hz).2
  have hWU : W ⊆ hullComp η := by
    intro w hw
    have hw' : w ∈ connectedComponentIn (H \ arcH η) q :=
      connectedComponentIn_mono q (G := H \ arcH η) (fun z hz => ⟨(hz.1).1, hz.2⟩) hw
    refine ⟨connectedComponentIn_subset _ _ hw', ?_⟩
    rw [← connectedComponentIn_eq hw']
    exact hq.2
  have hWH : W ⊆ H := fun z hz => (hWA hz).1
  have hreal : ∀ x : ℝ, r / 2 < ‖(x : ℂ) + 1‖ → ‖(x : ℂ) + 1‖ < 2 * r →
      (x : ℂ) ∉ closure (arcH η) := by
    intro x hx1 hx2
    refine lw3_real_not_mem_closure hη h0 h1 (by simp) ?_ ?_
    · intro he; rw [he] at hx1; norm_num at hx1; linarith
    · intro he; rw [he] at hx1 hx2; rcases ha with ha | ha <;> linarith
  have hne : ∀ x : ℝ, r / 2 < ‖(x : ℂ) + 1‖ → x + 1 ≠ 0 := by
    intro x hx he
    have : (x : ℂ) + 1 = 0 := by exact_mod_cast he
    rw [this, norm_zero] at hx; linarith
  obtain ⟨s, hs, hside⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x : ℝ, (x : ℂ) ∈ closure W →
      r / 2 < ‖(x : ℂ) + 1‖ → ‖(x : ℂ) + 1‖ < 2 * r → 0 < s * (x + 1) := by
    by_cases hL : ∃ x₁ : ℝ, x₁ + 1 < 0 ∧ (x₁ : ℂ) ∈ closure W ∧ r / 2 < ‖(x₁ : ℂ) + 1‖ ∧
        ‖(x₁ : ℂ) + 1‖ < 2 * r
    · obtain ⟨x₁, hx₁, hx₁W, hx₁a, hx₁b⟩ := hL
      refine ⟨-1, Or.inr rfl, fun x hxW hxa hxb => ?_⟩
      rcases lt_or_gt_of_ne (hne x hxa) with hlt | hgt
      · linarith
      · exact (lw3_sep hη h0 hr hfar hWo hWc hWA hWη hx₁ hgt hx₁W hxW (hreal x₁ hx₁a hx₁b)
          (hreal x hxa hxb) ⟨hx₁a, hx₁b⟩ ⟨hxa, hxb⟩).elim
    · refine ⟨1, Or.inl rfl, fun x hxW hxa hxb => ?_⟩
      rcases lt_or_gt_of_ne (hne x hxa) with hlt | hgt
      · exact (hL ⟨x, hlt, hxW, hxa, hxb⟩).elim
      · linarith
  have key := lwExc_harm_le_zero (U := W) (f := fun w => lw3Min s r w - h w) hWo
    (((lw3Min_harm hs hr).mono hWH).sub (hm.harm.mono hWU)) ?_ ?_
  · have hk : lw3Min s r q - h q ≤ 0 := key q (mem_connectedComponentIn hqS)
    linarith [lw3Min_circle hs hr hqim hqr]
  · intro x₀ hx₀ ε hε
    have hx₀cl : x₀ ∈ closure W := frontier_subset_closure hx₀
    obtain ⟨hi0, hn1, hn2⟩ := lw3_closure_ann hWA hx₀cl
    have hx₀ne : x₀ + 1 ≠ 0 := fun he => by rw [he, norm_zero] at hn1; linarith
    by_cases hcirc : ‖x₀ + 1‖ = r / 2 ∨ ‖x₀ + 1‖ = 2 * r
    · have hpos : 2 / r * ‖x₀ + 1‖ ≠ 0 :=
        mul_ne_zero (by positivity) (norm_ne_zero_iff.2 hx₀ne)
      have hn : ContinuousAt (fun y : ℂ => 2 / r * ‖y + 1‖) x₀ := by fun_prop
      have hl : ContinuousAt (fun y : ℂ => Real.log (2 / r * ‖y + 1‖)) x₀ := hn.log hpos
      have hg : ContinuousAt (fun y : ℂ => Real.sin (lw3k * Real.log (2 / r * ‖y + 1‖))) x₀ :=
        ContinuousAt.comp (g := Real.sin) (f := fun y : ℂ => lw3k * Real.log (2 / r * ‖y + 1‖))
          Real.continuous_sin.continuousAt (continuousAt_const.mul hl)
      have hg0 : Real.sin (lw3k * Real.log (2 / r * ‖x₀ + 1‖)) = 0 := by
        rcases hcirc with hc | hc <;> rw [hc]
        · rw [show 2 / r * (r / 2) = 1 by field_simp, Real.log_one, mul_zero, Real.sin_zero]
        · rw [show 2 / r * (2 * r) = 4 by field_simp; ring, lw3k_log4, Real.sin_pi]
      obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hg ε hε
      refine ⟨δ, hδ, fun y hy hdy => ?_⟩
      have h1 := hδs hdy
      rw [hg0, Real.dist_eq, sub_zero] at h1
      have h2 := lw3Min_le_S hs hr (hWH hy)
      have h3 := (hm.mem01 y (hWU hy)).1
      show lw3Min s r y - h y ≤ ε
      linarith
    push Not at hcirc
    have hn1' : r / 2 < ‖x₀ + 1‖ := lt_of_le_of_ne hn1 (Ne.symm hcirc.1)
    have hn2' : ‖x₀ + 1‖ < 2 * r := lt_of_le_of_ne hn2 hcirc.2
    rcases hi0.eq_or_lt with him | him
    · have hx₀r : x₀ = ((x₀.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [← him]
      have hsd := hside x₀.re (by rw [← hx₀r]; exact hx₀cl) (by rw [← hx₀r]; exact hn1')
        (by rw [← hx₀r]; exact hn2')
      have hre : ((s : ℂ) * (x₀ + 1)).re = s * (x₀.re + 1) := by simp
      have him' : ((s : ℂ) * (x₀ + 1)).im = 0 := by simp [← him]
      have hsl : (s : ℂ) * (x₀ + 1) ∈ slitPlane := by
        rw [mem_slitPlane_iff]; left; rw [hre]; exact hsd
      have harg0 : arg ((s : ℂ) * (x₀ + 1)) = 0 :=
        arg_eq_zero_iff.2 ⟨by rw [hre]; exact hsd.le, him'⟩
      have hA : ContinuousAt (fun y : ℂ => arg ((s : ℂ) * (y + 1))) x₀ :=
        ContinuousAt.comp (g := arg) (f := fun y : ℂ => (s : ℂ) * (y + 1)) (continuousAt_arg hsl)
          (by fun_prop)
      have hT : ContinuousAt (fun y : ℂ => Real.sinh (lw3k * (s * arg ((s : ℂ) * (y + 1)))) /
          Real.sinh (lw3k * π)) x₀ :=
        (ContinuousAt.comp (g := Real.sinh)
          (f := fun y : ℂ => lw3k * (s * arg ((s : ℂ) * (y + 1))))
          Real.continuous_sinh.continuousAt
          (continuousAt_const.mul (continuousAt_const.mul hA))).div_const _
      obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hT ε hε
      refine ⟨δ, hδ, fun y hy hdy => ?_⟩
      have h1 := hδs hdy
      rw [harg0, mul_zero, mul_zero, Real.sinh_zero, zero_div, Real.dist_eq, sub_zero] at h1
      have h2 := lw3Min_le_T hs hr (hWH hy)
      have h3 := (hm.mem01 y (hWU hy)).1
      show lw3Min s r y - h y ≤ ε
      linarith [le_abs_self (Real.sinh (lw3k * (s * arg ((s : ℂ) * (y + 1)))) /
          Real.sinh (lw3k * π))]
    · have hx₀A : x₀ ∈ lw3Ann r := show 0 < x₀.im ∧ _ ∧ _ from ⟨him, hn1', hn2'⟩
      have hx₀W : x₀ ∉ W := by rw [hWo.frontier_eq] at hx₀; exact hx₀.2
      have hx₀a : x₀ ∈ arcH η := by
        by_contra hna
        exact hx₀W (lw3_mem_comp_of_closure hSo ⟨hx₀A, hna⟩ hx₀cl)
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
      have h1 : 1 - ε < h y := hδs ⟨hdy, hWU hy⟩
      have h2 := lw3Min_le_one hs hr (hWH hy)
      show lw3Min s r y - h y ≤ ε
      linarith
  · intro ε hε
    refine ⟨2 * r + 2, fun y hy hRy => ?_⟩
    exfalso
    have h1 := (hWA hy).2.2
    have h2 : ‖y‖ ≤ ‖y + 1‖ + 1 := by
      calc ‖y‖ = ‖(y + 1) + (-1)‖ := by ring_nf
        _ ≤ ‖y + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
        _ = ‖y + 1‖ + 1 := by simp
    linarith

end LWFar
end Thm18Asm
end QuantumZipper
