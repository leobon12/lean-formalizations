/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8NativeWord
import InteractingSLE.Spec.Sec7.SideC5Relative
import InteractingSLE.Spec.Sec7.PocketSideInRealLanding
import InteractingSLE.Spec.ZhanGT4.A2Part3PC
import InteractingSLE.Spec.Sec7.R5PhaseClauses

/-!
# R.5's split cover, the pathwise core: wall coordinates and the hull-lift conversion

Packet PROVE-R5-WALL (ruling R86). Two pathwise facts used by the split clause-5 cover of `R5Phase.R5Clauses`:

* **Wall coordinates** (`wall_cover_pathwise`). At relative capacity `q`, a real current coordinate `ξ` outside the
  closed exposed interval `[v_L(q), v_R(q)]` (the images of the seeds, all marks at `0`) is the image of a real point
  `x ≠ 0` of the base chart that survives the relative Loewner flow up to `q` (`exists_surviving_of_wall`: the real
  flow is onto `(v_R, ∞)` and, by reflection, `(−∞, v_L)`). The **zero reference** (the relative chart at capacity `0`,
  i.e. the base chart) then has an unfilled collar at `x`, transition limit `x` and zero lift difference
  (`PocketStopSide.exists_own_collar_of_surviving_real`), the base-chart reading of any mean `v` at `x` transports to
  `ξ` along the inverse flow (`tendsto_inverse_of_surviving_real`), and the current word at `ξ` (with any phase) is the
  initial word at `x` (`PocketStopSide.force_word_of_surviving_real`). So the initial heights give R.5's clause 5 at
  `ξ` with `d = 0`; the landing of `ξ` is the base chart's boundary value at `x`.
* **The hull-lift conversion** (`tendsto_refLift_of_lift_sub`). On a collar of an earlier relative chart, a height
  limit read with any lift `ℓ` and a limit `d` of "current lift − `ℓ`" give the height limit read with the earlier
  chart's own lift, `b + χ d`, and lift difference `0` (`PocketStopSide.tendsto_relChart_lift_sub_zero`).

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open MartChar.RealFlow PocketStop PocketStopSide PocketTraversal Lemma71C PhaseSel

/-- **A surviving real point at every wall coordinate**: a real coordinate strictly left of the reflected seed image
`−rightImg(−W, 0, q) − W q` or strictly right of the seed image `rightImg(W, 0, q) − W q` is the image at time `q` of a
real point `x ≠ 0` alive up to `q`. -/
theorem exists_surviving_of_wall {W : ℝ → ℝ} (hW : Continuous W) {q : ℝ} (hq : 0 ≤ q) {ξ : ℝ}
    (hξ : ξ < -rightImg (fun s => -W s) 0 q - W q ∨ rightImg W 0 q - W q < ξ) :
    ∃ (x : ℝ) (a : ℝ → ℂ), x ≠ 0 ∧ QuantumZipper.IsForwardSol W (x : ℂ) q a ∧ (a q).re = ξ := by
  have hWn : Continuous fun s => -W s := continuous_neg.comp hW
  rcases hξ with hξ | hξ
  · obtain ⟨r, hr, hAlive, hg⟩ := ZhanGT4.A2X.P3.exists_alive_gImg_eq_of_rightImg_lt hWn hq
      (x := 0) (u := -ξ - W q) (by linarith)
    have hsol := QuantumZipper.RS.isForwardSol_neg (WangWu.isForwardSol_of_alive hWn hAlive)
    simp only [neg_neg] at hsol
    refine ⟨-r, fun t => -((cflow (fun s => -W s) r t : ℝ) : ℂ), by linarith, ?_, ?_⟩
    · rw [Complex.ofReal_neg]
      exact hsol
    · simp only [gImg] at hg
      simp only [Complex.neg_re, Complex.ofReal_re]
      linarith
  · obtain ⟨r, hr, hAlive, hg⟩ := ZhanGT4.A2X.P3.exists_alive_gImg_eq_of_rightImg_lt hW hq
      (u := ξ + W q) (by linarith)
    refine ⟨r, _, hr.ne', WangWu.isForwardSol_of_alive hW hAlive, ?_⟩
    simp only [gImg] at hg
    simp only [Complex.ofReal_re]
    linarith

/-- The boundary value `extendFrom ℍ f x` at a real point is any limit of `f` along `𝓝[ℍ] x`. -/
theorem extendFrom_eq_of_tendsto_H {f : ℂ → ℂ} {x : ℝ} {p : ℂ} (h : Tendsto f (𝓝[H] (x : ℂ)) (𝓝 p)) :
    extendFrom H f x = p := by
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (Complex.ofReal_im x))
  exact h.limUnder_eq

/-- **R.5's clause 5 at a wall coordinate from the initial heights, pathwise.** Let `q` be live, the base chart `c ω`
conformal with a continuous extension to `ℍ̄`, all marks at `0`, and let the base-chart reading
`v + u + χ ℓ_c` of a function `v` tend, at every real `x` off the initial jumps whose physical landing avoids `X`, to
the initial word at `x` minus `a`. Then at every real coordinate `ξ` off the jumps at `q`, outside the open exposed
interval, whose landing avoids `X`, the zero reference (the relative chart at capacity `0`) has an unfilled collar,
the transition limit, the reading of `v` in its own lift tending to some `b`, lift difference `d` tending to some `d`,
and `b + χ d` equal to the phase-shifted current word at `ξ` minus `a`, for every phase `δ`. -/
theorem wall_cover_pathwise {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω} {q : ℝ≥0}
    (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    (hcExt : ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : ∀ i, xL ω i = 0) (hxR : ∀ j, xR ω j = 0)
    {κ : ℝ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) {a δ : ℝ} {u v : ℂ → ℝ} {X : Set ℂ}
    (hInit : ∀ x : ℝ, x ∉ forceJumpSet (xL ω) (xR ω) → extendFrom H (c ω).2.1 x ∉ X →
      Tendsto (fun y => v ((c ω).2.1 y) + u ((c ω).2.1 y) + chiC κ * (c ω).2.2 ((c ω).2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (forceBoundaryData κ ρL ρR (xL ω) (xR ω) x - a)))
    {ξ : ℝ}
    (hξ : ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q))
    (hWall : ξ ∉ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
        (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q))
    (hX : extendFrom H (relChart c γ q ω).2.1 ξ ∉ X) :
    ∃ (x r b d : ℝ), 0 < r ∧
      (relChart c γ 0 ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
      Tendsto (fun z => (relChart c γ 0 ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (fun y => v ((relChart c γ q ω).2.1 y) + u ((relChart c γ q ω).2.1 y) +
          chiC κ * (relChart c γ 0 ω).2.2 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
          (relChart c γ 0 ω).2.2 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      b + chiC κ * d = phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) δ ξ - a := by
  obtain ⟨W, hW, hW0, q', hqq', hEq, hcur⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have h0 : relChart c γ 0 ω = (c ω).loewner W 0 := by
    change (c ω).loewner (fun s : ℝ => segDriver (γ ω) s.toNNReal) ((0 : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_zero]
    exact loewner_congr (c ω) le_rfl ((NNReal.coe_nonneg q).trans_lt hqq') hEq
  have hEqq : EqOn (fun r : ℝ => (fun t ω => segDriver (γ ω) t) r.toNNReal ω) W (Icc 0 (q : ℝ)) :=
    fun r hr => hEq r ⟨hr.1, hr.2.trans hqq'.le⟩
  obtain ⟨hposL, hposR⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hW hEqq
  have hL0 : geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q =
      -rightImg (fun s => -W s) 0 q - W q := by
    rw [congrFun hposL 0, hxL 0, neg_zero]
  have hR0 : geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q = rightImg W 0 q - W q := by
    rw [congrFun hposR 0, hxR 0]
  have hside : ξ < -rightImg (fun s => -W s) 0 q - W q ∨ rightImg W 0 q - W q < ξ := by
    have hne1 : ξ ≠ geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q :=
      fun h => hξ (Or.inr (Or.inl ⟨0, h.symm⟩))
    have hne2 : ξ ≠ geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q :=
      fun h => hξ (Or.inr (Or.inr ⟨0, h.symm⟩))
    rw [hL0] at hne1
    rw [hR0] at hne2
    rw [hL0, hR0] at hWall
    simp only [mem_Ioo, not_and_or, not_lt] at hWall
    rcases hWall with h | h
    · exact Or.inl (lt_of_le_of_ne h hne1)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hne2))
  obtain ⟨x, sol, hx0, ha, hre⟩ := exists_surviving_of_wall hW q.coe_nonneg hside
  subst hre
  have hxJ : x ∉ forceJumpSet (xL ω) (xR ω) := by
    rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
    · exact hx0 h
    · exact hx0 (by rw [← hi, hxL i])
    · exact hx0 (by rw [← hj, hxR j])
  have hy : (sol q).re ∉ forceJumpSet (fun i => -rightImg (fun s => -W s) (-xL ω i) q - W q)
      (fun j => rightImg W (xR ω j) q - W q) := by
    rw [← hposL, ← hposR]
    exact hξ
  have hword := force_word_of_surviving_real (κ := κ) hW hW0 q.coe_nonneg ha ρL ρR (xL ω) (xR ω) 0 0 (hxL 0)
    (hxR 0) hxJ hy δ
  have hInv := tendsto_inverse_of_surviving_real hW hW0 q.coe_nonneg ha
  obtain ⟨E, hE, hEc⟩ := hcExt
  have hcx : Tendsto (c ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 (E x)) := by
    have h1 : Tendsto E (𝓝[H] (x : ℂ)) (𝓝 (E x)) :=
      (hEc (x : ℂ) (mem_Hbar_of_im_eq_zero (Complex.ofReal_im x))).tendsto.mono_left
        (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)
    exact h1.congr' (eventually_nhdsWithin_of_forall fun z hz => hE hz)
  have hLand : extendFrom H (c ω).2.1 x = extendFrom H (relChart c γ q ω).2.1 (sol q).re := by
    rw [extendFrom_eq_of_tendsto_H hcx, hcur]
    exact (extendFrom_eq_of_tendsto_H (hcx.comp hInv)).symm
  have hXx : extendFrom H (c ω).2.1 x ∉ X := by
    rw [hLand]
    exact hX
  obtain ⟨ε, hε, hcol, htr, hlift⟩ := exists_own_collar_of_surviving_real hc hW hW0 le_rfl q.coe_nonneg ha
  have ha0 : (sol 0).re = x := by
    rw [QuantumZipper.FwdHolo.sol_zero ha q.coe_nonneg, hW0]
    simp
  rw [ha0] at hcol htr
  refine ⟨x, ε, forceBoundaryData κ ρL ρR (xL ω) (xR ω) x - a, 0, hε, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcur, h0]
    exact hcol
  · rw [hcur, h0]
    exact htr
  · rw [hcur, h0, Theorem14.GW2aCont.loewner_zero_lift]
    exact (hInit x hxJ hXx).comp hInv
  · rw [hcur, h0]
    exact hlift
  · rw [mul_zero, add_zero, hposL, hposR]
    simp only [phaseData]
    rw [hword]

/-- **The hull-lift conversion on a collar of an earlier relative chart**: a height limit `b` read with a lift `ℓ`
and a limit `d` of "current lift − `ℓ`" give the height limit `b + χ d` read with the earlier relative chart's own
lift, and lift difference `0`. -/
theorem tendsto_refLift_of_lift_sub {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω} {p q : ℝ≥0}
    (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q)
    {ξ x r : ℝ} (hr : 0 < r)
    (hcol : (relChart c γ p ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom)
    (htr : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    {κ b d : ℝ} {f g ℓ : ℂ → ℝ}
    (hb : Tendsto (fun y => f ((relChart c γ q ω).2.1 y) + g ((relChart c γ q ω).2.1 y) +
      chiC κ * ℓ ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 b))
    (hd : Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) - ℓ ((relChart c γ q ω).2.1 y))
      (𝓝[H] (ξ : ℂ)) (𝓝 d)) :
    Tendsto (fun y => f ((relChart c γ q ω).2.1 y) + g ((relChart c γ q ω).2.1 y) +
        chiC κ * (relChart c γ p ω).2.2 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (b + chiC κ * d)) ∧
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
        (relChart c γ p ω).2.2 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hz := tendsto_relChart_lift_sub_zero hc hγ hq hpq hr hcol htr
  refine ⟨?_, hz⟩
  have hsum := (hb.add (hd.const_mul (chiC κ))).sub (hz.const_mul (chiC κ))
  rw [mul_zero, sub_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun y => ?_)
  ring

end InteractingSLE.Sec7.R5Wall
