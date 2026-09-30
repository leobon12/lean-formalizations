import QuantumZipper.Proofs.Thm18.G1FrostAlphaDefs
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.Zipper.RegContEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FROST-B, part 1: a Koebe-type Frostman bound for univalent maps of `ℍ`

**`fcFrostmanα_of_univalent`**: if `ψ` is continuous on `Hbar`, holomorphic and injective on `ℍ`,
then `FcFrostmanα koebeFrostExp ψ`, with the explicit exponent
`koebeFrostExp = 1 / (2 (C₂ + 1))`, `C₂ = CA.Koebe.koebeDistExp` (the repository's non-sharp
Koebe distortion exponent). No regularity of the boundary is used.

Argument (fix `R`, a folded circle `fc(c, r)`, `‖c‖ ≤ 2R`, `r ∈ [e^{-R}, e^R]`, and a ball
`B̄(y, s)`; let `S` be the set of angles whose image lies in `B̄(y, s)`, and `t = (3s/(κa))^{2α}`):

* *(lower bound of `ψ'`)* `‖ψ'(w)‖ ≥ a (Im w)^{C₂}` on `ℍ ∩ {‖w‖ ≤ 2R + e^R}`
  (`G1.abs_log_norm_deriv_le_of_injOn`: Koebe distortion, Garnett–Marshall, *Harmonic Measure*,
  Ch. I, Thm 4.5, p. 22; Pommerenke, *Boundary Behaviour of Conformal Maps*, Prop. 1.2);
* *(all of `S` low)* if every point of the folded circle with angle in `S` has `Im < t`, the
  strip bound `TwoPoint.foldedCircle_strip_le` gives mass `≤ 18 √(t/r)`;
* *(a high point)* otherwise take `z₀` on the circle with `ψ z₀ ∈ B̄(y, s)`, `h = Im z₀ ≥ t`.
  With `ρ = 3s/(κ ‖ψ'(z₀)‖) ≤ t ≤ h`, Koebe's covering theorem
  (`CA.Koebe.ball_subset_image_koebe`, constant `κ = 1/48`; Garnett–Marshall Ch. I, Thm 4.3)
  gives `ψ(B(z₀, ρ)) ⊇ B(ψ z₀, 3s) ⊇ B̄(y, s)`; by injectivity on `ℍ` (and continuity on `Hbar`
  for the points on `ℝ`) every point of the circle with angle in `S` lies in `B̄(z₀, ρ)`, so
  the mass is `≤ 6ρ/r ≤ 6 e^R t` (`RegCont.foldedCircle_closedBall_le_arc`).

Both cases give `≲ t^{1/2} = (3s/(κa))^α`. This is an own argument (recorded in DEVIATIONS.md):
the sharp statement is Beurling's estimate (exponent `1/2`; Lawler, *Schramm–Loewner
evolution*, arXiv:0712.3256, Thm 2.10, p. 18), which needs harmonic measure /
extremal length, absent from mathlib and the repository; any positive exponent suffices
downstream (G1FrostAlphaVar.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open CircleFubini CA.Koebe

/-- The explicit Frostman exponent of the Koebe argument, `1 / (2 (C₂ + 1))`. -/
def koebeFrostExp : ℝ := 1 / (2 * (koebeDistExp + 1))

theorem koebeFrostExp_pos : 0 < koebeFrostExp := by
  unfold koebeFrostExp; have := koebeDistExp_pos; positivity

theorem koebeFrostExp_le_one : koebeFrostExp ≤ 1 := by
  unfold koebeFrostExp
  have := koebeDistExp_pos
  rw [div_le_one (by positivity)]
  linarith

/-- Angle sets of folded circles and the folded-circle measure. -/
theorem circM_foldH_preimage (c : ℂ) (r : ℝ) {E : Set ℂ} (hE : MeasurableSet E) :
    circM {θ | foldH (circleMap c r θ) ∈ E} = foldedCircle c r E := by
  rw [foldedCircle, Measure.map_apply measurable_foldH hE, circleUnif_eq_map,
    Measure.map_apply (continuous_circleMap c r).measurable (measurable_foldH hE)]
  rfl

/-- **Lower bound of `‖ψ'‖`** on bounded parts of `ℍ` (Koebe distortion). -/
theorem deriv_lower_of_injOn {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ H) (hinj : InjOn ψ H)
    {R1 : ℝ} (hR1 : 0 < R1) :
    ∃ a : ℝ, 0 < a ∧ ∀ w ∈ H, ‖w‖ ≤ R1 → a * w.im ^ koebeDistExp ≤ ‖deriv ψ w‖ := by
  obtain ⟨K, hK⟩ := G1.abs_log_norm_deriv_le_of_injOn hd hinj hR1
  refine ⟨Real.exp (-K - 2 * koebeDistExp * Real.log (R1 + 1)), Real.exp_pos _,
    fun w hw hwR => ?_⟩
  have hh : 0 < w.im := hw
  have hhR : w.im ≤ R1 := (le_abs_self _).trans ((Complex.abs_im_le_norm w).trans hwR)
  have hpd : 0 < ‖deriv ψ w‖ :=
    norm_pos_iff.2 (CA.Koebe.deriv_ne_zero_of_injOn isOpen_H hd hinj hw)
  have hk := (abs_le.1 (hK w hw hwR)).1
  have hC := koebeDistExp_pos
  have hlogR : Real.log w.im ≤ Real.log (R1 + 1) := Real.log_le_log hh (by linarith)
  have hlogR0 : 0 ≤ Real.log (R1 + 1) := Real.log_nonneg (by linarith)
  rw [Real.rpow_def_of_pos hh, ← Real.exp_add, ← Real.exp_log hpd]
  apply Real.exp_le_exp.2
  have h1 := mul_le_mul_of_nonneg_left hlogR hC.le
  have h2 := mul_nonneg hC.le hlogR0
  rcases le_total (Real.log w.im) 0 with hl | hl
  · rw [abs_of_nonpos hl] at hk; nlinarith
  · rw [abs_of_nonneg hl] at hk; nlinarith

/-- **Koebe covering + injectivity**: points of `Hbar` whose image is `ε`-close to `ψ z₀` lie
in `B̄(z₀, ρ)`, when `B(z₀, ρ) ⊆ ℍ` and `ε ≤ κ ρ ‖ψ'(z₀)‖`. -/
theorem mem_closedBall_of_image_near {ψ : ℂ → ℂ} (hc : ContinuousOn ψ Hbar)
    (hd : DifferentiableOn ℂ ψ H) (hinj : InjOn ψ H) {z0 : ℂ} {ρ ε : ℝ}
    (hball : ball z0 ρ ⊆ H) (hε : ε ≤ koebeCovConst * ρ * ‖deriv ψ z0‖) {z : ℂ}
    (hz : z ∈ Hbar) (hzε : ‖ψ z - ψ z0‖ < ε) : z ∈ closedBall z0 ρ := by
  have hH : ∀ z' ∈ H, ‖ψ z' - ψ z0‖ < ε → z' ∈ ball z0 ρ := by
    intro z' hz' hz'ε
    have hmem : ψ z' ∈ ball (ψ z0) (koebeCovConst * ρ * ‖deriv ψ z0‖) := by
      rw [mem_ball, dist_eq_norm]; linarith
    obtain ⟨z'', hz'', heq⟩ := ball_subset_image_koebe (hd.mono hball) (hinj.mono hball) hmem
    rwa [← hinj (hball hz'') hz' heq]
  by_contra hn
  rw [mem_closedBall, not_le] at hn
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hc z hz)
    (ε - ‖ψ z - ψ z0‖) (by linarith)
  set η := min (δ / 2) ((dist z z0 - ρ) / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  set z' : ℂ := z + (η : ℂ) * Complex.I with hz'
  have hz'im : z'.im = z.im + η := by simp [hz']
  have hz'H : z' ∈ H := by
    show 0 < z'.im
    have : (0 : ℝ) ≤ z.im := hz
    rw [hz'im]; linarith
  have hdz : dist z' z = η := by
    rw [dist_eq_norm, hz', add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
  have hz'Hb : z' ∈ Hbar := by show (0 : ℝ) ≤ z'.im; exact le_of_lt hz'H
  have hdz' : dist z' z < δ := by
    rw [hdz]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hclose := hδc hz'Hb hdz'
  rw [dist_eq_norm] at hclose
  have htri : ‖ψ z' - ψ z0‖ ≤ ‖ψ z' - ψ z‖ + ‖ψ z - ψ z0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hin := hH z' hz'H (by linarith)
  rw [mem_ball] at hin
  have h3 := dist_triangle z z' z0
  rw [dist_comm z z', hdz] at h3
  have : η ≤ (dist z z0 - ρ) / 2 := min_le_right _ _
  linarith

theorem koebeFrostExp_identity :
    2 * koebeFrostExp * koebeDistExp + 2 * koebeFrostExp = 1 := by
  unfold koebeFrostExp
  have := koebeDistExp_pos
  field_simp

/-- **Koebe-type Frostman bound for univalent maps of `ℍ`** (exponent `koebeFrostExp`). -/
theorem fcFrostmanα_of_univalent {ψ : ℂ → ℂ} (hc : ContinuousOn ψ Hbar)
    (hd : DifferentiableOn ℂ ψ H) (hinj : InjOn ψ H) : FcFrostmanα koebeFrostExp ψ := by
  intro R
  have hRr : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  set eR := Real.exp (R : ℝ) with heR
  have heR1 : 1 ≤ eR := Real.one_le_exp hRr
  set R1 : ℝ := 2 * R + eR with hR1def
  have hR1 : 0 < R1 := by positivity
  obtain ⟨a, ha, hlow⟩ := deriv_lower_of_injOn hd hinj hR1
  have hκ0 : 0 < koebeCovConst := koebeCovConst_pos
  have hq0 : 0 < koebeDistExp := koebeDistExp_pos
  have hα0 : 0 < koebeFrostExp := koebeFrostExp_pos
  set D := 3 / (koebeCovConst * a) with hD
  have hD0 : 0 < D := by positivity
  refine ⟨25 * eR * D ^ koebeFrostExp, by positivity, ?_⟩
  intro c hc2 r hr1 hr2 y s hs
  have hr : 0 < r := (Real.exp_pos _).trans_le hr1
  have hrinv : 1 / r ≤ eR := by
    rw [div_le_iff₀ hr]
    calc (1 : ℝ) = eR * Real.exp (-(R : ℝ)) := by rw [heR, ← Real.exp_add]; simp
      _ ≤ eR * r := mul_le_mul_of_nonneg_left hr1 (by positivity)
  set X := D * s with hX
  have hX0 : 0 < X := by positivity
  set u := X ^ koebeFrostExp with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hX0 _
  set t := X ^ (2 * koebeFrostExp) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hX0 _
  have htu : u ^ 2 = t := by
    rw [hu, ht, mul_comm 2 koebeFrostExp]
    exact_mod_cast (Real.rpow_mul_natCast hX0.le koebeFrostExp 2).symm
  have htq : t ^ koebeDistExp * t = X := by
    rw [ht, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, koebeFrostExp_identity,
      Real.rpow_one]
  have hXe : koebeCovConst * a * X = 3 * s := by
    rw [hX, hD]; field_simp
  set S := {θ : ℝ | ψ (foldH (circleMap c r θ)) ∈ closedBall y s} with hS
  have hzR : ∀ θ, ‖foldH (circleMap c r θ)‖ ≤ R1 := fun θ => by
    rw [CircleFubini.norm_foldH']
    exact (TwoPoint.norm_circleMap_le_add c hr.le θ).trans (by linarith)
  have hDu : D ^ koebeFrostExp * s ^ koebeFrostExp = u := by
    rw [hu, hX, Real.mul_rpow hD0.le hs.le]
  suffices hmain : (circM S).toReal ≤ 25 * eR * u by
    calc (circM S).toReal ≤ 25 * eR * u := hmain
      _ = 25 * eR * D ^ koebeFrostExp * s ^ koebeFrostExp := by rw [← hDu]; ring
  have heRu : 0 < eR * u := by positivity
  by_cases hB : ∃ θ ∈ S, t ≤ (foldH (circleMap c r θ)).im
  · obtain ⟨θ0, hθ0, hθt⟩ := hB
    set z0 := foldH (circleMap c r θ0) with hz0
    have hz0H : z0 ∈ H := show 0 < z0.im from ht0.trans_le hθt
    have hder := hlow z0 hz0H (hzR θ0)
    have hdpos : 0 < ‖deriv ψ z0‖ :=
      norm_pos_iff.2 (CA.Koebe.deriv_ne_zero_of_injOn isOpen_H hd hinj hz0H)
    set ρ := 3 * s / (koebeCovConst * ‖deriv ψ z0‖) with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρt : ρ ≤ t := by
      have h1 : a * t ^ koebeDistExp ≤ ‖deriv ψ z0‖ :=
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0.le hθt hq0.le) ha.le).trans hder
      rw [hρ, div_le_iff₀ (by positivity)]
      calc 3 * s = koebeCovConst * a * (t ^ koebeDistExp * t) := by rw [htq, hXe]
        _ = t * (koebeCovConst * (a * t ^ koebeDistExp)) := by ring
        _ ≤ t * (koebeCovConst * ‖deriv ψ z0‖) := by gcongr
    have hball : ball z0 ρ ⊆ H := fun w hw => by
      rw [mem_ball, dist_eq_norm] at hw
      have h1 := Complex.abs_im_le_norm (w - z0)
      rw [Complex.sub_im] at h1
      have h2 := neg_abs_le (w.im - z0.im)
      show 0 < w.im
      linarith
    have hε : 3 * s ≤ koebeCovConst * ρ * ‖deriv ψ z0‖ := by
      rw [hρ]; field_simp; exact le_rfl
    have hsub : S ⊆ {θ | foldH (circleMap c r θ) ∈ closedBall z0 ρ} := by
      intro θ hθ
      have hθ' : ψ (foldH (circleMap c r θ)) ∈ closedBall y s := hθ
      have hθ0' : ψ z0 ∈ closedBall y s := hθ0
      rw [mem_closedBall, dist_eq_norm] at hθ' hθ0'
      refine mem_closedBall_of_image_near hc hd hinj hball hε (foldH_mem_Hbar' _) ?_
      calc ‖ψ (foldH (circleMap c r θ)) - ψ z0‖
          ≤ ‖ψ (foldH (circleMap c r θ)) - y‖ + ‖y - ψ z0‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ s + s := by rw [norm_sub_rev y]; linarith
        _ < 3 * s := by linarith
    have hm1 : (circM S).toReal ≤ 6 * ρ / r := by
      have := (measure_mono hsub).trans ((circM_foldH_preimage c r
        measurableSet_closedBall).le.trans
          (RegCont.foldedCircle_closedBall_le_arc c z0 hr hρ0.le))
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
    have hm2 : (circM S).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    have h6 : 6 * ρ / r ≤ 6 * eR * t := by
      rw [div_eq_mul_one_div]
      calc 6 * ρ * (1 / r) ≤ 6 * t * eR :=
            mul_le_mul (by linarith) hrinv (by positivity) (by positivity)
        _ = 6 * eR * t := by ring
    rcases le_total u 1 with hu1 | hu1
    · have htu' : t ≤ u := by rw [← htu]; nlinarith
      have := mul_le_mul_of_nonneg_left htu' (by positivity : (0 : ℝ) ≤ 6 * eR)
      nlinarith
    · have := mul_le_mul_of_nonneg_right heR1 hu0.le
      nlinarith
  · push Not at hB
    have hmeas : MeasurableSet {x : ℂ | |x.im| < t} :=
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).measurableSet
    have hsub : S ⊆ {θ | foldH (circleMap c r θ) ∈ {x : ℂ | |x.im| < t}} := by
      intro θ hθ
      have h0 : (0 : ℝ) ≤ (foldH (circleMap c r θ)).im := foldH_mem_Hbar' _
      show |(foldH (circleMap c r θ)).im| < t
      rw [abs_of_nonneg h0]; exact hB θ hθ
    have hm := (measure_mono hsub).trans ((circM_foldH_preimage c r hmeas).le.trans
      (TwoPoint.foldedCircle_strip_le c hr ht0))
    have hm' := ENNReal.toReal_le_of_le_ofReal (by positivity) hm
    have hsq : Real.sqrt (t / r) ≤ eR * u := by
      rw [show eR * u = Real.sqrt ((eR * u) ^ 2) from (Real.sqrt_sq heRu.le).symm]
      apply Real.sqrt_le_sqrt
      rw [mul_pow, htu]
      calc t / r = t * (1 / r) := by ring
        _ ≤ t * eR := mul_le_mul_of_nonneg_left hrinv ht0.le
        _ ≤ eR ^ 2 * t := by
          nlinarith [mul_le_mul_of_nonneg_left heR1 (by positivity : (0 : ℝ) ≤ eR * t)]
    linarith

end G1RC
end Thm18Asm
end QuantumZipper
