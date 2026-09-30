import QuantumZipper.Proofs.Thm18.LWExcDefs
import QuantumZipper.Proofs.Thm18.LWHarmPoisson

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): existence of harmonic measure via a boundary parametrization

Task LW-HARM (A). Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge 2005,
Ch. I §1, p. 5 (`literature/GarnettMarshall_HarmonicMeasure_2005.pdf`, PDF p. 23, eq. (1.6)):
the harmonic measure of a boundary set in a simply connected domain is the half-plane harmonic
measure of its preimage under a conformal map, `ω(z, E, D) = ω(φ(z), φ(E), ℍ)`, for maps with a
boundary correspondence (Carathéodory, Pommerenke, *Boundary Behaviour of Conformal Maps*,
Thm 2.1/2.6). We formalize exactly this, for a conformal map `G : D → ℍ` whose inverse `F`
extends continuously to `ℍ̄` (`LWBdryParam`), as `F` provides for `ℍ` minus a Loewner hull
(`CaraR.revMapCaratheodory`, `IsCaratheodoryRevExt`):

`lwHarm_isHarmMeas`: `IsHarmMeas D A (ω(G(·), int {t ∈ ℝ | F t ∈ A}, ℍ))` for bounded `A`
disjoint from `D`, if `F → ∞` at `∞` or `F(∞) ∉ closure A`.

The boundary-value argument (a preimage cluster point of `x₀` in `ℍ̄` is a real `t` with
`F t = x₀`, by compactness of `closure B ∩ closedBall 0 R` and continuity of `F`) is our own
elementary write-up of the standard proof (GM p. 5 only says the conditions (i)–(iii) transfer).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology NNReal Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- `G : D → ℍ` holomorphic with a left inverse `F`, continuous on `ℍ̄`, mapping `ℍ` into `D`
and `ℝ` off `D` (a conformal map with continuous boundary extension of its inverse). -/
structure LWBdryParam (D : Set ℂ) (F G : ℂ → ℂ) : Prop where
  isOpen : IsOpen D
  diffG : DifferentiableOn ℂ G D
  mapsG : MapsTo G D H
  inv : ∀ z ∈ D, F (G z) = z
  contF : ContinuousOn F Hbar
  mapsF : MapsTo F H D
  bdry : ∀ t : ℝ, F t ∉ D

/-- The harmonic measure built from the parametrization (GM (1.6)). -/
def lwHarmOf (F G : ℂ → ℂ) (A : Set ℂ) (z : ℂ) : ℝ :=
  lwHarmOm (interior {t : ℝ | F t ∈ A}) (G z)

variable {D A : Set ℂ} {F G : ℂ → ℂ}

lemma lwHarm_ev_far {p : ℂ → Prop} (h : ∀ᶠ w in Bornology.cobounded ℂ ⊓ 𝓟 Hbar, p w) :
    ∃ R, ∀ w ∈ Hbar, R < ‖w‖ → p w := by
  rw [eventually_inf_principal] at h
  obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 h
  exact ⟨R, fun w hw hwR => hR (by simpa [mem_closedBall, dist_zero_right] using hwR) hw⟩

lemma lwHarm_real_mem_Hbar (t : ℝ) : (t : ℂ) ∈ Hbar := by simp [Hbar]

lemma lwHarm_cont_real (P : LWBdryParam D F G) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℝ, |s - t| < δ → dist (F s) (F t) < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1
    (P.contF (t : ℂ) (lwHarm_real_mem_Hbar t)) ε hε
  refine ⟨δ, hδ, fun s hs => h (lwHarm_real_mem_Hbar s) ?_⟩
  rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hs

lemma lwHarm_real_mem_closure_H (t : ℝ) : (t : ℂ) ∈ closure H := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(t : ℂ) + (ε / 2 : ℝ) * I, ?_, ?_⟩
  · show 0 < ((t : ℂ) + (ε / 2 : ℝ) * I).im
    simp; linarith
  · rw [Complex.dist_eq]
    simp only [sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    linarith

lemma lwHarm_F_frontier (P : LWBdryParam D F G) (t : ℝ) : F t ∈ frontier D := by
  rw [P.isOpen.frontier_eq]
  refine ⟨?_, P.bdry t⟩
  have hc : ContinuousWithinAt F H t :=
    (P.contF (t : ℂ) (lwHarm_real_mem_Hbar t)).mono H_subset_Hbar
  exact closure_mono (image_subset_iff.2 P.mapsF) (hc.mem_closure_image (lwHarm_real_mem_closure_H t))

lemma lwHarm_not_mem_closure {t : ℂ} {B : Set ℂ} (hB : B ⊆ H) (h : ∀ᶠ w in 𝓝[H] t, w ∉ B) :
    t ∉ closure B := by
  rw [mem_closure_iff_frequently, not_frequently]
  rw [eventually_nhdsWithin_iff] at h
  exact h.mono fun w hw hwB => hw (hB hwB) hwB

/-- Far behaviour at a point of `closure A`. -/
lemma lwHarm_far_sep (hinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) ∨
      ∃ p, p ∉ closure A ∧ Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p))
    {x₀ : ℂ} (hx₀ : x₀ ∈ closure A) : ∃ R r, 0 < r ∧ ∀ w ∈ Hbar, R < ‖w‖ → r ≤ ‖F w - x₀‖ := by
  rcases hinf with h | ⟨p, hp, h⟩
  · have hm : (closedBall (0 : ℂ) (‖x₀‖ + 1))ᶜ ∈ Bornology.cobounded ℂ :=
      Bornology.isBounded_def.1 isBounded_closedBall
    obtain ⟨R, hR⟩ := lwHarm_ev_far (h.eventually hm)
    refine ⟨R, 1, one_pos, fun w hw hwR => ?_⟩
    have h1 := hR w hw hwR
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at h1
    have := norm_sub_norm_le (F w) x₀
    linarith
  · have hne : 0 < ‖p - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 fun e => hp (e ▸ hx₀))
    obtain ⟨R, hR⟩ := lwHarm_ev_far (h.eventually (ball_mem_nhds p (half_pos hne)))
    refine ⟨R, ‖p - x₀‖ / 2, half_pos hne, fun w hw hwR => ?_⟩
    have h1 := hR w hw hwR
    rw [dist_eq_norm, norm_sub_rev] at h1
    have := norm_add_le (p - F w) (F w - x₀)
    rw [sub_add_sub_cancel] at this
    linarith

/-- The preimage of a bounded `A` is bounded. -/
lemma lwHarm_J_bdd (hA : Bornology.IsBounded A)
    (hinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) ∨
      ∃ p, p ∉ closure A ∧ Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p)) :
    ∃ R, 0 < R ∧ ∀ t : ℝ, F t ∈ A → |t| ≤ R := by
  have hev : ∀ᶠ w in Bornology.cobounded ℂ ⊓ 𝓟 Hbar, F w ∉ A := by
    rcases hinf with h | ⟨p, hp, h⟩
    · exact h.eventually (Bornology.isBounded_def.1 hA)
    · exact (h.eventually (isClosed_closure.isOpen_compl.mem_nhds hp)).mono
        fun w hw hwA => hw (subset_closure hwA)
  obtain ⟨R, hR⟩ := lwHarm_ev_far hev
  refine ⟨max R 1, by positivity, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  refine hR (t : ℂ) (lwHarm_real_mem_Hbar t) ?_ ht
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact lt_of_le_of_lt (le_max_left _ _) hlt

/-- **Key localization**: if no real preimage of `x₀` is in `closure B` and `F` stays away from
`x₀` on the far part of `B`, then `G z ∉ B` for `z ∈ D` near `x₀`. -/
theorem lwHarm_key (P : LWBdryParam D F G) {x₀ : ℂ} (hx₀ : x₀ ∉ D) {B : Set ℂ} (hB : B ⊆ H)
    (hloc : ∀ t : ℝ, F t = x₀ → (t : ℂ) ∉ closure B)
    (hfar : ∃ R r, 0 < r ∧ ∀ w ∈ B, R < ‖w‖ → r ≤ ‖F w - x₀‖) :
    ∀ᶠ z in 𝓝[D] x₀, G z ∉ B := by
  obtain ⟨R, r, hr, hRr⟩ := hfar
  set K := closure B ∩ closedBall 0 R
  have hKc : IsCompact K := (isCompact_closedBall 0 R).inter_left isClosed_closure
  have hKH : K ⊆ Hbar := fun w hw =>
    (isClosed_Hbar.closure_subset_iff.2 (hB.trans H_subset_Hbar)) hw.1
  have hFK : IsCompact (F '' K) := hKc.image_of_continuousOn (P.contF.mono hKH)
  have hx : x₀ ∉ F '' K := by
    rintro ⟨w, hwK, hw⟩
    have h0 : (0 : ℝ) ≤ w.im := hKH hwK
    rcases lt_or_eq_of_le h0 with him | him
    · exact hx₀ (hw ▸ P.mapsF him)
    · have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [← him])
      exact hloc w.re (by rw [← hwr]; exact hw) (hwr ▸ hwK.1)
  have hU : (F '' K)ᶜ ∩ ball x₀ r ∈ 𝓝 x₀ :=
    inter_mem (hFK.isClosed.isOpen_compl.mem_nhds hx) (ball_mem_nhds x₀ hr)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hzD hGB
  by_cases hGR : ‖G z‖ ≤ R
  · exact hz.1 ⟨G z, ⟨subset_closure hGB, by simpa [mem_closedBall] using hGR⟩, P.inv z hzD⟩
  · have h1 := hRr (G z) hGB (not_le.1 hGR)
    rw [P.inv z hzD] at h1
    have h2 := hz.2
    rw [mem_ball, dist_eq_norm] at h2
    linarith

/-- **Harmonic measure exists** for a domain with a boundary-continuous conformal
parametrization (GM (1.6), p. 5): `ω(G z, int {t | F t ∈ A}, ℍ)` is a harmonic measure of `A`
in `D`, for bounded `A` disjoint from `D`, provided `F → ∞` at `∞` or `F(∞) ∉ closure A`. -/
theorem lwHarm_isHarmMeas (P : LWBdryParam D F G) (hA : Bornology.IsBounded A)
    (hAD : Disjoint A D)
    (hinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) ∨
      ∃ p, p ∉ closure A ∧ Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 p)) :
    IsHarmMeas D A (lwHarmOf F G A) := by
  set O := interior {t : ℝ | F t ∈ A} with hOdef
  have hOm : MeasurableSet O := isOpen_interior.measurableSet
  obtain ⟨R₁, hR₁, hJ⟩ := lwHarm_J_bdd hA hinf
  have hOI : O ⊆ Icc (-R₁) R₁ := fun t ht => abs_le.1 (hJ t (interior_subset (s := {t : ℝ | F t ∈ A}) ht))
  have hOf : volume O < ⊤ := (measure_mono hOI).trans_lt (by simp)
  have hGH : ∀ z ∈ D, 0 < (G z).im := fun z hz => P.mapsG hz
  -- the far part of the superlevel sets is empty
  have hsmall : ∀ a > 0, ∃ M, ∀ w : ℂ, 0 < w.im → M < ‖w‖ → lwHarmOm O w < a :=
    fun a ha => lwHarm_small_far hR₁ hOI ha
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- harmonic: `Im (Φ_O ∘ G) / π`
    intro z hz
    have hd : DifferentiableOn ℂ (lwHarmPhi O ∘ G) D := (lwHarm_diffOn hOf).comp P.diffG P.mapsG
    have han : AnalyticAt ℂ (lwHarmPhi O ∘ G) z := hd.analyticAt (P.isOpen.mem_nhds hz)
    have h1 := (han.harmonicAt_im).const_smul (c := π⁻¹)
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h1
    filter_upwards [P.isOpen.mem_nhds hz] with v hv
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, lwHarmOf]
    rw [lwHarm_eq_im hOf (hGH v hv)]
    ring
  · intro z hz
    exact ⟨lwHarm_nonneg _ _, lwHarm_le_one _ (hGH z hz)⟩
  · -- boundary value `1` on `A`
    intro x₀ hx₀A hx₀cl
    have hx₀D : x₀ ∉ D := fun h => hAD.ne_of_mem hx₀A h rfl
    rw [Metric.mem_closure_iff] at hx₀cl
    push Not at hx₀cl
    obtain ⟨ε, hε, hεA⟩ := hx₀cl
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hB : {w | w ∈ H ∧ lwHarmOm O w ≤ a} ⊆ H := fun w hw => hw.1
      have hk := lwHarm_key P hx₀D hB ?_ ?_
      · filter_upwards [hk, self_mem_nhdsWithin] with z hz hzD
        exact lt_of_not_ge fun h => hz ⟨hGH z hzD, h⟩
      · intro t ht
        obtain ⟨δ, hδ, hc⟩ := lwHarm_cont_real P t hε
        have hsub : Ioo (t - δ) (t + δ) ⊆ O := by
          rw [hOdef]
          refine interior_maximal ?_ isOpen_Ioo
          intro s hs
          have hsd : |s - t| < δ := abs_sub_lt_iff.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩
          have h1 := hc s hsd
          rw [ht] at h1
          by_contra hsA
          exact (hεA (F s) ⟨lwHarm_F_frontier P s, hsA⟩ |>.not_gt) (by rwa [dist_comm])
        have hT := lwHarm_tendsto_one hOm hδ hsub
        refine lwHarm_not_mem_closure hB ?_
        filter_upwards [hT.eventually (lt_mem_nhds ha)] with w hw hwB
        exact absurd hwB.2 (not_le.2 hw)
      · obtain ⟨R, r, hr, h⟩ := lwHarm_far_sep hinf (subset_closure hx₀A)
        exact ⟨R, r, hr, fun w hw hwR => h w (H_subset_Hbar hw.1) hwR⟩
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact lt_of_le_of_lt (lwHarm_le_one _ (hGH z hz)) ha
  · -- boundary value `0` off `closure A`
    intro x₀ hx₀f hx₀cl
    have hx₀D : x₀ ∉ D := by
      rw [P.isOpen.frontier_eq] at hx₀f; exact hx₀f.2
    rw [Metric.mem_closure_iff] at hx₀cl
    push Not at hx₀cl
    obtain ⟨ε, hε, hεA⟩ := hx₀cl
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards with z
      exact lt_of_lt_of_le ha (lwHarm_nonneg _ _)
    · have hB : {w | w ∈ H ∧ a ≤ lwHarmOm O w} ⊆ H := fun w hw => hw.1
      obtain ⟨M, hM⟩ := hsmall a ha
      have hk := lwHarm_key P hx₀D hB ?_ ⟨M, 1, one_pos, fun w hw hwM =>
        absurd hw.2 (not_le.2 (hM w hw.1 hwM))⟩
      · filter_upwards [hk, self_mem_nhdsWithin] with z hz hzD
        exact lt_of_not_ge fun h => hz ⟨hGH z hzD, h⟩
      · intro t ht
        obtain ⟨δ, hδ, hc⟩ := lwHarm_cont_real P t hε
        have hdisj : ∀ s ∈ O, δ ≤ |s - t| := by
          intro s hs
          by_contra hlt
          push Not at hlt
          have h1 := hc s hlt
          rw [ht] at h1
          exact (hεA (F s) (interior_subset (s := {t : ℝ | F t ∈ A}) hs)).not_gt (by rwa [dist_comm])
        have hT := lwHarm_tendsto_zero hOm hδ hdisj
        refine lwHarm_not_mem_closure hB ?_
        filter_upwards [hT.eventually (gt_mem_nhds ha)] with w hw hwB
        exact absurd hwB.2 (not_le.2 hw)
  · -- decay at `∞`
    intro _
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Eventually.of_forall fun z => lt_of_lt_of_le ha (lwHarm_nonneg _ _)
    · obtain ⟨M, hM⟩ := hsmall a ha
      set B := {w | w ∈ H ∧ a ≤ lwHarmOm O w}
      have hBb : B ⊆ closedBall 0 (max M 0) := fun w hw => by
        rw [mem_closedBall, dist_zero_right]
        by_contra h
        exact absurd hw.2 (not_le.2 (hM w hw.1 (lt_of_le_of_lt (le_max_left _ _) (not_le.1 h))))
      have hKc : IsCompact (closure B) :=
        (isCompact_closedBall 0 (max M 0)).of_isClosed_subset isClosed_closure
          (closure_minimal hBb isClosed_closedBall)
      have hKH : closure B ⊆ Hbar :=
        isClosed_Hbar.closure_subset_iff.2 (fun w hw => H_subset_Hbar hw.1)
      obtain ⟨N, hN⟩ := (hKc.image_of_continuousOn (P.contF.mono hKH)).isBounded.subset_closedBall 0
      rw [eventually_inf_principal]
      filter_upwards [Bornology.isBounded_def.1 (isBounded_closedBall (x := (0 : ℂ)) (r := N))]
        with z hz hzD
      by_contra hle
      have hGB : G z ∈ B := ⟨hGH z hzD, not_lt.1 hle⟩
      exact hz (hN ⟨G z, subset_closure hGB, P.inv z hzD⟩)

end LWFar
end Thm18Asm
end QuantumZipper
