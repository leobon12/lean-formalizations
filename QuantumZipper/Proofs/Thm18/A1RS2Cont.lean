import QuantumZipper.Proofs.Thm18.A1RS2Ext
import QuantumZipper.Proofs.Thm18.A1RFCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (3): joint continuity of the smeared-loop pairings at positive radius (deterministic)

For a good driver `W` and `Φ_t = f_t ∘ ψ` (`ψ = g1zSideMap left W`):

* `sidePush_time_cont`, `sidePush_continuousAt`: `(t, w) ↦ Φ_t(w)` is jointly continuous on
  `(0, ∞) × ℍ` (time modulus `norm_sidePush_add_sub_le`, uniform on `ℍ`, plus holomorphy in `w`);
* `sidePush_bound`: `Φ_t` is bounded on bounded parts of `ℍ`, uniformly for `t ∈ (0, T]`;
* **`continuousOn_integral_a1rMu`**: if `L(t, z, ρ)` is continuous on `(0,∞) × ℍ̄ × (0,∞)`, then
  `(p, ρ) ↦ ∫ L(t, ·, ρ) d a1rMu(t, d, s)` is continuous on `smearU × (0, ∞)` (dominated
  convergence in the angle, `a1rMu = circM.map (Φ_t ∘ fold ∘ circle(d, s))`);
* **`continuousOn_evalReg_smearFam`**: hence, for a regular sample whose pairings along the
  pulled-back folded circles converge uniformly (`A1RFLoopUCStmt` form) with a continuous limit
  `L(t, z, ρ) = evalReg x ((f_t⁻¹)_* fc(z, ρ))`, the pairings `evalReg x (ν_{p,ρ})` are jointly
  continuous on `smearU × (0, ∞)` (`A1RF.integral_evalReg_fc_eq_nu`). This is the pathwise
  continuity input (R2) of the extension `tendsto_of_ratCauchy`.

Own elementary bookkeeping (dominated convergence).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

theorem parD_eq (p : Fin 4 → ℝ) : parD p = (p 1 : ℂ) + (p 2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [parD]

theorem continuous_parD : Continuous parD := by
  have : parD = fun p : Fin 4 → ℝ => (p 1 : ℂ) + (p 2 : ℂ) * Complex.I := funext parD_eq
  rw [this]; fun_prop

/-- **Time continuity of `f_t ∘ ψ`, uniformly on `ℍ`.** -/
theorem sidePush_time_cont {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {t₀ : ℝ}
    (ht₀ : 0 < t₀) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ t : ℝ, 0 < t → |t - t₀| < δ → ∀ w ∈ H,
      ‖fwdMap W t (g1zSideMap left W w) - fwdMap W t₀ (g1zSideMap left W w)‖ < ε := by
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * t₀ + 1)).uniformContinuousOn_of_continuous
    hG.1.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηc⟩ := huc (ε / 48) (by positivity)
  set δ : ℝ := min (min η t₀) ((ε / 32) ^ 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hη ht₀) (by positivity)
  have hδη : δ ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hδt : δ ≤ t₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ ≤ (ε / 32) ^ 2 := min_le_right _ _
  have hsq : ∀ h : ℝ, 0 ≤ h → h < δ → 8 * Real.sqrt h < ε / 2 := by
    intro h hh0 hhδ
    have : Real.sqrt h < ε / 32 := by
      rw [Real.sqrt_lt' (by positivity)]; linarith
    linarith
  -- the displacement between `a` and `a + h`, `0 ≤ a`, `a + h ≤ 2 t₀`
  have key : ∀ a h : ℝ, 0 ≤ a → 0 < h → h < δ → a + h ≤ 2 * t₀ → ∀ w ∈ H,
      ‖fwdMap W (a + h) (g1zSideMap left W w) - fwdMap W a (g1zSideMap left W w)‖ < ε := by
    intro a h ha hh hhδ hah w hw
    have hM : ∀ r ∈ Icc (0 : ℝ) h, |W (a + r) - W a| ≤ ε / 48 := by
      intro r hr
      have := hηc (a + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩ a ⟨ha, by linarith⟩
        (by rw [Real.dist_eq, show a + r - a = r by ring, abs_of_nonneg hr.1]; linarith [hr.2])
      rw [Real.dist_eq] at this
      exact this.le
    have h1 := norm_sidePush_add_sub_le hG ha hh hM left hw
    have h2 := hsq h hh.le hhδ
    linarith
  refine ⟨δ, hδ0, fun t ht htd w hw => ?_⟩
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · have hd : t₀ - t < δ := by rw [abs_sub_comm, abs_of_pos (by linarith)] at htd; exact htd
    have := key t (t₀ - t) ht.le (by linarith) hd (by linarith) w hw
    rw [show t + (t₀ - t) = t₀ by ring, norm_sub_rev] at this
    exact this
  · subst heq; simp [hε]
  · have hd : t - t₀ < δ := by rw [abs_of_pos (by linarith)] at htd; exact htd
    have := key t₀ (t - t₀) ht₀.le (by linarith) hd (by linarith) w hw
    rw [show t₀ + (t - t₀) = t by ring] at this
    exact this

/-- **Joint continuity of `(t, w) ↦ f_t(ψ(w))` on `(0, ∞) × ℍ`.** -/
theorem sidePush_continuousAt {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {t₀ : ℝ}
    (ht₀ : 0 < t₀) {w₀ : ℂ} (hw₀ : w₀ ∈ H) :
    ContinuousAt (fun q : ℝ × ℂ => fwdMap W q.1 (g1zSideMap left W q.2)) (t₀, w₀) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := sidePush_time_cont hG left ht₀ (half_pos hε)
  have hc : ContinuousAt (fun w => fwdMap W t₀ (g1zSideMap left W w)) w₀ :=
    ((A1R.sidePush_props hG ht₀ left).1.continuousOn).continuousAt (isOpen_H.mem_nhds hw₀)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (half_pos hε)
  obtain ⟨δ₃, hδ₃, h₃⟩ := Metric.isOpen_iff.1 isOpen_H w₀ hw₀
  refine ⟨min (min δ₁ δ₂) (min δ₃ t₀), lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ ht₀),
    fun {q} hq => ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hq1' : |q.1 - t₀| < δ₁ := by
    rw [← Real.dist_eq]; exact hq1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hqt : 0 < q.1 := by
    have : |q.1 - t₀| < t₀ := by
      rw [← Real.dist_eq]; exact hq1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [abs_lt] at this; linarith
  have hqH : q.2 ∈ H := h₃ (hq2.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have e1 := h₁ q.1 hqt hq1' q.2 hqH
  have e2 := h₂ (hq2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  calc dist (fwdMap W q.1 (g1zSideMap left W q.2)) (fwdMap W t₀ (g1zSideMap left W w₀))
      ≤ dist (fwdMap W q.1 (g1zSideMap left W q.2)) (fwdMap W t₀ (g1zSideMap left W q.2)) +
        dist (fwdMap W t₀ (g1zSideMap left W q.2)) (fwdMap W t₀ (g1zSideMap left W w₀)) :=
          dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_eq_norm]; exact add_lt_add e1 e2
    _ = ε := by ring

/-- **`f_t ∘ ψ` is bounded on bounded parts of `ℍ`, uniformly for `t ∈ (0, T]`.** -/
theorem sidePush_bound {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ} (R : ℝ) :
    ∃ B : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, ∀ w ∈ H, ‖w‖ ≤ R →
      ‖fwdMap W t (g1zSideMap left W w)‖ ≤ B := by
  obtain ⟨ψe, -, hψc, hψeq, -⟩ := exists_sideMap_ext hG left
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).inter_left isClosed_Hbar
  obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn (hψc.mono inter_subset_left)
  obtain ⟨MW, hMW⟩ := RegCont.exists_abs_le_on_Icc hG.1 T
  refine ⟨Bψ + 24 * MW + 8 * Real.sqrt T, fun t ht w hw hwR => ?_⟩
  have hmem := sideMap_mem_compl_fwdHull hG ht.1.le left hw
  have h1 := CoreArc.norm_fwdMap_sub_le_uniform hG.1 hG.2.1 ht.1
    (fun r hr => hMW r ⟨hr.1, hr.2.trans ht.2⟩) hmem
  have h2 : ‖g1zSideMap left W w‖ ≤ Bψ := by
    rw [hψeq hw]
    exact hBψ w ⟨show 0 ≤ w.im from le_of_lt hw, by rw [mem_closedBall, dist_zero_right]; exact hwR⟩
  have h3 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
  have h4 := norm_sub_norm_le (fwdMap W t (g1zSideMap left W w)) (g1zSideMap left W w)
  linarith

/-- **Continuity of the smeared integrals at positive radius** (dominated convergence). -/
theorem continuousOn_integral_a1rMu {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool)
    {L : ℝ × ℂ × ℝ → ℝ} (hL : ContinuousOn L (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)))
    (hLm : ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, Measurable fun z => L (t, z, ρ)) :
    ContinuousOn (fun x : (Fin 4 → ℝ) × ℝ =>
      ∫ w, L (x.1 0, w, x.2) ∂(a1rMu W (x.1 0) left (parD x.1) (x.1 3))) (smearU ×ˢ Ioi 0) := by
  have hHH : ∀ {z : ℂ}, z ∈ H → z ∈ Hbar := fun {z} hz => show 0 ≤ z.im from le_of_lt hz
  set Φ : ℝ → ℂ → ℂ := fun t w => fwdMap W t (g1zSideMap left W w) with hΦ
  set u : ℝ → (Fin 4 → ℝ) × ℝ → ℂ := fun θ x => foldH (circleMap (parD x.1) (x.1 3) θ) with hu
  set F : (Fin 4 → ℝ) × ℝ → ℝ → ℝ := fun x θ => L (x.1 0, Φ (x.1 0) (u θ x), x.2) with hF
  have hucont : ∀ θ, Continuous (u θ) := by
    intro θ
    have h1 : Continuous fun x : (Fin 4 → ℝ) × ℝ => parD x.1 := continuous_parD.comp continuous_fst
    simp only [hu, circleMap]
    exact CircleFubini.continuous_foldH'.comp (h1.add ((Complex.continuous_ofReal.comp
      ((continuous_apply 3).comp continuous_fst)).mul continuous_const))
  -- the integral in the angle parametrization
  have hA : ∀ x : (Fin 4 → ℝ) × ℝ, 0 < x.1 0 → 0 < x.1 3 →
      ∫ w, L (x.1 0, w, x.2) ∂(a1rMu W (x.1 0) left (parD x.1) (x.1 3)) = ∫ θ, F x θ ∂G1RC.circM
      ∧ AEStronglyMeasurable (F x) G1RC.circM := by
    intro x ht hs
    obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht left
    have hc₁ : Measurable fun θ : ℝ => foldH (circleMap (parD x.1) (x.1 3) θ) :=
      (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap _ _).measurable
    have hae : (fun θ => L (x.1 0, g (foldH (circleMap (parD x.1) (x.1 3) θ)), x.2))
        =ᵐ[G1RC.circM] F x := by
      filter_upwards [ae_circM_mem_H (parD x.1) hs] with θ hθ
      have e := hEq hθ
      simp only at e
      simp only [hF, hΦ, hu, e]
    have hm : Measurable fun θ : ℝ => g (foldH (circleMap (parD x.1) (x.1 3) θ)) := hgm.comp hc₁
    refine ⟨?_, (((hLm _ ht _).comp hm).aestronglyMeasurable).congr hae⟩
    rw [a1rMu_eq_map_circM hgm hEq _ hs, integral_map hm.aemeasurable
      (hLm _ ht _).aestronglyMeasurable]
    exact integral_congr_ae hae
  intro x₀ hx₀
  obtain ⟨⟨ht₀, hs₀⟩, hρ₀⟩ := hx₀
  have hρ₀' : (0 : ℝ) < x₀.2 := hρ₀
  refine ContinuousAt.continuousWithinAt ?_
  have hO : smearU ×ˢ Ioi (0 : ℝ) ∈ 𝓝 x₀ :=
    (isOpen_smearU.prod isOpen_Ioi).mem_nhds ⟨⟨ht₀, hs₀⟩, hρ₀⟩
  -- neighbourhood bounds
  have c0 : Continuous fun x : (Fin 4 → ℝ) × ℝ => x.1 0 := (continuous_apply 0).comp continuous_fst
  have c3 : Continuous fun x : (Fin 4 → ℝ) × ℝ => x.1 3 := (continuous_apply 3).comp continuous_fst
  have cd : Continuous fun x : (Fin 4 → ℝ) × ℝ => ‖parD x.1‖ :=
    continuous_norm.comp (continuous_parD.comp continuous_fst)
  have e1 : ∀ᶠ x in 𝓝 x₀, x.1 0 ∈ Ioo (x₀.1 0 / 2) (2 * x₀.1 0) :=
    c0.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have e3 : ∀ᶠ x in 𝓝 x₀, x.1 3 ∈ Ioo (x₀.1 3 / 2) (2 * x₀.1 3) :=
    c3.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have e4 : ∀ᶠ x in 𝓝 x₀, x.2 ∈ Ioo (x₀.2 / 2) (2 * x₀.2) :=
    continuous_snd.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have e2 : ∀ᶠ x in 𝓝 x₀, ‖parD x.1‖ < ‖parD x₀.1‖ + 1 :=
    cd.continuousAt.eventually (Iio_mem_nhds (by linarith))
  set R : ℝ := ‖parD x₀.1‖ + 1 + 2 * x₀.1 3 with hR
  obtain ⟨B, hB⟩ := sidePush_bound hG left (T := 2 * x₀.1 0) R
  set K : Set (ℝ × ℂ × ℝ) := Icc (x₀.1 0 / 2) (2 * x₀.1 0) ×ˢ
    ((Hbar ∩ closedBall (0 : ℂ) B) ×ˢ Icc (x₀.2 / 2) (2 * x₀.2)) with hK
  have hKc : IsCompact K := isCompact_Icc.prod
    (((isCompact_closedBall (0 : ℂ) B).inter_left isClosed_Hbar).prod isCompact_Icc)
  have hKsub : K ⊆ Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0) := by
    rintro ⟨a, z, r⟩ ⟨ha, hz, hr⟩
    exact ⟨show (0 : ℝ) < a by linarith [ha.1], hz.1,
      show (0 : ℝ) < r by linarith [hr.1]⟩
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hL.mono hKsub)
  have hmemK : ∀ x : (Fin 4 → ℝ) × ℝ, x.1 0 ∈ Ioo (x₀.1 0 / 2) (2 * x₀.1 0) →
      ‖parD x.1‖ < ‖parD x₀.1‖ + 1 → x.1 3 ∈ Ioo (x₀.1 3 / 2) (2 * x₀.1 3) →
      x.2 ∈ Ioo (x₀.2 / 2) (2 * x₀.2) → ∀ θ, u θ x ∈ H →
      (x.1 0, Φ (x.1 0) (u θ x), x.2) ∈ K := by
    intro x h1 h2 h3 h4 θ hθ
    have ht : 0 < x.1 0 := by linarith [h1.1]
    have hΦH : Φ (x.1 0) (u θ x) ∈ H := (A1R.sidePush_props hG ht left).2.1 hθ
    have hun : ‖u θ x‖ ≤ R := by
      simp only [hu]
      rw [TwoPoint.norm_foldH]
      have := TwoPoint.norm_circleMap_le_add (parD x.1) (show 0 ≤ x.1 3 by linarith [h3.1]) θ
      rw [hR]; linarith [h3.2]
    refine ⟨⟨h1.1.le, h1.2.le⟩, ⟨hHH hΦH, ?_⟩, ⟨h4.1.le, h4.2.le⟩⟩
    rw [mem_closedBall, dist_zero_right]
    exact hB (x.1 0) ⟨ht, h1.2.le⟩ (u θ x) hθ hun
  have hcont : ContinuousAt (fun x => ∫ θ, F x θ ∂G1RC.circM) x₀ := by
    refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C) ?_ ?_
      (integrable_const C) ?_
    · filter_upwards [hO] with x hx
      exact (hA x hx.1.1 hx.1.2).2
    · filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
      filter_upwards [ae_circM_mem_H (parD x.1) (show 0 < x.1 3 by linarith [h3.1])] with θ hθ
      exact hC _ (hmemK x h1 h2 h3 h4 θ hθ)
    · filter_upwards [ae_circM_mem_H (parD x₀.1) hs₀] with θ hθ
      have hθ' : u θ x₀ ∈ H := hθ
      have hinner : ContinuousAt (fun x : (Fin 4 → ℝ) × ℝ =>
          ((x.1 0, Φ (x.1 0) (u θ x), x.2) : ℝ × ℂ × ℝ)) x₀ := by
        refine c0.continuousAt.prodMk (ContinuousAt.prodMk ?_ continuous_snd.continuousAt)
        exact (sidePush_continuousAt hG left ht₀ hθ').comp
          (f := fun x : (Fin 4 → ℝ) × ℝ => (x.1 0, u θ x))
          (c0.continuousAt.prodMk (hucont θ).continuousAt)
      have hev : ∀ᶠ x in 𝓝 x₀, ((x.1 0, Φ (x.1 0) (u θ x), x.2) : ℝ × ℂ × ℝ) ∈
          Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0) := by
        filter_upwards [e1, e4, (hucont θ).continuousAt.eventually (isOpen_H.mem_nhds hθ')]
          with x h1 h4 hH
        have ht : 0 < x.1 0 := by linarith [h1.1]
        exact ⟨ht, hHH ((A1R.sidePush_props hG ht left).2.1 hH),
          show (0 : ℝ) < x.2 by linarith [h4.1]⟩
      have hmem0 : ((x₀.1 0, Φ (x₀.1 0) (u θ x₀), x₀.2) : ℝ × ℂ × ℝ) ∈
          Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0) :=
        ⟨ht₀, hHH ((A1R.sidePush_props hG ht₀ left).2.1 hθ'), hρ₀⟩
      exact (hL _ hmem0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hinner.tendsto, hev⟩)
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards [hO] with x hx
  exact (hA x hx.1.1 hx.1.2).1

/-- **(R2) Joint continuity of the smeared-loop pairings at positive radius.** For a regular
sample whose pairings along the pulled-back folded circles converge uniformly on bounded sets of
centres, with the limit `L(t, z, ρ) = evalReg x ((f_t⁻¹)_* fc(z, ρ))` jointly continuous. -/
theorem continuousOn_evalReg_smearFam {x : FieldSample} {FX : ℂ × ℝ → ℝ}
    (hFX : IsRegularWith x FX) {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool)
    (hL : ContinuousOn (fun q : ℝ × ℂ × ℝ =>
      evalReg x ((foldedCircle q.2.1 q.2.2).map (fwdMapInv W q.1))) (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)))
    (hUC : ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ R : ℝ,
      TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg x k u
          ∂((foldedCircle z ρ).map (fwdMapInv W t)))
        (fun z => evalReg x ((foldedCircle z ρ).map (fwdMapInv W t))) atTop
        (Hbar ∩ closedBall 0 R)) :
    ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ => evalReg x (smearFam W left z.1 z.2))
      (smearU ×ˢ Ioi 0) := by
  have hLm : ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, Measurable fun z =>
      (fun q : ℝ × ℂ × ℝ => evalReg x ((foldedCircle q.2.1 q.2.2).map (fwdMapInv W q.1)))
        (t, z, ρ) := fun t ht ρ =>
    A1RF.measurable_evalReg_fcmap x (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le) ρ
  refine (continuousOn_integral_a1rMu hG left hL hLm).congr fun z hz => ?_
  exact (A1RF.integral_evalReg_fc_eq_nu hFX hG hz.1.1 left (parD z.1) hz.1.2 hz.2
    (hUC _ hz.1.1 _ hz.2)).symm

end A1RS
end R18
end QuantumZipper
