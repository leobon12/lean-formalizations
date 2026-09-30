import QuantumZipper.Proofs.Zipper.WedgeRC3All2Basic

/-!
# WEDGE-RC3ALL2 (2): raw = regularized for the wedge field on every folded circle

Proof of the node `F1.WedgeRC3AllStmt` (Theorem 1.3, F1 B4(c)): a.s., for every folded circle
`fc(w, ρ)` (missing `0`, centred at `0`, through `0` or enclosing `0` alike),
`evalReg W (fc w ρ) = W (fc w ρ)` for the wedge field `W = wedgeField (lateralPart X) A (Qc γ)`.

Route (own elementary argument; AGENT_GUIDE cost rule):

* the wedge profile is the radial function `rp (wg x A Q)`, with `wg` measurable, continuous on
  `(0, ∞)` and `|wg t| ≤ C (1 − log t)` on `(0, 1]` (`bd_wg`, from the a.s. linear growth bounds
  `ae_growth_radAvgReg`, `ae_growth_wedge` in the log-scale);
* on **every** folded circle the raw value of `W` is `evalReg x + ∫ profile`
  (`WedgeCan.wedgeField_eq_evalReg_add_ofFun`, integrability from `wedgeCircleIntStmt_holds`), and
  the circle average of the profile is continuous in the centre (`continuous_smoothFun_rp`), so
  `avgReg W k u = F(u, 2^{-k}) + ∫ profile d fc(u, 2^{-k})` for every `u ∈ Hbar`
  (`avgReg_wedgeField_eq_all`);
* integrating over `fc(w, ρ)` and letting `k → ∞`: the free part tends to `F(foldH w, ρ)`
  (regularity of the sample), the profile part to `∫ profile d fc(w, ρ)`
  (`tendsto_integral_smoothFun_rp`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1
namespace RC3Two

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q C : ℝ}

/-- The radial function of the wedge profile. -/
def wg (x : FieldSample) (A : ℝ → ℝ) (Q : ℝ) : ℝ → ℝ :=
  fun t => -radAvgReg x t + Q * -Real.log t + A (-Real.log t)

theorem measurable_wg (hA : Continuous A) : Measurable (wg x A Q) :=
  ((WedgeTK.measurable_radAvgReg₂.comp (measurable_const.prodMk measurable_id)).neg.add
    (measurable_const.mul Real.measurable_log.neg)).add
    (hA.measurable.comp Real.measurable_log.neg)

theorem continuousOn_wg (hG : WedgeTK.GoodRad x F) (hA : Continuous A) :
    ContinuousOn (wg x A Q) (Ioi 0) := by
  have hF : ContinuousOn (fun t : ℝ => F (0, t)) (Ioi 0) :=
    hG.1.1.comp (continuousOn_const.prodMk continuousOn_id) fun t ht =>
      ⟨WedgeMeasCoord.zero_mem_Hbar_wm, ht⟩
  have hr : ContinuousOn (fun t => radAvgReg x t) (Ioi 0) :=
    hF.congr fun t ht => hG.radAvgReg_eq ht
  have hl : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun t (ht : 0 < t) => ht.ne'
  exact (hr.neg.add (continuousOn_const.mul hl.neg)).add (hA.comp_continuousOn hl.neg)

/-- The logarithmic bound of the wedge profile near `0`, from linear growth in the log-scale. -/
theorem bd_wg {K₁ M₁ K₂ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ s, 0 ≤ s → |radAvgReg x (Real.exp (-s))| ≤ K₁ + M₁ * s)
    (h₂ : ∀ s, 0 ≤ s → |A s| ≤ K₂ + M₂ * s) :
    ∀ t, 0 < t → t ≤ 1 →
      |wg x A Q t| ≤ (|K₁| + |K₂| + M₁ + M₂ + |Q|) * (1 - Real.log t) := by
  intro t ht ht1
  have hs : 0 ≤ -Real.log t := neg_nonneg.2 (Real.log_nonpos ht.le ht1)
  have a1 := h₁ (-Real.log t) hs
  rw [neg_neg, Real.exp_log ht] at a1
  have a2 := h₂ (-Real.log t) hs
  have a3 : |Q * -Real.log t| = |Q| * -Real.log t := by rw [abs_mul, abs_of_nonneg hs]
  have tri := abs_add_three (-radAvgReg x t) (Q * -Real.log t) (A (-Real.log t))
  rw [abs_neg, a3] at tri
  unfold wg
  have p1 := mul_nonneg (abs_nonneg K₁) hs
  have p2 := mul_nonneg (abs_nonneg K₂) hs
  have p3 := mul_nonneg (abs_nonneg Q) hs
  have p4 := mul_nonneg hM₁ hs
  have p5 := mul_nonneg hM₂ hs
  have q1 := le_abs_self K₁
  have q2 := le_abs_self K₂
  nlinarith [abs_nonneg Q]

section Main

variable (hG : WedgeTK.GoodRad x F)
  (hray : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
    x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
  (hint : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ →
    Integrable (fun u => radAvgReg x ‖u‖) (foldedCircle w ρ) ∧
      Integrable (fun u => A (-Real.log ‖u‖)) (foldedCircle w ρ))
  (hA : Continuous A)
  (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t))

include hG hray hint hA hbd

/-- **Dyadic averages of the wedge field at every point of `Hbar`.** -/
theorem avgReg_wedgeField_eq_all (k : ℕ) {u : ℂ} (hu : u ∈ Hbar) :
    avgReg (wedgeField (lateralPart x) A Q) k u =
      F (u, radius k) + GoodSample.smoothFun (rp (wg x A Q)) u (radius k) := by
  have e : (fun n => wedgeField (lateralPart x) A Q
        (foldedCircle (dyadicRoundC n u) (radius k))) =
      fun n => x (foldedCircle (dyadicRoundC n u) (radius k)) +
        GoodSample.smoothFun (rp (wg x A Q)) (dyadicRoundC n u) (radius k) := by
    funext n
    have hdn : dyadicRoundC n u ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hu n
    rw [WedgeCan.wedgeField_eq_evalReg_add_ofFun (hint _ _ (radius_pos k)).1
      (WedgeCan.integrable_logProfile_foldedCircle Q _ _) (hint _ _ (radius_pos k)).2,
      hG.1.evalReg_fc_of_mem hdn (radius_pos k), hray n u hu k]
    rfl
  unfold avgReg
  rw [e]
  exact ((hG.1.2.1 k u hu).add (((continuous_smoothFun_rp (measurable_wg hA)
    (continuousOn_wg hG hA) hbd (radius_pos k)).tendsto u).comp
      (RegClosure.tendsto_dyadicRoundC u))).limUnder_eq

/-- **Raw = regularized for the wedge field on every folded circle.** -/
theorem evalReg_wedgeField_fc_all (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    evalReg (wedgeField (lateralPart x) A Q) (foldedCircle w ρ) =
      wedgeField (lateralPart x) A Q (foldedCircle w ρ) := by
  have hk : ∀ k : ℕ, ∫ u, avgReg (wedgeField (lateralPart x) A Q) k u ∂foldedCircle w ρ =
      ∫ u, F (u, radius k) ∂foldedCircle w ρ +
        ∫ u, GoodSample.smoothFun (rp (wg x A Q)) u (radius k) ∂foldedCircle w ρ := by
    intro k
    rw [← integral_add
      (RegClosure.integrable_fc (RegClosure.continuousOn_slice hG.1.1 (radius_pos k)) w hρ.le)
      (RegClosure.integrable_fc (continuous_smoothFun_rp (measurable_wg hA)
        (continuousOn_wg hG hA) hbd (radius_pos k)).continuousOn w hρ.le)]
    exact integral_congr_ae ((RegClosure.fc_ae_mem_Hbar w ρ).mono fun u hu =>
      avgReg_wedgeField_eq_all hG hray hint hA hbd k hu)
  have hF : Tendsto (fun k => ∫ u, F (u, radius k) ∂foldedCircle w ρ) atTop
      (𝓝 (F (foldH w, ρ))) := by
    have := (hG.1.2.2.tendsto_at (a := (foldH w, ρ)) ⟨CircleFubini.foldH_mem_Hbar' w, hρ⟩).comp
      RegClosure.tendsto_radius_nhdsGT
    exact this.congr fun k => RegClosure.integral_fc_foldH
      (RegClosure.continuousOn_slice hG.1.1 (radius_pos k)) w ρ
  have hS := tendsto_integral_smoothFun_rp (measurable_wg hA) (continuousOn_wg hG hA) hbd w hρ
  have hlim : evalReg (wedgeField (lateralPart x) A Q) (foldedCircle w ρ) =
      F (foldH w, ρ) + ∫ v, rp (wg x A Q) v ∂foldedCircle w ρ := by
    unfold evalReg
    simp_rw [hk]
    exact (hF.add hS).limUnder_eq
  rw [hlim, WedgeCan.wedgeField_eq_evalReg_add_ofFun (hint w ρ hρ).1
    (WedgeCan.integrable_logProfile_foldedCircle Q w ρ) (hint w ρ hρ).2, hG.1.evalReg_fc w hρ]
  rfl

end Main

end RC3Two

/-- **Node `F1.WedgeRC3AllStmt` (Theorem 1.3, F1 B4(c)).** A.s. the raw value of the wedge field
on every folded circle is its regularized value. -/
theorem wedgeRC3AllStmt_holds (γ α : ℝ) : WedgeRC3AllStmt γ α := by
  intro Ω' _ P' _ X A hX hA hI
  obtain ⟨G, hGv⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hGv.ae_good, WedgeCan.ae_raw_dyadic hGv,
    WedgeCan4.ae_continuous_wedgeProcess hA, wedgeCircleIntStmt_holds γ α P' X A hX hA hI,
    ae_growth_radAvgReg hX, ae_growth_wedge hA] with ω hg hray hAc hint hr hw
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  intro w ρ hρ
  exact RC3Two.evalReg_wedgeField_fc_all hg hray hint hAc
    (RC3Two.bd_wg (Q := Qc γ) (A := fun t => A t ω) hM₁ hM₂ h₁ h₂) w hρ

/-- **Field-level B4(c)** (`WedgeAddConstLawStmt`), now unconditional. -/
theorem wedgeAddConstLawStmt_holds : WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_rc3All fun γ α _ _ _ => wedgeRC3AllStmt_holds γ α

end F1
end QuantumZipper
