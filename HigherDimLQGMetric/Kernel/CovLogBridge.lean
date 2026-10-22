import HigherDimLQGMetric.Kernel.FourierDensity

/-!
# Log covariance of unbounded density measures
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {f g : Rd d → ℝ}

private theorem integrable_logTerm_of_pairable
    (_hf : Measurable f) (hg : Measurable g)
    [IsFiniteMeasure (posM f)] [IsFiniteMeasure (posM (-f))]
    [IsFiniteMeasure (posM g)] [IsFiniteMeasure (posM (-g))]
    (hlog : HigherDimLFPP.LogPairable (posM f) (posM (-f))
      (posM g) (posM (-g)))
    {a b : Rd d → ℝ} (_ha : a = f ∨ a = -f)
    (hb : b = g ∨ b = -g)
    (hα : posM a ≤ posM f + posM (-f) + posM g + posM (-g))
    (hβ : posM b ≤ posM f + posM (-f) + posM g + posM (-g))
    (hma : Measurable a) (hmb : Measurable b) :
    Integrable (fun p : Rd d × Rd d =>
      max (a p.1) 0 * max (b p.2) 0 * (-Real.log ‖p.1 - p.2‖)) := by
  haveI : SFinite (posM b) := by
    rcases hb with rfl | rfl <;> infer_instance
  have hi := hlog.integrable_prod hα hβ
  have hi' : Integrable (fun p : Rd d × Rd d =>
      -Real.log ‖p.1 - p.2‖) ((posM a).prod (posM b)) := hi.neg
  exact (integrable_prod_posM_iff hma hmb _).mp hi'

theorem logCov_posM_of_pairable
    (hf : Measurable f) (hg : Measurable g)
    [IsFiniteMeasure (posM f)] [IsFiniteMeasure (posM (-f))]
    [IsFiniteMeasure (posM g)] [IsFiniteMeasure (posM (-g))]
    (hlog : HigherDimLFPP.LogPairable (posM f) (posM (-f))
      (posM g) (posM (-g))) :
    HigherDimLFPP.logCov (posM f) (posM (-f)) (posM g) (posM (-g)) =
      logCovF f g := by
  have h1 : Integrable (fun p : Rd d × Rd d =>
      max (f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inl rfl) (Or.inl rfl)
      (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _) hf hg
  have h2 : Integrable (fun p : Rd d × Rd d =>
      max (f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inl rfl) (Or.inr rfl)
      (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _) hf hg.neg
  have h3 : Integrable (fun p : Rd d × Rd d =>
      max (-f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inr rfl) (Or.inl rfl)
      (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _) hf.neg hg
  have h4 : Integrable (fun p : Rd d × Rd d =>
      max (-f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inr rfl) (Or.inr rfl)
      (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _) hf.neg hg.neg
  rw [HigherDimLFPP.logCov, integral_prod_posM hf hg,
    integral_prod_posM hf hg.neg,
    integral_prod_posM hf.neg hg,
    integral_prod_posM hf.neg hg.neg]
  simp only [Pi.neg_apply]
  rw [← integral_sub_sub_add h1 h2 h3 h4]
  unfold logCovF
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    change
      max (f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖) -
        max (f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖) -
        max (-f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖) +
        max (-f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖) =
      f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)
    have hf' : max (f p.1) 0 - max (-f p.1) 0 = f p.1 :=
      max_zero_sub_max_neg_zero_eq_self _
    have hg' : max (g p.2) 0 - max (-g p.2) 0 = g p.2 :=
      max_zero_sub_max_neg_zero_eq_self _
    rw [show f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖) =
        (max (f p.1) 0 - max (-f p.1) 0) *
          (max (g p.2) 0 - max (-g p.2) 0) *
            (-Real.log ‖p.1 - p.2‖) by rw [hf', hg']]
    ring

theorem integrable_logCovF_of_pairable
    (hf : Measurable f) (hg : Measurable g)
    [IsFiniteMeasure (posM f)] [IsFiniteMeasure (posM (-f))]
    [IsFiniteMeasure (posM g)] [IsFiniteMeasure (posM (-g))]
    (hlog : HigherDimLFPP.LogPairable (posM f) (posM (-f))
      (posM g) (posM (-g))) :
    Integrable (fun p : Rd d × Rd d =>
      f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)) := by
  have h1 : Integrable (fun p : Rd d × Rd d =>
      max (f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inl rfl) (Or.inl rfl)
      (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _) hf hg
  have h2 : Integrable (fun p : Rd d × Rd d =>
      max (f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inl rfl) (Or.inr rfl)
      (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _) hf hg.neg
  have h3 : Integrable (fun p : Rd d × Rd d =>
      max (-f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inr rfl) (Or.inl rfl)
      (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _) hf.neg hg
  have h4 : Integrable (fun p : Rd d × Rd d =>
      max (-f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    integrable_logTerm_of_pairable hf hg hlog (Or.inr rfl) (Or.inr rfl)
      (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _) hf.neg hg.neg
  have hsum := ((h1.sub h2).sub h3).add h4
  have heq : (fun p : Rd d × Rd d =>
      f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)) =
      (fun p => max (f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖) -
        max (f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖) -
        max (-f p.1) 0 * max (g p.2) 0 * (-Real.log ‖p.1 - p.2‖) +
        max (-f p.1) 0 * max (-g p.2) 0 * (-Real.log ‖p.1 - p.2‖)) := by
    funext p
    have hf' : max (f p.1) 0 - max (-f p.1) 0 = f p.1 :=
      max_zero_sub_max_neg_zero_eq_self _
    have hg' : max (g p.2) 0 - max (-g p.2) 0 = g p.2 :=
      max_zero_sub_max_neg_zero_eq_self _
    calc
      f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖) =
          (max (f p.1) 0 - max (-f p.1) 0) *
            (max (g p.2) 0 - max (-g p.2) 0) *
              (-Real.log ‖p.1 - p.2‖) := by rw [hf', hg']
      _ = _ := by ring
  rw [heq]
  exact hsum

theorem logCovF_eq_iterated_of_pairable
    (hf : Measurable f) (hg : Measurable g)
    [IsFiniteMeasure (posM f)] [IsFiniteMeasure (posM (-f))]
    [IsFiniteMeasure (posM g)] [IsFiniteMeasure (posM (-g))]
    (hlog : HigherDimLFPP.LogPairable (posM f) (posM (-f))
      (posM g) (posM (-g))) :
    logCovF f g =
      ∫ x : Rd d, ∫ y : Rd d,
        f x * (-Real.log ‖x - y‖) * g y := by
  rw [logCovF, Measure.volume_eq_prod (Rd d) (Rd d),
    integral_prod _ (integrable_logCovF_of_pairable hf hg hlog)]
  congr 1
  funext x
  congr 1
  funext y
  ring

end HigherDimLQGMetric
