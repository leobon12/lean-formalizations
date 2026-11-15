/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2CapKernels

/-!
# Reading censored capacity events in forward marks

Clock-cut driver observations suffice even for the completed retained-driver
filtration. This discharges the event-version field of the forward-kernel
interface once the physical inverse clock and protected marks are supplied.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb
open DomainMarkov.Aux79 WangWu.ChartConst
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {Qc : ℝ≥0 → Ω → ℝ≥0}
  {τ : Ω → ℝ≥0} {q : ℝ≥0}

/-- A capacity event observable on every clock cut is observable on each
upper-dyadic inverse-clock piece. The inverse identity is needed only on that
event, and the inverse may have arbitrary values elsewhere. -/
theorem measurableSet_fcCap_dyadic_piece_of_cuts {D : Set Ω}
    (hcut : ∀ ω ∈ D, ∀ t, τ ω ≤ t ↔ q ≤ Qc t ω)
    (hD : ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω})) (n k : ℕ) :
    MeasurableSet[𝓖 (dyq n k)] (D ∩ {ω | dyIdx n (τ ω) = k}) := by
  classical
  let τD : Ω → WithTop ℝ≥0 := fun ω => if ω ∈ D then τ ω else ⊤
  have hτ : IsStoppingTime 𝓖 τD := by
    intro t
    have he : {ω | τD ω ≤ t} = D ∩ {ω | q ≤ Qc t ω} := by
      ext ω
      by_cases hω : ω ∈ D
      · simp only [τD, hω, ite_true, WithTop.coe_le_coe, mem_ofPred_eq,
          mem_inter_iff, true_and]
        exact hcut ω hω t
      · simp only [τD, hω, ite_false, WithTop.not_top_le_coe, mem_ofPred_eq,
          mem_inter_iff, false_and]
    rw [he]
    exact hD t
  have hlow : (k : ℝ≥0) / 2 ^ n ≤ dyq n k := by
    unfold dyq
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) zero_le
  have hge := 𝓖.mono hlow _ (hτ.measurableSet_ge ((k : ℝ≥0) / 2 ^ n))
  have hlt := hτ.measurableSet_lt (dyq n k)
  have he : D ∩ {ω | dyIdx n (τ ω) = k} =
      {ω | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0) ≤ τD ω} ∩
        {ω | τD ω < (dyq n k : WithTop ℝ≥0)} := by
    ext ω
    by_cases hω : ω ∈ D
    · simp only [mem_inter_iff, mem_ofPred_eq, hω, true_and, dyIdx_eq_iff,
        τD, ite_true, WithTop.coe_le_coe, WithTop.coe_lt_coe]
    · simp only [mem_inter_iff, mem_ofPred_eq, hω, false_and, τD, ite_false,
        le_top, WithTop.not_top_lt, and_false]
  rw [he]
  exact hge.inter hlt

/-- Censored events of the completed retained-driver filtration have versions
in forward marks. Samples which never reach `q` are removed using the union
of observed cuts; no global finite inverse or global reachability is assumed. -/
theorem fcCap_censored_versions_of_observed_cuts {d : PairData Ω} (hd : d.IsMeasGood)
    (W : ℝ≥0 → Ω → ℝ) (hm : ∀ r, Measurable (W r))
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ r t, Measurable[𝓖 t] ({ω | r ≤ Qc t ω}.indicator (W r)))
    (hcut : ∀ ω, (∃ t, q ≤ Qc t ω) → ∀ t, τ ω ≤ t ↔ q ≤ Qc t ω)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} (h𝓖𝓜 : ∀ t, 𝓖 t ≤ 𝓜 t)
    {Av : ℝ≥0 → Set Ω} (hAv : ∀ t, MeasurableSet[𝓜 t] (Av t))
    {D : Set Ω} (hD : MeasurableSet[fcRetainedDriverFiltration P hd W hm q] D)
    (hr : ∀ᵐ ω ∂P, ω ∈ D → ∃ t, q ≤ Qc t ω) (n k : ℕ) :
    ∃ B, MeasurableSet[𝓜 (dyq n k)] B ∧
      B =ᵐ[P] (D ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k)) := by
  obtain ⟨A, hA, hDA⟩ := fcRetained_events_of_observed_cuts hd W hm hQa hret hobs q D hD
  let Ar := A ∩ {ω | ∃ t, q ≤ Qc t ω}
  have hAr (t) : Ar ∩ {ω | q ≤ Qc t ω} = A ∩ {ω | q ≤ Qc t ω} := by
    ext ω
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ⟨t, h.2⟩⟩, h.2⟩⟩
  have hArD : Ar =ᵐ[P] D := by
    filter_upwards [hDA, hr] with ω he hrω
    exact propext ⟨fun h => he.mpr h.1, fun h => ⟨he.mp h, hrω h⟩⟩
  refine ⟨Ar ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k), ?_,
    (hArD.inter EventuallyEqSet.rfl).inter EventuallyEqSet.rfl⟩
  apply MeasurableSet.inter ?_ (hAv _)
  apply h𝓖𝓜 _
  exact measurableSet_fcCap_dyadic_piece_of_cuts (fun ω hω => hcut ω hω.2)
    (fun t => by rw [hAr]; exact hA.2 t) n k

/-- The censored event-version field follows from observed clock cuts and
reachability on the protected event. Only the deterministic field kernels,
their limit, and physical observations remain as hypotheses. -/
theorem fcCapForwardKernel_of_observed_cuts {d : PairData Ω} (hd : d.IsMeasGood)
    (W : ℝ≥0 → Ω → ℝ) (hm : ∀ r, Measurable (W r))
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ r t, Measurable[𝓖 t] ({ω | r ≤ Qc t ω}.indicator (W r)))
    (hτ : Measurable τ)
    (hcut : ∀ ω, (∃ t, q ≤ Qc t ω) → ∀ t, τ ω ≤ t ↔ q ≤ Qc t ω)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} (h𝓖𝓜 : ∀ t, 𝓖 t ≤ 𝓜 t)
    (h𝓜 : ∀ t, 𝓜 t ≤ mΩ) {Av : ℝ≥0 → Set Ω}
    (hAv : ∀ t, MeasurableSet[𝓜 t] (Av t)) {K : ℝ≥0 → Ω → ℂ} {X G : Ω → ℂ}
    (hb : ∀ t ω, ω ∈ Av t → ‖K t ω‖ ≤ 1)
    (hdet : ∀ t, ∀ᵐ ω ∂P, ω ∈ Av t → P[X | 𝓜 t] ω = K t ω)
    {S : Set Ω} (hr : ∀ᵐ ω ∂P, ω ∈ S → ∃ t, q ≤ Qc t ω)
    (hlim : ∀ᵐ ω ∂P, ω ∈ S → (∀ᶠ n in atTop, ω ∈ Av (dyF n (τ ω))) ∧
      Tendsto (fun n => K (dyF n (τ ω)) ω) atTop (𝓝 (G ω))) :
    HasFCK2CapForwardKernel P (fcRetainedDriverFiltration P hd W hm q) S X G := by
  refine ⟨𝓜, Av, K, τ, h𝓜, hτ, hb, hdet, ?_, hlim⟩
  intro D hD hs n k
  exact fcCap_censored_versions_of_observed_cuts hd W hm hQa hret hobs hcut h𝓖𝓜 hAv hD
    (by filter_upwards [hs, hr] with ω hsω hrω hωD using hrω (hsω hωD)) n k

end InteractingSLE.Restart.FCPlumb
