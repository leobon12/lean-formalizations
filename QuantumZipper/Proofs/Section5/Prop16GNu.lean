import QuantumZipper.Proofs.LQG.MeasurabilityAE
import QuantumZipper.Statements.Prop16

/-!
# Proposition 1.6, node D4-G (part 2): the boundary measure as a random measure

`aemeasurable_qBoundaryMeasureOn_Ioo_of_ae`: if `Y : Ω → FieldSample` has measurable
coordinates and, almost surely, the approximations `bdryApprox γ (Y ω)` have a vague limit on
the open interval `(a,b)` (A17), then `ω ↦ qBoundaryMeasureOn γ (Y ω) (a,b)` is a.e.-measurable
into the Giry σ-algebra. This is the local analogue of
`LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae`, with the exhaustion of `(a,b)` by the
intervals `(a + 1/(N+1), b - 1/(N+1))`.

`aemeasurable_prop16Nu`: the random boundary measure `ω ↦ ν_{h(ω)}` of Proposition 1.6 is
a.e.-measurable, given a.s. existence of the local boundary measure of `𝔥₀ + X` on `(a,b)`.
This is the hypothesis `hν` under which `prop16Law` is a genuine `bind` (not a junk measure).

Own elementary argument (AGENT_GUIDE cost rule), copied from the global version.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace G

open LQGMeas LQGMeasAE

/-- The exhausting intervals of `(a,b)`. -/
def ioo (a b : ℝ) (N : ℕ) : Set ℝ := Ioo (a + 1 / ((N : ℝ) + 1)) (b - 1 / ((N : ℝ) + 1))

theorem ioo_subset (a b : ℝ) (N : ℕ) : ioo a b N ⊆ Ioo a b := fun t ht => by
  have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem Icc_subset_Ioo' (a b : ℝ) (N : ℕ) :
    Icc (a + 1 / ((N : ℝ) + 2)) (b - 1 / ((N : ℝ) + 2)) ⊆ Ioo a b := fun t ht => by
  have : (0 : ℝ) < 1 / ((N : ℝ) + 2) := by positivity
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem ioo_mono (a b : ℝ) : Monotone (ioo a b) := by
  intro m n hmn t ht
  have h : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem mem_iUnion_ioo {a b t : ℝ} (ht : t ∈ Ioo a b) : ∃ N, t ∈ ioo a b N := by
  have hm : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / min (t - a) (b - t))
  have h1 : 1 / ((N : ℝ) + 1) < min (t - a) (b - t) := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hm] at hN
    nlinarith [min_le_left (t - a) (b - t)]
  exact ⟨N, by linarith [min_le_left (t - a) (b - t)],
    by linarith [min_le_right (t - a) (b - t)]⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The local boundary measure on `(a,b)` is a random measure**, given its a.s. existence. -/
theorem aemeasurable_qBoundaryMeasureOn_Ioo_of_ae {Y : Ω → FieldSample}
    (hYm : ∀ μ, Measurable fun ω => Y ω μ) {γ a b : ℝ}
    (hex : ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitOnR (Ioo a b) (bdryApprox γ (Y ω)) ν) :
    AEMeasurable (fun ω => qBoundaryMeasureOn γ (Y ω) (Ioo a b)) P := by
  classical
  have hae : ∀ᵐ ω ∂P, IsVagueLimitOnR (Ioo a b) (bdryApprox γ (Y ω))
      (qBoundaryMeasureOn γ (Y ω) (Ioo a b)) := hex.mono fun ω h => by
    unfold qBoundaryMeasureOn
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact h.choose_spec
  obtain ⟨S, hSm, hSp, hS0⟩ := exists_measurableSet_subset_ae hae
  let M : Ω → Measure ℝ := fun ω => if ω ∈ S then qBoundaryMeasureOn γ (Y ω) (Ioo a b) else 0
  refine ⟨M, ?_, ?_⟩
  · refine measurable_measure_of_open M (ioo a b) (fun N => measurableSet_Ioo) (ioo_mono a b)
      (fun ω => ?_) (fun ω N => ?_) (fun U N hU => ?_)
    · by_cases hω : ω ∈ S
      · simp only [M, hω, ite_true]
        refine measure_mono_null (fun t ht => ?_) (hSp ω hω).1
        intro htI
        obtain ⟨N, hN⟩ := mem_iUnion_ioo htI
        exact ht (mem_iUnion.2 ⟨N, hN⟩)
      · simp [M, hω]
    · by_cases hω : ω ∈ S
      · simp only [M, hω, ite_true]
        refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun t ht => ?_))
          ((hSp ω hω).2.1 _ isCompact_Icc (Icc_subset_Ioo' a b N)))
        have h : 1 / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) :=
          one_div_lt_one_div_of_lt (by positivity) (by linarith)
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · simp [M, hω]
    · set W := U ∩ ioo a b N
      have hW : IsOpen W := hU.inter isOpen_Ioo
      have hWb : Bornology.IsBounded W := Metric.isBounded_Ioo _ _ |>.subset inter_subset_right
      have hWc : Wᶜ.Nonempty := ⟨b, fun h => by
        have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        linarith [h.2.2]⟩
      have key : ∀ ω, M ω W = S.indicator
          (fun ω => ⨆ n : ℕ, ENNReal.ofReal (bdryFun γ (openBump W n) (Y ω))) ω := by
        intro ω
        by_cases hω : ω ∈ S
        · simp only [M, hω, ite_true, indicator_of_mem hω]
          have hv := hSp ω hω
          rw [measure_open_eq_iSup _ hW hWc]
          congr 1
          funext n
          have hc := continuous_openBump W n
          have hcs := hasCompactSupport_openBump hWb n
          have hts : tsupport (openBump W n) ⊆ Ioo a b :=
            (tsupport_openBump_subset W n).trans (inter_subset_right.trans (ioo_subset a b N))
          rw [show bdryFun γ (openBump W n) (Y ω) =
                ∫ t, openBump W n t ∂qBoundaryMeasureOn γ (Y ω) (Ioo a b)
              from (hv.2.2 _ hc hcs hts).liminf_eq,
            ofReal_integral_eq_lintegral_ofReal ?_
              (ae_of_all _ fun z => openBump_nonneg W n z)]
          have hμK : qBoundaryMeasureOn γ (Y ω) (Ioo a b) (tsupport (openBump W n)) ≠ ⊤ :=
            (hv.2.1 _ hcs hts).ne
          refine ((integrableOn_const (C := (1 : ℝ)) hμK).integrable_indicator
            (isClosed_tsupport _).measurableSet).mono' hc.aestronglyMeasurable
            (ae_of_all _ fun t => ?_)
          by_cases ht : t ∈ tsupport (openBump W n)
          · rw [indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg (openBump_nonneg W n t)]
            exact openBump_le_one W n t
          · rw [indicator_of_notMem ht, image_eq_zero_of_notMem_tsupport ht, norm_zero]
        · simp [M, hω]
      simp_rw [key]
      exact (Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
        (measurable_bdryFun_comp hYm γ (continuous_openBump W n).measurable)).indicator hSm
  · refine measure_mono_null (fun ω hω => ?_) hS0
    by_contra h
    exact hω (by simp [M, show ω ∈ S from not_not.1 h])

/-- **`hν` for Proposition 1.6**: the random boundary measure `ω ↦ ν_{h(ω)}` is
a.e.-measurable, given a.s. existence of the local boundary measure of `𝔥₀ + X` on `(a,b)`. -/
theorem aemeasurable_prop16Nu {X : Ω → FieldSample} (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ)
    {γ : ℝ} {h0 : ℂ → ℝ} {a b : ℝ}
    (hex : ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitOnR (Ioo a b) (bdryApprox γ (ofFun h0 + X ω)) ν) :
    AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P :=
  aemeasurable_qBoundaryMeasureOn_Ioo_of_ae (Y := fun ω => ofFun h0 + X ω)
    (fun μ => measurable_const.add (hX μ)) hex

end G

end Prop16Area

end QuantumZipper
