import HigherDimLQGMetric.Events.Defs
import LQGMetric.Papers.GM.S2.TightCore

/-!
# The common compactness step from Axiom V

Port of the generic part of `LQGMetric.GM.Tight.tight_mapsTo` to the frozen
`TightOver` predicate. It is shared with the configuration tightness argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X : ℝ → Ω → C(Rd d × Rd d, ℝ)} {S : Set ℝ}

/-- Uniform `MapsTo` control for a tight family of metric laws. The bad sets are
closed and decrease to a set that every limit law assigns measure zero. -/
theorem tightMapsTo_of_tightOver (hT : TightOver P X S)
    {A : ℕ → Set (Rd d × Rd d)} (hA : ∀ n, IsCompact (A n)) (hAa : Antitone A)
    {U : ℕ → Set ℝ} (hU : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hmet : ∀ f : C(Rd d × Rd d, ℝ), IsContinuousMetric f →
      ∀ x ∈ ⋂ n, A n, ∃ n, f x ∈ U n)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ r ∈ S, P {ω | ¬ MapsTo (X r ω) (A n) (U n)} < ε := by
  let Q : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ν | ∃ r ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)}
  have hQc : IsCompact (closure Q) := by
    apply isCompact_closure_of_isTightMeasureSet (hT.2.1.subset ?_)
    rintro _ ⟨ν, ⟨r, hr, hν⟩, rfl⟩
    exact ⟨r, hr, hν⟩
  let C : ℕ → Set C(Rd d × Rd d, ℝ) := fun n => {f | ¬ MapsTo f (A n) (U n)}
  have hCc : ∀ n, IsClosed (C n) :=
    fun n => LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo (hA n) (hU n)
  have hCa : Antitone C := by
    intro m n hmn f hf hfn
    exact hf (fun x hx => hUm hmn (hfn (hAa hmn hx)))
  have hzero : ∀ ν ∈ closure Q,
      (ν : Measure C(Rd d × Rd d, ℝ)) (⋂ n, C n) = 0 := by
    intro ν hν
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hT.2.2 ν hν] with f hf hmem
    obtain ⟨x, hx, hxu⟩ :=
      LQGMetric.GM.Tight.exists_mem_iInter_of_not_mapsTo hA hAa hU hUm
        (d := f) (mem_iInter.1 hmem)
    obtain ⟨n, hn⟩ := hmet f hf x hx
    exact hxu n hn
  obtain ⟨n, hn⟩ :=
    LQGMetric.GM.Tight.exists_measure_lt_of_isCompact_closure hQc hCc hCa hzero hε
  refine ⟨n, fun r hr => ?_⟩
  have hm := hT.1 r hr
  have hprob : IsProbabilityMeasure (P.map (X r)) := inferInstance
  have he : P {ω | ¬ MapsTo (X r ω) (A n) (U n)} = (P.map (X r)) (C n) := by
    rw [Measure.map_apply_of_aemeasurable hm (hCc n).measurableSet]
    rfl
  rw [he]
  exact hn ⟨_, hprob⟩ ⟨r, hr, rfl⟩

/-- Nonnegativity follows from the triangle and symmetry fields of `IsMetricFn`. -/
private theorem metricFn_nonneg {f : C(Rd d × Rd d, ℝ)}
    (hf : IsContinuousMetric f) (x y : Rd d) : 0 ≤ f (x, y) := by
  have h := hf.triangle x y x
  rw [hf.self_eq_zero, hf.symm y x] at h
  linarith

private theorem one_div_succ_anti : Antitone fun n : ℕ => (1 : ℝ) / (n + 1) :=
  fun m n hmn => one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hmn)

/-- The uniform lower bound of GM S2.4a, expressed directly for any `TightOver` family.
It is the part of Lemma R shared with configuration tightness. -/
theorem tightLowerOffDiag (hT : TightOver P X S) {K : Set (Rd d × Rd d)}
    (hK : IsCompact K) (hKd : ∀ p ∈ K, p.1 ≠ p.2)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ S,
      P {ω | ¬ ∀ p ∈ K, a < X r ω p} < ε := by
  obtain ⟨n, hn⟩ := tightMapsTo_of_tightOver hT
    (A := fun _ => K) (fun _ => hK) (fun _ _ _ => le_rfl)
    (U := fun n => Ioi ((1 : ℝ) / (n + 1))) (fun _ => isOpen_Ioi)
    (fun m n hmn => Ioi_subset_Ioi
      (one_div_succ_anti hmn))
    (fun f hf p hp => by
      have hpK : p ∈ K := mem_iInter.1 hp 0
      have hpos : 0 < f p := lt_of_le_of_ne (metricFn_nonneg hf p.1 p.2)
        (fun h0 => hKd p hpK (hf.eq_of_eq_zero p.1 p.2 h0.symm))
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact ⟨m, hm⟩) hε
  exact ⟨1 / (n + 1), by positivity, fun r hr => hn r hr⟩

/-- Compact pairs at Euclidean distance at most `b`. -/
private theorem isCompact_nearDiag {K : Set (Rd d)} (hK : IsCompact K) (b : ℝ) :
    IsCompact {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ b} :=
  (hK.prod hK).inter_right
    (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)

/-- The uniform near-diagonal modulus of GM S2.4b, at the level of `TightOver`. -/
theorem tightModulus (hT : TightOver P X S) {K : Set (Rd d)} (hK : IsCompact K)
    {a : ℝ} (ha : 0 < a) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ r ∈ S,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → X r ω (u, v) < a} < ε := by
  obtain ⟨n, hn⟩ := tightMapsTo_of_tightOver hT
    (A := fun n => {p : Rd d × Rd d | p ∈ K ×ˢ K ∧
      ‖p.1 - p.2‖ ≤ 1 / (n + 1)})
    (fun n => isCompact_nearDiag hK _)
    (fun m n hmn p hp => ⟨hp.1,
      hp.2.trans (one_div_succ_anti hmn)⟩)
    (U := fun _ => Iio a) (fun _ => isOpen_Iio) (fun _ _ _ => le_rfl)
    (fun f hf p hp => by
      have h0 : ‖p.1 - p.2‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
        exact ((mem_iInter.1 hp m).2.trans hm.le).trans (by linarith)
      have heq : p.1 = p.2 := sub_eq_zero.1 (norm_le_zero_iff.1 h0)
      refine ⟨0, ?_⟩
      show f p < a
      rcases p with ⟨u, v⟩
      simp only at heq
      subst v
      rw [hf.self_eq_zero]
      exact ha) hε
  refine ⟨1 / (n + 1), by positivity, fun r hr => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (hn r hr)
  intro ω hω hmaps
  exact hω (fun u hu v hv huv => hmaps ⟨⟨hu, hv⟩, huv⟩)

/-- Uniform boundedness of a compact set of metric values under `TightOver`. -/
theorem tightDiameter (hT : TightOver P X S) {K : Set (Rd d)} (hK : IsCompact K)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ r ∈ S,
      P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, X r ω (u, v) < A} < ε := by
  obtain ⟨n, hn⟩ := tightMapsTo_of_tightOver hT
    (A := fun _ => K ×ˢ K) (fun _ => hK.prod hK) (fun _ _ _ => le_rfl)
    (U := fun n => Iio ((n : ℝ) + 1)) (fun _ => isOpen_Iio)
    (fun m n hmn => Iio_subset_Iio (by exact_mod_cast Nat.succ_le_succ hmn))
    (fun f _ p _ => by
      obtain ⟨m, hm⟩ := exists_nat_gt (f p)
      exact ⟨m, show f p < (m : ℝ) + 1 by linarith⟩) hε
  refine ⟨n + 1, by positivity, fun r hr => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (hn r hr)
  intro ω hω hmaps
  exact hω (fun u hu v hv => hmaps ⟨hu, hv⟩)

end HigherDimLQGMetric
