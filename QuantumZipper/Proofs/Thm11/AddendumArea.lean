import QuantumZipper.Proofs.Thm11.AddendumAreaBound
import QuantumZipper.Proofs.Thm11.AddendumAreaDet
import QuantumZipper.Proofs.RS.TraceGen
import QuantumZipper.Proofs.Thm12.CharFun

/-!
# THM11 AD-2: for κ ∈ (4,8), points are swallowed, not hit; the SLE trace has zero area

Blueprint `blueprint/THM11_BLUEPRINT.md` §9, node AD-2 (and `EXT_RS_BLUEPRINT.md` §5, AD1-2).

* `ae_notMem_sleTrace`: for κ ∈ (4,8) and a fixed `a ∈ ℍ`, almost surely `a ∉ η[0,∞)`,
  `η = sleTrace κ B ω`.
* `ae_volume_sleTrace_eq_zero`: almost surely the trace `η[0,∞)` has zero Lebesgue area.

Proof of the first: the probabilistic lower bound on the log conformral radius
(`ae_logCR_lower_bound`, from the bounded FD-8 Lyapunov function `L − g∘arg`) and the
deterministic Koebe/generation argument (`notMem_trace_image_of_logCR_bound`), on the good event
of TR4 (`RS.ae_sleTrace_good`) and AD1-0 (`RS.rohdeSchrammTraceGen`). The second follows by
Fubini–Tonelli, using the jointly measurable continuous version of the trace
(`RS.exists_measurable_sleTrace`, TR6) and that the trace lies in `ℍ ∪ ℝ`
(`RS.trace_mem_fwdHull_or_real`).

Sources: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1, Theorem 1.1
addendum (p. 12) (the area of the trace must vanish for the field restricted to the complement
to be the whole field); Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005),
Thm 6.4 (pp. 29–31) and Lemma 6.3 (p. 25) (κ < 8: the trace has zero area; points are not hit);
Kemppainen, *Schramm–Loewner Evolution* (2017), Prop 5.6 (p. 85). Our route is the blueprint's
(FD-8 with bounded `g`, Koebe 1/4), not RS's Hausdorff-dimension/one-point-estimate route.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm11Area

open RS FwdClock

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **AD-2 (THM11).** For κ ∈ (4,8) and a fixed `a ∈ ℍ`, almost surely the SLE trace never
hits `a`: `P(a ∈ η[0,∞)) = 0`. -/
theorem ae_notMem_sleTrace (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8)
    {a : ℂ} (ha : a ∈ H) : ∀ᵐ ω ∂P, a ∉ sleTrace κ B ω '' Ici 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have ha0 : 0 < a.im := ha
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB' : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  have hbd : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ ((N : ℝ≥0) : ℝ) →
      a ∉ fwdHull (drive κ B' ω) t → Real.log a.im - M ≤ fwdLogCR (drive κ B' ω) t a :=
    ae_all_iff.2 fun N => ae_logCR_lower_bound hB' hB'm hB'c hκ hκ8 ha0 N
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hB (by linarith) hκ8
  have hgen := rohdeSchrammTraceGen hκ hκ8 P B hB
  filter_upwards [hbd, hdrive, hgood, hgen, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hω hd hg hgen' hc h0
  rintro ⟨s, hs, hsa⟩
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  obtain ⟨N, hN⟩ := exists_nat_ge s
  obtain ⟨M, hM⟩ := hω N
  rw [hd] at hM
  have hlim : ∀ t, 0 ≤ t → Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * Complex.I))
      (𝓝[>] 0) (𝓝 (trace (drive κ B ω) t)) := fun t ht => by
    obtain ⟨C, hC⟩ := hg.2.2 ⌈t⌉₊
    exact tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht, Nat.le_ceil t⟩)
  exact notMem_trace_image_of_logCR_bound hW hW0 hg.2.1 hlim hgen'.2.2 ha (T := N) (M := M)
    (fun t ht0 htT hat => hM t ht0 (by simpa using htT) hat) ⟨s, ⟨hs, hN⟩, hsa⟩

/-- The trace lies in the closed upper half-plane (a.s., on the good event of TR4). -/
theorem ae_im_sleTrace_nonneg (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → 0 ≤ (sleTrace κ B ω t).im := by
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hB hκ hκ8
  filter_upwards [hgood, hB.cont, hB.eval_zero_ae_eq_zero] with ω hg hc h0 t ht
  obtain ⟨C, hC⟩ := hg.2.2 ⌈t⌉₊
  rcases trace_mem_fwdHull_or_real (drive_continuous hc) (drive_zero h0) ht
    (tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht, Nat.le_ceil t⟩)) with h | h
  · exact (show (0 : ℝ) < (sleTrace κ B ω t).im from h.1).le
  · exact h.ge

/-- The set `{(ω, z) : z ∈ η_ω[0,∞)}` is measurable for a jointly measurable family of
continuous paths (via countable dense times and `infEDist`). -/
theorem measurableSet_mem_image_Ici {η : Ω → ℝ → ℂ} (hη : Measurable η)
    (hc : ∀ ω, Continuous (η ω)) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ η p.1 '' Ici 0} := by
  set D : ℕ → Set ℝ := fun N => Ioo 0 ((N : ℝ) + 1) ∩ range ((↑) : ℚ → ℝ) with hDdef
  have hDc : ∀ N, (D N).Countable := fun N => (countable_range _).mono inter_subset_right
  have hkey : ∀ ω (N : ℕ), η ω '' Icc 0 ((N : ℝ) + 1) = closure (η ω '' D N) := by
    intro ω N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    refine subset_antisymm ?_ (closure_minimal
      (image_mono (inter_subset_left.trans Ioo_subset_Icc_self))
      ((isCompact_Icc.image (hc ω)).isClosed))
    have h1 : Icc 0 ((N : ℝ) + 1) ⊆ closure (D N) := by
      rw [← closure_Ioo hN.ne]
      exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
        isClosed_closure
    exact (image_mono h1).trans (image_closure_subset_closure_image (hc ω))
  have hU : {p : Ω × ℂ | p.2 ∈ η p.1 '' Ici 0}
      = ⋃ N : ℕ, {p : Ω × ℂ | infEDist p.2 (η p.1 '' D N) = 0} := by
    ext p
    simp only [mem_iUnion]
    change p.2 ∈ η p.1 '' Ici 0 ↔ ∃ N : ℕ, infEDist p.2 (η p.1 '' D N) = 0
    simp_rw [← mem_closure_iff_infEDist_zero, ← hkey]
    constructor
    · rintro ⟨t, ht, hpt⟩
      obtain ⟨N, hN⟩ := exists_nat_ge t
      exact ⟨N, t, ⟨ht, hN.trans (by linarith)⟩, hpt⟩
    · rintro ⟨N, t, ht, hpt⟩
      exact ⟨t, ht.1, hpt⟩
  rw [hU]
  refine MeasurableSet.iUnion fun N => ?_
  have hm : Measurable fun p : Ω × ℂ => infEDist p.2 (η p.1 '' D N) := by
    have e : (fun p : Ω × ℂ => infEDist p.2 (η p.1 '' D N))
        = fun p => ⨅ t : D N, edist p.2 (η p.1 t) := by
      funext p
      rw [infEDist, iInf_image, iInf_subtype']
    rw [e]
    have := (hDc N).to_subtype
    exact Measurable.iInf fun t => measurable_snd.edist
      ((measurable_pi_apply (t : ℝ)).comp (hη.comp measurable_fst))
  exact hm (measurableSet_singleton 0)

theorem volume_setOf_im_eq_zero : volume {z : ℂ | z.im = 0} = 0 := by
  have e : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ {0}) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [e, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **AD-2, area form.** For κ ∈ (4,8), almost surely the SLE trace `η[0,∞)` has zero
two-dimensional Lebesgue measure. -/
theorem ae_volume_sleTrace_eq_zero (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ)
    (hκ8 : κ < 8) : ∀ᵐ ω ∂P, volume (sleTrace κ B ω '' Ici 0) = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := exists_measurable_sleTrace hB (by linarith) hκ8
  set S := {p : Ω × ℂ | p.2 ∈ η p.1 '' Ici 0} with hSdef
  have hS : MeasurableSet S := measurableSet_mem_image_Ici hηm hηc
  have himg : ∀ᵐ ω ∂P, η ω '' Ici 0 = sleTrace κ B ω '' Ici 0 :=
    hηeq.mono fun ω h => h.image_eq
  -- each `z ∉ ℝ` is a.s. not on the trace
  have hpt : ∀ z : ℂ, z.im ≠ 0 → P ((fun ω => (ω, z)) ⁻¹' S) = 0 := by
    intro z hz
    have hae : ∀ᵐ ω ∂P, z ∉ η ω '' Ici 0 := by
      rcases lt_or_gt_of_ne hz with hneg | hpos
      · filter_upwards [himg, ae_im_sleTrace_nonneg hB (by linarith) hκ8] with ω hi hnn
        rw [hi]
        rintro ⟨t, ht, rfl⟩
        exact absurd (hnn t ht) (not_le.2 hneg)
      · filter_upwards [himg, ae_notMem_sleTrace hB hκ hκ8 (show z ∈ H from hpos)] with ω hi h
        rwa [hi]
    exact measure_mono_null (t := {ω | ¬ z ∉ η ω '' Ici 0}) (fun ω hω => not_not.2 hω)
      (ae_iff.1 hae)
  have hprod : (P.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hS]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    refine measure_mono_null (fun z hz => ?_) volume_setOf_im_eq_zero
    by_contra hz'
    exact hz (hpt z hz')
  rw [Measure.prod_apply hS] at hprod
  have hzero := (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).1 hprod
  filter_upwards [hzero, himg] with ω h hi
  rw [← hi]
  exact h

end Thm11Area
end QuantumZipper
