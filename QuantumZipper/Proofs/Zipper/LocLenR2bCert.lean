import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.Proofs.Zipper.E1Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R2b (tool): a countable certificate for local limits
on an open interval

For `p < q`, the open interval `(p,q)` is identified with `ℝ` by the chart
`σ t = log ((t − p)/(q − t))`, inverse `τ u = p + (q − p) eᵘ/(1 + eᵘ)`. A sequence `νs` of
measures finite on compacts has a local vague limit on `(p,q)` iff the integrals of the glued
test functions `(p,q).indicator (g ∘ σ)` converge for the countable family
`BdryVague.testFam N m`, `BdryVague.bump N` (`LCert`). For `νs = bdryApprox γ x` this is a
measurable condition on `x` (`measurableSet_lCert`).

This is the interval analogue of the half-line certificate `Thm18Asm.G1Z5.SideCert`
(G1Z5SideCert.lean), with the dyadic sequence `k ↦ bdryApprox γ x k` in place of the radii
filter; the limit is produced by Riesz–Markov (`BdryVague.exists_isVagueLimitR_of_testFam`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen
namespace R2b

open BdryVague (testFam bump continuous_testFam hasCompactSupport_testFam continuous_bump
  hasCompactSupport_bump)

variable {p q : ℝ}

/-- The logistic chart `τ : ℝ → (p,q)`. -/
def tau (p q : ℝ) (u : ℝ) : ℝ := p + (q - p) * (Real.exp u / (1 + Real.exp u))

/-- Its inverse `σ : (p,q) → ℝ`. -/
def sig (p q : ℝ) (t : ℝ) : ℝ := Real.log ((t - p) / (q - t))

theorem continuous_tau (p q : ℝ) : Continuous (tau p q) := by
  unfold tau
  refine continuous_const.add (continuous_const.mul ?_)
  exact Real.continuous_exp.div (continuous_const.add Real.continuous_exp)
    fun u => by positivity

theorem measurable_sig (p q : ℝ) : Measurable (sig p q) :=
  Real.measurable_log.comp ((measurable_id.sub_const p).div (measurable_const.sub measurable_id))

theorem tau_mem (hpq : p < q) (u : ℝ) : tau p q u ∈ Ioo p q := by
  have he := Real.exp_pos u
  have h1 : 0 < Real.exp u / (1 + Real.exp u) := by positivity
  have h2 : Real.exp u / (1 + Real.exp u) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hd := sub_pos.2 hpq
  refine ⟨?_, ?_⟩ <;> unfold tau
  · nlinarith
  · nlinarith

theorem tau_sig (_hpq : p < q) {t : ℝ} (ht : t ∈ Ioo p q) : tau p q (sig p q t) = t := by
  have h1 : 0 < t - p := sub_pos.2 ht.1
  have h2 : 0 < q - t := sub_pos.2 ht.2
  unfold tau sig
  rw [Real.exp_log (div_pos h1 h2)]
  have hq : q - p ≠ 0 := by linarith
  field_simp
  ring

theorem sig_tau (hpq : p < q) (u : ℝ) : sig p q (tau p q u) = u := by
  have he := Real.exp_pos u
  have hd : 0 < q - p := sub_pos.2 hpq
  have e : (tau p q u - p) / (q - tau p q u) = Real.exp u := by
    unfold tau
    have h1 : (1 + Real.exp u) ≠ 0 := by positivity
    have h2 : q - (p + (q - p) * (Real.exp u / (1 + Real.exp u))) = (q - p) / (1 + Real.exp u) := by
      field_simp; ring
    rw [h2]
    field_simp
    ring
  unfold sig
  rw [e, Real.log_exp]

theorem continuousOn_sig (p q : ℝ) : ContinuousOn (sig p q) (Ioo p q) := by
  refine Real.continuousOn_log.comp ?_ ?_
  · refine ((continuous_id.sub continuous_const).continuousOn).div
      ((continuous_const.sub continuous_id).continuousOn) fun t ht => ?_
    exact (sub_pos.2 ht.2).ne'
  · intro t ht
    exact (div_pos (sub_pos.2 ht.1) (sub_pos.2 ht.2)).ne'

/-- The glued test function `(p,q).indicator (g ∘ σ)`. -/
def glue (p q : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := (Ioo p q).indicator (g ∘ sig p q)

theorem tsupport_glue_subset (hpq : p < q) {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    tsupport (glue p q g) ⊆ tau p q '' tsupport g := by
  have hc : IsCompact (tau p q '' tsupport g) := hgc.image (continuous_tau p q)
  refine closure_minimal (fun t ht => ?_) hc.isClosed
  have hts : t ∈ Ioo p q := by
    by_contra h; exact ht (indicator_of_notMem h _)
  have hg0 : g (sig p q t) ≠ 0 := by
    intro h0; apply ht; rw [glue, indicator_of_mem hts]; exact h0
  exact ⟨sig p q t, subset_closure hg0, tau_sig hpq hts⟩

theorem tsupport_glue_Ioo (hpq : p < q) {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    tsupport (glue p q g) ⊆ Ioo p q := by
  refine (tsupport_glue_subset hpq hgc).trans ?_
  rintro _ ⟨u, -, rfl⟩; exact tau_mem hpq u

theorem hasCompactSupport_glue (hpq : p < q) {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    HasCompactSupport (glue p q g) :=
  IsCompact.of_isClosed_subset (hgc.image (continuous_tau p q)) (isClosed_tsupport _)
    (tsupport_glue_subset hpq hgc)

theorem continuous_glue (hpq : p < q) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Continuous (glue p q g) := by
  have hon : ContinuousOn (glue p q g) (Ioo p q) :=
    (hg.comp_continuousOn (continuousOn_sig p q)).congr fun t ht => by
      simp [glue, indicator_of_mem ht]
  refine continuous_of_tsupport fun t ht => ?_
  exact hon.continuousAt (isOpen_Ioo.mem_nhds (tsupport_glue_Ioo hpq hgc ht))

theorem measurable_glue (p q : ℝ) {g : ℝ → ℝ} (hg : Continuous g) : Measurable (glue p q g) :=
  (hg.measurable.comp (measurable_sig p q)).indicator measurableSet_Ioo

/-- The measures pushed to `ℝ` by the chart. -/
def pushR (p q : ℝ) (μ : Measure ℝ) : Measure ℝ := (μ.restrict (Ioo p q)).map (sig p q)

theorem integral_glue (p q : ℝ) (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t, glue p q g t ∂μ = ∫ u, g u ∂pushR p q μ := by
  rw [pushR, integral_map (measurable_sig p q).aemeasurable hg.aestronglyMeasurable, glue,
    integral_indicator measurableSet_Ioo]
  rfl

theorem integral_Ioo (hpq : p < q) (μ : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (hfS : tsupport f ⊆ Ioo p q) :
    ∫ t, f t ∂μ = ∫ u, f (tau p q u) ∂pushR p q μ := by
  rw [pushR, integral_map (f := fun u => f (tau p q u)) (measurable_sig p q).aemeasurable
    (hf.comp (continuous_tau p q)).aestronglyMeasurable]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo p q) fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hfS h)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp [tau_sig hpq ht]

theorem pushR_apply_compact_lt_top (hpq : p < q) {μ : Measure ℝ} [IsFiniteMeasureOnCompacts μ]
    {K : Set ℝ} (hK : IsCompact K) : pushR p q μ K < ⊤ := by
  rw [pushR, Measure.map_apply (measurable_sig p q) hK.isClosed.measurableSet,
    Measure.restrict_apply (measurable_sig p q hK.isClosed.measurableSet)]
  refine (measure_mono fun t ht => ?_).trans_lt (hK.image (continuous_tau p q)).measure_lt_top
  exact ⟨sig p q t, ht.1, tau_sig hpq ht.2⟩

/-- **The countable certificate for a local vague limit on `(p,q)`.** -/
def LCert (νs : ℕ → Measure ℝ) (p q : ℝ) : Prop :=
  (∀ N m : ℕ, ∃ l, Tendsto (fun k => ∫ t, glue p q (testFam N m) t ∂νs k) atTop (𝓝 l)) ∧
    ∀ N : ℕ, ∃ l, Tendsto (fun k => ∫ t, glue p q (bump N) t ∂νs k) atTop (𝓝 l)

theorem lCert_of_lim (hpq : p < q) {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitOnR (Ioo p q) νs ν) : LCert νs p q :=
  ⟨fun N m => ⟨_, hν.2.2 _ (continuous_glue hpq (continuous_testFam N m)
      (hasCompactSupport_testFam N m)) (hasCompactSupport_glue hpq (hasCompactSupport_testFam N m))
      (tsupport_glue_Ioo hpq (hasCompactSupport_testFam N m))⟩,
    fun N => ⟨_, hν.2.2 _ (continuous_glue hpq (continuous_bump N) (hasCompactSupport_bump N))
      (hasCompactSupport_glue hpq (hasCompactSupport_bump N))
      (tsupport_glue_Ioo hpq (hasCompactSupport_bump N))⟩⟩

/-- **Local limit from the certificate** (measures finite on compacts). -/
theorem exists_lim_of_lCert (hpq : p < q) {νs : ℕ → Measure ℝ}
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k)) (hc : LCert νs p q) :
    ∃ ν, IsVagueLimitOnR (Ioo p q) νs ν := by
  have hfinP : ∀ k, IsFiniteMeasureOnCompacts (pushR p q (νs k)) :=
    fun k => ⟨fun K hK => pushR_apply_compact_lt_top (μ := νs k) hpq hK⟩
  obtain ⟨ν₀, hν₀⟩ := BdryVague.exists_isVagueLimitR_of_testFam (νs := fun k => pushR p q (νs k))
    hfinP (fun N m => by
      obtain ⟨l, hl⟩ := hc.1 N m
      exact ⟨l, hl.congr fun k => integral_glue p q _ (continuous_testFam N m)⟩)
    (fun N => by
      obtain ⟨l, hl⟩ := hc.2 N
      exact ⟨l, hl.congr fun k => integral_glue p q _ (continuous_bump N)⟩)
  have := hν₀.1
  refine ⟨ν₀.map (tau p q), ?_, fun K hK hKS => ?_, fun f hf hfc hfS => ?_⟩
  · rw [Measure.map_apply (continuous_tau p q).measurable measurableSet_Ioo.compl]
    have : tau p q ⁻¹' (Ioo p q)ᶜ = ∅ := by
      ext u; simp [tau_mem hpq u]
    rw [this, measure_empty]
  · rw [Measure.map_apply (continuous_tau p q).measurable hK.isClosed.measurableSet]
    have hc : IsCompact (sig p q '' K) :=
      hK.image_of_continuousOn ((continuousOn_sig p q).mono hKS)
    refine (measure_mono (s := tau p q ⁻¹' K) (t := sig p q '' K) fun u hu =>
      ⟨tau p q u, hu, sig_tau hpq u⟩).trans_lt hc.measure_lt_top
  · have hfτ : Continuous fun u => f (tau p q u) := hf.comp (continuous_tau p q)
    have hfτc : HasCompactSupport fun u => f (tau p q u) := by
      have hc : IsCompact (sig p q '' tsupport f) :=
        hfc.image_of_continuousOn ((continuousOn_sig p q).mono hfS)
      refine IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (closure_minimal ?_ hc.isClosed)
      intro u hu
      exact ⟨tau p q u, subset_closure hu, sig_tau hpq u⟩
    rw [integral_map (continuous_tau p q).aemeasurable hf.aestronglyMeasurable]
    exact (hν₀.2 _ hfτ hfτc).congr fun k => (integral_Ioo hpq _ hf hfS).symm

/-- A local limit on an empty interval. -/
theorem lim_Ioo_of_le {νs : ℕ → Measure ℝ} (hqp : q ≤ p) :
    ∃ ν, IsVagueLimitOnR (Ioo p q) νs ν := by
  have he : Ioo p q = ∅ := Ioo_eq_empty (not_lt.2 hqp)
  refine ⟨0, by simp, fun K _ _ => by simp, fun f _ _ hfS => ?_⟩
  rw [he, subset_empty_iff, tsupport_eq_empty_iff] at hfS
  subst hfS
  simp

/-- **Measurability of the certificate for the dyadic boundary approximations.** -/
theorem measurableSet_lCert (γ p q : ℝ) :
    MeasurableSet {x : FieldSample | LCert (bdryApprox γ x) p q} := by
  refine measurableSet_setOfPred.2 ((Measurable.forall fun N => Measurable.forall fun m =>
    measurableSet_setOfPred.1 ?_).and (Measurable.forall fun N => measurableSet_setOfPred.1 ?_))
  · exact E1.M4.measurableSet_exists_tendsto_bdry γ (measurable_glue p q (continuous_testFam N m))
  · exact E1.M4.measurableSet_exists_tendsto_bdry γ (measurable_glue p q (continuous_bump N))

/-- **Gluing over rational windows**: if the certificate holds on every rational window whose
closure lies in the open interval `U = (a,b)`, the local limit on `U` exists. -/
theorem exists_lim_of_windows {νs : ℕ → Measure ℝ} (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    {a b : ℝ} (hc : ∀ n : ℕ, a < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < b →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 → LCert νs (E1.winPQ n).1 (E1.winPQ n).2) :
    ∃ ν, IsVagueLimitOnR (Ioo a b) νs ν := by
  refine E1.exists_isVagueLimitOnR_of_winW isOpen_Ioo hfin fun n =>
    E1.exists_isVagueLimitOnR_winW n fun hsub => ?_
  by_cases hpq : ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2
  · have h1 := hsub ⟨le_rfl, hpq.le⟩
    have h2 := hsub ⟨hpq.le, le_rfl⟩
    exact exists_lim_of_lCert hpq hfin (hc n h1.1 h2.2 hpq)
  · exact lim_Ioo_of_le (not_lt.1 hpq)

end R2b
end LocLen
end QuantumZipper
