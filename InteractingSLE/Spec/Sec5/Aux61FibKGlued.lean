/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKRat

/-!
# From countably many glued-space identities to the fibre kernel

Packet PROVE-AUX61-FIB2, piece (F3)'s transfer. On the glued space, with a retained history `Z`, the code `Y` of the
restarted chart path and field, history-dependent fibre data `d z` and a cutoff `(F₀ z, N₀ z)` of `(d z).q`:

* `ratKer d F₀ n k p`: the explicit kernel `cfVal(∫ meanF(canonExt) ψ_p, E_q(ψ_p))` at the dyadic time `q = k/2ⁿ` and
  the test `ψ_p = ratTest p`; `ratAvoid n k p`: the event `{q < life, ψ_p off the hull at q}`;
* `measurableSet_ratAvoid` (an event of the raw code σ-algebra at `q`), `norm_ratKer_le_one`;
* `condExp_nullAugmented_ae_eq`: conditioning on the null augmentation changes nothing;
* **`ae_fibKernelRaw_of_glued`**: if on the history event `B` the path facts hold, the kernel `1_{ratAvoid} ratKer` is
  jointly measurable for `(history) ⊗ (raw code σ-algebra at q)`, and the rectangle identities
  `∫_{Z ∈ B', Y ∈ ratPi T} 1_{ratAvoid}(e^{i h(ψ_p)} − ratKer) dμ = 0` hold for every `n, k, p`, every finite family
  `T` of rational generators and every history event `B' ⊆ B`, then almost every fibre over `B` satisfies
  `FibKernelRaw` — hence (with `FibMembers`) is a `DyActFibre` (`Aux61FibKCode`).

The rectangle identities are the set-integral form of the glued-space conditional kernel at the dyadic fibre times
(given the history and the restarted path through fibre time `q`): Astra's follow-up 4 §§1.1–1.2 (R71), the union kernel
and Aux. 61's identity (1.1) relative to the reference word. Conditional helpers with distinct names; they replace no
source theorem. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any
`*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61FibK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Restart.DomainMarkov (RatIdx ratTest dyT)
open Aux61Win (meanF IsCutoffOn)
open Aux61Fib (FibCode FibData PathGood FibMembers fibW fibΓ fibU fibField)

universe u

/-- The test `ψ_p` on `ℍ`. -/
abbrev ratψ (p : RatIdx) : TestOn upperHalfPlaneOpens := ratTest upperHalfPlaneOpens p

/-- **The explicit kernel** at the dyadic time `k/2ⁿ` and the test `ψ_p`, for the data `d` and the cutoff `F₀`. -/
def ratKer (d : FibData) (F₀ : CMCut) (n k : ℕ) (p : RatIdx) (s : ULift.{u} FibCode) : ℂ :=
  cfVal (∫ z, meanF d.κ (canonExt d s (dyT n k)) d.q F₀ (Ito.rpath (fibW · s)) (dyT n k : ℝ≥0) z * ratψ p z)
    (loewnerGreenEnergy (Ito.rpath (fibW · s)) (dyT n k : ℝ≥0) (ratψ p))

/-- **The avoidance event** at the dyadic time `k/2ⁿ`: before the lifetime, `ψ_p` off the hull. -/
def ratAvoid (n k : ℕ) (p : RatIdx) : Set (ULift.{u} FibCode) :=
  Restart.DomainMarkov.avoidSet fibW fibU (ratψ p) (dyT n k)

/-- The raw σ-algebra of the codes at the dyadic time `k/2ⁿ`. -/
abbrev codeSigma (n k : ℕ) : MeasurableSpace (ULift.{u} FibCode) := codeFiltration.{u} (dyT n k)

theorem exists_rat_dyT (n k : ℕ) : ∃ q₀ : ℚ, (q₀ : ℝ).toNNReal = dyT n k := by
  refine ⟨(k : ℚ) / 2 ^ n, ?_⟩
  rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by push_cast; positivity)]
  simp [Restart.DomainMarkov.dyT]

/-- The decoded driver and its absent marks are weak paths. -/
theorem isWeakPath_fib (ω : ULift.{u} FibCode) :
    Restart.DomainMarkov.IsWeakPath (fibW · ω) (fun i t => noMarks (S := ULift.{u} FibCode) i t ω)
      (fun j t => noMarks (S := ULift.{u} FibCode) j t ω) (fibU ω) :=
  ⟨Aux61Fib.FibCode.driver_zero ω.down, (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn,
    fun i => i.elim0, fun j => j.elim0, fun _ _ i => i.elim0, fun _ _ j => j.elim0⟩

/-- The avoidance event is an event of the raw code σ-algebra. -/
theorem measurableSet_ratAvoid (n k : ℕ) (p : RatIdx) : MeasurableSet[codeSigma.{u} n k] (ratAvoid n k p) := by
  have hWa := Coupling.adaptedBefore_killedDriving_W Aux61Fib.isMeasurableKilledDriving_fib.{u}
  have e : ratAvoid.{u} n k p = Restart.DomainMarkov.safeU fibW fibU univ (ratψ p) (dyT n k) :=
    Subset.antisymm (fun ω hω => Restart.DomainMarkov.mem_safeU_of_mem_avoidSet isWeakPath_fib (ratψ p)
        (mem_univ ω) hω)
      (Restart.DomainMarkov.safeU_subset_avoidSet_of_weak isWeakPath_fib univ (ratψ p) (dyT n k))
  rw [e]
  exact Restart.DomainMarkov.measurableSet_safeU isWeakPath_fib hWa MeasurableSet.univ (ratψ p) (dyT n k)

/-- The kernel is bounded by `1` on the avoidance event. -/
theorem norm_ratKer_le_one (d : FibData) (F₀ : CMCut) {n k : ℕ} {p : RatIdx} {s : ULift.{u} FibCode}
    (hs : s ∈ ratAvoid n k p) : ‖ratKer d F₀ n k p s‖ ≤ 1 := by
  rw [ratKer, LocalExt.norm_cfVal, Real.exp_le_one_iff]
  have hw : Continuous (Ito.rpath (fibW · s)) :=
    (Aux61Fib.FibCode.continuous_driver s.down).comp continuous_real_toNNReal
  have hw0 : Ito.rpath (fibW · s) 0 = 0 := by simp [Ito.rpath, Aux61Fib.FibCode.driver_zero s.down]
  have hE := Coupling.loewnerGreenEnergy_nonneg hw hw0 (dyT n k).coe_nonneg (ratψ p) hs.2
  linarith

/-- The indicator of the kernel on the avoidance event is bounded by `1`. -/
theorem norm_indicator_ratKer_le_one (d : FibData) (F₀ : CMCut) (n k : ℕ) (p : RatIdx)
    (s : ULift.{u} FibCode) : ‖(ratAvoid n k p).indicator (ratKer d F₀ n k p) s‖ ≤ 1 := by
  by_cases hs : s ∈ ratAvoid n k p
  · rw [indicator_of_mem hs]; exact norm_ratKer_le_one d F₀ hs
  · rw [indicator_of_notMem hs, norm_zero]; exact zero_le_one

/-- **Conditioning on the null augmentation changes nothing.** -/
theorem condExp_nullAugmented_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) {f : Ω → ℂ} (hf : Integrable f P) :
    P[f | Ito.nullAugmented 𝓕 P t] =ᵐ[P] P[f | 𝓕 t] := by
  have hle : 𝓕 t ≤ Ito.nullAugmented 𝓕 P t := Ito.le_nullAugmented 𝓕 P t
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((Ito.nullAugmented 𝓕 P).le t) hf
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_)
    ((stronglyMeasurable_condExp.mono hle).aestronglyMeasurable)).symm
  obtain ⟨s', hs', hss'⟩ := Ito.exists_ae_eq_of_measurableSet_nullAugmented hs
  rw [setIntegral_congr_set hss', setIntegral_congr_set hss', setIntegral_condExp (𝓕.le t) hf hs']

/-- The integrand of the rectangle identities: on the history event `B`, the indicator of the avoidance event times
`e^{i h(ψ_p)} − ratKer`. -/
def gluedInt {β : Type*} (B : Set β) (d : β → FibData) (F₀ : β → CMCut) (n k : ℕ) (p : RatIdx)
    (zs : β × ULift.{u} FibCode) : ℂ :=
  B.indicator (fun z => (ratAvoid n k p).indicator
    (fun s => Complex.exp (Complex.I * (fibField s (ratψ p) : ℂ)) - ratKer (d z) (F₀ z) n k p s) zs.2) zs.1

/-- **Almost every fibre over the history event satisfies `FibKernelRaw`**, from the rectangle identities on the
glued space (see the module docstring). -/
theorem ae_fibKernelRaw_of_glued {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {β : Type*} [mβ : MeasurableSpace β] {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y)
    {B : Set β} (hB : MeasurableSet B) (d : β → FibData) (F₀ : β → CMCut) (N₀ : β → Set ℂ)
    (hcut : ∀ z ∈ B, IsCutoffOn (F₀ z) (d z).q (N₀ z) (d z).O₀ ∧ (d z).buffer ⊆ N₀ z)
    (G : Set (β × FibCode)) (hG : MeasurableSet G) (hGgood : ∀ z s, z ∈ B → (z, s) ∈ G → PathGood (d z) s)
    (hYG : ∀ᵐ x ∂μ, Z x ∈ B → (Z x, Y x) ∈ G)
    (hmeas : ∀ (n k : ℕ) (p : RatIdx), Measurable[mβ.prod (codeSigma.{u} n k)]
      (fun zs : β × ULift.{u} FibCode => (ratAvoid n k p).indicator (ratKer (d zs.1) (F₀ zs.1) n k p) zs.2))
    (hint : ∀ (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' → B' ⊆ B →
      ∫ x in Z ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y x)) ⁻¹' ratPi fibW fibU (dyT n k) T,
        gluedInt B d F₀ n k p (Z x, ULift.up (Y x)) ∂μ = 0) :
    ∀ᵐ x ∂μ, Z x ∈ B →
      FibKernelRaw (d (Z x)) (condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)) := by
  set Y' : X → ULift.{u} FibCode := fun x => ULift.up (Y x) with hY'def
  have hY' : Measurable Y' := measurable_up.comp hY
  -- the joint measurability of the integrands
  have hfm : ∀ p : RatIdx, Measurable fun s : ULift.{u} FibCode =>
      Complex.exp (Complex.I * (fibField s (ratψ p) : ℂ)) := fun p =>
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((LQGMetric.measurable_distOn_apply (ratψ p)).comp
        (Aux61Fib.FibCode.measurable_field.comp measurable_down))))
  have hsig : ∀ n k : ℕ, codeSigma.{u} n k ≤ (inferInstance : MeasurableSpace (ULift.{u} FibCode)) :=
    fun n k => codeFiltration.le (dyT n k)
  have hprod : ∀ n k : ℕ, mβ.prod (codeSigma.{u} n k) ≤
      (inferInstance : MeasurableSpace (β × ULift.{u} FibCode)) := fun n k =>
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (hsig n k))
  have hgm : ∀ (n k : ℕ) (p : RatIdx), Measurable (gluedInt.{u} B d F₀ n k p) := by
    intro n k p
    have h1 : Measurable fun zs : β × ULift.{u} FibCode =>
        (ratAvoid n k p).indicator (fun s => Complex.exp (Complex.I * (fibField s (ratψ p) : ℂ))) zs.2 :=
      ((hfm p).indicator (hsig n k _ (measurableSet_ratAvoid n k p))).comp measurable_snd
    have h2 := (hmeas n k p).mono (hprod n k) le_rfl
    have e : gluedInt.{u} B d F₀ n k p = (Prod.fst ⁻¹' B).indicator (fun zs =>
        (ratAvoid n k p).indicator (fun s => Complex.exp (Complex.I * (fibField s (ratψ p) : ℂ))) zs.2 -
          (ratAvoid n k p).indicator (ratKer (d zs.1) (F₀ zs.1) n k p) zs.2) := by
      funext zs
      simp only [gluedInt, Set.indicator, mem_preimage]
      split_ifs <;> simp_all
    rw [e]
    exact (h1.sub h2).indicator (measurable_fst hB)
  have hgb : ∀ (n k : ℕ) (p : RatIdx) (zs : β × ULift.{u} FibCode), ‖gluedInt.{u} B d F₀ n k p zs‖ ≤ 2 := by
    intro n k p zs
    simp only [gluedInt, Set.indicator]
    split_ifs with h1 h2
    · refine (norm_sub_le _ _).trans ?_
      have := norm_ratKer_le_one (d zs.1) (F₀ zs.1) h2
      rw [Complex.norm_exp_I_mul_ofReal]
      linarith
    · simp
    · simp
  -- the rectangle identities for every history event
  have hT : ∀ (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' →
      ∫ x in Z ⁻¹' B' ∩ Y' ⁻¹' ratPi fibW fibU (dyT n k) T, gluedInt.{u} B d F₀ n k p (Z x, Y' x) ∂μ = 0 := by
    intro n k p T B' hB'
    have hAm : MeasurableSet (ratPi fibW fibU (dyT n k) T) := by
      have h : MeasurableSet[ratSigma fibW fibU (dyT n k)] (ratPi fibW fibU (dyT n k) T) :=
        MeasurableSpace.measurableSet_generateFrom ⟨T, rfl⟩
      rw [generateFrom_ratPi fibW fibU (fun s => Aux61Fib.FibCode.continuous_driver s.down)
        (exists_rat_dyT n k)] at h
      exact hsig n k _ h
    have hint' : IntegrableOn (fun x => gluedInt.{u} B d F₀ n k p (Z x, Y' x))
        (Z ⁻¹' B' ∩ Y' ⁻¹' ratPi fibW fibU (dyT n k) T) μ :=
      (Integrable.of_bound ((hgm n k p).comp (hZ.prodMk hY')).aestronglyMeasurable 2
        (ae_of_all _ fun x => hgb n k p _)).integrableOn
    rw [← integral_inter_add_sdiff (hZ hB) hint']
    have e1 : Z ⁻¹' B' ∩ Y' ⁻¹' ratPi fibW fibU (dyT n k) T ∩ Z ⁻¹' B =
        Z ⁻¹' (B' ∩ B) ∩ Y' ⁻¹' ratPi fibW fibU (dyT n k) T := by
      ext x; simp only [mem_inter_iff, mem_preimage]; tauto
    have h0 : ∫ x in Z ⁻¹' (B' ∩ B) ∩ Y' ⁻¹' ratPi fibW fibU (dyT n k) T,
        gluedInt.{u} B d F₀ n k p (Z x, Y' x) ∂μ = 0 := hint n k p T (B' ∩ B) (hB'.inter hB) inter_subset_right
    rw [e1, h0, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hxB : Z x ∉ B := hx.2
    simp only [gluedInt]
    exact indicator_of_notMem hxB _
  -- the identities in almost every fibre
  have hfib : ∀ᵐ x ∂μ, ∀ i : ℕ × ℕ × RatIdx, ∀ A : Set (ULift.{u} FibCode),
      MeasurableSet[ratSigma fibW fibU (dyT i.1 i.2.1)] A →
      ∫ s in A, gluedInt.{u} B d F₀ i.1 i.2.1 i.2.2 (Z x, s) ∂(condDistrib Y' Z μ (Z x)) = 0 := by
    refine ae_all_iff.2 fun i => ?_
    obtain ⟨n, k, p⟩ := i
    refine ae_forall_setIntegral_condDistrib_eq_zero₂ hZ hY' (hgm n k p) (hgb n k p)
      (𝒜 := ratPi fibW fibU (dyT n k)) (fun T => ?_) (isPiSystem_ratPi _ _ _) (fun T B' hB' => hT n k p T B' hB')
      (fun B' hB' => ?_)
    · have h : MeasurableSet[ratSigma fibW fibU (dyT n k)] (ratPi fibW fibU (dyT n k) T) :=
        MeasurableSpace.measurableSet_generateFrom ⟨T, rfl⟩
      rw [generateFrom_ratPi fibW fibU (fun s => Aux61Fib.FibCode.continuous_driver s.down)
        (exists_rat_dyT n k)] at h
      exact hsig n k _ h
    · have h := hT n k p ∅ B' hB'
      have e : ratPi fibW fibU (dyT n k) (∅ : Finset (ℚ × ℚ × ℚ)) = univ := by
        simp [ratPi]
      rw [e, preimage_univ, inter_univ] at h
      exact h
  -- the path facts in almost every fibre
  set G' : Set (β × ULift.{u} FibCode) := {zs | zs.1 ∈ B → (zs.1, zs.2.down) ∈ G} with hG'def
  have hG' : MeasurableSet G' := by
    have e : G' = (Prod.fst ⁻¹' B)ᶜ ∪ (fun zs : β × ULift.{u} FibCode => (zs.1, zs.2.down)) ⁻¹' G := by
      ext zs
      simp only [hG'def, mem_ofPred_eq, mem_union, mem_preimage, mem_compl_iff]
      tauto
    rw [e]
    exact (measurable_fst hB).compl.union ((measurable_fst.prodMk (measurable_down.comp measurable_snd)) hG)
  have htr := Aux61Fib.ae_ae_condDistrib_of_ae_prod hZ hY' hG' (hYG.mono fun x hx hxB => hx hxB)
  filter_upwards [hfib, htr] with x hx hgx hxB
  have hgood : ∀ᵐ s ∂(condDistrib Y' Z μ (Z x)), PathGood (d (Z x)) s.down :=
    hgx.mono fun s hs => hGgood _ _ hxB (hs hxB)
  refine fibKernelRaw_of_rat (d (Z x)) (condDistrib Y' Z μ (Z x)) hgood (hcut _ hxB).1 (hcut _ hxB).2
    fun n k p => ?_
  set P := condDistrib Y' Z μ (Z x) with hPdef
  set f : ULift.{u} FibCode → ℂ := fun s => Complex.exp (Complex.I * (fibField s (ratψ p) : ℂ)) with hfdef
  set Φ : ULift.{u} FibCode → ℂ := (ratAvoid n k p).indicator (ratKer (d (Z x)) (F₀ (Z x)) n k p) with hΦdef
  have hAv := measurableSet_ratAvoid.{u} n k p
  have hAvm : MeasurableSet (ratAvoid.{u} n k p) := hsig n k _ hAv
  have hΦm : Measurable[codeSigma.{u} n k] Φ :=
    (hmeas n k p).comp (@measurable_prodMk_left β (ULift.{u} FibCode) mβ (codeSigma.{u} n k) (Z x))
  have hfint : Integrable f P :=
    Integrable.of_bound (hfm p).aestronglyMeasurable 1 (ae_of_all _ fun s => (Complex.norm_exp_I_mul_ofReal _).le)
  have hΦint : Integrable Φ P :=
    Integrable.of_bound (hΦm.mono (hsig n k) le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun s => norm_indicator_ratKer_le_one _ _ n k p s)
  have hH : ∀ A : Set (ULift.{u} FibCode), MeasurableSet[codeSigma.{u} n k] A →
      ∫ s in A ∩ ratAvoid n k p, f s ∂P = ∫ s in A ∩ ratAvoid n k p, Φ s ∂P := by
    intro A hA
    have hA' : MeasurableSet[ratSigma fibW fibU (dyT n k)] A := by
      rw [generateFrom_ratPi fibW fibU (fun s => Aux61Fib.FibCode.continuous_driver s.down) (exists_rat_dyT n k)]
      exact hA
    have h0 := hx (n, k, p) A hA'
    have e1 : (fun s => gluedInt.{u} B d F₀ n k p (Z x, s)) = fun s => (ratAvoid n k p).indicator f s - Φ s := by
      funext s
      simp only [gluedInt, indicator_of_mem hxB, hΦdef, hfdef]
      by_cases hs : s ∈ ratAvoid n k p
      · simp only [indicator_of_mem hs]
      · simp only [indicator_of_notMem hs, sub_zero]
    simp only [e1] at h0
    rw [integral_sub (hfint.indicator hAvm).integrableOn hΦint.integrableOn, sub_eq_zero] at h0
    rw [← setIntegral_indicator hAvm, h0, ← setIntegral_indicator hAvm, hΦdef, indicator_indicator, inter_self]
  have hce := ae_condExp_eq_of_forall_setIntegral (hsig n k) hfint hΦm.stronglyMeasurable
    (norm_indicator_ratKer_le_one _ _ n k p) hAv hH
  have hnull := condExp_nullAugmented_ae_eq (P := P) codeFiltration.{u} (dyT n k) hfint
  filter_upwards [hce, hnull] with s h1 h2 hlt hdis
  have hs : s ∈ ratAvoid.{u} n k p := ⟨hlt, hdis⟩
  rw [h2, h1 hs, hΦdef, indicator_of_mem hs]
  rfl

/-- **The path facts pass to almost every fibre over the history event.** -/
theorem ae_pathGood_condDistrib {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {β : Type*} [MeasurableSpace β] {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y)
    {B : Set β} (hB : MeasurableSet B) (d : β → FibData) (G : Set (β × FibCode)) (hG : MeasurableSet G)
    (hGgood : ∀ z s, z ∈ B → (z, s) ∈ G → PathGood (d z) s) (hYG : ∀ᵐ x ∂μ, Z x ∈ B → (Z x, Y x) ∈ G) :
    ∀ᵐ x ∂μ, Z x ∈ B →
      ∀ᵐ s ∂(condDistrib (fun x => ULift.up.{u} (Y x)) Z μ (Z x)), PathGood (d (Z x)) s.down := by
  set G' : Set (β × ULift.{u} FibCode) := {zs | zs.1 ∈ B → (zs.1, zs.2.down) ∈ G} with hG'def
  have hG' : MeasurableSet G' := by
    have e : G' = (Prod.fst ⁻¹' B)ᶜ ∪ (fun zs : β × ULift.{u} FibCode => (zs.1, zs.2.down)) ⁻¹' G := by
      ext zs
      simp only [hG'def, mem_ofPred_eq, mem_union, mem_preimage, mem_compl_iff]
      tauto
    rw [e]
    exact (measurable_fst hB).compl.union ((measurable_fst.prodMk (measurable_down.comp measurable_snd)) hG)
  have htr := Aux61Fib.ae_ae_condDistrib_of_ae_prod hZ (measurable_up.comp hY) hG' (hYG.mono fun x hx hxB => hx hxB)
  filter_upwards [htr] with x hx hxB
  exact hx.mono fun s hs => hGgood _ _ hxB (hs hxB)

/-- **The restart-fibre cover from the glued-space rectangle identities** (PROVE-AUX61-FIB's
`hasDyActFibreCover_of_fib` with `FibKernel` replaced by the rectangle identities of `ae_fibKernelRaw_of_glued`): a
countable family of histories, codes, history events, data, reference sets and visit events with (cover), (event),
the path facts, a cutoff of the data's correction with the joint measurability of the explicit kernel, the rectangle
identities and the member identities in almost every fibre. -/
theorem hasDyActFibreCover_of_glued {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} {ι : Type} [Countable ι]
    {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (Y : ι → X → FibCode) (hY : ∀ i, Measurable (Y i))
    (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i)) (d : ∀ i, β i → FibData) (I : ι → Set ℝ)
    (L : ι → Set FibCode) (hL : ∀ i, MeasurableSet (L i))
    (hLv : ∀ i, ∀ s ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ s.life ∧ ∃ y ∈ I i, s.trace v = (y : ℂ))
    (hRef : ∀ i, ∀ z ∈ B i, Ref (d i z).κ (d i z).bR (d i z).JR (I i))
    (G : ∀ i, Set (β i × FibCode)) (hG : ∀ i, MeasurableSet (G i))
    (hGgood : ∀ i z s, z ∈ B i → (z, s) ∈ G i → PathGood (d i z) s)
    (hYG : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → (Z i x, Y i x) ∈ G i)
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i) (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x → Y i x ∈ L i)
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    (hmeas : ∀ i (n k : ℕ) (p : RatIdx), Measurable[(mβ i).prod (codeSigma.{u} n k)]
      (fun zs : β i × ULift.{u} FibCode => (ratAvoid n k p).indicator (ratKer (d i zs.1) (F₀ i zs.1) n k p) zs.2))
    (hint : ∀ i (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set (β i)), MeasurableSet B' → B' ⊆ B i →
      ∫ x in Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y i x)) ⁻¹' ratPi fibW fibU (dyT n k) T,
        gluedInt (B i) (d i) (F₀ i) n k p (Z i x, ULift.up (Y i x)) ∂μ = 0)
    (hmem : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i →
      FibMembers (d i (Z i x)) (condDistrib (fun x => ULift.up.{u} (Y i x)) (Z i) μ (Z i x))) :
    Aux61Act.HasDyActFibreCover μ E Ref := by
  refine Aux61Fib.hasDyActFibreCover_of_fib Z hZ Y hY B hB d I L hL hLv hRef G hG hGgood hYG hcover hE
    (fun i => ?_) hmem
  filter_upwards [ae_fibKernelRaw_of_glued (hZ i) (hY i) (hB i) (d i) (F₀ i) (N₀ i) (hcut i) (G i) (hG i)
      (hGgood i) (hYG i) (hmeas i) (hint i),
    ae_pathGood_condDistrib (hZ i) (hY i) (hB i) (d i) (G i) (hG i) (hGgood i) (hYG i), hmem i]
    with x h1 h2 h3 hxB
  exact fibKernel_of_raw _ _ (h2 hxB) (h1 hxB) (h3 hxB)

end InteractingSLE.Sec5.Aux61FibK
