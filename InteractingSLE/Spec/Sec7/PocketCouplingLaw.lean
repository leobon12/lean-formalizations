/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketCouplingInf
import InteractingSLE.Spec.Sec7.MarkedProp39
import InteractingSLE.Spec.Sec7.Lemma71PinNull

/-!
# Theorem 1.3's pocket word: the physical pocket kernel from the marked union law (R.5)

Packet PROVE-STRIPSYS26. Specification §7.4, Aux. lemma 124 (`source/spec/p385-432.md` L171–L196, pp. 393–394:
"Assume the marked optional union law for `A ∪ R_t`, with its stopped history and individual germs retained. … On each
component of `C ∖ R_t`, its harmonic conditional mean is the same as the mean with only the marked `A ∪ R_t` initially
retained") and Aux. lemma 125's proof (p. 396: "The marked local-set law gives its active Dirichlet covariance").

`PocketCoupling` reduces the coupling inputs of the pocket word to the physical kernel `PocketKernel` and the mean
identification `PocketMeanIdent`. Here the physical kernel is derived from the **marked union law** at every relative
capacity time `q` (`PocketUnionLaw`): a local set `K_q` of the zero-boundary field `h₀` (the walls and the counterflow
stopped at the ambient time of the relative clock) with marks `ℋ_q` satisfying the history-marked avoidance criterion,
whose germ and marks know the walls and the traversal's prefix events up to null sets, and of whose complement the
active pocket domain is a union of components. The field is `h = h₀ + 𝔥` with a deterministic boundary mean `𝔥`; the
mean `M_q` of the kernel is then the local-set mean of `K_q` plus `𝔥`
(`MarkedProp39.ae_condExp_exp_eq_of_le_markedOffCover`, `Lemma71S.condExp_ae_eq_of_le_sup_nullSets`).

## Main results

* `activeDom`, `activeDom_eq`: the active pocket domain on the live event;
* `PocketUnionLaw` (the marked union law, as an input);
* **`pocketKernel_of_unionLaw`**;
* `PocketUnionChartLaw`, `PocketUnionInput`, `PocketUnionInputInf` (the pocket inputs in local-set form),
  `pocketChartLaw_of_union`, `pocketChartInput_of_unionInput`, `pocketChartInputInf_of_unionInputInf`;
* **`pocketWordEvolution_of_unionInput'`**: hPW from the pocket inputs in local-set form.

Conditional helpers; they replace no source theorem. Ruling R48 respected (as in `PocketCoupling`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketCoupling

open PocketTraversal PocketAdapt PhaseSel Lemma71C LocalSets WholeField MarkedProp39

section Union

variable {Ω : Type*}

/-- **The active pocket domain** at relative capacity time `q` on the live event of `A` (empty off it): the chart
preimage `inv(ℍ ∖ K_q)` of the complement of the relative hull of the traversal. -/
def activeDom (A : Set Ω) (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  {z | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧
    z ∈ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)}

theorem activeDom_eq {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) :
    activeDom A γ c q ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) := by
  ext z
  exact ⟨fun h => h.2.2, fun h => ⟨hω, hq, h⟩⟩

/-- **The marked union law at the relative capacity times** (R.5; the hypothesis of Aux. lemma 124 and of marked
Proposition 3.9): at every fixed relative capacity time `q`, a random closed set `K_q` (in the source: the complete
marked incoming walls together with the counterflow stopped at the ambient stopping time `T(q)` of the relative clock,
read in the counterflow chart) with marks `ℋ_q` (the walls' labels and the stopped counterflow history) is a local set
of the zero-boundary field `h₀` with local-set mean `g_q`, satisfying the history-marked avoidance criterion; the
walls' information and the traversal's prefix events on `A` up to `q` are known to its germ and marks up to null sets;
and the active pocket domain is measurable from `K_q` and the marks and is almost surely a union of components of
`ℍ ∖ K_q` (in the source: the active component of `C ∖ η[0, T(q)]`). -/
def PocketUnionLaw (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (h₀ : Ω → DistOn upperHalfPlaneOpens) (K : ℝ≥0 → Ω → Set ℂ)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ q : ℝ≥0, Measurable[mΩ, hittingSigma] (K q) ∧ ℋ q ≤ mΩ ∧ IsLocalSet (K q) h₀ P ∧
    IsHistoryAvoidanceLocal (ℋ q) (K q) h₀ P ∧ IsLocalSetMean (K q) h₀ P (g q) ∧
    locPrefixSigma 𝓦 A γ q ≤ germSigma (K q) h₀ ⊔ ℋ q ⊔ Ito.nullSets P ∧
    Measurable[MeasurableSpace.comap (K q) hittingSigma ⊔ ℋ q, hittingSigma]
      (fun ω => H \ activeDom A γ c q ω) ∧
    ∀ᵐ ω ∂P, activeDom A γ c q ω ⊆ H \ K q ω ∧
      ∀ z ∈ activeDom A γ c q ω, connectedComponentIn (H \ K q ω) z ⊆ activeDom A γ c q ω

variable {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The physical pocket kernel from the marked union law**: for `h = h₀ + 𝔥` with `h₀` a zero-boundary GFF and `𝔥`
deterministic, the marked union law gives the kernel `PocketKernel` with the σ-algebras `germ(K_q) ∨ ℋ_q ∨ 𝒩` and the
means `g_q + 𝔥`. -/
theorem pocketKernel_of_unionLaw {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (𝔥 : DistOn upperHalfPlaneOpens) {h : Ω → DistOn upperHalfPlaneOpens} (hh : ∀ ω, h ω = h₀ ω + 𝔥)
    {K : ℝ≥0 → Ω → Set ℂ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hU : PocketUnionLaw 𝓦 P A γ c h₀ K ℋ g) :
    PocketKernel 𝓦 P A γ c h (fun q => germSigma (K q) h₀ ⊔ ℋ q ⊔ Ito.nullSets P) (fun q ω => g q ω + 𝔥) := by
  have hh₀m : Measurable h₀ := hh₀.measurable
  refine ⟨fun q => sup_le (sup_le (germSigma_le (hU q).1 hh₀m) (hU q).2.1) (Ito.nullSets_le P),
    fun q => (hU q).2.2.2.2.2.1, fun q φ => ?_⟩
  obtain ⟨hK, hℋ, hloc, hmark, hg, -, hCm, hC⟩ := hU q
  have hm₁ : germSigma (K q) h₀ ⊔ ℋ q ≤ mΩ := sup_le (germSigma_le hK hh₀m) hℋ
  have hX₀ : Integrable (fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh₀m)
  have h1 := ae_condExp_exp_eq_of_le_markedOffCover hh₀ hK hℋ hloc hmark hCm hC hg le_rfl
    (le_markedOffCoverSigma_germ _) φ
  have h2 := Lemma71S.condExp_ae_eq_of_le_sup_nullSets (m₁ := germSigma (K q) h₀ ⊔ ℋ q)
    (m₂ := germSigma (K q) h₀ ⊔ ℋ q ⊔ Ito.nullSets P) le_sup_left le_rfl
    (sup_le hm₁ (Ito.nullSets_le P)) hX₀
  have e : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) =
      (Complex.exp (Complex.I * (𝔥 φ : ℂ))) • fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) := by
    funext ω
    rw [hh ω, IsAddApply.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
    push_cast
    ring_nf
  have h3 := condExp_smul (μ := P) (Complex.exp (Complex.I * (𝔥 φ : ℂ)))
    (fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ))) (germSigma (K q) h₀ ⊔ ℋ q ⊔ Ito.nullSets P)
  filter_upwards [h1, h2, h3] with ω e1 e2 e3 hωA hq hs
  have hs' : tsupport φ ⊆ activeDom A γ c q ω := by
    rw [activeDom_eq hωA hq]
    exact hs
  rw [e, e3, Pi.smul_apply, e2, e1 hs', activeDom_eq hωA hq, IsAddApply.add_apply, smul_eq_mul,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A measurable field shifted by a deterministic distribution is measurable. -/
theorem measurable_add_const {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀)
    (𝔥 : DistOn upperHalfPlaneOpens) {h : Ω → DistOn upperHalfPlaneOpens} (hh : ∀ ω, h ω = h₀ ω + 𝔥) :
    Measurable h := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  have e : (fun ω => h ω φ) = fun ω => h₀ ω φ + 𝔥 φ := by
    funext ω
    rw [hh ω, IsAddApply.add_apply]
  rw [e]
  exact ((LQGMetric.measurable_distOn_apply φ).comp hh₀).add_const _

end Union

/-! ### The pocket inputs in local-set form -/

section UnionInputs

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks

variable {Ω : Type*}

/-- **The pocket chart law in local-set form**: a pocket chart, the marked union law and the mean identification
for the local-set means shifted by the deterministic boundary mean `𝔥`. -/
def PocketUnionChartLaw (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓦 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (c : Ω → Chart) (a k : ℝ) (K : ℝ≥0 → Ω → Set ℂ) (ℋ : ℝ≥0 → MeasurableSpace Ω)
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
    IsPocketChartOn 𝓦 A C ψ c ∧ PocketUnionLaw 𝓦 P A γ c h₀ K ℋ g ∧
      PocketMeanIdent κ ρL ρR P A γ xL xR c a k fun q ω => g q ω + 𝔥

/-- **The pocket inputs in local-set form on every word-shape event** (bounded change pocket): `PocketChartInput`
with the pocket chart law in local-set form for the field `h₀ + 𝔥`. -/
def PocketUnionInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, PocketWordAssembly.IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @PocketWordAssembly.IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL))
        (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A (travAll R L r η ψ) (marksL2All R ψ)
        (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL))
        (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A (travAll R L r η ψ) marksL1All
        (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥)

/-- **The pocket inputs in local-set form on every word-shape event, pocket opening at the flow seed**
(`PocketChartInputInf` in local-set form). -/
def PocketUnionInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, PocketSeedOpen.IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
    @PocketSeedOpen.IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL))
        (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A (travAllInf R L r η ψ) (marksL2All R ψ)
        (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL))
        (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A (travAllInf R L r η ψ) marksL1All
        (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥)

end UnionInputs

section UnionThms

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h₀ : Ω → DistOn upperHalfPlaneOpens} {𝔥 : DistOn upperHalfPlaneOpens} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The pocket chart law from its local-set form.** -/
theorem pocketChartLaw_of_union (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) (hh : ∀ ω, h ω = h₀ ω + 𝔥)
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    (hU : PocketUnionChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ h₀ 𝔥) : PocketChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ h := by
  obtain ⟨c, a, k, K, ℋ, g, hc, hL, hM⟩ := hU
  exact ⟨c, a, k, _, _, hc, pocketKernel_of_unionLaw hh₀ 𝔥 hh hL, hM⟩

/-- **The pocket chart inputs from their local-set form** (bounded change pocket). -/
theorem pocketChartInput_of_unionInput (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hh : ∀ ω, h ω = h₀ ω + 𝔥) {κ rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    (hin : PocketUnionInput κ rL rR 𝓦 P R L r η G h₀ 𝔥) : PocketChartInput κ rL rR 𝓦 P R L r η G h :=
  fun A hA hAG hPA ψ hψ hψm => ⟨fun hs => pocketChartLaw_of_union hh₀ hh ((hin A hA hAG hPA ψ hψ hψm).1 hs),
    fun hs => pocketChartLaw_of_union hh₀ hh ((hin A hA hAG hPA ψ hψ hψm).2 hs)⟩

/-- **The pocket chart inputs at infinity from their local-set form.** -/
theorem pocketChartInputInf_of_unionInputInf (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hh : ∀ ω, h ω = h₀ ω + 𝔥) {κ rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    (hin : PocketUnionInputInf κ rL rR 𝓦 P R L r η G h₀ 𝔥) : PocketChartInputInf κ rL rR 𝓦 P R L r η G h :=
  fun A hA hAG hPA ψ hψ hψm => ⟨fun hs => pocketChartLaw_of_union hh₀ hh ((hin A hA hAG hPA ψ hψ hψm).1 hs),
    fun hs => pocketChartLaw_of_union hh₀ hh ((hin A hA hAG hPA ψ hψ hψm).2 hs)⟩

end UnionThms

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks in
/-- **hPW from the pocket inputs in local-set form** (`κ′ > 4`, both-low seed weights; Lemma 7.25's proof with
Aux. lemmas 119–125 and 130): `pocketWordEvolution_of_chartInput'` for the field `h₀ + 𝔥`, with the physical kernels
from the marked union laws. -/
theorem pocketWordEvolution_of_unionInput'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r →
      PocketWordAssembly.IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 →
      PocketSeedOpen.IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : PocketUnionInput (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ 𝔥)
    (hinI : PocketUnionInputInf (16 / κ') rL rR 𝓦 P R L r η
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR :=
  pocketWordEvolution_of_chartInput' hκ' hL hLd hR hRd h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm
    (measurable_add_const hh₀.measurable 𝔥 (fun _ => rfl))
    (pocketChartInput_of_unionInput hh₀ (fun _ => rfl) hin)
    (pocketChartInputInf_of_unionInputInf hh₀ (fun _ => rfl) hinI)

end InteractingSLE.Sec7.PocketCoupling
