/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdNested
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Sec7.LocalExtDCov
import InteractingSLE.GFF.LocalSets.SubdomainCov

/-!
# The nested Gaussian identity on an event of the finer σ-algebra

Worker REVIEW-FABLE-T14 (proving phase; the retained law at the first tail stage, orchestrator split of
PROVE-SB2-LCMEAN's handoff R13.8, items 2–3).

Supplement p. 632: "The initial erased portion adds no set in `D_A`. Its conditional covariance there remains
`G_{D_A}`, and the nested conditional-variance identity forces the harmonic mean to remain the initial projection."
The landed form of that identity (`Lcd.ae_map_condExpKernel_eq_of_norm_eq`) compares the regular conditional laws
given `𝒢 ≤ 𝒢'` on an event `F` **of the coarser σ-algebra `𝒢`**: under the coarser law the finer characteristic value
then has constant modulus, and a variable of constant modulus `‖w‖` with mean `w` is `w`. For the lower walk the
event "the stages before `ℓ` are erased" is an event of the finer σ-algebra only (it is read from B's own records),
and on its complement the finer conditional variance is smaller, so that argument does not apply.

The statement is still true for Gaussian laws, by a different argument. Let `X` be, given `𝒢`, Gaussian `N(μ, v)` on
`L ∈ 𝒢`, and given `𝒢' ≥ 𝒢` Gaussian `N(μ', v)` **with the same variance** on an event `G ∈ 𝒢'`, `G ⊆ L`. Then
`μ' = μ` almost surely on `G`: under the coarser law the part of the law of `X` carried by `G` is a mixture of the
`N(μ', v)` and is dominated by `N(μ, v)`; comparing exponential moments,
`E[1_G e^{s(μ' − μ)} | 𝒢] ≤ 1` for every real `s`, which forces `μ' = μ` on `G`.

* `ae_lintegral_lintegral_condExpKernel_eq`: the tower identity for nested regular conditional laws, for a
  nonnegative measurable function;
* `ae_map_condExpKernel_eq_gaussianReal`: a Gaussian conditional characteristic function gives a Gaussian regular
  conditional law;
* **`ae_eq_of_gaussian_le_on`**: the nested Gaussian identity on an event of the finer σ-algebra;
* **`ae_condExp_cexp_eq_gaussCF_of_le_on`**: its field form. If given `m` the field `Y` has the Gaussian
  characteristic functional of a word `β` on `L ∈ m`, and given `m' ≥ m` it has, on `G ∈ m'`, `G ⊆ L`, a Gaussian
  characteristic functional with the same covariance and some mean distribution `M'`, then on `G` it has the
  characteristic functional of `β` given `m'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Qt

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω}

/-! ### The tower identity for nonnegative functions -/

/-- **The tower identity for nested regular conditional laws**, for a nonnegative measurable function: for almost
every `ω`, integrating the finer conditional integral against the coarser conditional law gives the coarser
conditional integral. -/
theorem ae_lintegral_lintegral_condExpKernel_eq [IsFiniteMeasure P] (hm : m ≤ m') (hm' : m' ≤ mΩ)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∀ᵐ ω ∂P, ∫⁻ x, ∫⁻ y, f y ∂(condExpKernel P m' x) ∂(condExpKernel P m ω) =
      ∫⁻ y, f y ∂(condExpKernel P m ω) := by
  have hset : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ r ∈ (SimpleFunc.eapprox f n).range,
      condExpKernel P m ω (SimpleFunc.eapprox f n ⁻¹' {r}) =
        ∫⁻ x, condExpKernel P m' x (SimpleFunc.eapprox f n ⁻¹' {r}) ∂(condExpKernel P m ω) := by
    rw [ae_all_iff]
    intro n
    exact (Finset.eventually_all _).2 fun r _ =>
      KernelTower.ae_condExpKernel_eq_lintegral hm hm' (SimpleFunc.measurableSet_fiber _ r)
  filter_upwards [hset] with ω hω
  have hmeas : ∀ (n : ℕ) (r : ℝ≥0∞),
      Measurable fun x => condExpKernel P m' x (SimpleFunc.eapprox f n ⁻¹' {r}) := fun n r =>
    (measurable_condExpKernel (SimpleFunc.measurableSet_fiber _ r)).mono hm' le_rfl
  have hsf : ∀ n : ℕ, ∫⁻ x, (SimpleFunc.eapprox f n).lintegral (condExpKernel P m' x) ∂(condExpKernel P m ω) =
      (SimpleFunc.eapprox f n).lintegral (condExpKernel P m ω) := by
    intro n
    simp only [SimpleFunc.lintegral]
    rw [lintegral_finsetSum _ fun r _ => (hmeas n r).const_mul r]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [lintegral_const_mul _ (hmeas n r), ← hω n r hr]
  have hmeas2 : ∀ n : ℕ, Measurable fun x => (SimpleFunc.eapprox f n).lintegral (condExpKernel P m' x) := by
    intro n
    simp only [SimpleFunc.lintegral]
    exact Finset.measurable_sum _ fun r _ => (hmeas n r).const_mul r
  have hmono : Monotone fun (n : ℕ) (x : Ω) => (SimpleFunc.eapprox f n).lintegral (condExpKernel P m' x) :=
    fun i j hij x => SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox f hij) le_rfl
  calc ∫⁻ x, ∫⁻ y, f y ∂(condExpKernel P m' x) ∂(condExpKernel P m ω)
      = ∫⁻ x, ⨆ n, (SimpleFunc.eapprox f n).lintegral (condExpKernel P m' x) ∂(condExpKernel P m ω) := by
        simp_rw [lintegral_eq_iSup_eapprox_lintegral hf]
    _ = ⨆ n, ∫⁻ x, (SimpleFunc.eapprox f n).lintegral (condExpKernel P m' x) ∂(condExpKernel P m ω) :=
        lintegral_iSup hmeas2 hmono
    _ = ⨆ n, (SimpleFunc.eapprox f n).lintegral (condExpKernel P m ω) := by simp_rw [hsf]
    _ = ∫⁻ y, f y ∂(condExpKernel P m ω) := (lintegral_eq_iSup_eapprox_lintegral hf).symm

/-! ### Gaussian conditional laws -/

/-- **A Gaussian conditional characteristic function gives a Gaussian regular conditional law.** If, almost surely
on `L`, the conditional characteristic function of `X` given `m` at every real `t` is that of `N(μ ω, v)`, then almost
surely on `L` the law of `X` under the regular conditional law given `m` is `N(μ ω, v)`. -/
theorem ae_map_condExpKernel_eq_gaussianReal [IsProbabilityMeasure P] (hm : m ≤ mΩ) {X : Ω → ℝ}
    (hX : Measurable X) {v : ℝ≥0} {μ : Ω → ℝ} {L : Set Ω}
    (hc : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp ((t : ℂ) * (X ω' : ℂ) * Complex.I) | m] ω =
        Complex.exp ((t : ℂ) * (μ ω : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) :
    ∀ᵐ ω ∂P, ω ∈ L → (condExpKernel P m ω).map X = gaussianReal (μ ω) v := by
  have hmeas : ∀ t : ℝ, Measurable fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := fun t =>
    Complex.measurable_exp.comp ((measurable_const.mul Complex.measurable_ofReal).mul measurable_const)
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∈ L →
      ∫ y, Complex.exp ((((q : ℝ)) : ℂ) * (X y : ℂ) * Complex.I) ∂(condExpKernel P m ω) =
        Complex.exp ((((q : ℝ)) : ℂ) * (μ ω : ℂ) * Complex.I - ((v : ℝ) : ℂ) * (((q : ℝ)) : ℂ) ^ 2 / 2) := by
    rw [ae_all_iff]
    intro q
    have hint : Integrable (fun ω' => Complex.exp ((((q : ℝ)) : ℂ) * (X ω' : ℂ) * Complex.I)) P := by
      refine (integrable_const (1 : ℝ)).mono' ((hmeas q).comp hX).aestronglyMeasurable
        (Eventually.of_forall fun ω' => ?_)
      rw [← Complex.ofReal_mul]
      exact (Complex.norm_exp_ofReal_mul_I _).le
    filter_upwards [condExp_ae_eq_integral_condExpKernel hm hint, hc q] with ω h1 h2 hL
    rw [← h1]
    exact h2 hL
  filter_upwards [hq] with ω hω hL
  apply Measure.ext_of_charFun
  refine Continuous.ext_on Rat.denseRange_cast continuous_charFun continuous_charFun ?_
  rintro _ ⟨q, rfl⟩
  rw [charFun_apply_real, charFun_gaussianReal, integral_map hX.aemeasurable (hmeas q).aestronglyMeasurable]
  exact hω q hL

omit [StandardBorelSpace Ω] in
/-- The exponential moment of a variable with a Gaussian law, as a lower integral. -/
theorem lintegral_exp_mul_of_map_eq_gaussianReal {ν : Measure Ω} {X : Ω → ℝ} (hX : Measurable X) {a : ℝ}
    {v : ℝ≥0} (hlaw : ν.map X = gaussianReal a v) (s : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * X y)) ∂ν = ENNReal.ofReal (Real.exp (a * s + v * s ^ 2 / 2)) := by
  have hF : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (s * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have h1 : ∫⁻ y, ENNReal.ofReal (Real.exp (s * X y)) ∂ν =
      ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂(ν.map X) := (lintegral_map hF hX).symm
  rw [h1, hlaw, ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  have hmgf := mgf_gaussianReal (p := gaussianReal a v) (X := id) (μ := a) (v := v)
    ⟨aemeasurable_id, Measure.map_id⟩ s
  simp only [mgf, id] at hmgf
  rw [hmgf]

/-! ### The nested Gaussian identity -/

/-- **The nested Gaussian identity on an event of the finer σ-algebra.** Let `m ≤ m'`, let `X` have, almost surely
on `L ∈ m`, the regular conditional law `N(μ ω, v)` given `m`, and, almost surely on `G ∈ m'` with `G ⊆ L`, the regular
conditional law `N(μ' ω, v)` given `m'`, with the same variance `v`. Then `μ' = μ` almost surely on `G`. -/
theorem ae_eq_of_gaussian_le_on [IsProbabilityMeasure P] (hm : m ≤ m') (hm' : m' ≤ mΩ) {X : Ω → ℝ}
    (hX : Measurable X) {v : ℝ≥0} {μ μ' : Ω → ℝ} (hμ : Measurable[m] μ) (hμ' : Measurable[m'] μ')
    {L G : Set Ω} (hL : MeasurableSet[m] L) (hG : MeasurableSet[m'] G) (hGL : G ⊆ L)
    (hc : ∀ᵐ ω ∂P, ω ∈ L → (condExpKernel P m ω).map X = gaussianReal (μ ω) v)
    (hf : ∀ᵐ ω ∂P, ω ∈ G → (condExpKernel P m' ω).map X = gaussianReal (μ' ω) v) :
    ∀ᵐ ω ∂P, ω ∈ G → μ' ω = μ ω := by
  have hmΩ : m ≤ mΩ := hm.trans hm'
  have hGm : MeasurableSet G := hm' _ hG
  have hμm : Measurable μ := hμ.mono hmΩ le_rfl
  have hμ'm : Measurable μ' := hμ'.mono hm' le_rfl
  have hFm : ∀ s : ℝ, Measurable fun y => ENNReal.ofReal (Real.exp (s * X y)) := fun s =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hX))
  have hT : ∀ᵐ ω₀ ∂P, ∀ s : ℤ,
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp ((s : ℝ) * X y)) ∂(condExpKernel P m' x) ∂(condExpKernel P m ω₀) =
        ∫⁻ y, ENNReal.ofReal (Real.exp ((s : ℝ) * X y)) ∂(condExpKernel P m ω₀) :=
    ae_all_iff.2 fun s => ae_lintegral_lintegral_condExpKernel_eq hm hm' (hFm s)
  have hfK := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hmΩ hf
  have hfr := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hmΩ hμ
  have hLm := KernelTower.ae_condExpKernel_compl_eq_zero (P := P) hmΩ hL
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ x ∂(condExpKernel P m ω₀), x ∈ {x | x ∈ G → μ' x = μ x} := by
    filter_upwards [hc, hT, hfK, hfr, hLm] with ω₀ hc₀ hT₀ hfK₀ hfr₀ hLm₀
    by_cases hω₀ : ω₀ ∈ L
    · have hlaw := hc₀ hω₀
      -- the exponential moments carried by `G` are at most one
      have key : ∀ s : ℤ, ∫⁻ x in G, ENNReal.ofReal (Real.exp ((s : ℝ) * (μ' x - μ ω₀)))
          ∂(condExpKernel P m ω₀) ≤ 1 := by
        intro s
        have h1 := lintegral_exp_mul_of_map_eq_gaussianReal hX hlaw (s : ℝ)
        have h3 : ∫⁻ x in G, ENNReal.ofReal (Real.exp (μ' x * (s : ℝ) + v * (s : ℝ) ^ 2 / 2))
            ∂(condExpKernel P m ω₀) ≤
            ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp ((s : ℝ) * X y)) ∂(condExpKernel P m' x)
              ∂(condExpKernel P m ω₀) := by
          refine le_trans (le_of_eq ?_) (setLIntegral_le_lintegral G _)
          refine lintegral_congr_ae ((ae_restrict_iff' hGm).2 (hfK₀.mono fun x hx hxG => ?_))
          exact (lintegral_exp_mul_of_map_eq_gaussianReal hX (hx hxG) (s : ℝ)).symm
        have h4 : ∀ x, ENNReal.ofReal (Real.exp (μ' x * (s : ℝ) + v * (s : ℝ) ^ 2 / 2)) =
            ENNReal.ofReal (Real.exp ((s : ℝ) * (μ' x - μ ω₀))) *
              ENNReal.ofReal (Real.exp (μ ω₀ * (s : ℝ) + v * (s : ℝ) ^ 2 / 2)) := by
          intro x
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
        have hC0 : ENNReal.ofReal (Real.exp (μ ω₀ * (s : ℝ) + v * (s : ℝ) ^ 2 / 2)) ≠ 0 :=
          (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
        have h5 : (∫⁻ x in G, ENNReal.ofReal (Real.exp ((s : ℝ) * (μ' x - μ ω₀))) ∂(condExpKernel P m ω₀)) *
            ENNReal.ofReal (Real.exp (μ ω₀ * (s : ℝ) + v * (s : ℝ) ^ 2 / 2)) ≤
            1 * ENNReal.ofReal (Real.exp (μ ω₀ * (s : ℝ) + v * (s : ℝ) ^ 2 / 2)) := by
          have hmeasE : Measurable fun x => ENNReal.ofReal (Real.exp ((s : ℝ) * (μ' x - μ ω₀))) :=
            ENNReal.measurable_ofReal.comp
              (Real.measurable_exp.comp (measurable_const.mul (hμ'm.sub measurable_const)))
          rw [one_mul, ← lintegral_mul_const _ hmeasE]
          simp_rw [← h4]
          exact h3.trans (le_of_eq ((hT₀ s).trans h1))
        exact (ENNReal.mul_le_mul_iff_left hC0 ENNReal.ofReal_ne_top).1 h5
      -- Chebyshev on both sides
      have hcheb : ∀ (σ : ℤ) (S : Set Ω), MeasurableSet S → S ⊆ G → ∀ ε : ℝ, 0 < ε →
          (∀ x ∈ S, ε ≤ (σ : ℝ) * (μ' x - μ ω₀)) → (σ = 1 ∨ σ = -1) → condExpKernel P m ω₀ S = 0 := by
        intro σ S hS hSG ε hε hSε hσ
        by_contra hne
        have hfin : condExpKernel P m ω₀ S ≠ ⊤ := measure_ne_top _ _
        have hcpos : 0 < (condExpKernel P m ω₀ S).toReal := ENNReal.toReal_pos hne hfin
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (ε * (condExpKernel P m ω₀ S).toReal))
        have hle : ENNReal.ofReal (Real.exp ((n : ℝ) * ε)) * condExpKernel P m ω₀ S ≤ 1 := by
          calc ENNReal.ofReal (Real.exp ((n : ℝ) * ε)) * condExpKernel P m ω₀ S
              = ∫⁻ _ in S, ENNReal.ofReal (Real.exp ((n : ℝ) * ε)) ∂(condExpKernel P m ω₀) := by
                rw [setLIntegral_const]
            _ ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp ((((n : ℤ) * σ : ℤ) : ℝ) * (μ' x - μ ω₀)))
                  ∂(condExpKernel P m ω₀) := by
                refine setLIntegral_mono' hS fun x hx => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
                have h1 := hSε x hx
                push_cast
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
            _ ≤ ∫⁻ x in G, ENNReal.ofReal (Real.exp ((((n : ℤ) * σ : ℤ) : ℝ) * (μ' x - μ ω₀)))
                  ∂(condExpKernel P m ω₀) := lintegral_mono_set hSG
            _ ≤ 1 := key _
        have hreal : Real.exp ((n : ℝ) * ε) * (condExpKernel P m ω₀ S).toReal ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hle
          rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_one] at this
        have h2 : (n : ℝ) * ε ≤ Real.exp ((n : ℝ) * ε) := by linarith [Real.add_one_le_exp ((n : ℝ) * ε)]
        have h3 : 1 < (n : ℝ) * (ε * (condExpKernel P m ω₀ S).toReal) := by
          rw [div_lt_iff₀ (mul_pos hε hcpos)] at hn
          exact hn
        nlinarith [mul_le_mul_of_nonneg_right h2 hcpos.le]
      have hpos : ∀ k : ℕ, condExpKernel P m ω₀ (G ∩ {x | μ ω₀ + 1 / ((k : ℝ) + 1) ≤ μ' x}) = 0 := fun k =>
        hcheb 1 _ (hGm.inter (measurableSet_le measurable_const hμ'm)) inter_subset_left
          (1 / ((k : ℝ) + 1)) (by positivity) (fun x hx => by
            have := hx.2
            simp only [mem_ofPred_eq] at this
            push_cast
            linarith) (Or.inl rfl)
      have hneg : ∀ k : ℕ, condExpKernel P m ω₀ (G ∩ {x | μ' x ≤ μ ω₀ - 1 / ((k : ℝ) + 1)}) = 0 := fun k =>
        hcheb (-1) _ (hGm.inter (measurableSet_le hμ'm measurable_const)) inter_subset_left
          (1 / ((k : ℝ) + 1)) (by positivity) (fun x hx => by
            have := hx.2
            simp only [mem_ofPred_eq] at this
            push_cast
            linarith) (Or.inr rfl)
      rw [ae_iff]
      refine measure_mono_null (t := {x | μ x ≠ μ ω₀} ∪
        ((⋃ k : ℕ, G ∩ {x | μ ω₀ + 1 / ((k : ℝ) + 1) ≤ μ' x}) ∪
          ⋃ k : ℕ, G ∩ {x | μ' x ≤ μ ω₀ - 1 / ((k : ℝ) + 1)})) ?_ ?_
      · intro x hx
        simp only [mem_ofPred_eq, Classical.not_imp] at hx
        obtain ⟨hxG, hne⟩ := hx
        by_cases hμx : μ x = μ ω₀
        · right
          rw [hμx] at hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · right
            obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
            exact mem_iUnion.2 ⟨k, hxG, by simp only [mem_ofPred_eq]; linarith⟩
          · left
            obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
            exact mem_iUnion.2 ⟨k, hxG, by simp only [mem_ofPred_eq]; linarith⟩
        · left
          exact hμx
      · refine measure_union_null ?_ (measure_union_null (measure_iUnion_null hpos) (measure_iUnion_null hneg))
        have := hfr₀
        rw [ae_iff] at this
        exact this
    · rw [ae_iff]
      exact measure_mono_null (fun x hx => hGL (Classical.not_imp.1 hx).1) (hLm₀.2 hω₀)
  have hEm : MeasurableSet {x | x ∈ G → μ' x = μ x} := by
    have e : {x | x ∈ G → μ' x = μ x} = Gᶜ ∪ {x | μ' x = μ x} := by
      ext x
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [e]
    exact hGm.compl.union (measurableSet_eq_fun hμ'm hμm)
  exact Sec5.Lemma56Stages.ae_of_ae_condExpKernel hmΩ hEm hker

/-! ### The field form -/

open LQGMetric QuantumZipper Restart in
/-- **The nested Gaussian identity for a field, on an event of the finer σ-algebra.** Let `m ≤ m'`. If, given `m`,
the field `Y` has on `L ∈ m` the Gaussian characteristic functional of the word `β ω` (`β` measurable for `m`), and,
given `m'`, it has on `G ∈ m'`, `G ⊆ L`, a Gaussian characteristic functional with the same covariance and a mean
distribution `M' ω` whose pairings are measurable for `m'`, then on `G` the characteristic functional given `m'` is
that of `β ω`: the finer conditioning does not move the mean. -/
theorem ae_condExp_cexp_eq_gaussCF_of_le_on [IsProbabilityMeasure P] (hm : m ≤ m') (hm' : m' ≤ mΩ)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y) {β : Ω → BoundaryWord} (hβ : Measurable[m] β)
    {M' : Ω → DistOn upperHalfPlaneOpens}
    (hM' : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable[m'] fun ω => M' ω ψ)
    {L G : Set Ω} (hL : MeasurableSet[m] L) (hG : MeasurableSet[m'] G) (hGL : G ⊆ L)
    (hc : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m] ω = gaussCF (β ω) ψ)
    (hf : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m'] ω =
        Complex.exp (Complex.I * (M' ω ψ : ℂ) -
          (zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ : ℂ) / 2))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ G → P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m'] ω = gaussCF (β ω) ψ := by
  have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  have hXm : Measurable fun ω => Y ω ψ := (measurable_distOn_apply ψ).comp hY
  have hcov0 : 0 ≤ zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ := by
    rw [hH, LocalExt.zeroGFFTestCov_self_eq_norm_sq isOpen_H Subset.rfl]
    positivity
  have hfun : ∀ t : ℝ, (fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I)) =
      fun ω' => Complex.exp (Complex.I * ((Y ω' (t • ψ) : ℝ) : ℂ)) := by
    intro t
    funext ω'
    rw [map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  have hcovt : ∀ t : ℝ, zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ⇑(t • ψ) ⇑(t • ψ) =
      t ^ 2 * zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ := fun t => by
    rw [hH]
    exact LocalSets.zeroGFFTestCov_smul_self isOpen_H Subset.rfl t ψ
  have hmeant : ∀ (t : ℝ) (c : BoundaryWord), ∫ z, c.mean z * (t • ψ) z = t * ∫ z, c.mean z * ψ z := by
    intro t c
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show c.mean z * (t • ψ) z = t * (c.mean z * ψ z)
    rw [show (t • ψ) z = t * ψ z from rfl]
    ring
  -- the two Gaussian conditional characteristic functions of the pairing `Y ψ`
  have hc' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I) | m] ω =
        Complex.exp ((t : ℂ) * ((∫ z, (β ω).mean z * ψ z : ℝ) : ℂ) * Complex.I -
          (((zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ).toNNReal : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro t
    filter_upwards [hc (t • ψ)] with ω hω hωL
    rw [hfun t, hω hωL, gaussCF, hcovt, hmeant, Real.coe_toNNReal _ hcov0]
    congr 1
    push_cast
    ring
  have hf' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I) | m'] ω =
        Complex.exp ((t : ℂ) * ((M' ω ψ : ℝ) : ℂ) * Complex.I -
          (((zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ).toNNReal : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro t
    filter_upwards [hf (t • ψ)] with ω hω hωG
    rw [hfun t, hω hωG, hcovt, map_smul, smul_eq_mul, Real.coe_toNNReal _ hcov0]
    congr 1
    push_cast
    ring
  have hcK := ae_map_condExpKernel_eq_gaussianReal (hm.trans hm') hXm hc'
  have hfK := ae_map_condExpKernel_eq_gaussianReal hm' hXm hf'
  have hμ : Measurable[m] fun ω => ∫ z, (β ω).mean z * ψ z :=
    (BoundaryWord.measurable_integral_mean_mul ψ).comp hβ
  have heq := ae_eq_of_gaussian_le_on hm hm' hXm hμ (hM' ψ) hL hG hGL hcK hfK
  filter_upwards [hf ψ, heq] with ω h1 h2 hωG
  rw [h1 hωG, h2 hωG, gaussCF]

end InteractingSLE.Theorem14.SB.Qt
