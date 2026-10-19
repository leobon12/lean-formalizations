import GaussianLQG.Core.Setup

/-!
# Measurability of the Hölder constant, separated infimum and annulus crossing

For a continuous `d : C(ℂ × ℂ, ℝ)` the supremum defining `A(K) = holderConst d K` and the infima
defining `I(K, δ) = sepInf d K δ` and `L_R = annulusCross d R` may be taken over a countable set
that does not depend on `d` (blueprint §1.6: "the supremum and infimum may be taken over countable
dense sets"). Hence these are measurable functions on `C(ℂ × ℂ, ℝ)` with its Borel σ-algebra
(`measurable_holderConst_cont`, `measurable_sepInf_cont`, `measurable_annulusCross_cont`), and,
composed with the random metric `D^γ` of a `Setup`, random variables
(`Setup.measurable_holderConst`, `Setup.measurable_sepInf`, `Setup.measurable_annulusCross`; also
`Setup.measurable_coe_D`, `Setup.measurable_D_apply`, `Setup.measurable_log_D`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-! ## Suprema and infima over dense subsets -/

theorem biSup_eq_biSup_of_subset_closure {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hTS : T ⊆ S) (hST : S ⊆ closure T) {F : X → ℝ≥0∞} (hF : ContinuousOn F S) :
    ⨆ x ∈ S, F x = ⨆ x ∈ T, F x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (biSup_mono hTS)
  have h1 : F x ∈ closure (F '' T) := ((hF x hx).mono hTS).mem_closure_image (hST hx)
  have h2 : F '' T ⊆ Iic (⨆ y ∈ T, F y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_iSup₂ (f := fun y (_ : y ∈ T) => F y) y hy
  exact closure_minimal h2 isClosed_Iic h1

theorem biInf_eq_biInf_of_subset_closure {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hTS : T ⊆ S) (hST : S ⊆ closure T) {F : X → ℝ≥0∞} (hF : ContinuousOn F S) :
    ⨅ x ∈ S, F x = ⨅ x ∈ T, F x := by
  refine le_antisymm (biInf_mono hTS) (le_iInf₂ fun x hx => ?_)
  have h1 : F x ∈ closure (F '' T) := ((hF x hx).mono hTS).mem_closure_image (hST hx)
  have h2 : F '' T ⊆ Ici (⨅ y ∈ T, F y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact iInf₂_le (f := fun y (_ : y ∈ T) => F y) y hy
  exact closure_minimal h2 isClosed_Ici h1

/-- A supremum over a set of `ℂ × ℂ` of functions continuous on the set, each measurable in the
parameter `d`, is measurable in `d`. -/
theorem measurable_biSup_of_continuousOn {β : Type*} [MeasurableSpace β] (S : Set (ℂ × ℂ))
    {G : β → ℂ × ℂ → ℝ≥0∞} (hG : ∀ d, ContinuousOn (G d) S)
    (hGm : ∀ p, Measurable fun d => G d p) : Measurable fun d => ⨆ p ∈ S, G d p := by
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have h : (fun d => ⨆ p ∈ S, G d p) = fun d => ⨆ p ∈ T, G d p :=
    funext fun d => biSup_eq_biSup_of_subset_closure hTS hST (hG d)
  rw [h]
  exact Measurable.biSup T hTc fun p _ => hGm p

/-- The infimum version of `measurable_biSup_of_continuousOn`. -/
theorem measurable_biInf_of_continuousOn {β : Type*} [MeasurableSpace β] (S : Set (ℂ × ℂ))
    {G : β → ℂ × ℂ → ℝ≥0∞} (hG : ∀ d, ContinuousOn (G d) S)
    (hGm : ∀ p, Measurable fun d => G d p) : Measurable fun d => ⨅ p ∈ S, G d p := by
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have h : (fun d => ⨅ p ∈ S, G d p) = fun d => ⨅ p ∈ T, G d p :=
    funext fun d => biInf_eq_biInf_of_subset_closure hTS hST (hG d)
  rw [h]
  exact Measurable.biInf T hTc fun p _ => hGm p

/-! ## The three functionals as suprema/infima over sets of pairs -/

/-- `A(K)` as a supremum over the off-diagonal pairs of `K`. -/
theorem holderConst_eq_biSup_pairs (d : ℂ × ℂ → ℝ) (K : Set ℂ) :
    holderConst d K = ⨆ p ∈ {p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ≠ p.2},
      ENNReal.ofReal (d p / ‖p.1 - p.2‖ ^ (1 / 2 : ℝ)) := by
  unfold holderConst
  refine le_antisymm (iSup₂_le fun z hz => iSup₂_le fun w hw => iSup_le fun hzw => ?_)
    (iSup₂_le fun p hp => ?_)
  · exact le_iSup₂ (f := fun (p : ℂ × ℂ) (_ : p ∈ {p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ≠ p.2}) =>
      ENNReal.ofReal (d p / ‖p.1 - p.2‖ ^ (1 / 2 : ℝ))) (z, w) ⟨hz, hw, hzw⟩
  · exact le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2.1 (le_iSup_of_le hp.2.2 le_rfl))

/-- `I(K, δ)` as an infimum over the `δ`-separated pairs of `K`. -/
theorem sepInf_eq_biInf_pairs (d : ℂ × ℂ → ℝ) (K : Set ℂ) (δ : ℝ) :
    sepInf d K δ = ⨅ p ∈ {p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ ‖p.1 - p.2‖},
      ENNReal.ofReal (d p) := by
  unfold sepInf
  refine le_antisymm (le_iInf₂ fun p hp => ?_)
    (le_iInf₂ fun z hz => le_iInf₂ fun w hw => le_iInf fun hzw => ?_)
  · exact iInf₂_le_of_le p.1 hp.1 (iInf₂_le_of_le p.2 hp.2.1 (iInf_le_of_le hp.2.2 le_rfl))
  · exact iInf₂_le (f := fun (p : ℂ × ℂ)
      (_ : p ∈ {p : ℂ × ℂ | p.1 ∈ K ∧ p.2 ∈ K ∧ δ ≤ ‖p.1 - p.2‖}) => ENNReal.ofReal (d p))
      (z, w) ⟨hz, hw, hzw⟩

/-- `L_R` as an infimum over the pairs of the two circles. -/
theorem annulusCross_eq_biInf_pairs (d : ℂ × ℂ → ℝ) (R : ℝ) :
    annulusCross d R = ⨅ p ∈ {p : ℂ × ℂ | p.1 ∈ Metric.sphere (0 : ℂ) R ∧
      p.2 ∈ Metric.sphere (0 : ℂ) (2 * R)}, ENNReal.ofReal (d p) := by
  unfold annulusCross
  refine le_antisymm (le_iInf₂ fun p hp => ?_) (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  · exact iInf₂_le_of_le p.1 hp.1 (iInf₂_le_of_le p.2 hp.2 le_rfl)
  · exact iInf₂_le (f := fun (p : ℂ × ℂ) (_ : p ∈ {p : ℂ × ℂ | p.1 ∈ Metric.sphere (0 : ℂ) R ∧
      p.2 ∈ Metric.sphere (0 : ℂ) (2 * R)}) => ENNReal.ofReal (d p)) (x, y) ⟨hx, hy⟩

/-! ## Measurability on `C(ℂ × ℂ, ℝ)` -/

theorem measurable_ofReal_eval_div (p : ℂ × ℂ) (c : ℝ) :
    Measurable fun d : C(ℂ × ℂ, ℝ) => ENNReal.ofReal (d p / c) :=
  ENNReal.measurable_ofReal.comp ((ContinuousMap.measurable_eval p).div_const c)

theorem measurable_ofReal_eval (p : ℂ × ℂ) :
    Measurable fun d : C(ℂ × ℂ, ℝ) => ENNReal.ofReal (d p) :=
  ENNReal.measurable_ofReal.comp (ContinuousMap.measurable_eval p)

/-- `d ↦ A_d(K)` is measurable on `C(ℂ × ℂ, ℝ)`, for every set `K`. -/
theorem measurable_holderConst_cont (K : Set ℂ) :
    Measurable fun d : C(ℂ × ℂ, ℝ) => holderConst d K := by
  simp_rw [holderConst_eq_biSup_pairs]
  refine measurable_biSup_of_continuousOn _ (fun d => ?_)
    fun p => measurable_ofReal_eval_div p _
  refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.div d.continuous.continuousOn
    ?_ fun p hp => ?_)
  · exact (Continuous.continuousOn (by fun_prop)).rpow_const fun _ _ => Or.inr (by norm_num)
  · have : p.1 - p.2 ≠ 0 := sub_ne_zero.2 hp.2.2
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2 this) _).ne'

/-- `d ↦ I_d(K, δ)` is measurable on `C(ℂ × ℂ, ℝ)`. -/
theorem measurable_sepInf_cont (K : Set ℂ) (δ : ℝ) :
    Measurable fun d : C(ℂ × ℂ, ℝ) => sepInf d K δ := by
  simp_rw [sepInf_eq_biInf_pairs]
  exact measurable_biInf_of_continuousOn _
    (fun d => (ENNReal.continuous_ofReal.comp d.continuous).continuousOn) measurable_ofReal_eval

/-- `d ↦ L_R(d)` is measurable on `C(ℂ × ℂ, ℝ)`. -/
theorem measurable_annulusCross_cont (R : ℝ) :
    Measurable fun d : C(ℂ × ℂ, ℝ) => annulusCross d R := by
  simp_rw [annulusCross_eq_biInf_pairs]
  exact measurable_biInf_of_continuousOn _
    (fun d => (ENNReal.continuous_ofReal.comp d.continuous).continuousOn) measurable_ofReal_eval

/-! ## The random variables of a `Setup` -/

namespace Setup

variable (S : Setup)

theorem measurable_coe_D (γ : ℝ) : Measurable fun ω => (S.D γ ω).1 :=
  measurable_subtype_coe.comp (S.measurable_D γ)

theorem measurable_D_apply (γ : ℝ) (p : ℂ × ℂ) : Measurable fun ω => (S.D γ ω).1 p :=
  (ContinuousMap.measurable_eval p).comp (S.measurable_coe_D γ)

theorem measurable_log_D (γ : ℝ) (z w : ℂ) :
    Measurable fun ω => Real.log ((S.D γ ω).1 (z, w)) :=
  Real.measurable_log.comp (S.measurable_D_apply γ _)

/-- `A_γ(K)` is a random variable, for every set `K`. -/
theorem measurable_holderConst (γ : ℝ) (K : Set ℂ) :
    Measurable fun ω => holderConst (S.D γ ω).1 K :=
  (measurable_holderConst_cont K).comp (S.measurable_coe_D γ)

/-- `I_γ(K, δ)` is a random variable. -/
theorem measurable_sepInf (γ : ℝ) (K : Set ℂ) (δ : ℝ) :
    Measurable fun ω => sepInf (S.D γ ω).1 K δ :=
  (measurable_sepInf_cont K δ).comp (S.measurable_coe_D γ)

/-- The annulus crossing distance `L_R` of `D^γ` is a random variable. -/
theorem measurable_annulusCross (γ R : ℝ) :
    Measurable fun ω => annulusCross (S.D γ ω).1 R :=
  (measurable_annulusCross_cont R).comp (S.measurable_coe_D γ)

end Setup

end GaussianLQG
