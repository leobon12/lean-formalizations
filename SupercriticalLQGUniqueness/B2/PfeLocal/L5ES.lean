import SupercriticalLQGUniqueness.B2.PfeLocal.L5Compare
import LQGMetric.Papers.LM.T1_7V2

 






















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric.LM

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [MeasurableSpace E]

theorem l5_integrable_of_bound {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

theorem l5_memLp_of_bound {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) : MemLp g 2 μ :=
  MemLp.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

 
theorem l5_lintegral_disint (ν : Measure Ω) [IsFiniteMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) {H : (ι → E) × Ω → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (Y ω, ω) ∂ν = ∫⁻ y, ∫⁻ ω, H (y, ω) ∂(condDistrib id Y ν y) ∂(ν.map Y) := by
  rw [← Measure.lintegral_compProd hH,
    compProd_map_condDistrib hY.aemeasurable aemeasurable_id,
    lintegral_map hH (hY.prodMk measurable_id)]
  rfl

 
theorem l5_integral_disint (ν : Measure Ω) [IsFiniteMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) {H : (ι → E) × Ω → ℝ} (hH : Measurable H) {C : ℝ}
    (hC : ∀ p, |H p| ≤ C) :
    ∫ ω, H (Y ω, ω) ∂ν = ∫ y, ∫ ω, H (y, ω) ∂(condDistrib id Y ν y) ∂(ν.map Y) := by
  rw [← Measure.integral_compProd (l5_integrable_of_bound _ hH hC),
    compProd_map_condDistrib hY.aemeasurable aemeasurable_id,
    integral_map (hY.prodMk measurable_id).aemeasurable hH.aestronglyMeasurable]
  rfl

 
def l5CondMean (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Ω → ι → E) (f : Ω → ℝ) (y : ι → E) :
    ℝ :=
  ∫ ω, f ω ∂(condDistrib id Y ν y)

theorem measurable_l5CondMean (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Ω → ι → E) {f : Ω → ℝ}
    (hf : Measurable f) : Measurable (l5CondMean ν Y f) :=
  (hf.stronglyMeasurable.integral_kernel (κ := condDistrib id Y ν)).measurable

theorem l5CondMean_bound (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Ω → ι → E) {f : Ω → ℝ}
    {B : ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfB : ∀ ω, f ω ≤ B) (y : ι → E) :
    0 ≤ l5CondMean ν Y f y ∧ l5CondMean ν Y f y ≤ B := by
  refine ⟨integral_nonneg hf0, ?_⟩
  calc l5CondMean ν Y f y ≤ ∫ _, B ∂(condDistrib id Y ν y) :=
        integral_mono_of_nonneg (Eventually.of_forall hf0) (integrable_const B)
          (Eventually.of_forall hfB)
    _ = B := by simp

 
theorem l5_var_eq_posPart {α : Type} [MeasurableSpace α] (κ : Measure α) [IsProbabilityMeasure κ]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfB : ∀ ω, f ω ≤ B) :
    ∫ ω, (f ω - ∫ x, f x ∂κ) ^ 2 ∂κ = ∫ p, max (f p.2 - f p.1) 0 ^ 2 ∂(κ.prod κ) := by
  have hB : ∀ ω, |f ω| ≤ B := fun ω => by rw [abs_of_nonneg (hf0 ω)]; exact hfB ω
  have hfi : Integrable f κ := l5_integrable_of_bound κ hf hB
  have hf2 : Integrable (fun ω => f ω ^ 2) κ := l5_integrable_of_bound κ (hf.pow_const 2)
    (C := B ^ 2) fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hf0 ω) (hfB ω) 2
  set m := ∫ x, f x ∂κ
  set s := ∫ ω, f ω ^ 2 ∂κ
  
  have hL : ∫ ω, (f ω - m) ^ 2 ∂κ = s - m ^ 2 := by
    have : (fun ω => (f ω - m) ^ 2) = fun ω => f ω ^ 2 - 2 * m * f ω + m ^ 2 := by
      funext ω; ring
    have i1 : Integrable (fun ω => f ω ^ 2 - 2 * m * f ω) κ := hf2.sub (hfi.const_mul _)
    have i2 : Integrable (fun ω => 2 * m * f ω) κ := hfi.const_mul _
    rw [this, integral_add i1 (integrable_const _), integral_sub hf2 i2, integral_const_mul,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, s, m]
    ring
  
  have hm1 : Measurable fun p : α × α => f p.1 := hf.comp measurable_fst
  have hm2 : Measurable fun p : α × α => f p.2 := hf.comp measurable_snd
  have hbd : ∀ (g : α × α → ℝ), Measurable g → (∀ p, |g p| ≤ 4 * B ^ 2) →
      Integrable g (κ.prod κ) := fun g hg hC => l5_integrable_of_bound _ hg hC
  have hdiff : ∀ p : α × α, |f p.2 - f p.1| ≤ B := fun p => by
    rw [abs_le]; constructor <;> linarith [hf0 p.1, hf0 p.2, hfB p.1, hfB p.2]
  have hsqb : ∀ x : ℝ, |x| ≤ B → |max x 0 ^ 2| ≤ 4 * B ^ 2 := fun x hx => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 : max x 0 ≤ B := max_le (le_of_abs_le hx) hB0
    have h2 : 0 ≤ max x 0 := le_max_right _ _
    nlinarith
  have hpos : Measurable fun p : α × α => max (f p.2 - f p.1) 0 ^ 2 :=
    ((hm2.sub hm1).max measurable_const).pow_const 2
  have hneg : Measurable fun p : α × α => max (f p.1 - f p.2) 0 ^ 2 :=
    ((hm1.sub hm2).max measurable_const).pow_const 2
  have hipos := hbd _ hpos fun p => hsqb _ (hdiff p)
  have hineg := hbd _ hneg fun p => hsqb _ (by rw [abs_sub_comm]; exact hdiff p)
  have hswap : ∫ p, max (f p.1 - f p.2) 0 ^ 2 ∂(κ.prod κ) =
      ∫ p, max (f p.2 - f p.1) 0 ^ 2 ∂(κ.prod κ) := by
    have := integral_prod_swap (μ := κ) (ν := κ) (fun p : α × α => max (f p.2 - f p.1) 0 ^ 2)
    simpa only [Prod.fst_swap, Prod.snd_swap] using this
  have hsplit : ∀ x : ℝ, x ^ 2 = max x 0 ^ 2 + max (-x) 0 ^ 2 := fun x => by
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hsq : ∫ p, (f p.2 - f p.1) ^ 2 ∂(κ.prod κ) = 2 * (s - m ^ 2) := by
    have e : (fun p : α × α => (f p.2 - f p.1) ^ 2) =
        fun p => f p.2 ^ 2 + f p.1 ^ 2 - 2 * (f p.1 * f p.2) := by funext p; ring
    have i1 : Integrable (fun p : α × α => f p.2 ^ 2) (κ.prod κ) :=
      hf2.comp_snd (μ := κ)
    have i2 : Integrable (fun p : α × α => f p.1 ^ 2) (κ.prod κ) :=
      hf2.comp_fst (ν := κ)
    have i3 : Integrable (fun p : α × α => f p.1 * f p.2) (κ.prod κ) :=
      hfi.mul_prod hfi
    have i12 : Integrable (fun p : α × α => f p.2 ^ 2 + f p.1 ^ 2) (κ.prod κ) := i1.add i2
    have i3' : Integrable (fun p : α × α => 2 * (f p.1 * f p.2)) (κ.prod κ) := i3.const_mul 2
    rw [e, integral_sub i12 i3', integral_add i1 i2, integral_const_mul,
      integral_prod_mul (μ := κ) (ν := κ) f f]
    have j1 : ∫ p : α × α, f p.2 ^ 2 ∂(κ.prod κ) = s := by
      rw [integral_prod _ i1]; simp [s]
    have j2 : ∫ p : α × α, f p.1 ^ 2 ∂(κ.prod κ) = s := by
      rw [integral_prod _ i2]; simp [s]
    rw [j1, j2]
    ring
  have hsum : ∫ p, (f p.2 - f p.1) ^ 2 ∂(κ.prod κ) =
      ∫ p, max (f p.2 - f p.1) 0 ^ 2 ∂(κ.prod κ) +
        ∫ p, max (f p.1 - f p.2) 0 ^ 2 ∂(κ.prod κ) := by
    rw [← integral_add hipos hineg]
    congr 1
    funext p
    rw [hsplit (f p.2 - f p.1), neg_sub]
  rw [hL]
  linarith [hsq, hsum, hswap]

 
theorem l5_sq_integral_le {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h := variance_nonneg g μ
  rw [variance_eq_sub (l5_memLp_of_bound μ hg hC)] at h
  have : μ[g ^ 2] = ∫ x, g x ^ 2 ∂μ := rfl
  linarith

 
theorem l5_condMean_diff_le (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Ω → ι → E) {f : Ω → ℝ}
    (hf : Measurable f) {B : ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hfB : ∀ ω, f ω ≤ B) (y y' : ι → E) :
    ENNReal.ofReal (max (l5CondMean ν Y f y' - l5CondMean ν Y f y) 0 ^ 2) ≤
      ∫⁻ a, ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2) ∂(condDistrib id Y ν y')
        ∂(condDistrib id Y ν y) := by
  set κ := condDistrib id Y ν y
  set κ' := condDistrib id Y ν y'
  have hB : ∀ ω, |f ω| ≤ B := fun ω => by rw [abs_of_nonneg (hf0 ω)]; exact hfB ω
  have hB0 : 0 ≤ B := (hf0 (Classical.arbitrary _)).trans (hfB _)
  set g : Ω × Ω → ℝ := fun p => max (f p.2 - f p.1) 0
  have hgm : Measurable g := ((hf.comp measurable_snd).sub (hf.comp measurable_fst)).max
    measurable_const
  have hgb : ∀ p, |g p| ≤ B := fun p => by
    simp only [g]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [hf0 p.1, hfB p.2]) hB0
  have hgi : Integrable g (κ.prod κ') := l5_integrable_of_bound _ hgm hgb
  have hdi : Integrable (fun p : Ω × Ω => f p.2 - f p.1) (κ.prod κ') :=
    l5_integrable_of_bound _ ((hf.comp measurable_snd).sub (hf.comp measurable_fst))
      (C := B) fun p => by rw [abs_le]; constructor <;> linarith [hf0 p.1, hf0 p.2, hfB p.1, hfB p.2]
  have hmean : l5CondMean ν Y f y' - l5CondMean ν Y f y =
      ∫ p, (f p.2 - f p.1) ∂(κ.prod κ') := by
    rw [integral_sub ((l5_integrable_of_bound κ' hf hB).comp_snd (μ := κ))
      ((l5_integrable_of_bound κ hf hB).comp_fst (ν := κ')),
      integral_prod _ ((l5_integrable_of_bound κ' hf hB).comp_snd (μ := κ)),
      integral_prod _ ((l5_integrable_of_bound κ hf hB).comp_fst (ν := κ'))]
    simp [l5CondMean, κ, κ']
  have hle1 : max (l5CondMean ν Y f y' - l5CondMean ν Y f y) 0 ≤ ∫ p, g p ∂(κ.prod κ') := by
    rw [hmean]
    exact max_le (integral_mono hdi hgi fun p => le_max_left _ _)
      (integral_nonneg fun p => le_max_right _ _)
  have hle2 : (∫ p, g p ∂(κ.prod κ')) ^ 2 ≤ ∫ p, g p ^ 2 ∂(κ.prod κ') :=
    l5_sq_integral_le _ hgm hgb
  have hsq : max (l5CondMean ν Y f y' - l5CondMean ν Y f y) 0 ^ 2 ≤
      ∫ p, g p ^ 2 ∂(κ.prod κ') :=
    (pow_le_pow_left₀ (le_max_right _ _) hle1 2).trans hle2
  have hg2m : Measurable fun p => g p ^ 2 := hgm.pow_const 2
  have hg2b : ∀ p, |g p ^ 2| ≤ B ^ 2 := fun p => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 := hgb p
    rw [abs_of_nonneg (le_max_right _ _)] at h1
    exact pow_le_pow_left₀ (le_max_right _ _) h1 2
  refine (ENNReal.ofReal_le_ofReal hsq).trans_eq ?_
  rw [ofReal_integral_eq_lintegral_ofReal (l5_integrable_of_bound _ hg2m hg2b)
    (Eventually.of_forall fun p => sq_nonneg _),
    lintegral_prod (fun p => ENNReal.ofReal (g p ^ 2))
      (ENNReal.measurable_ofReal.comp hg2m).aemeasurable]

 
theorem l5_var_split (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfB : ∀ ω, f ω ≤ B) :
    variance f ν = ∫ ω, (f ω - l5CondMean ν Y f (Y ω)) ^ 2 ∂ν +
      variance (fun ω => l5CondMean ν Y f (Y ω)) ν := by
  set Φ := l5CondMean ν Y f
  have hΦ : Measurable Φ := measurable_l5CondMean ν Y hf
  have hΦY : Measurable fun ω => Φ (Y ω) := hΦ.comp hY
  have hΦb := l5CondMean_bound ν Y hf0 hfB
  set m := ∫ ω, f ω ∂ν
  have hfb : ∀ ω, |f ω| ≤ B := fun ω => by rw [abs_of_nonneg (hf0 ω)]; exact hfB ω
  have hΦab : ∀ y, |Φ y| ≤ B := fun y => by rw [abs_of_nonneg (hΦb y).1]; exact (hΦb y).2
  have hmean : ∫ ω, Φ (Y ω) ∂ν = m := by
    have h1 : m = ∫ y, Φ y ∂(ν.map Y) :=
      l5_integral_disint ν hY (H := fun p : (ι → E) × Ω => f p.2) (hf.comp measurable_snd)
        (C := B) fun p => hfb p.2
    rw [h1, integral_map hY.aemeasurable hΦ.aestronglyMeasurable]
  have hm0 : 0 ≤ m := integral_nonneg hf0
  have hmB : m ≤ B := by
    calc m ≤ ∫ _, B ∂ν := integral_mono_of_nonneg (Eventually.of_forall hf0)
          (integrable_const B) (Eventually.of_forall hfB)
      _ = B := by simp
  
  have hcross : ∫ ω, (f ω - Φ (Y ω)) * (Φ (Y ω) - m) ∂ν = 0 := by
    have hH : Measurable fun p : (ι → E) × Ω => (f p.2 - Φ p.1) * (Φ p.1 - m) :=
      ((hf.comp measurable_snd).sub (hΦ.comp measurable_fst)).mul
        ((hΦ.comp measurable_fst).sub measurable_const)
    rw [l5_integral_disint ν hY (H := fun p : (ι → E) × Ω => (f p.2 - Φ p.1) * (Φ p.1 - m)) hH
      (C := B * B) fun p => by
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) hB0 <;> rw [abs_le] <;> constructor <;>
          linarith [hf0 p.2, hfB p.2, (hΦb p.1).1, (hΦb p.1).2]]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    show ∫ ω, (f ω - Φ y) * (Φ y - m) ∂(condDistrib id Y ν y) = 0
    rw [integral_mul_const, integral_sub (l5_integrable_of_bound _ hf hfb) (integrable_const _),
      integral_const, probReal_univ, one_smul]
    simp [Φ, l5CondMean]
  have hmA : Measurable fun ω => (f ω - Φ (Y ω)) ^ 2 := (hf.sub hΦY).pow_const 2
  have hmC : Measurable fun ω => (f ω - Φ (Y ω)) * (Φ (Y ω) - m) :=
    (hf.sub hΦY).mul (hΦY.sub measurable_const)
  have hmD : Measurable fun ω => (Φ (Y ω) - m) ^ 2 := (hΦY.sub measurable_const).pow_const 2
  have iA : Integrable (fun ω => (f ω - Φ (Y ω)) ^ 2) ν :=
    l5_integrable_of_bound ν hmA (C := (2 * B) ^ 2) fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have : |f ω - Φ (Y ω)| ≤ 2 * B := by
        rw [abs_le]; constructor <;> linarith [hf0 ω, hfB ω, (hΦb (Y ω)).1, (hΦb (Y ω)).2]
      calc (f ω - Φ (Y ω)) ^ 2 = |f ω - Φ (Y ω)| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have iC : Integrable (fun ω => 2 * ((f ω - Φ (Y ω)) * (Φ (Y ω) - m))) ν :=
    (l5_integrable_of_bound ν hmC (C := B * B)
      fun ω => by
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) hB0 <;> rw [abs_le] <;> constructor <;>
          linarith [hf0 ω, hfB ω, (hΦb (Y ω)).1, (hΦb (Y ω)).2]).const_mul 2
  have iD : Integrable (fun ω => (Φ (Y ω) - m) ^ 2) ν :=
    l5_integrable_of_bound ν hmD (C := B ^ 2) fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have : |Φ (Y ω) - m| ≤ B := by
        rw [abs_le]; constructor <;> linarith [(hΦb (Y ω)).1, (hΦb (Y ω)).2]
      calc (Φ (Y ω) - m) ^ 2 = |Φ (Y ω) - m| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [variance_eq_integral hf.aemeasurable, variance_eq_integral hΦY.aemeasurable, hmean]
  have e : (fun ω => (f ω - m) ^ 2) = fun ω => (f ω - Φ (Y ω)) ^ 2 +
      2 * ((f ω - Φ (Y ω)) * (Φ (Y ω) - m)) + (Φ (Y ω) - m) ^ 2 := by
    funext ω; ring
  have iAC : Integrable (fun ω => (f ω - Φ (Y ω)) ^ 2 +
      2 * ((f ω - Φ (Y ω)) * (Φ (Y ω) - m))) ν := iA.add iC
  rw [e, integral_add iAC iD, integral_add iA iC, integral_const_mul, hcross, mul_zero, add_zero]

 
theorem l5_termA (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ι → E} (hY : Measurable Y)
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfB : ∀ ω, f ω ≤ B) :
    ENNReal.ofReal (∫ ω, (f ω - l5CondMean ν Y f (Y ω)) ^ 2 ∂ν) =
      ∫⁻ a, ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2) ∂(condDistrib id Y ν (Y a)) ∂ν := by
  set κ := condDistrib id Y ν
  set Φ := l5CondMean ν Y f
  have hΦ : Measurable Φ := measurable_l5CondMean ν Y hf
  have hΦb := l5CondMean_bound ν Y hf0 hfB
  have hfb : ∀ ω, |f ω| ≤ B := fun ω => by rw [abs_of_nonneg (hf0 ω)]; exact hfB ω
  have hsqb : ∀ ω y, |(f ω - Φ y) ^ 2| ≤ (2 * B) ^ 2 := fun ω y => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have : |f ω - Φ y| ≤ 2 * B := by
      rw [abs_le]; constructor <;> linarith [hf0 ω, hfB ω, (hΦb y).1, (hΦb y).2]
    calc (f ω - Φ y) ^ 2 = |f ω - Φ y| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hH : Measurable fun p : (ι → E) × Ω => ENNReal.ofReal ((f p.2 - Φ p.1) ^ 2) :=
    ENNReal.measurable_ofReal.comp (((hf.comp measurable_snd).sub
      (hΦ.comp measurable_fst)).pow_const 2)
  have hmA : Measurable fun ω => (f ω - Φ (Y ω)) ^ 2 := (hf.sub (hΦ.comp hY)).pow_const 2
  rw [ofReal_integral_eq_lintegral_ofReal
      (l5_integrable_of_bound ν hmA fun ω => hsqb ω (Y ω))
      (Eventually.of_forall fun ω => sq_nonneg _),
    l5_lintegral_disint ν hY (H := fun p : (ι → E) × Ω => ENNReal.ofReal ((f p.2 - Φ p.1) ^ 2)) hH]
  have hG : Measurable fun p : (ι → E) × Ω =>
      ∫⁻ b, ENNReal.ofReal (max (f b - f p.2) 0 ^ 2) ∂(κ p.1) := by
    have := Measurable.lintegral_kernel_prod_right' (κ := κ.comap Prod.fst measurable_fst)
      (f := fun q : ((ι → E) × Ω) × Ω => ENNReal.ofReal (max (f q.2 - f q.1.2) 0 ^ 2))
      (ENNReal.measurable_ofReal.comp ((((hf.comp measurable_snd).sub
        (hf.comp (measurable_snd.comp measurable_fst))).max measurable_const).pow_const 2))
    simpa only [Kernel.comap_apply] using this
  rw [l5_lintegral_disint ν hY
    (H := fun p : (ι → E) × Ω => ∫⁻ b, ENNReal.ofReal (max (f b - f p.2) 0 ^ 2) ∂(κ p.1)) hG]
  refine lintegral_congr fun y => ?_
  have hmy : Measurable fun ω => (f ω - Φ y) ^ 2 := (hf.sub measurable_const).pow_const 2
  rw [← ofReal_integral_eq_lintegral_ofReal
      (l5_integrable_of_bound (κ y) hmy fun ω => hsqb ω y)
      (Eventually.of_forall fun ω => sq_nonneg _)]
  have hv := l5_var_eq_posPart (κ y) hf hB0 hf0 hfB
  have hΦy : Φ y = ∫ x, f x ∂(κ y) := rfl
  rw [hΦy, hv]
  have hgm : Measurable fun p : Ω × Ω => max (f p.2 - f p.1) 0 ^ 2 :=
    (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).max measurable_const).pow_const 2
  rw [ofReal_integral_eq_lintegral_ofReal (l5_integrable_of_bound _ hgm (C := (2 * B) ^ 2)
      fun p => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h1 : max (f p.2 - f p.1) 0 ≤ 2 * B := max_le (by linarith [hf0 p.1, hfB p.2])
          (by linarith)
        exact pow_le_pow_left₀ (le_max_right _ _) h1 2)
      (Eventually.of_forall fun p => sq_nonneg _),
    lintegral_prod (fun p : Ω × Ω => ENNReal.ofReal (max (f p.2 - f p.1) 0 ^ 2))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable]

 
theorem l5_termB (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ι → E} (hY : Measurable Y)
    (hprod : ν.map Y = Measure.pi fun j => ν.map fun ω => Y ω j)
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfB : ∀ ω, f ω ≤ B) :
    ENNReal.ofReal (variance (fun ω => l5CondMean ν Y f (Y ω)) ν) ≤
      ∫⁻ a, ∑ i, ∫⁻ ω', ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2)
        ∂(condDistrib id Y ν (Function.update (Y a) i (Y ω' i))) ∂ν ∂ν := by
  set κ := condDistrib id Y ν
  set Φ := l5CondMean ν Y f
  have hΦ : Measurable Φ := measurable_l5CondMean ν Y hf
  have hΦb := l5CondMean_bound ν Y hf0 hfB
  have hΦab : ∀ y, |Φ y| ≤ B := fun y => by rw [abs_of_nonneg (hΦb y).1]; exact (hΦb y).2
  have hes := t17v_es ν hY hprod (F := fun ω => Φ (Y ω)) (Φ := Φ) hΦ (hΦ.comp hY)
    EventuallyEq.rfl (l5_memLp_of_bound ν (hΦ.comp hY) fun ω => hΦab (Y ω))
  rw [variance_eq_integral (show AEMeasurable (fun ω => Φ (Y ω)) ν from
    (hΦ.comp hY).aemeasurable)]
  refine hes.trans ?_
  set h : Ω × Ω → ℝ≥0∞ := fun q => ENNReal.ofReal (max (f q.2 - f q.1) 0 ^ 2)
  have hhm : Measurable h := ENNReal.measurable_ofReal.comp ((((hf.comp measurable_snd).sub
    (hf.comp measurable_fst)).max measurable_const).pow_const 2)
  
  set G : ι → (ι → E) × Ω × Ω → ℝ≥0∞ := fun i q =>
    ∫⁻ b, h (q.2.1, b) ∂(κ (Function.update q.1 i (Y q.2.2 i)))
  have hupd : ∀ i, Measurable fun q : (ι → E) × Ω × Ω => Function.update q.1 i (Y q.2.2 i) :=
    fun i => (t17v_measurable_update i).comp (measurable_fst.prodMk
      (hY.comp (measurable_snd.comp measurable_snd)))
  have hG : ∀ i, Measurable (G i) := fun i => by
    have := Measurable.lintegral_kernel_prod_right' (κ := κ.comap _ (hupd i))
      (f := fun r : ((ι → E) × Ω × Ω) × Ω => h (r.1.2.1, r.2))
      (hhm.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
    simpa only [Kernel.comap_apply] using this
  set H : (ι → E) × Ω → ℝ≥0∞ := fun p => ∑ i, ∫⁻ ω', G i (p.1, p.2, ω') ∂ν
  have hH : Measurable H := Finset.measurable_sum _ fun i _ => by
    have hm : Measurable fun q : ((ι → E) × Ω) × Ω => G i (q.1.1, q.1.2, q.2) :=
      (hG i).comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact hm.lintegral_prod_right'
  have hK : Measurable fun y => ∫⁻ a, H (y, a) ∂(κ y) :=
    Measurable.lintegral_kernel_prod_right' (κ := κ) hH
  calc ∫⁻ d, ∑ i, ∫⁻ d', ENNReal.ofReal
        (max (Φ (Function.update (Y d) i (Y d' i)) - Φ (Y d)) 0 ^ 2) ∂ν ∂ν
      ≤ ∫⁻ d, ∑ i, ∫⁻ d', ∫⁻ a, G i (Y d, a, d') ∂(κ (Y d)) ∂ν ∂ν := by
        refine lintegral_mono fun d => Finset.sum_le_sum fun i _ => lintegral_mono fun d' => ?_
        exact l5_condMean_diff_le ν Y hf hf0 hfB (Y d) (Function.update (Y d) i (Y d' i))
    _ = ∫⁻ d, ∫⁻ a, H (Y d, a) ∂(κ (Y d)) ∂ν := by
        refine lintegral_congr fun d => ?_
        simp only [H]
        rw [lintegral_finset_sum _ fun i _ => Measurable.lintegral_prod_right' (ν := ν)
          (f := fun q : Ω × Ω => G i (Y d, q.1, q.2))
          ((hG i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact lintegral_lintegral_swap (f := fun x y => G i (Y d, y, x))
          ((hG i).comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))).aemeasurable
    _ = ∫⁻ y, ∫⁻ a, H (y, a) ∂(κ y) ∂(ν.map Y) := (lintegral_map hK hY).symm
    _ = ∫⁻ a, H (Y a, a) ∂ν := (l5_lintegral_disint ν hY hH).symm

 
theorem l5_es_kernel (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) (hprod : ν.map Y = Measure.pi fun j => ν.map fun ω => Y ω j)
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfB : ∀ ω, f ω ≤ B) :
    ENNReal.ofReal (variance f ν) ≤
      ∫⁻ a, ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2) ∂(condDistrib id Y ν (Y a)) ∂ν +
      ∫⁻ a, ∑ i, ∫⁻ ω', ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2)
        ∂(condDistrib id Y ν (Function.update (Y a) i (Y ω' i))) ∂ν ∂ν := by
  rw [l5_var_split ν hY hf hB0 hf0 hfB,
    ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _) (variance_nonneg _ _),
    l5_termA ν hY hf hB0 hf0 hfB]
  exact add_le_add le_rfl (l5_termB ν hY hprod hf hB0 hf0 hfB)

 

theorem l5_condDistrib_support (ν : Measure Ω) [IsFiniteMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) (hdiag : MeasurableSet {p : (ι → E) × Ω | Y p.2 = p.1})
    {G : Set Ω} (hG : ∀ᵐ ω ∂ν, ω ∈ G) :
    ∀ᵐ y ∂(ν.map Y), ∀ᵐ b ∂(condDistrib id Y ν y), Y b = y ∧ b ∈ G := by
  set G' := (toMeasurable ν Gᶜ)ᶜ
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable _ _).compl
  have hG'G : G' ⊆ G := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable ν Gᶜ h)
  have hG' : ∀ᵐ ω ∂ν, ω ∈ G' := by
    rw [ae_iff]
    show ν G'ᶜ = 0
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hG
  set S := {p : (ι → E) × Ω | Y p.2 = p.1 ∧ p.2 ∈ G'}
  have hS : MeasurableSet S := hdiag.inter (measurable_snd hG'm)
  have hae : ∀ᵐ p ∂((ν.map Y) ⊗ₘ condDistrib id Y ν), p ∈ S := by
    rw [compProd_map_condDistrib hY.aemeasurable aemeasurable_id,
      ae_map_iff (p := fun q => q ∈ S) (hY.prodMk measurable_id).aemeasurable hS]
    filter_upwards [hG'] with ω hω
    exact ⟨rfl, hω⟩
  filter_upwards [(Measure.ae_compProd_iff hS).1 hae] with y hy
  filter_upwards [hy] with b hb
  exact ⟨hb.1, hG'G hb.2⟩

theorem l5_support_A (ν : Measure Ω) [IsFiniteMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) (hdiag : MeasurableSet {p : (ι → E) × Ω | Y p.2 = p.1})
    {G : Set Ω} (hG : ∀ᵐ ω ∂ν, ω ∈ G) :
    ∀ᵐ a ∂ν, ∀ᵐ b ∂(condDistrib id Y ν (Y a)), Y b = Y a ∧ b ∈ G :=
  ae_of_ae_map hY.aemeasurable (l5_condDistrib_support ν hY hdiag hG)

theorem l5_support_B (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) (hprod : ν.map Y = Measure.pi fun j => ν.map fun ω => Y ω j)
    (hdiag : MeasurableSet {p : (ι → E) × Ω | Y p.2 = p.1})
    {G : Set Ω} (hG : ∀ᵐ ω ∂ν, ω ∈ G) :
    ∀ᵐ a ∂ν, ∀ i, ∀ᵐ ω' ∂ν, ∀ᵐ b ∂(condDistrib id Y ν (Function.update (Y a) i (Y ω' i))),
      Y b = Function.update (Y a) i (Y ω' i) ∧ b ∈ G := by
  have hsupp := l5_condDistrib_support ν hY hdiag hG
  refine ae_all_iff.2 fun i => ?_
  set μ : ι → Measure E := fun j => ν.map fun d => Y d j with hμ
  have : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    (Measure.isProbabilityMeasure_map_iff ((measurable_pi_apply j).comp hY).aemeasurable).2
      inferInstance
  set yS : Ω × Ω → ι → E := fun p => Function.update (Y p.1) i (Y p.2 i)
  have hyS : Measurable yS := (t17v_measurable_update i).comp (hY.prodMap hY)
  have hlaw : (ν.prod ν).map yS = ν.map Y := by
    have : yS = (fun q : (ι → E) × (ι → E) => Function.update q.1 i (q.2 i)) ∘ Prod.map Y Y :=
      rfl
    rw [this, ← Measure.map_map (t17v_measurable_update i) (hY.prodMap hY),
      ← Measure.map_prod_map _ _ hY hY, hprod, t17v_update_law μ i]
  have h1 : ∀ᵐ p ∂(ν.prod ν), ∀ᵐ b ∂(condDistrib id Y ν (yS p)), Y b = yS p ∧ b ∈ G :=
    ae_of_ae_map hyS.aemeasurable (by rw [hlaw]; exact hsupp)
  exact Measure.ae_ae_of_ae_prod h1

 

theorem l5_es_bound (ν : Measure Ω) [IsProbabilityMeasure ν] {Y : Ω → ι → E}
    (hY : Measurable Y) (hprod : ν.map Y = Measure.pi fun j => ν.map fun ω => Y ω j)
    (hdiag : MeasurableSet {p : (ι → E) × Ω | Y p.2 = p.1})
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfB : ∀ ω, f ω ≤ B) {G : Set Ω} (hG : ∀ᵐ ω ∂ν, ω ∈ G)
    (c₀ : Ω → ℝ≥0∞) (c : ι → Ω → ℝ≥0∞)
    (h₀ : ∀ a ∈ G, ∀ b ∈ G, Y b = Y a → ENNReal.ofReal (max (f b - f a) 0 ^ 2) ≤ c₀ a)
    (h₁ : ∀ a ∈ G, ∀ i, ∀ b ∈ G, (∀ j, j ≠ i → Y b j = Y a j) →
      ENNReal.ofReal (max (f b - f a) 0 ^ 2) ≤ c i a) :
    ENNReal.ofReal (variance f ν) ≤ ∫⁻ a, (c₀ a + ∑ i, c i a) ∂ν := by
  refine (l5_es_kernel ν hY hprod hf hB0 hf0 hfB).trans ?_
  refine le_trans (add_le_add ?_ ?_) (le_lintegral_add c₀ fun a => ∑ i, c i a)
  · refine lintegral_mono_ae ?_
    filter_upwards [hG, l5_support_A ν hY hdiag hG] with a ha hsa
    calc ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2) ∂(condDistrib id Y ν (Y a))
        ≤ ∫⁻ _, c₀ a ∂(condDistrib id Y ν (Y a)) :=
          lintegral_mono_ae (hsa.mono fun b hb => h₀ a ha b hb.2 hb.1)
      _ = c₀ a := by rw [lintegral_const, measure_univ, mul_one]
  · refine lintegral_mono_ae ?_
    filter_upwards [hG, l5_support_B ν hY hprod hdiag hG] with a ha hsb
    refine Finset.sum_le_sum fun i _ => ?_
    calc ∫⁻ ω', ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2)
          ∂(condDistrib id Y ν (Function.update (Y a) i (Y ω' i))) ∂ν
        ≤ ∫⁻ _, c i a ∂ν := by
          refine lintegral_mono_ae ((hsb i).mono fun ω' hω' => ?_)
          calc ∫⁻ b, ENNReal.ofReal (max (f b - f a) 0 ^ 2)
                ∂(condDistrib id Y ν (Function.update (Y a) i (Y ω' i)))
              ≤ ∫⁻ _, c i a ∂(condDistrib id Y ν (Function.update (Y a) i (Y ω' i))) :=
                lintegral_mono_ae (hω'.mono fun b hb => h₁ a ha i b hb.2 fun j hj => by
                  rw [hb.1, Function.update_of_ne hj])
            _ = c i a := by rw [lintegral_const, measure_univ, mul_one]
      _ = c i a := by rw [lintegral_const, measure_univ, mul_one]

end SupercriticalLQGUniqueness.B2.PfeLocal
