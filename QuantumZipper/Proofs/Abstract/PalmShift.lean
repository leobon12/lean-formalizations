import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Blueprint A6: the Palm-shift lemma

A random measure on `ℝ` is an s-finite kernel `ν : Kernel Ω ℝ` (a Giry-measurable family
`ω ↦ ν ω`). For `I = [a, b]` the size-biased (Palm) law is
`𝐏_I(dω, dx) = ν_ω|_I(dx) P(dω) / E ν(I)`, here `palmLaw P ν a b`.
The shifted point is `x_ℓ := inf {y ≤ x : ν[y, x] ≤ ℓ}` (`palmShiftLeft`), and its mirror
`x^ℓ := sup {y ≥ x : ν[x, y] ≤ ℓ}` (`palmShiftRight`).

Main results: `palm_shift_left_bound` and `palm_shift_right_bound`:
`|E_{𝐏_I} G(ω, x_ℓ) − E_{𝐏_I} G(ω, x)| ≤ 2 ℓ M / E ν(I)` for `|G| ≤ M` measurable,
if a.s. `ν` is atomless, positive on intervals and `ν(−∞, a] ≥ ℓ` (resp. `ν[b, ∞) ≥ ℓ`).

Proof: for a fixed good `ω`, the map `x ↦ x_ℓ` pushes `ν|_(a,b]` to a measure which agrees
with `ν` on `(a, τ]`, `τ = b_ℓ`, puts mass `≤ ℓ` on `(−∞, a]` and none on `(τ, ∞)`, while
`ν((τ, b]) ≤ ℓ`.
-/

namespace QuantumZipper.PalmShift

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-- `x_ℓ := inf {y ≤ x : μ[y, x] ≤ ℓ}`. -/
noncomputable def palmShiftLeft (μ : Measure ℝ) (ℓ : ℝ≥0) (x : ℝ) : ℝ :=
  sInf {y | y ≤ x ∧ μ (Icc y x) ≤ ℓ}

/-- Mirror: `x^ℓ := sup {y ≥ x : μ[x, y] ≤ ℓ}`. -/
noncomputable def palmShiftRight (μ : Measure ℝ) (ℓ : ℝ≥0) (x : ℝ) : ℝ :=
  sSup {y | x ≤ y ∧ μ (Icc x y) ≤ ℓ}

/-! ### Deterministic part -/

section Det

variable {μ : Measure ℝ}

lemma ps_Ioc_le {c x : ℝ} {L : ℝ≥0∞} (h : ∀ y, c < y → y ≤ x → μ (Icc y x) ≤ L) :
    μ (Ioc c x) ≤ L := by
  have hU : Ioc c x = ⋃ n : ℕ, Icc (c + 1 / ((n : ℝ) + 1)) x := by
    ext y; simp only [mem_Ioc, mem_iUnion, mem_Icc]; constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h1)
      exact ⟨n, by linarith, h2⟩
    · rintro ⟨n, h1, h2⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith, h2⟩
  have hmono : Monotone fun n : ℕ => Icc (c + 1 / ((n : ℝ) + 1)) x := by
    intro n m hnm; apply Icc_subset_Icc_left
    have := Nat.one_div_le_one_div (α := ℝ) hnm
    linarith
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  by_cases hn : c + 1 / ((n : ℝ) + 1) ≤ x
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact h _ (by linarith) hn
  · rw [Icc_eq_empty hn, measure_empty]; exact zero_le

lemma ps_Ico_le {c s : ℝ} {L : ℝ≥0∞} (h : ∀ y, c ≤ y → y < s → μ (Icc c y) ≤ L) :
    μ (Ico c s) ≤ L := by
  have hU : Ico c s = ⋃ n : ℕ, Icc c (s - 1 / ((n : ℝ) + 1)) := by
    ext y; simp only [mem_Ico, mem_iUnion, mem_Icc]; constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h2)
      exact ⟨n, h1, by linarith⟩
    · rintro ⟨n, h1, h2⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨h1, by linarith⟩
  have hmono : Monotone fun n : ℕ => Icc c (s - 1 / ((n : ℝ) + 1)) := by
    intro n m hnm; apply Icc_subset_Icc_right
    have := Nat.one_div_le_one_div (α := ℝ) hnm
    linarith
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  by_cases hn : c ≤ s - 1 / ((n : ℝ) + 1)
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact h _ hn (by linarith)
  · rw [Icc_eq_empty hn, measure_empty]; exact zero_le

lemma ps_le_Icc_right {c s b : ℝ} {L : ℝ≥0∞} (hsb : s < b) (hfin : μ (Icc c b) ≠ ∞)
    (h : ∀ y, s < y → y ≤ b → L < μ (Icc c y)) : L ≤ μ (Icc c s) := by
  have hI : Icc c s = ⋂ n : ℕ, Icc c (min b (s + 1 / ((n : ℝ) + 1))) := by
    ext y; simp only [mem_Icc, mem_iInter, le_min_iff]; constructor
    · rintro ⟨h1, h2⟩ n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨h1, by linarith, by linarith⟩
    · intro hy
      refine ⟨(hy 0).1, ?_⟩
      by_contra hys
      push Not at hys
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hys)
      have := (hy n).2.2
      linarith
  have hanti : Antitone fun n : ℕ => Icc c (min b (s + 1 / ((n : ℝ) + 1))) := by
    intro n m hnm; apply Icc_subset_Icc_right
    have := Nat.one_div_le_one_div (α := ℝ) hnm
    exact min_le_min le_rfl (by linarith)
  rw [hI, hanti.measure_iInter (fun _ => measurableSet_Icc.nullMeasurableSet)
    ⟨0, ne_top_of_le_ne_top hfin (measure_mono (Icc_subset_Icc_right (min_le_left _ _)))⟩]
  refine le_iInf fun n => (h _ ?_ (min_le_left _ _)).le
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact lt_min hsb (by linarith)

lemma ps_le_Icc_left {a t b : ℝ} {L : ℝ≥0∞} (hat : a < t) (hfin : μ (Icc a b) ≠ ∞)
    (h : ∀ y, a < y → y < t → L < μ (Icc y b)) : L ≤ μ (Icc t b) := by
  have hI : Icc t b = ⋂ n : ℕ, Icc (max ((a + t) / 2) (t - 1 / ((n : ℝ) + 1))) b := by
    ext y; simp only [mem_Icc, mem_iInter, max_le_iff]; constructor
    · rintro ⟨h1, h2⟩ n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨⟨by linarith, by linarith⟩, h2⟩
    · intro hy
      refine ⟨?_, (hy 0).2⟩
      by_contra hyt
      push Not at hyt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hyt)
      have := (hy n).1.2
      linarith
  have hanti : Antitone fun n : ℕ => Icc (max ((a + t) / 2) (t - 1 / ((n : ℝ) + 1))) b := by
    intro n m hnm; apply Icc_subset_Icc_left
    have := Nat.one_div_le_one_div (α := ℝ) hnm
    exact max_le_max le_rfl (by linarith)
  rw [hI, hanti.measure_iInter (fun _ => measurableSet_Icc.nullMeasurableSet)
    ⟨0, ne_top_of_le_ne_top hfin (measure_mono (Icc_subset_Icc_left
      (by have := le_max_left ((a + t) / 2) (t - 1 / (((0 : ℕ) : ℝ) + 1)); linarith)))⟩]
  refine le_iInf fun n => (h _ ?_ ?_).le
  · have := le_max_left ((a + t) / 2) (t - 1 / ((n : ℝ) + 1)); linarith
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact max_lt (by linarith) (by linarith)

lemma ps_exists_big {x : ℝ} {L : ℝ≥0∞} (hL : L < μ (Iic x)) : ∃ y₀ ≤ x, L < μ (Icc y₀ x) := by
  have hU : Iic x = ⋃ n : ℕ, Icc (x - n) x := by
    ext y; simp only [mem_Iic, mem_iUnion, mem_Icc]; constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_gt (x - y)
      exact ⟨n, by linarith, h⟩
    · rintro ⟨n, -, h⟩; exact h
  have hmono : Monotone fun n : ℕ => Icc (x - n) x := by
    intro n m hnm; apply Icc_subset_Icc_left
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  rw [hU, hmono.measure_iUnion] at hL
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hL
  exact ⟨x - n, by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith, hn⟩

variable [NullSingletonClass μ] {ℓ : ℝ≥0} {a : ℝ}

lemma ps_mem_self (x : ℝ) : x ∈ {y | y ≤ x ∧ μ (Icc y x) ≤ ℓ} :=
  ⟨le_rfl, by simp⟩

lemma ps_Icc_of_le {c x : ℝ} (h : x ≤ c) : μ (Icc c x) = 0 := by
  refine measure_mono_null (fun y hy => ?_) (measure_singleton x)
  exact le_antisymm hy.2 (h.trans hy.1)

section Good

variable (hpos : ∀ x y, x < y → 0 < μ (Ioo x y)) (hℓ : (ℓ : ℝ≥0∞) ≤ μ (Iic a))
include hpos hℓ

lemma ps_lt_Iic {x : ℝ} (hx : a < x) : (ℓ : ℝ≥0∞) < μ (Iic x) := by
  have hdisj : Disjoint (Iic a) (Ioo a x) :=
    disjoint_left.mpr fun y h1 h2 => absurd h1 (not_le.mpr h2.1)
  have hsub : Iic a ∪ Ioo a x ⊆ Iic x := by
    intro y hy; rcases hy with h | h
    · exact le_trans h hx.le
    · exact h.2.le
  calc (ℓ : ℝ≥0∞) < ℓ + μ (Ioo a x) := ENNReal.lt_add_right ENNReal.coe_ne_top (hpos a x hx).ne'
    _ ≤ μ (Iic a) + μ (Ioo a x) := by gcongr
    _ = μ (Iic a ∪ Ioo a x) := (measure_union hdisj measurableSet_Ioo).symm
    _ ≤ μ (Iic x) := measure_mono hsub

lemma ps_bdd {x : ℝ} (hx : a < x) : BddBelow {y | y ≤ x ∧ μ (Icc y x) ≤ ℓ} := by
  obtain ⟨y₀, -, hy₀⟩ := ps_exists_big (ps_lt_Iic hpos hℓ hx)
  refine ⟨y₀, fun y hy => le_of_not_gt fun hlt => ?_⟩
  exact absurd ((measure_mono (Icc_subset_Icc_left hlt.le)).trans hy.2) (not_le.mpr hy₀)

/-- Key characterization: for `x > a`, `x_ℓ ≤ c ↔ μ[c, x] ≤ ℓ`. -/
lemma ps_le_iff {x : ℝ} (hx : a < x) (c : ℝ) :
    palmShiftLeft μ ℓ x ≤ c ↔ μ (Icc c x) ≤ ℓ := by
  constructor
  · intro h
    rcases le_or_gt x c with hxc | hcx
    · rw [ps_Icc_of_le hxc]; exact zero_le
    · rw [← measure_congr Ioc_ae_eq_Icc]
      refine ps_Ioc_le fun y hcy hyx => ?_
      obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt ⟨x, ps_mem_self x⟩ (h.trans_lt hcy)
      exact (measure_mono (Icc_subset_Icc_left hzy.le)).trans hz.2
  · intro h
    rcases le_or_gt c x with hcx | hxc
    · exact csInf_le (ps_bdd hpos hℓ hx) ⟨hcx, h⟩
    · exact (csInf_le (ps_bdd hpos hℓ hx) (ps_mem_self x)).trans hxc.le

/-- The countable-infimum formula for `x_ℓ` (used for joint measurability). -/
lemma ps_hat_eq {x : ℝ} (hx : a < x) :
    (⨅ q : ℚ, if μ (Icc (q : ℝ) x) ≤ ℓ then (q : ℝ) else x) = palmShiftLeft μ ℓ x := by
  set t := palmShiftLeft μ ℓ x
  have hb : ∀ q : ℚ, t ≤ (if μ (Icc (q : ℝ) x) ≤ ℓ then (q : ℝ) else x) := by
    intro q
    split_ifs with h
    · exact (ps_le_iff hpos hℓ hx q).mpr h
    · exact (ps_le_iff hpos hℓ hx x).mpr (by rw [ps_Icc_of_le le_rfl]; exact zero_le)
  have hbdd : BddBelow (range fun q : ℚ => if μ (Icc (q : ℝ) x) ≤ ℓ then (q : ℝ) else x) :=
    ⟨t, by rintro _ ⟨q, rfl⟩; exact hb q⟩
  refine le_antisymm ?_ (le_ciInf hb)
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn hr
  refine (ciInf_le hbdd q).trans ?_
  rw [if_pos ((ps_le_iff hpos hℓ hx q).mp h1.le)]
  exact h2.le

end Good

/-- Exact `ℓ`-window: `μ {x ∈ (c, b] : μ[c, x] ≤ ℓ} = ℓ` when `ℓ ≤ μ[c, b] < ∞`
(and `≤ ℓ` in general). -/
lemma ps_window {c b : ℝ} :
    μ {x | x ∈ Ioc c b ∧ μ (Icc c x) ≤ ℓ} ≤ ℓ ∧
    (μ (Icc c b) ≠ ∞ → (ℓ : ℝ≥0∞) ≤ μ (Icc c b) → μ {x | x ∈ Ioc c b ∧ μ (Icc c x) ≤ ℓ} = ℓ) := by
  set A := {x | x ∈ Ioc c b ∧ μ (Icc c x) ≤ ℓ}
  have hbdd : BddAbove (insert c A) := by
    refine ⟨max c b, fun y hy => ?_⟩
    rcases hy with rfl | hy
    · exact le_max_left _ _
    · exact hy.1.2.trans (le_max_right _ _)
  set s := sSup (insert c A)
  have hcs : c ≤ s := le_csSup hbdd (mem_insert _ _)
  have hAs : A ⊆ Ioc c s := fun x hx => ⟨hx.1.1, le_csSup hbdd (mem_insert_of_mem _ hx)⟩
  have hIoo : Ioo c s ⊆ A := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup (insert_nonempty _ _) hy.2
    rcases hz with rfl | hz
    · exact absurd hy.1 (not_lt.mpr hyz.le)
    · exact ⟨⟨hy.1, hyz.le.trans hz.1.2⟩, (measure_mono (Icc_subset_Icc_right hyz.le)).trans hz.2⟩
  have hup : μ A ≤ ℓ := by
    refine (measure_mono hAs).trans ?_
    rw [measure_congr Ioc_ae_eq_Icc, ← measure_congr Ico_ae_eq_Icc]
    refine ps_Ico_le fun y hcy hys => ?_
    rcases eq_or_lt_of_le hcy with rfl | hcy'
    · rw [Icc_self, measure_singleton]; exact zero_le
    · exact (hIoo ⟨hcy', hys⟩).2
  refine ⟨hup, fun hfin hL => le_antisymm hup ?_⟩
  have hls : (ℓ : ℝ≥0∞) ≤ μ (Icc c s) := by
    rcases lt_or_ge s b with hsb | hbs
    · refine ps_le_Icc_right hsb hfin fun y hsy hyb => lt_of_not_ge fun hle => ?_
      have : y ∈ A := ⟨⟨hcs.trans_lt hsy, hyb⟩, hle⟩
      exact absurd (le_csSup hbdd (mem_insert_of_mem _ this)) (not_le.mpr hsy)
    · exact hL.trans (measure_mono (Icc_subset_Icc_right hbs))
  calc (ℓ : ℝ≥0∞) ≤ μ (Icc c s) := hls
    _ = μ (Ioo c s) := (measure_congr Ioo_ae_eq_Icc).symm
    _ ≤ μ A := measure_mono hIoo

/-- **Deterministic Palm-shift bound.** `T₁` is any measurable function agreeing with
`x ↦ x_ℓ` on `(a, ∞)`. -/
theorem ps_det_left (hpos : ∀ x y, x < y → 0 < μ (Ioo x y)) (hℓ : (ℓ : ℝ≥0∞) ≤ μ (Iic a))
    {b : ℝ} (hfin : μ (Icc a b) ≠ ∞) {T₁ : ℝ → ℝ} (hT₁ : Measurable T₁)
    (hT : ∀ x, a < x → T₁ x = palmShiftLeft μ ℓ x) {G : ℝ → ℝ} (hG : Measurable G) {M : ℝ}
    (hGM : ∀ x, |G x| ≤ M) :
    |∫ x in Icc a b, G (T₁ x) ∂μ - ∫ x in Icc a b, G x ∂μ| ≤ 2 * ℓ * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hGM 0)
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rcases le_or_gt b a with hba | hab
  · rw [Ioc_eq_empty (not_lt.mpr hba)]; simp; positivity
  have hfin' : μ (Ioc a b) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono Ioc_subset_Icc_self)
  set ρ := μ.restrict (Ioc a b) with hρ
  haveI : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hfin'
  set m1 := ρ.map T₁ with hm1
  have hint : ∀ m : Measure ℝ, IsFiniteMeasure m → Integrable G m := fun m _ =>
    Integrable.mono' (integrable_const M) hG.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hGM x)
  have hmap : ∫ x, G (T₁ x) ∂ρ = ∫ y, G y ∂m1 :=
    (integral_map hT₁.aemeasurable hG.aestronglyMeasurable).symm
  rw [hmap]
  have hm1s : ∀ s, MeasurableSet s → m1 s = μ (T₁ ⁻¹' s ∩ Ioc a b) := fun s hs => by
    rw [hm1, Measure.map_apply hT₁ hs, hρ, Measure.restrict_apply (hT₁ hs)]
  set τ := palmShiftLeft μ ℓ b
  have hτb : μ (Icc τ b) ≤ ℓ := (ps_le_iff hpos hℓ hab τ).mp le_rfl
  have hτleb : τ ≤ b := (ps_le_iff hpos hℓ hab b).mpr (by rw [ps_Icc_of_le le_rfl]; exact zero_le)
  have hTle : ∀ x ∈ Ioc a b, T₁ x ≤ τ := fun x hx => by
    rw [hT x hx.1]
    exact (ps_le_iff hpos hℓ hx.1 τ).mpr ((measure_mono (Icc_subset_Icc_right hx.2)).trans hτb)
  -- the sets `A c`
  have hpre : ∀ c, T₁ ⁻¹' Iic c ∩ Ioc a b = {x | x ∈ Ioc a b ∧ μ (Icc c x) ≤ ℓ} := by
    intro c; ext x; constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (ps_le_iff hpos hℓ h2.1 c).mp (by rw [← hT x h2.1]; exact h1)⟩
    · rintro ⟨h2, h1⟩
      exact ⟨by show T₁ x ≤ c; rw [hT x h2.1]; exact (ps_le_iff hpos hℓ h2.1 c).mpr h1, h2⟩
  have hAmeas : ∀ c, MeasurableSet {x | x ∈ Ioc a b ∧ μ (Icc c x) ≤ ℓ} := fun c => by
    rw [← hpre c]; exact (hT₁ measurableSet_Iic).inter measurableSet_Ioc
  -- (F4) and (F6), (F5)
  have hF4 : m1 (Iic a) ≤ ℓ := by rw [hm1s _ measurableSet_Iic, hpre a]; exact ps_window.1
  have hF6 : m1 (Ioi τ) = 0 := by
    rw [hm1s _ measurableSet_Ioi]
    convert measure_empty (μ := μ)
    ext x; simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun ⟨h1, h2⟩ => absurd (hTle x h2) (not_le.mpr h1)
  have hF5 : ρ (Ioi τ) ≤ ℓ := by
    rw [hρ, Measure.restrict_apply measurableSet_Ioi]
    exact (measure_mono fun x (hx : x ∈ Ioi τ ∩ Ioc a b) =>
      (⟨le_of_lt hx.1, hx.2.2⟩ : x ∈ Icc τ b)).trans hτb
  have hρa : ρ (Iic a) = 0 := by
    rw [hρ, Measure.restrict_apply measurableSet_Iic]
    convert measure_empty (μ := μ)
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
    exact fun ⟨h1, h2, _⟩ => absurd h1 (not_le.mpr h2)
  set A2 := Ioc a τ
  have hcompl : A2ᶜ ⊆ Iic a ∪ Ioi τ := by
    intro x hx
    simp only [A2, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hm1c : m1 A2ᶜ ≤ ℓ :=
    (measure_mono hcompl).trans ((measure_union_le _ _).trans (by rw [hF6, add_zero]; exact hF4))
  have hρc : ρ A2ᶜ ≤ ℓ :=
    (measure_mono hcompl).trans ((measure_union_le _ _).trans (by rw [hρa, zero_add]; exact hF5))
  -- (F7)
  have hF7 : m1.restrict A2 = ρ.restrict A2 := by
    rcases le_or_gt τ a with hτa | haτ
    · simp [A2, Ioc_eq_empty (not_lt.mpr hτa)]
    have hτL : (ℓ : ℝ≥0∞) ≤ μ (Icc τ b) := by
      refine ps_le_Icc_left haτ hfin fun y hay hyτ => lt_of_not_ge fun h => ?_
      exact absurd ((ps_le_iff hpos hℓ hab y).mpr h) (not_le.mpr hyτ)
    have hAa : μ {x | x ∈ Ioc a b ∧ μ (Icc a x) ≤ ℓ} = ℓ :=
      ps_window.2 hfin (hτL.trans (measure_mono (Icc_subset_Icc_left haτ.le)))
    refine Measure.ext_of_Iic _ _ fun c => ?_
    rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic, hρ,
      Measure.restrict_apply (measurableSet_Iic.inter measurableSet_Ioc)]
    set d := min c τ
    have hd : Iic c ∩ A2 = Ioc a d := by
      ext x; simp only [A2, d, mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]; tauto
    rw [hd]
    rcases le_or_gt d a with hda | had
    · simp [Ioc_eq_empty (not_lt.mpr hda)]
    have hdτ : d ≤ τ := min_le_right _ _
    have hdb : Ioc a d ∩ Ioc a b = Ioc a d :=
      inter_eq_left.mpr (Ioc_subset_Ioc_right (hdτ.trans hτleb))
    rw [hdb, hm1s _ measurableSet_Ioc]
    have hpre2 : T₁ ⁻¹' Ioc a d ∩ Ioc a b =
        {x | x ∈ Ioc a b ∧ μ (Icc d x) ≤ ℓ} \ {x | x ∈ Ioc a b ∧ μ (Icc a x) ≤ ℓ} := by
      rw [← hpre d, ← hpre a]; ext x; constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h2, h3⟩, fun h => absurd h.1 (not_le.mpr h1)⟩
      · rintro ⟨⟨h2, h3⟩, h4⟩
        exact ⟨⟨lt_of_not_ge fun h => h4 ⟨h, h3⟩, h2⟩, h3⟩
    have hsub : {x | x ∈ Ioc a b ∧ μ (Icc a x) ≤ ℓ} ⊆ {x | x ∈ Ioc a b ∧ μ (Icc d x) ≤ ℓ} :=
      fun x hx => ⟨hx.1, (measure_mono (Icc_subset_Icc_left had.le)).trans hx.2⟩
    rw [hpre2, measure_diff hsub (hAmeas a).nullMeasurableSet (by rw [hAa]; exact ENNReal.coe_ne_top),
      hAa]
    -- `A d = W_d ∪ (a, d]`
    have hsplit : {x | x ∈ Ioc a b ∧ μ (Icc d x) ≤ ℓ} =
        {x | x ∈ Ioc d b ∧ μ (Icc d x) ≤ ℓ} ∪ Ioc a d := by
      ext x; simp only [mem_setOf_eq, mem_union, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases lt_or_ge d x with hdx | hxd
        · exact Or.inl ⟨⟨hdx, h2⟩, h3⟩
        · exact Or.inr ⟨h1, hxd⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩)
        · exact ⟨⟨had.trans h1, h2⟩, h3⟩
        · exact ⟨⟨h1, h2.trans (hdτ.trans hτleb)⟩, by rw [ps_Icc_of_le h2]; exact zero_le⟩
    have hdisj : Disjoint {x | x ∈ Ioc d b ∧ μ (Icc d x) ≤ ℓ} (Ioc a d) :=
      disjoint_left.mpr fun x h1 h2 => absurd h2.2 (not_le.mpr h1.1.1)
    have hWd : μ {x | x ∈ Ioc d b ∧ μ (Icc d x) ≤ ℓ} = ℓ :=
      ps_window.2 (ne_top_of_le_ne_top hfin (measure_mono (Icc_subset_Icc_left had.le)))
        (hτL.trans (measure_mono (Icc_subset_Icc_left hdτ)))
    rw [hsplit, measure_union hdisj measurableSet_Ioc, hWd,
      ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
  -- assemble
  have hm1fin : IsFiniteMeasure m1 := inferInstance
  rw [← integral_add_compl (s := A2) measurableSet_Ioc (hint m1 hm1fin),
    ← integral_add_compl (s := A2) measurableSet_Ioc (hint ρ inferInstance), hF7]
  have hb1 : ‖∫ x in A2ᶜ, G x ∂m1‖ ≤ M * ℓ := by
    refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
      fun x _ => by rw [Real.norm_eq_abs]; exact hGM x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top hm1c).trans_eq (ENNReal.coe_toReal ℓ)
  have hb2 : ‖∫ x in A2ᶜ, G x ∂ρ‖ ≤ M * ℓ := by
    refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
      fun x _ => by rw [Real.norm_eq_abs]; exact hGM x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top hρc).trans_eq (ENNReal.coe_toReal ℓ)
  rw [Real.norm_eq_abs] at hb1 hb2
  have : ∫ x in A2, G x ∂ρ + ∫ x in A2ᶜ, G x ∂m1 - (∫ x in A2, G x ∂ρ + ∫ x in A2ᶜ, G x ∂ρ)
      = ∫ x in A2ᶜ, G x ∂m1 - ∫ x in A2ᶜ, G x ∂ρ := by ring
  rw [this]
  calc _ ≤ |∫ x in A2ᶜ, G x ∂m1| + |∫ x in A2ᶜ, G x ∂ρ| := abs_sub _ _
    _ ≤ M * ℓ + M * ℓ := add_le_add hb1 hb2
    _ = 2 * ℓ * M := by ring

end Det

/-! ### Reflection (for the mirror version) -/

section Reflect

variable {μ : Measure ℝ} {ℓ : ℝ≥0}

lemma ps_preimage_neg_Icc (u v : ℝ) : Neg.neg ⁻¹' Icc u v = Icc (-v) (-u) := by
  ext y; simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma ps_reflect (y : ℝ) :
    palmShiftLeft (μ.map Neg.neg) ℓ y = -palmShiftRight μ ℓ (-y) := by
  unfold palmShiftLeft palmShiftRight
  rw [← Real.sInf_neg]
  congr 1
  ext z
  simp only [mem_setOf_eq, Set.mem_neg]
  rw [Measure.map_apply measurable_neg measurableSet_Icc, ps_preimage_neg_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨neg_le_neg h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨neg_le_neg_iff.mp h1, h2⟩

lemma ps_reflect_good [NullSingletonClass μ] (hpos : ∀ x y, x < y → 0 < μ (Ioo x y)) {b : ℝ}
    (hℓ : (ℓ : ℝ≥0∞) ≤ μ (Ici b)) :
    NullSingletonClass (μ.map Neg.neg) ∧ (∀ x y, x < y → 0 < μ.map Neg.neg (Ioo x y)) ∧
      (ℓ : ℝ≥0∞) ≤ μ.map Neg.neg (Iic (-b)) := by
  refine ⟨⟨fun x => ?_⟩, fun x y hxy => ?_, ?_⟩
  · rw [Measure.map_apply measurable_neg (measurableSet_singleton x)]
    refine measure_mono_null (fun y hy => ?_) (measure_singleton (-x))
    simp only [mem_preimage, mem_singleton_iff] at hy ⊢; linarith
  · rw [Measure.map_apply measurable_neg measurableSet_Ioo]
    have : Neg.neg ⁻¹' Ioo x y = Ioo (-y) (-x) := by
      ext z; simp only [mem_preimage, mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [this]; exact hpos _ _ (by linarith)
  · rw [Measure.map_apply measurable_neg measurableSet_Iic]
    have : Neg.neg ⁻¹' Iic (-b) = Ici b := by
      ext z; simp only [mem_preimage, mem_Iic, mem_Ici]; constructor <;> intro h <;> linarith
    rw [this]; exact hℓ

/-- **Deterministic mirror bound.** -/
theorem ps_det_right [NullSingletonClass μ] (hpos : ∀ x y, x < y → 0 < μ (Ioo x y)) {a b : ℝ}
    (hℓ : (ℓ : ℝ≥0∞) ≤ μ (Ici b)) (hfin : μ (Icc a b) ≠ ∞) {T₁ : ℝ → ℝ} (hT₁ : Measurable T₁)
    (hT : ∀ x, x < b → T₁ x = palmShiftRight μ ℓ x) {G : ℝ → ℝ} (hG : Measurable G) {M : ℝ}
    (hGM : ∀ x, |G x| ≤ M) :
    |∫ x in Icc a b, G (T₁ x) ∂μ - ∫ x in Icc a b, G x ∂μ| ≤ 2 * ℓ * M := by
  obtain ⟨hna, hpos', hℓ'⟩ := ps_reflect_good hpos hℓ
  haveI := hna
  have hfin' : μ.map Neg.neg (Icc (-b) (-a)) ≠ ∞ := by
    rw [Measure.map_apply measurable_neg measurableSet_Icc, ps_preimage_neg_Icc]
    simpa using hfin
  have key := ps_det_left (μ := μ.map Neg.neg) (a := -b) (b := -a) hpos' hℓ' hfin'
    (T₁ := fun y => -T₁ (-y)) (hT₁.comp measurable_neg).neg
    (fun y hy => by rw [hT (-y) (by linarith), ps_reflect])
    (G := fun y => G (-y)) (hG.comp measurable_neg) (fun y => hGM _)
  have htrans : ∀ f : ℝ → ℝ, Measurable f →
      ∫ y in Icc (-b) (-a), f (-y) ∂μ.map Neg.neg = ∫ x in Icc a b, f x ∂μ := by
    intro f hf
    have hm := integral_map (μ := μ.restrict (Neg.neg ⁻¹' Icc (-b) (-a)))
      measurable_neg.aemeasurable (f := fun y => f (-y)) (hf.comp measurable_neg).aestronglyMeasurable
    rw [Measure.restrict_map measurable_neg measurableSet_Icc, hm, ps_preimage_neg_Icc]
    simp only [neg_neg]
  simp only [neg_neg] at key
  rw [htrans (fun x => G (T₁ x)) (hG.comp hT₁), htrans G hG] at key
  exact key

end Reflect

/-! ### Random measures and the Palm law -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E ν(I)` for `I = [a, b]`. -/
noncomputable def palmMass (P : Measure Ω) (ν : Kernel Ω ℝ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ν ω (Icc a b) ∂P

/-- The size-biased law `𝐏_I(dω, dx) = ν_ω|_I(dx) P(dω) / E ν(I)`, `I = [a, b]`. -/
noncomputable def palmLaw (P : Measure Ω) (ν : Kernel Ω ℝ) (a b : ℝ) : Measure (Ω × ℝ) :=
  (palmMass P ν a b)⁻¹ • (P ⊗ₘ ν.restrict (measurableSet_Icc (a := a) (b := b)))

/-- Jointly measurable version of `x_ℓ` (a countable infimum). -/
noncomputable def palmShiftLeftHat (ν : Kernel Ω ℝ) (ℓ : ℝ≥0) (p : Ω × ℝ) : ℝ :=
  ⨅ q : ℚ, if ν p.1 (Icc (q : ℝ) p.2) ≤ ℓ then (q : ℝ) else p.2

/-- Jointly measurable version of `x^ℓ`, via reflection. -/
noncomputable def palmShiftRightHat (ν : Kernel Ω ℝ) (ℓ : ℝ≥0) (p : Ω × ℝ) : ℝ :=
  -palmShiftLeftHat (Kernel.map ν Neg.neg) ℓ (p.1, -p.2)

lemma measurable_palmShiftLeftHat (ν : Kernel Ω ℝ) [IsSFiniteKernel ν] (ℓ : ℝ≥0) :
    Measurable (palmShiftLeftHat ν ℓ) := by
  unfold palmShiftLeftHat
  refine Measurable.iInf fun q => Measurable.ite ?_ measurable_const measurable_snd
  have ht : MeasurableSet {z : (Ω × ℝ) × ℝ | (q : ℝ) ≤ z.2 ∧ z.2 ≤ z.1.2} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hf : Measurable fun p : Ω × ℝ => ν p.1 (Icc (q : ℝ) p.2) :=
    Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ ν) ht
  exact measurableSet_le hf measurable_const

lemma measurable_palmShiftRightHat (ν : Kernel Ω ℝ) [IsSFiniteKernel ν] (ℓ : ℝ≥0) :
    Measurable (palmShiftRightHat ν ℓ) :=
  ((measurable_palmShiftLeftHat _ ℓ).comp (measurable_fst.prodMk measurable_snd.neg)).neg

lemma ps_hatR_eq (ν : Kernel Ω ℝ) (ℓ : ℝ≥0) (ω : Ω) [NullSingletonClass (ν ω)]
    (hpos : ∀ x y, x < y → 0 < ν ω (Ioo x y)) {b : ℝ} (hℓ : (ℓ : ℝ≥0∞) ≤ ν ω (Ici b))
    {x : ℝ} (hx : x < b) : palmShiftRightHat ν ℓ (ω, x) = palmShiftRight (ν ω) ℓ x := by
  have hmap : Kernel.map ν Neg.neg ω = (ν ω).map Neg.neg := Kernel.map_apply _ measurable_neg _
  obtain ⟨hna, hpos', hℓ'⟩ := ps_reflect_good hpos hℓ
  haveI := hna
  show -(⨅ q : ℚ, if (Kernel.map ν Neg.neg) ω (Icc (q : ℝ) (-x)) ≤ ℓ then (q : ℝ) else -x) = _
  rw [hmap, ps_hat_eq hpos' hℓ' (show -b < -x by linarith), ps_reflect, neg_neg, neg_neg]

/-- Transfer from a Palm-law statement to `ω`-wise statements. -/
lemma ps_wrapper (P : Measure Ω) [IsProbabilityMeasure P] (ν : Kernel Ω ℝ) [IsSFiniteKernel ν]
    (a b : ℝ) (hmass : palmMass P ν a b ≠ ∞) {G : Ω × ℝ → ℝ} (hG : Measurable G) {M : ℝ}
    (hGM : ∀ p, |G p| ≤ M) {T T' : Ω × ℝ → ℝ} (hT' : Measurable T')
    (hae : ∀ᵐ p ∂(P ⊗ₘ ν.restrict (measurableSet_Icc (a := a) (b := b))), T p = T' p) {B : ℝ}
    (hbound : ∀ᵐ ω ∂P, ν ω (Icc a b) ≠ ∞ →
      |∫ x in Icc a b, G (ω, T' (ω, x)) ∂ν ω - ∫ x in Icc a b, G (ω, x) ∂ν ω| ≤ B) :
    |∫ p, G (p.1, T p) ∂palmLaw P ν a b - ∫ p, G p ∂palmLaw P ν a b| ≤
      B / (palmMass P ν a b).toReal := by
  set κ := ν.restrict (measurableSet_Icc (a := a) (b := b)) with hκ
  set Q := P ⊗ₘ κ with hQ
  have hκω : ∀ ω, κ ω = (ν ω).restrict (Icc a b) := fun ω => Kernel.restrict_apply _ _ _
  haveI : IsFiniteMeasure Q := by
    constructor
    rw [hQ, Measure.compProd_apply MeasurableSet.univ]
    simp only [preimage_univ, hκω, Measure.restrict_apply_univ]
    exact hmass.lt_top
  have hfin : ∀ᵐ ω ∂P, ν ω (Icc a b) < ∞ := ae_lt_top (ν.measurable_coe measurableSet_Icc) hmass
  have hint1 : Integrable (fun p : Ω × ℝ => G (p.1, T' p)) Q :=
    Integrable.mono' (integrable_const M) (hG.comp (measurable_fst.prodMk hT')).aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hGM _)
  have hint2 : Integrable G Q :=
    Integrable.mono' (integrable_const M) hG.aestronglyMeasurable
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hGM _)
  have h1 : ∫ p, G (p.1, T p) ∂Q = ∫ p, G (p.1, T' p) ∂Q :=
    integral_congr_ae (hae.mono fun p h => by simp only [h])
  have hdiff : ∫ p, G (p.1, T p) ∂Q - ∫ p, G p ∂Q =
      ∫ ω, (∫ x, G (ω, T' (ω, x)) ∂κ ω - ∫ x, G (ω, x) ∂κ ω) ∂P := by
    rw [h1, ← integral_sub hint1 hint2, Measure.integral_compProd (f := fun p => G (p.1, T' p) - G p) (hint1.sub hint2)]
    refine integral_congr_ae ?_
    filter_upwards [hfin] with ω hω
    haveI : IsFiniteMeasure (κ ω) := by rw [hκω]; exact isFiniteMeasure_restrict.mpr hω.ne
    refine integral_sub ?_ ?_
    · exact Integrable.mono' (integrable_const M)
        ((hG.comp (measurable_fst.prodMk hT')).comp measurable_prodMk_left).aestronglyMeasurable
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hGM _)
    · exact Integrable.mono' (integrable_const M)
        (hG.comp measurable_prodMk_left).aestronglyMeasurable
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hGM _)
  have hnorm : |∫ ω, (∫ x, G (ω, T' (ω, x)) ∂κ ω - ∫ x, G (ω, x) ∂κ ω) ∂P| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := B)
      (f := fun ω => ∫ x, G (ω, T' (ω, x)) ∂κ ω - ∫ x, G (ω, x) ∂κ ω) (by
        filter_upwards [hbound, hfin] with ω h hω
        rw [Real.norm_eq_abs, hκω]; exact h hω.ne)
    simpa using this
  rw [palmLaw, integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_sub,
    abs_mul, hdiff, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_inv, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- Null-set bookkeeping for the Palm law. -/
lemma ps_ae_eq (P : Measure Ω) [SFinite P] (ν : Kernel Ω ℝ) [IsSFiniteKernel ν] (a b : ℝ)
    {T T' : Ω × ℝ → ℝ} {Good : Ω → Prop} (hgood : ∀ᵐ ω ∂P, Good ω) {E : Set ℝ}
    (hE : MeasurableSet E) (hEnull : ∀ᵐ ω ∂P, ν ω (E ∩ Icc a b) = 0)
    (heq : ∀ ω x, Good ω → x ∉ E → T (ω, x) = T' (ω, x)) :
    ∀ᵐ p ∂(P ⊗ₘ ν.restrict (measurableSet_Icc (a := a) (b := b))), T p = T' p := by
  rw [ae_iff]
  refine measure_mono_null (t := toMeasurable P {ω | ¬ Good ω} ×ˢ univ ∪ univ ×ˢ E) ?_ ?_
  · intro p hp
    by_cases hg : Good p.1
    · by_cases hx : p.2 ∈ E
      · exact Or.inr ⟨trivial, hx⟩
      · exact absurd (heq p.1 p.2 hg hx) hp
    · exact Or.inl ⟨subset_toMeasurable _ _ hg, trivial⟩
  · refine measure_union_null ?_ ?_
    · rw [Measure.compProd_apply_prod (measurableSet_toMeasurable _ _) MeasurableSet.univ]
      exact setLIntegral_measure_zero _ _ (by rw [measure_toMeasurable]; exact ae_iff.mp hgood)
    · rw [Measure.compProd_apply_prod MeasurableSet.univ hE, Measure.restrict_univ,
        lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
      filter_upwards [hEnull] with ω h
      rw [Kernel.restrict_apply, Measure.restrict_apply hE]; exact h

/-- **Blueprint A6, mirror version (right shift).** With `x^ℓ := sup {y ≥ x : ν[x, y] ≤ ℓ}`
and a.s. `ν[b, ∞) ≥ ℓ`. -/
theorem palm_shift_right_bound (P : Measure Ω) [IsProbabilityMeasure P] (ν : Kernel Ω ℝ)
    [IsSFiniteKernel ν] (a b : ℝ) (ℓ : ℝ≥0) (hatom : ∀ᵐ ω ∂P, NullSingletonClass (ν ω))
    (hpos : ∀ᵐ ω ∂P, ∀ x y, x < y → 0 < ν ω (Ioo x y))
    (hℓ : ∀ᵐ ω ∂P, (ℓ : ℝ≥0∞) ≤ ν ω (Ici b)) (hmass : palmMass P ν a b ≠ ∞)
    {G : Ω × ℝ → ℝ} (hG : Measurable G) {M : ℝ} (hGM : ∀ p, |G p| ≤ M) :
    |∫ p, G (p.1, palmShiftRight (ν p.1) ℓ p.2) ∂palmLaw P ν a b - ∫ p, G p ∂palmLaw P ν a b|
      ≤ 2 * ℓ * M / (palmMass P ν a b).toReal := by
  refine ps_wrapper P ν a b hmass hG hGM (T := fun p => palmShiftRight (ν p.1) ℓ p.2)
    (measurable_palmShiftRightHat ν ℓ) ?_ ?_
  · refine ps_ae_eq P ν a b (Good := fun ω => NullSingletonClass (ν ω) ∧
        (∀ x y, x < y → 0 < ν ω (Ioo x y)) ∧ (ℓ : ℝ≥0∞) ≤ ν ω (Ici b))
      (by filter_upwards [hatom, hpos, hℓ] with ω h1 h2 h3; exact ⟨h1, h2, h3⟩)
      (E := Ici b) measurableSet_Ici ?_ ?_
    · filter_upwards [hatom] with ω h
      haveI := h
      exact measure_mono_null (fun x hx => le_antisymm hx.2.2 hx.1) (measure_singleton b)
    · rintro ω x ⟨h1, h2, h3⟩ hx
      haveI := h1
      exact (ps_hatR_eq ν ℓ ω h2 h3 (not_le.mp hx)).symm
  · filter_upwards [hatom, hpos, hℓ] with ω h1 h2 h3 hfin
    haveI := h1
    exact ps_det_right h2 h3 hfin ((measurable_palmShiftRightHat ν ℓ).comp measurable_prodMk_left)
      (fun x hx => ps_hatR_eq ν ℓ ω h2 h3 hx) (hG.comp measurable_prodMk_left) (fun x => hGM _)

end Random

end QuantumZipper.PalmShift
