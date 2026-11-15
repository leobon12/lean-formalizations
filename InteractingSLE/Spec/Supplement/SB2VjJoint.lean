/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ViAbs

/-!
# SB2(1)'s version half: the absolute lift is jointly measurable

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The relative curve fed to the measurable
driver is the absolute lift read at random times (the entrance plus a relative time), so a jointly measurable version
is needed.

* `dfl n T = ⌊T 2ⁿ⌋ / 2ⁿ`: the dyadic floor (`dfl_le`, `tendsto_dfl`: it tends to `T` from below);
* **`exists_jointly_measurable`** (generic): a family `f ω T` measurable in `ω` for each `T` has a jointly measurable
  `F : Ω × ℝ≥0 → ℂ` equal to `f ω T` wherever `f ω` is continuous at `T` (the limit of the values at the dyadic floors);
* **`exists_joint_absLift`**: a measurable conull event `G` and a jointly measurable `F` with
  `F (ω, T) = absLift ω T` for `ω ∈ G ∩ D.event` and `T < ζ ω`.

Theorem 1.3 and the named S3 input as before (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vj

open Lv Exist.Staged Exist.StagedLaw

/-- The dyadic floor `⌊T 2ⁿ⌋ / 2ⁿ`. -/
def dfl (n : ℕ) (T : ℝ≥0) : ℝ≥0 := (⌊T * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n

theorem dfl_le (n : ℕ) (T : ℝ≥0) : dfl n T ≤ T := by
  unfold dfl
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem tendsto_dfl (T : ℝ≥0) : Tendsto (fun n => dfl n T) atTop (𝓝 T) := by
  rw [← NNReal.tendsto_coe]
  have hlow : ∀ n : ℕ, (T : ℝ) - (1 / 2) ^ n ≤ (dfl n T : ℝ) := fun n => by
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hfl : (T : ℝ) * 2 ^ n - 1 < ⌊T * 2 ^ n⌋₊ := by
      have := Nat.lt_floor_add_one (T * 2 ^ n)
      have h' : ((T * 2 ^ n : ℝ≥0) : ℝ) < (⌊T * 2 ^ n⌋₊ : ℝ) + 1 := by exact_mod_cast this
      push_cast at h'
      linarith
    unfold dfl
    push_cast
    rw [le_div_iff₀ h2, sub_mul, one_div_pow, one_div, inv_mul_cancel₀ h2.ne']
    linarith
  have hup : ∀ n : ℕ, (dfl n T : ℝ) ≤ T := fun n => NNReal.coe_le_coe.2 (dfl_le n T)
  have hlim : Tendsto (fun n : ℕ => (T : ℝ) - (1 / 2) ^ n) atTop (𝓝 T) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_sub (T : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

/-- **A jointly measurable version of a family continuous at the times where it is read.** -/
theorem exists_jointly_measurable {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ≥0 → ℂ}
    (hf : ∀ T, Measurable fun ω => f ω T) :
    ∃ F : Ω × ℝ≥0 → ℂ, Measurable F ∧ ∀ ω T, ContinuousAt (f ω) T → F (ω, T) = f ω T := by
  set F₀ : ℕ → Ω × ℝ≥0 → ℂ := fun n p => f p.1 (dfl n p.2) with hF₀
  have hF₀m : ∀ n, Measurable (F₀ n) := fun n => by
    have h1 : Measurable fun q : Ω × ℕ => f q.1 ((q.2 : ℝ≥0) / 2 ^ n) :=
      measurable_from_prod_countable_left fun k => hf ((k : ℝ≥0) / 2 ^ n)
    have h2 : Measurable fun p : Ω × ℝ≥0 => (p.1, ⌊p.2 * 2 ^ n⌋₊) :=
      measurable_fst.prodMk ((measurable_snd.mul_const _).nat_floor)
    exact h1.comp h2
  refine ⟨fun p => limUnder atTop fun n => F₀ n p,
    (StronglyMeasurable.limUnder fun n => (hF₀m n).stronglyMeasurable).measurable, fun ω T hc => ?_⟩
  exact ((hc.tendsto.comp (tendsto_dfl T))).limUnder_eq

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The absolute lift is jointly measurable** on a measurable conull event inside the entrance event, below the
lifetime. -/
theorem exists_joint_absLift (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ (G : Set Ω) (F : Ω × ℝ≥0 → ℂ), MeasurableSet G ∧ P Gᶜ = 0 ∧ Measurable F ∧
      ∀ ω ∈ G ∩ D.event, ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω → F (ω, T) = Vi.absLift κ b jumps E k u η ζ ω T := by
  classical
  obtain ⟨G₁, hG₁m, hG₁n, hmeas⟩ := Vi.exists_measurable_absLift h13 hS3 HP I D
  have hfacts : ∀ᵐ ω ∂P, (ω ∈ launchSet κ b jumps E (k + 1) →
      (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω)) ∧
      (ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω → ContinuousAt (Vi.absLift κ b jumps E k u η ζ ω) T) := by
    filter_upwards [D.ae_mem_event_iff, Vi.ae_absLift_good h13 hS3 HP I D] with ω hev hgd
    exact ⟨hev, fun hl hT T hTζ => (hgd hl hT T hTζ).1⟩
  obtain ⟨G₂, hG₂m, hG₂n, hG₂⟩ := Vf.exists_measurable_conull hfacts
  set f : Ω → ℝ≥0 → ℂ := fun ω T =>
    if ω ∈ G₁ ∩ D.event ∩ {ω | (T : ℝ≥0∞) < ζ ω} then Vi.absLift κ b jumps E k u η ζ ω T else 0 with hf
  have hfm : ∀ T, Measurable fun ω => f ω T := fun T => by
    have := (hmeas T).mono ((D.lineFiltC HP).le T) le_rfl
    convert this using 2
  obtain ⟨F, hFm, hF⟩ := exists_jointly_measurable hfm
  refine ⟨G₁ ∩ G₂, F, hG₁m.inter hG₂m, ?_, hFm, fun ω hω T hTζ => ?_⟩
  · rw [compl_inter]
    exact measure_union_null hG₁n hG₂n
  · obtain ⟨⟨hω1, hω2⟩, hωE⟩ := hω
    have hl := D.event_subset hωE
    have hT := ((hG₂ ω hω2).1 hl).1 hωE
    have hcont := (hG₂ ω hω2).2 hl hT T hTζ
    have hev : f ω =ᶠ[𝓝 T] Vi.absLift κ b jumps E k u η ζ ω := by
      have hopen : IsOpen {T' : ℝ≥0 | (T' : ℝ≥0∞) < ζ ω} :=
        isOpen_lt ENNReal.continuous_coe continuous_const
      filter_upwards [hopen.mem_nhds hTζ] with T' hT'
      simp only [hf, show ω ∈ G₁ ∩ D.event ∩ {ω | (T' : ℝ≥0∞) < ζ ω} from ⟨⟨hω1, hωE⟩, hT'⟩, ↓reduceIte]
    rw [hF ω T (hcont.congr hev.symm)]
    simp only [hf, show ω ∈ G₁ ∩ D.event ∩ {ω | (T : ℝ≥0∞) < ζ ω} from ⟨⟨hω1, hωE⟩, hTζ⟩, ↓reduceIte]

end

end InteractingSLE.Theorem14.SB.Vj
