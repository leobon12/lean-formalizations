import QuantumZipper.Proofs.LQG.VagueOpenExist
import QuantumZipper.Proofs.Zipper.AreaCoordCov
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: a Borel event forcing the local area limit (COORD-CHANGE, D98)

Strategy for the Palm transfer of the literal nodes (`Prop16LitRepMeasAtStmt`, `Prop16LitExStmt`):
instead of proving that the set of readings where a chosen local limit exists is Borel, use a
**Borel subset** of it, described by countably many convergence statements. For a measurable
family of fields `Z q` and a measurable radius `r q > 0`:

* `ExA.goodExA`: eventually finite approximations on the exhausting compacts `hbK (r q) m` of
  `U_q = B(0, r q) ∩ ℍ`, and convergence of `∫ χ_{q,n} g d(areaApprox γ (Z q) k)` for every
  cutoff `χ_{q,n} = hbCut (r q) n` of `U_q` and every `g` of a countable dense test family on `ℍ`;
* `ExA.measurableSet_goodExA`: this set is measurable;
* `ExA.exists_vague_of_goodExA`: on it the local vague limit on `U_q` exists
  (`VagueOpen.exists_isVagueLimitOn_of_cutoff`, Riesz–Markov–Kakutani).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

namespace ExA

/-- The cutoff of `B(0, r) ∩ ℍ` at level `n`. -/
def hbCut (r : ℝ) (n : ℕ) (z : ℂ) : ℝ := min 1 (max 0 ((n : ℝ) * min (r - ‖z‖) z.im - 1))

/-- The exhausting compacts of `B(0, r) ∩ ℍ`. -/
def hbK (r : ℝ) (m : ℕ) : Set ℂ := {z | ‖z‖ ≤ r - 1 / ((m : ℝ) + 1) ∧ 1 / ((m : ℝ) + 1) ≤ z.im}

theorem continuous_hbCut (r : ℝ) (n : ℕ) : Continuous (hbCut r n) := by
  unfold hbCut; fun_prop

theorem hbCut_nonneg (r : ℝ) (n : ℕ) (z : ℂ) : 0 ≤ hbCut r n z :=
  le_min zero_le_one (le_max_left _ _)

theorem hbCut_le_one (r : ℝ) (n : ℕ) (z : ℂ) : hbCut r n z ≤ 1 := min_le_left _ _

theorem tsupport_hbCut (r : ℝ) (n : ℕ) : tsupport (hbCut r n) ⊆ ball 0 r ∩ H := by
  have hcl : IsClosed {z : ℂ | 1 ≤ (n : ℝ) * min (r - ‖z‖) z.im} :=
    isClosed_le continuous_const (by fun_prop)
  have hsub : Function.support (hbCut r n) ⊆ {z : ℂ | 1 ≤ (n : ℝ) * min (r - ‖z‖) z.im} := by
    intro z hz
    by_contra h
    apply hz
    simp only [mem_setOf_eq, not_le] at h
    simp only [hbCut]
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  intro z hz
  have h1 : 1 ≤ (n : ℝ) * min (r - ‖z‖) z.im := closure_minimal hsub hcl hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : 0 < min (r - ‖z‖) z.im := by
    by_contra h
    push_neg at h
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right]; linarith [min_le_left (r - ‖z‖) z.im]
  · show 0 < z.im; linarith [min_le_right (r - ‖z‖) z.im]

theorem hbCut_eventually_one {r : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ ball 0 r ∩ H) :
    ∃ n : ℕ, ∀ z ∈ K, hbCut r n z = 1 := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he]⟩
  have hc : ContinuousOn (fun z : ℂ => min (r - ‖z‖) z.im) K := by fun_prop
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hc
  set d := min (r - ‖z₀‖) z₀.im with hd
  have hd0 : 0 < d := by
    obtain ⟨h1, h2⟩ := hKU hz₀
    rw [mem_ball, dist_zero_right] at h1
    exact lt_min (by linarith) h2
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / d)
  refine ⟨n, fun z hz => ?_⟩
  have hzd : d ≤ min (r - ‖z‖) z.im := hmin hz
  have h2 : 2 ≤ (n : ℝ) * min (r - ‖z‖) z.im := by
    have : 2 < (n : ℝ) * d := by rwa [div_lt_iff₀ hd0] at hn
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simp only [hbCut]
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

theorem isCompact_hbK (r : ℝ) (m : ℕ) : IsCompact (hbK r m) := by
  refine (isCompact_closedBall (0 : ℂ) (r - 1 / ((m : ℝ) + 1))).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  · intro z hz; rw [mem_closedBall, dist_zero_right]; exact hz.1

theorem hbK_subset (r : ℝ) (m : ℕ) : hbK r m ⊆ ball 0 r ∩ H := by
  intro z hz
  have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right]; linarith [hz.1]
  · show 0 < z.im; linarith [hz.2]

theorem exists_hbK {r : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ ball 0 r ∩ H) :
    ∃ m : ℕ, K ⊆ hbK r m := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he]⟩
  have hc : ContinuousOn (fun z : ℂ => min (r - ‖z‖) z.im) K := by fun_prop
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hc
  have hd0 : 0 < min (r - ‖z₀‖) z₀.im := by
    obtain ⟨h1, h2⟩ := hKU hz₀
    rw [mem_ball, dist_zero_right] at h1
    exact lt_min (by linarith) h2
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / min (r - ‖z₀‖) z₀.im)
  have hm' : 1 / ((m : ℝ) + 1) < min (r - ‖z₀‖) z₀.im := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hd0] at hm
    nlinarith
  refine ⟨m, fun z hz => ?_⟩
  have := hmin hz
  simp only [mem_setOf_eq] at this
  exact ⟨by linarith [min_le_left (r - ‖z‖) z.im], by linarith [min_le_right (r - ‖z‖) z.im]⟩

/-- The countable dense test family on `ℍ`. -/
def famF : Set (ℂ → ℝ) := VagueH.exists_denseTestFamily.choose

theorem famF_countable : famF.Countable := VagueH.exists_denseTestFamily.choose_spec.1

theorem famF_dense : VagueH.IsDenseTestFamily famF := VagueH.exists_denseTestFamily.choose_spec.2

variable {α : Type*} [MeasurableSpace α]

/-- **The Borel event** forcing the local vague limit on `B(0, r q) ∩ ℍ`. -/
def goodExA (γ : ℝ) (Z : α → FieldSample) (r : α → ℝ) : Set α :=
  {q | (∀ m : ℕ, ∀ᶠ k in atTop, areaApprox γ (Z q) k (hbK (r q) m) < ∞) ∧
    ∀ n : ℕ, ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, hbCut (r q) n z * g z ∂(areaApprox γ (Z q) k))
      atTop (𝓝 l)}

/-- **The local vague limit exists on the event.** -/
theorem exists_vague_of_goodExA {γ : ℝ} {Z : α → FieldSample} {r : α → ℝ} {q : α}
    (hq : q ∈ goodExA γ Z r) :
    ∃ μ, IsVagueLimitOn (ball 0 (r q) ∩ H) (areaApprox γ (Z q)) μ := by
  obtain ⟨hfin, hconv⟩ := hq
  refine VagueOpen.exists_isVagueLimitOn_of_cutoff (isOpen_ball.inter isOpen_H)
    inter_subset_right (χ := hbCut (r q)) (continuous_hbCut _) (hbCut_nonneg _)
    (hbCut_le_one _) (tsupport_hbCut _) (fun K hK hKU => hbCut_eventually_one hK hKU)
    famF_dense (fun K hK hKU => ?_) hconv
  obtain ⟨m, hm⟩ := exists_hbK hK hKU
  exact (hfin m).mono fun k hk => (measure_mono hm).trans_lt hk

/-- Joint measurability of the area density of a measurable family. -/
theorem measurable_dens {Z : α → FieldSample} (hZ : Measurable Z) (γ : ℝ) (k : ℕ) :
    Measurable fun p : α × ℂ => E6.areaDensK γ (Z p.1) k p.2 := by
  unfold E6.areaDensK
  exact measurable_const.mul (Real.measurable_exp.comp (((measurable_avgReg k).comp
    ((hZ.comp measurable_fst).prodMk measurable_snd)).const_mul γ))

theorem measurableSet_goodExA {γ : ℝ} {Z : α → FieldSample} (hZ : Measurable Z) {r : α → ℝ}
    (hr : Measurable r) : MeasurableSet (goodExA γ Z r) := by
  have hsplit : goodExA γ Z r =
      (⋂ m : ℕ, {q | ∀ᶠ k in atTop, areaApprox γ (Z q) k (hbK (r q) m) < ∞}) ∩
      ⋂ n : ℕ, {q | ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, hbCut (r q) n z * g z
        ∂(areaApprox γ (Z q) k)) atTop (𝓝 l)} := by
    ext q; simp only [goodExA, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [hsplit]
  refine MeasurableSet.inter ?_ ?_
  · -- eventual finiteness on the exhausting compacts
    refine MeasurableSet.iInter fun m => ?_
    have hmeas : ∀ k : ℕ, Measurable fun q => areaApprox γ (Z q) k (hbK (r q) m) := by
      intro k
      have hS : MeasurableSet {p : α × ℂ | p.2 ∈ hbK (r p.1) m} := by
        refine (measurableSet_le (f := fun p : α × ℂ => ‖p.2‖)
          (g := fun p : α × ℂ => r p.1 - 1 / ((m : ℝ) + 1)) (by fun_prop)
          ((hr.comp measurable_fst).sub measurable_const)).inter
          (measurableSet_le measurable_const (Complex.measurable_im.comp measurable_snd))
      have e : ∀ q, areaApprox γ (Z q) k (hbK (r q) m) =
          ∫⁻ z, {p : α × ℂ | p.2 ∈ hbK (r p.1) m}.indicator
            (fun p => ENNReal.ofReal (E6.areaDensK γ (Z p.1) k p.2)) (q, z) ∂(volume.restrict H) := by
        intro q
        have hK : MeasurableSet (hbK (r q) m) := (isCompact_hbK _ _).isClosed.measurableSet
        rw [show areaApprox γ (Z q) k = (volume.restrict H).withDensity
          (fun z => ENNReal.ofReal (E6.areaDensK γ (Z q) k z)) from rfl,
          withDensity_apply _ hK, ← lintegral_indicator hK]
        rfl
      simp_rw [e]
      exact Measurable.lintegral_prod_right' (((measurable_dens hZ γ k).ennreal_ofReal).indicator hS)
    have hset : {q : α | ∀ᶠ k in atTop, areaApprox γ (Z q) k (hbK (r q) m) < ∞} =
        ⋃ K : ℕ, ⋂ k ≥ K, {q | areaApprox γ (Z q) k (hbK (r q) m) < ∞} := by
      ext q; simp only [eventually_atTop, mem_setOf_eq, mem_iUnion, mem_iInter, ge_iff_le]
    rw [hset]
    exact MeasurableSet.iUnion fun K => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hmeas k) measurable_const
  · -- convergence of the countably many test integrals
    refine MeasurableSet.iInter fun n => ?_
    have hset : {q : α | ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, hbCut (r q) n z * g z
        ∂(areaApprox γ (Z q) k)) atTop (𝓝 l)} = ⋂ g ∈ famF, {q | ∃ l, Tendsto (fun k =>
        ∫ z, hbCut (r q) n z * g z ∂(areaApprox γ (Z q) k)) atTop (𝓝 l)} := by
      ext q; simp only [mem_setOf_eq, mem_iInter]
    rw [hset]
    refine MeasurableSet.biInter famF_countable fun g hg => ?_
    have hgm : Measurable g := (famF_dense.1 g hg).1.measurable
    refine StronglyMeasurable.measurableSet_exists_tendsto fun k => ?_
    have e : ∀ q, ∫ z, hbCut (r q) n z * g z ∂(areaApprox γ (Z q) k) =
        ∫ z, E6.areaDensK γ (Z q) k z * (hbCut (r q) n z * g z) ∂(volume.restrict H) :=
      fun q => E6.integral_areaApprox_eq γ (Z q) k _
    simp_rw [e]
    refine StronglyMeasurable.integral_prod_right' (f := fun p : α × ℂ =>
      E6.areaDensK γ (Z p.1) k p.2 * (hbCut (r p.1) n p.2 * g p.2)) ?_
    refine ((measurable_dens hZ γ k).mul ((?_ : Measurable fun p : α × ℂ =>
      hbCut (r p.1) n p.2).mul (hgm.comp measurable_snd))).stronglyMeasurable
    unfold hbCut
    fun_prop

end ExA

end Prop16Lit

end QuantumZipper
