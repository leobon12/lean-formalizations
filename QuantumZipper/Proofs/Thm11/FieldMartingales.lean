import QuantumZipper.Proofs.Thm11.FrozenMartingales
import QuantumZipper.Proofs.ItoLite.OptionalStopping
import QuantumZipper.Proofs.ItoLite.Exponential
import QuantumZipper.Proofs.ItoLite.Oscillation
import QuantumZipper.Proofs.GFF.Admissible

/-!
# Theorem 1.1, MF-3, MF-4 (kernel part) and MF-5: the smeared frozen field

Blueprint `blueprint/THM11_BLUEPRINT.md`, §6.  Fix a real test function `ρ`, continuous with
compact support inside `{Im ≥ δ}`, and `0 < c ≤ δ`.  With `𝔥^δ = frozenField` and
`K^δ = frozenKernel` (file `FrozenMartingales.lean`) put

* `X^δ_t := ∫ ρ(a) 𝔥^δ_t(a) da` (`fieldX`),
* `V^δ_t := ∬ ρ(a) ρ(b) K^δ_t(a,b) da db` (`fieldV`, integral over `ℂ × ℂ`).

Main results:

* `measurable_frozenField_joint`, `measurable_frozenKernel_joint`: joint measurability of the
  frozen field and kernel with respect to `Borel ⊗ 𝓕_t`;
* `frozenKernel_nonneg`, `frozenKernel_le_greenH`, `abs_frozenKernel_sub_le` (MF-4, kernel);
* `fieldX_martingale`, `fieldXV_martingale` (MF-3);
* `abs_fieldX_sub_le`, `abs_fieldV_sub_le`, `abs_fieldV_le` (MF-4, integrated);
* `integral_exp_fieldX_fieldV` (MF-5).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace FieldMart

open FrozenMart

/-! ## A. Joint measurability of frozen values -/

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The filtration `m_α ⊗ 𝓕_t` on `α × Ω`. -/
def prodFiltration {α : Type*} [mα : MeasurableSpace α] (𝓕 : Filtration ℝ≥0 mΩ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (α × Ω)) where
  seq t := mα.prod (𝓕 t)
  mono' _ _ h := sup_le_sup_left (MeasurableSpace.comap_mono (𝓕.mono h)) _
  le' t := sup_le_sup_left (MeasurableSpace.comap_mono (𝓕.le t)) _

/-- A process continuous in time and jointly measurable (for `m_α ⊗ 𝓕_t`) in the parameter and
`ω`, stopped at its (capped) hitting time of a closed set and at `t`, is jointly measurable. -/
theorem measurable_stopped_joint {α β : Type*} [mα : MeasurableSpace α] [PseudoMetricSpace β]
    [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (𝓕 : Filtration ℝ≥0 mΩ) (U : α → ℝ≥0 → Ω → β)
    (hU : ∀ t, Measurable[mα.prod (𝓕 t)] (fun p : α × Ω => U p.1 t p.2))
    (hc : ∀ a ω, Continuous fun t => U a t ω) {K : Set β} (hK : IsClosed K) (T t : ℝ≥0) :
    Measurable[mα.prod (𝓕 t)]
      (fun p : α × Ω => U p.1 (min t (hittingBtwn (U p.1) K 0 T p.2)) p.2) := by
  set 𝓖 := prodFiltration (α := α) 𝓕
  set V : ℝ≥0 → α × Ω → β := fun t p => U p.1 t p.2 with hV
  have hVad : Adapted 𝓖 V := hU
  have hVc : ∀ p, Continuous fun t => V t p := fun p => hc p.1 p.2
  have hτ := ItoLite.isStoppingTime_hittingBtwn_of_isClosed hVad hVc hK T
  have hτt := hτ.min_const t
  have hprog : IsStronglyProgressive 𝓖 V :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hU t).stronglyMeasurable) hVc
  have h := stronglyMeasurable_stoppedValue_of_le hprog hτt (n := t) (fun _ => min_le_right _ _)
  have e : stoppedValue V (fun p => min ((hittingBtwn V K 0 T p : ℝ≥0) : WithTop ℝ≥0)
      (t : WithTop ℝ≥0)) = fun p => U p.1 (min t (hittingBtwn (U p.1) K 0 T p.2)) p.2 := by
    funext p
    simp only [stoppedValue]
    rw [← WithTop.coe_min, min_comm]
    rfl
  rw [← e]
  exact h.measurable

/-- The Bochner integral in a parameter of a jointly measurable function is measurable. -/
theorem measurable_integral_joint {α Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω']
    {μ : Measure α} [SFinite μ] {f : α → Ω' → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun ω => ∫ a, f a ω ∂μ) :=
  hf.stronglyMeasurable.integral_prod_left.measurable

theorem measurable_fzU_joint {Ω : Type*} [MeasurableSpace Ω] {κ c : ℝ} (hc : 0 < c)
    {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0)
    (hBm : ∀ r : ℝ≥0, r ≤ t → Measurable (B r)) :
    Measurable (fun p : ℂ × Ω => fzU κ c B p.1 t p.2) := by
  obtain ⟨h1, h2⟩ := measurable_tamed_drive κ hc B hBc t.coe_nonneg
    (fun r hr => hBm r (by exact_mod_cast hr))
  exact h1.prodMk h2

theorem measurable_fzU2_joint {Ω : Type*} [MeasurableSpace Ω] {κ c : ℝ} (hc : 0 < c)
    {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0)
    (hBm : ∀ r : ℝ≥0, r ≤ t → Measurable (B r)) :
    Measurable (fun p : (ℂ × ℂ) × Ω => fzU2 κ c B p.1.1 p.1.2 t p.2) := by
  have h := measurable_fzU_joint (κ := κ) hc hBc t hBm
  exact (h.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    (h.comp (measurable_fst.snd.prodMk measurable_snd))

theorem measurable_fzPhi (κ : ℝ) : Measurable (fzPhi κ) := by
  unfold fzPhi h0fwd
  exact ((Complex.measurable_arg.comp measurable_fst).const_mul _).sub
    (measurable_snd.const_mul _)

end Generic

section Joint

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- Joint measurability of `(a, ω) ↦ 𝔥^δ_t(a)(ω)` for `Borel ⊗ 𝓕_t`. -/
theorem measurable_frozenField_joint (hBc : ∀ ω, Continuous (B · ω)) (𝓕 : Filtration ℝ≥0 mΩ)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hc : 0 < c) (T t : ℝ≥0) :
    Measurable[(inferInstance : MeasurableSpace ℂ).prod (𝓕 t)]
      (fun p : ℂ × Ω => frozenField κ c δ T B p.1 t p.2) := by
  have hU : ∀ s, Measurable[(inferInstance : MeasurableSpace ℂ).prod (𝓕 s)]
      (fun p : ℂ × Ω => fzU κ c B p.1 s p.2) := fun s =>
    @measurable_fzU_joint Ω (𝓕 s) κ c hc B hBc s
      (fun r hr => (hBad r).mono (𝓕.mono hr) le_rfl)
  have h := measurable_stopped_joint 𝓕 (fun a => fzU κ c B a) hU
    (fun a ω => continuous_fzU hBc hc a ω) (isClosed_fzCl δ) T t
  exact (measurable_fzPhi κ).comp h

/-- Joint measurability of `((a,b), ω) ↦ K^δ_t(a,b)(ω)` for `Borel ⊗ 𝓕_t`. -/
theorem measurable_frozenKernel_joint (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hc : 0 < c)
    (T t : ℝ≥0) :
    Measurable[(inferInstance : MeasurableSpace (ℂ × ℂ)).prod (𝓕 t)]
      (fun p : (ℂ × ℂ) × Ω => frozenKernel κ c δ T B p.1.1 p.1.2 t p.2) := by
  have hU : ∀ s, Measurable[(inferInstance : MeasurableSpace (ℂ × ℂ)).prod (𝓕 s)]
      (fun p : (ℂ × ℂ) × Ω => fzU2 κ c B p.1.1 p.1.2 s p.2) := fun s =>
    @measurable_fzU2_joint Ω (𝓕 s) κ c hc B hBc s
      (fun r hr => (hBad r).mono (𝓕.mono hr) le_rfl)
  have h := measurable_stopped_joint 𝓕 (fun q : ℂ × ℂ => fzU2 κ c B q.1 q.2) hU
    (fun q ω => (continuous_fzU hBc hc q.1 ω).prodMk (continuous_fzU hBc hc q.2 ω))
    (isClosed_fzCl2 δ) T t
  have e : (fun p : (ℂ × ℂ) × Ω => frozenKernel κ c δ T B p.1.1 p.1.2 t p.2) =
      (fun x : E2 => greenH x.1.1 x.2.1) ∘ (fun p : (ℂ × ℂ) × Ω =>
        fzU2 κ c B p.1.1 p.1.2 (min t (hittingBtwn (fzU2 κ c B p.1.1 p.1.2) (fzCl2 δ) 0 T p.2))
          p.2) := by
    funext p
    simp only [Function.comp, fzCl2, hittingBtwn_union]
    rfl
  rw [e]
  exact (measurable_greenH.comp (measurable_fst.fst.prodMk measurable_snd.fst)).comp h

end Joint

/-! ## B. MF-4, kernel part: `0 ≤ K^δ ≤ G(a,b)` and `|ΔK^δ| ≤ (4/δ²) Δt` (via FD-3) -/

theorem im_two_div_nonpos_abs_le {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : δ ≤ z.im) :
    (2 / z).im ≤ 0 ∧ |(2 / z).im| ≤ 2 / δ := by
  have hzi : 0 < z.im := hδ.trans_le hz
  have hN : z.im * z.im ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg z.re]
  have hNpos : 0 < Complex.normSq z := (mul_pos hzi hzi).trans_le hN
  have e : (2 / z).im = -(2 * z.im / Complex.normSq z) := by
    rw [Complex.div_im]; simp
  rw [e]
  have h0 : 0 ≤ 2 * z.im / Complex.normSq z := by positivity
  refine ⟨by linarith, ?_⟩
  rw [abs_neg, abs_of_nonneg h0, div_le_div_iff₀ hNpos hδ]
  nlinarith [mul_le_mul_of_nonneg_left hz hzi.le]

section Kernel

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

theorem im_fzZ_ge_of_le_frozenTime (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    {a : ℂ} (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω) {u : ℝ≥0}
    (hu : u ≤ frozenTime κ c δ T B a ω) : δ ≤ (fzZ κ c B a u ω).im := by
  have h := (fzU_frozen_mem (κ := κ) hBc hc hδa (T := T) u ω).1
  rw [min_eq_left hu] at h
  exact h

/-- Before `σ_a ∧ σ_b` both tamed points are forward solutions in `{Im ≥ δ}`, so FD-3 applies. -/
theorem kernel_hasDerivWithinAt (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a b : ℂ} (hδa : δ ≤ a.im) (hδb : δ ≤ b.im) (hab : a ≠ b) (T : ℝ≥0) (ω : Ω) :
    ∀ s ∈ Icc (0 : ℝ) (min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) : ℝ≥0),
      HasDerivWithinAt
        (fun s => greenH (tamedZ (drive κ B ω) c a s) (tamedZ (drive κ B ω) c b s))
        (-((2 / tamedZ (drive κ B ω) c a s).im * (2 / tamedZ (drive κ B ω) c b s).im))
        (Icc 0 (min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) : ℝ≥0)) s ∧
      δ ≤ (tamedZ (drive κ B ω) c a s).im ∧ δ ≤ (tamedZ (drive κ B ω) c b s).im := by
  have hδ : 0 < δ := hc.trans_le hcδ
  set ρ := min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) with hρ
  have hW := continuous_drive_path (κ := κ) hBc ω
  have him : ∀ a' : ℂ, δ ≤ a'.im → ρ ≤ frozenTime κ c δ T B a' ω →
      ∀ s ∈ Icc (0 : ℝ) ρ, δ ≤ (tamedZ (drive κ B ω) c a' s).im := by
    intro a' h1 h2 s hs
    have hu : s.toNNReal ≤ frozenTime κ c δ T B a' ω :=
      (show s.toNNReal ≤ ρ by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2).trans h2
    have h := im_fzZ_ge_of_le_frozenTime hBc hc h1 ω hu
    unfold fzZ at h
    rwa [Real.coe_toNNReal _ hs.1] at h
  have ha := him a hδa (min_le_left _ _)
  have hb := him b hδb (min_le_right _ _)
  have hsa := isForwardSol_tamedZ hW hc ρ.coe_nonneg (fun s hs => hcδ.trans (ha s hs))
  have hsb := isForwardSol_tamedZ hW hc ρ.coe_nonneg (fun s hs => hcδ.trans (hb s hs))
  intro s hs
  exact ⟨FwdClock.sol_greenH_hasDerivWithinAt hW (hδ.trans_le hδa) (hδ.trans_le hδb) hab hsa hsb
    hs, ha s hs, hb s hs⟩

/-- **MF-4 (kernel), upper bound.** `K^δ_t(a,b) ≤ G(a,b)`. -/
theorem frozenKernel_le_greenH (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a b : ℂ} (hδa : δ ≤ a.im) (hδb : δ ≤ b.im) (hab : a ≠ b) (T : ℝ≥0) (t : ℝ≥0)
    (ω : Ω) : frozenKernel κ c δ T B a b t ω ≤ greenH a b := by
  have hδ : 0 < δ := hc.trans_le hcδ
  have hW := continuous_drive_path (κ := κ) hBc ω
  have hd := kernel_hasDerivWithinAt (κ := κ) hBc hc hcδ hδa hδb hab T ω
  set ρ := min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) with hρ
  set g := fun s => greenH (tamedZ (drive κ B ω) c a s) (tamedZ (drive κ B ω) c b s) with hg
  have hanti : AntitoneOn g (Icc 0 (ρ : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun s hs => (hd s hs).1.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).1.mono interior_subset)
      (fun s hs => by
        obtain ⟨_, h1, h2⟩ := hd s (interior_subset hs)
        have := mul_nonneg_of_nonpos_of_nonpos (im_two_div_nonpos_abs_le hδ h1).1
          (im_two_div_nonpos_abs_le hδ h2).1
        linarith)
  have h0 : g 0 = greenH a b := by
    simp only [hg, tamedZ, tamedUnc_zero hW hc]
    exact FwdClock.greenH_sub_ofReal a b _
  show g ((min t ρ : ℝ≥0) : ℝ) ≤ greenH a b
  rw [← h0]
  have hu0 : (0 : ℝ) ≤ ((min t ρ : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have huρ : ((min t ρ : ℝ≥0) : ℝ) ≤ ρ := by exact_mod_cast min_le_right t ρ
  exact hanti (left_mem_Icc.2 ρ.coe_nonneg) ⟨hu0, huρ⟩ hu0

/-- **MF-4 (kernel), lower bound.** `0 ≤ K^δ_t(a,b)`. -/
theorem frozenKernel_nonneg (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a b : ℂ} (hδa : δ ≤ a.im) (hδb : δ ≤ b.im) (hab : a ≠ b) (T : ℝ≥0) (t : ℝ≥0)
    (ω : Ω) : 0 ≤ frozenKernel κ c δ T B a b t ω := by
  have hδ : 0 < δ := hc.trans_le hcδ
  have hW := continuous_drive_path (κ := κ) hBc ω
  have hd := kernel_hasDerivWithinAt (κ := κ) hBc hc hcδ hδa hδb hab T ω
  set ρ := min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) with hρ
  set u : ℝ≥0 := min t ρ with hu
  have huρ : (u : ℝ) ≤ ρ := by exact_mod_cast min_le_right t ρ
  have hsep := norm_sub_tamedZ_ge hW hc u.coe_nonneg
    (fun s hs => hcδ.trans (hd s ⟨hs.1, hs.2.trans huρ⟩).2.1)
    (fun s hs => hcδ.trans (hd s ⟨hs.1, hs.2.trans huρ⟩).2.2)
  have hpos : 0 < ‖a - b‖ * Real.exp (-(2 / c ^ 2 * (u : ℝ))) :=
    mul_pos (norm_pos_iff.2 (sub_ne_zero.2 hab)) (Real.exp_pos _)
  have hne : tamedZ (drive κ B ω) c a u ≠ tamedZ (drive κ B ω) c b u := fun h => by
    rw [h, sub_self, norm_zero] at hsep; linarith
  have hmem := hd u ⟨u.coe_nonneg, huρ⟩
  exact greenH_nonneg (show 0 ≤ (tamedZ (drive κ B ω) c a u).im by linarith [hmem.2.1])
    (show 0 ≤ (tamedZ (drive κ B ω) c b u).im by linarith [hmem.2.2]) hne

/-- **MF-4 (kernel), increments.** `|K^δ_{t'} − K^δ_t| ≤ (4/δ²)(t' − t)` for `t ≤ t'`. -/
theorem abs_frozenKernel_sub_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a b : ℂ} (hδa : δ ≤ a.im) (hδb : δ ≤ b.im) (hab : a ≠ b) (T : ℝ≥0) (ω : Ω)
    {t t' : ℝ≥0} (htt : t ≤ t') :
    |frozenKernel κ c δ T B a b t' ω - frozenKernel κ c δ T B a b t ω| ≤
      4 / δ ^ 2 * ((t' : ℝ) - t) := by
  have hδ : 0 < δ := hc.trans_le hcδ
  have hd := kernel_hasDerivWithinAt (κ := κ) hBc hc hcδ hδa hδb hab T ω
  set ρ := min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) with hρ
  set g := fun s => greenH (tamedZ (drive κ B ω) c a s) (tamedZ (drive κ B ω) c b s) with hg
  have hmem : ∀ t : ℝ≥0, ((min t ρ : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) ρ := fun t =>
    ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right t ρ⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (C := 4 / δ ^ 2)
    (fun s hs => (hd s hs).1)
    (fun s hs => by
      obtain ⟨_, h1, h2⟩ := hd s hs
      have e1 := (im_two_div_nonpos_abs_le hδ h1).2
      have e2 := (im_two_div_nonpos_abs_le hδ h2).2
      rw [Real.norm_eq_abs, abs_neg, abs_mul]
      calc _ ≤ 2 / δ * (2 / δ) := mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
        _ = 4 / δ ^ 2 := by ring)
    (convex_Icc _ _) (hmem t) (hmem t')
  show |g ((min t' ρ : ℝ≥0) : ℝ) - g ((min t ρ : ℝ≥0) : ℝ)| ≤ _
  rw [← Real.norm_eq_abs]
  refine hmvt.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Real.norm_eq_abs, NNReal.coe_min t' ρ, NNReal.coe_min t ρ]
  have hdt : (0 : ℝ) ≤ (t' : ℝ) - t := sub_nonneg.2 (by exact_mod_cast htt)
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, abs_of_nonneg hdt]
  exact max_le le_rfl hdt

end Kernel

/-! ## C. Test functions, the diagonal, and Fubini -/

section TestFn

variable {ρ : ℂ → ℝ} {δ : ℝ}

theorem integrable_rho_mul (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) {C : ℝ}
    (hb : ∀ a : ℂ, δ ≤ a.im → |g a| ≤ C) : Integrable (fun a => ρ a * g a) := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  refine Integrable.mono' (hρi.abs.mul_const C) (hρc.aestronglyMeasurable.mul hg)
    (ae_of_all _ fun a => ?_)
  by_cases h : a.im < δ
  · simp [hρδ a h]
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hb a (not_lt.1 h)) (abs_nonneg _)

/-- The diagonal of `ℂ × ℂ` is Lebesgue-null. -/
theorem volume_diag_eq_zero : ((volume : Measure ℂ).prod volume) {p | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (show MeasurableSet {p : ℂ × ℂ | p.1 = p.2} from
    measurableSet_diagonal)]
  have e : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := fun x => by
    ext y; simp [eq_comm]
  simp only [e, measure_singleton, lintegral_zero]

theorem ae_ne_diag : ∀ᵐ p ∂((volume : Measure ℂ).prod volume), p.1 ≠ p.2 := by
  rw [ae_iff]; simpa using volume_diag_eq_zero

theorem ae_ne_diag_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] :
    ∀ᵐ q ∂(((volume : Measure ℂ).prod volume).prod P), q.1.1 ≠ q.1.2 := by
  rw [ae_iff]
  have e : {q : (ℂ × ℂ) × Ω | ¬ q.1.1 ≠ q.1.2} = {p : ℂ × ℂ | p.1 = p.2} ×ˢ univ := by
    ext q; simp
  rw [e, Measure.prod_prod, volume_diag_eq_zero, zero_mul]

/-- `∬ |ρ(a)| |ρ(b)| G(a,b) da db < ∞`. -/
theorem integrable_rho_rho_greenH (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hδ : 0 < δ)
    (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) :
    Integrable (fun p : ℂ × ℂ => |ρ p.1| * |ρ p.2| * greenH p.1 p.2)
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨M, hM⟩ := hρc.bounded_above_of_compact_support hρs
  set f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal |ρ x| with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (continuous_abs.comp hρc).measurable
  have hsupp : tsupport ρ ⊆ {z : ℂ | δ ≤ z.im} :=
    closure_minimal (fun z hz => not_lt.1 fun h => hz (hρδ z h))
      (isClosed_le continuous_const Complex.continuous_im)
  have hμ : IsAdmissibleH (volume.withDensity f) :=
    isAdmissibleH_withDensity hfm (M := ENNReal.ofReal M) ENNReal.ofReal_lt_top
      (fun x => ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hM x)) hρs
      (fun z hz => (show (0 : ℝ) ≤ z.im from hδ.le.trans (hsupp hz)))
      (fun x hx => by
        have : ρ x = 0 := by
          by_contra h; exact hx (subset_tsupport _ h)
        simp [hf, this])
  have h := integrable_greenH_prod hμ hμ
  rw [prod_withDensity hfm hfm] at h
  have hm2 : Measurable (fun z : ℂ × ℂ => f z.1 * f z.2) :=
    (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
  have h' := (integrable_withDensity_iff hm2
    (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).1 h
  refine h'.congr (ae_of_all _ fun p => ?_)
  simp only [hf, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  ring

theorem integrable_rho_rho_mul (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hδ : 0 < δ)
    (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) {g : ℂ × ℂ → ℝ}
    (hg : AEStronglyMeasurable g ((volume : Measure ℂ).prod volume)) {C : ℝ}
    (hb : ∀ p : ℂ × ℂ, p.1 ≠ p.2 → δ ≤ p.1.im → δ ≤ p.2.im → |g p| ≤ C + greenH p.1 p.2) :
    Integrable (fun p : ℂ × ℂ => ρ p.1 * ρ p.2 * g p) ((volume : Measure ℂ).prod volume) := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  refine Integrable.mono' (((hρi.abs.mul_prod hρi.abs).mul_const C).add
    (integrable_rho_rho_greenH hρc hρs hδ hρδ))
    (((hρc.comp continuous_fst).aestronglyMeasurable.mul
      (hρc.comp continuous_snd).aestronglyMeasurable).mul hg) ?_
  filter_upwards [ae_ne_diag] with p hp
  by_cases ha : p.1.im < δ
  · simp [hρδ _ ha]
  by_cases hb' : p.2.im < δ
  · simp [hρδ _ hb']
  push Not at ha hb'
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (hb p hp ha hb') (by positivity)

end TestFn

theorem measurable_integral_mul_joint {α Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω']
    {μ : Measure α} [SFinite μ] {ρ : α → ℝ} (hρ : Measurable ρ) {F : α × Ω' → ℝ}
    (hF : Measurable F) : Measurable (fun ω => ∫ a, ρ a * F (a, ω) ∂μ) :=
  measurable_integral_joint (f := fun a ω => ρ a * F (a, ω)) ((hρ.comp measurable_fst).mul hF)

theorem measurable_pair_of {Ω' : Type*} [MeasurableSpace Ω'] {F : ℂ × Ω' → ℝ} (hF : Measurable F)
    {K : (ℂ × ℂ) × Ω' → ℝ} (hK : Measurable K) :
    Measurable (fun q : (ℂ × ℂ) × Ω' => F (q.1.1, q.2) * F (q.1.2, q.2) + K q) :=
  ((hF.comp (measurable_fst.fst.prodMk measurable_snd)).mul
    (hF.comp (measurable_fst.snd.prodMk measurable_snd))).add hK

theorem setIntegral_integral_swap' {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure α} [SFinite μ] {P : Measure Ω} [SFinite P] {f : α → Ω → ℝ}
    (hf : Integrable (Function.uncurry f) (μ.prod P)) (A : Set Ω) :
    ∫ ω in A, ∫ a, f a ω ∂μ ∂P = ∫ a, ∫ ω in A, f a ω ∂P ∂μ := by
  have h : Integrable (Function.uncurry f) (μ.prod (P.restrict A)) := by
    have := hf.restrict (s := univ ×ˢ A)
    rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
  exact (integral_integral_swap h).symm

/-! ## D. MF-3: the smeared field and its variance process are martingales -/

section Fields

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- `X^δ_t = ∫ ρ(a) 𝔥^δ_t(a) da`. -/
def fieldX (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ρ : ℂ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ a, ρ a * frozenField κ c δ T B a t ω

/-- `V^δ_t = ∬ ρ(a) ρ(b) K^δ_t(a,b) da db`. -/
def fieldV (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ρ : ℂ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ p, ρ p.1 * ρ p.2 * frozenKernel κ c δ T B p.1 p.2 t ω ∂((volume : Measure ℂ).prod volume)

/-- `∬ ρ(a) ρ(b) N_t(a,b) da db`, `N = 𝔥^δ(a)𝔥^δ(b) + K^δ(a,b)` (equal to `(X^δ)² + V^δ`). -/
def fieldQ (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ρ : ℂ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ p, ρ p.1 * ρ p.2 * frozenPair κ c δ T B p.1 p.2 t ω ∂((volume : Measure ℂ).prod volume)

theorem measurable_frozenField_amb (hBc : ∀ ω, Continuous (B · ω)) (𝓕 : Filtration ℝ≥0 mΩ)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hc : 0 < c) (T t : ℝ≥0) :
    Measurable (fun p : ℂ × Ω => frozenField κ c δ T B p.1 t p.2) :=
  (measurable_frozenField_joint hBc 𝓕 hBad hc T t).mono ((prodFiltration (α := ℂ) 𝓕).le t)
    le_rfl

theorem measurable_frozenKernel_amb (hBc : ∀ ω, Continuous (B · ω)) (𝓕 : Filtration ℝ≥0 mΩ)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hc : 0 < c) (T t : ℝ≥0) :
    Measurable (fun p : (ℂ × ℂ) × Ω => frozenKernel κ c δ T B p.1.1 p.1.2 t p.2) :=
  (measurable_frozenKernel_joint hBc 𝓕 hBad hc T t).mono
    ((prodFiltration (α := ℂ × ℂ) 𝓕).le t) le_rfl

theorem norm_rho_rho_pair_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {ρ : ℂ → ℝ} (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) {a b : ℂ} (hab : a ≠ b)
    (T t : ℝ≥0) (ω : Ω) :
    ‖ρ a * ρ b * frozenPair κ c δ T B a b t ω‖ ≤
      |ρ a| * |ρ b| * (fzBound κ c T * fzBound κ c T) + |ρ a| * |ρ b| * greenH a b := by
  by_cases ha : a.im < δ
  · simp [hρδ a ha]
  by_cases hb : b.im < δ
  · simp [hρδ b hb]
  push Not at ha hb
  have hFa := abs_frozenField_le (κ := κ) hBc hc ha T t ω
  have hFb := abs_frozenField_le (κ := κ) hBc hc hb T t ω
  have hK0 := frozenKernel_nonneg (κ := κ) hBc hc hcδ ha hb hab T t ω
  have hK1 := frozenKernel_le_greenH (κ := κ) hBc hc hcδ ha hb hab T t ω
  rw [Real.norm_eq_abs, abs_mul, abs_mul, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold frozenPair
  calc _ ≤ |frozenField κ c δ T B a t ω * frozenField κ c δ T B b t ω|
        + |frozenKernel κ c δ T B a b t ω| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hK0]
        exact add_le_add (mul_le_mul hFa hFb (abs_nonneg _) ((abs_nonneg _).trans hFa)) hK1

/-- **MF-3 (first martingale).** `X^δ` is a martingale. -/
theorem fieldX_martingale (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ) {ρ : ℂ → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T : ℝ≥0) :
    Martingale (fieldX κ c δ T B ρ) 𝓕 P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hFm := measurable_frozenField_amb (κ := κ) (δ := δ) hBc 𝓕 hBad hc T
  have hint : ∀ t, Integrable (fun p : ℂ × Ω => ρ p.1 * frozenField κ c δ T B p.1 t p.2)
      ((volume : Measure ℂ).prod P) := by
    intro t
    refine Integrable.mono' (hρi.abs.mul_prod (integrable_const (fzBound κ c T)))
      ((hρc.measurable.comp measurable_fst).mul (hFm t)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    by_cases h : p.1.im < δ
    · simp [hρδ _ h]
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_frozenField_le hBc hc (not_lt.1 h) T t p.2)
        (abs_nonneg _)
  refine ItoLite.martingale_of_setIntegral_eq_nnreal (fun t => ?_)
    (fun t => (hint t).integral_prod_right) ?_
  · exact (@measurable_integral_mul_joint ℂ Ω _ (𝓕 t) volume _ ρ hρc.measurable
      (fun p => frozenField κ c δ T B p.1 t p.2)
      (measurable_frozenField_joint hBc 𝓕 hBad hc T t)).stronglyMeasurable
  · intro s t hst A hA
    have e1 := setIntegral_integral_swap'
      (f := fun a ω => ρ a * frozenField κ c δ T B a s ω) (hint s) A
    have e2 := setIntegral_integral_swap'
      (f := fun a ω => ρ a * frozenField κ c δ T B a t ω) (hint t) A
    beta_reduce at e1 e2
    unfold fieldX
    rw [e1, e2]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [integral_const_mul]
    by_cases h : a.im < δ
    · simp [hρδ a h]
    · rw [(frozenField_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ (not_lt.1 h) T).setIntegral_eq
        hst hA]

set_option maxHeartbeats 1000000 in
/-- Pointwise: `(X^δ_t)² + V^δ_t = ∬ ρρ N_t`. -/
theorem fieldX_sq_add_fieldV (hBc : ∀ ω, Continuous (B · ω)) (𝓕 : Filtration ℝ≥0 mΩ)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hc : 0 < c) (hcδ : c ≤ δ) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0)
    (T t : ℝ≥0) (ω : Ω) :
    fieldX κ c δ T B ρ t ω ^ 2 + fieldV κ c δ T B ρ t ω = fieldQ κ c δ T B ρ t ω := by
  have hδ : 0 < δ := hc.trans_le hcδ
  have hFa : Measurable (fun a => frozenField κ c δ T B a t ω) :=
    (measurable_frozenField_amb (κ := κ) (δ := δ) hBc 𝓕 hBad hc T t).comp
      (measurable_id.prodMk measurable_const)
  have h1 : Integrable (fun a => ρ a * frozenField κ c δ T B a t ω) :=
    integrable_rho_mul hρc hρs hρδ hFa.aestronglyMeasurable
      (fun a ha => abs_frozenField_le hBc hc ha T t ω)
  have h2 : Integrable (fun p : ℂ × ℂ => ρ p.1 * ρ p.2 * frozenKernel κ c δ T B p.1 p.2 t ω)
      ((volume : Measure ℂ).prod volume) :=
    integrable_rho_rho_mul hρc hρs hδ hρδ (C := 0)
      ((measurable_frozenKernel_amb (κ := κ) (δ := δ) hBc 𝓕 hBad hc T t).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (fun p hne ha hb => by
        rw [zero_add, abs_of_nonneg (frozenKernel_nonneg (κ := κ) hBc hc hcδ ha hb hne T t ω)]
        exact frozenKernel_le_greenH (κ := κ) hBc hc hcδ ha hb hne T t ω)
  have hsq : fieldX κ c δ T B ρ t ω ^ 2 = ∫ z, (ρ z.1 * frozenField κ c δ T B z.1 t ω) *
      (ρ z.2 * frozenField κ c δ T B z.2 t ω) ∂((volume : Measure ℂ).prod volume) := by
    rw [integral_prod_mul (fun a => ρ a * frozenField κ c δ T B a t ω)
      (fun a => ρ a * frozenField κ c δ T B a t ω), sq]
    rfl
  have hsum : ∫ z, ((ρ z.1 * frozenField κ c δ T B z.1 t ω) *
        (ρ z.2 * frozenField κ c δ T B z.2 t ω)
        + ρ z.1 * ρ z.2 * frozenKernel κ c δ T B z.1 z.2 t ω) ∂((volume : Measure ℂ).prod volume)
      = (∫ z, (ρ z.1 * frozenField κ c δ T B z.1 t ω) *
        (ρ z.2 * frozenField κ c δ T B z.2 t ω) ∂((volume : Measure ℂ).prod volume))
        + ∫ z, ρ z.1 * ρ z.2 * frozenKernel κ c δ T B z.1 z.2 t ω
          ∂((volume : Measure ℂ).prod volume) :=
    integral_add (h1.mul_prod h1) h2
  have hQ : fieldQ κ c δ T B ρ t ω = ∫ z, ((ρ z.1 * frozenField κ c δ T B z.1 t ω) *
        (ρ z.2 * frozenField κ c δ T B z.2 t ω)
        + ρ z.1 * ρ z.2 * frozenKernel κ c δ T B z.1 z.2 t ω)
        ∂((volume : Measure ℂ).prod volume) := by
    unfold fieldQ frozenPair
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    ring
  rw [hQ, hsum, hsq]
  rfl

theorem fieldQ_martingale (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ) {ρ : ℂ → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T : ℝ≥0) :
    Martingale (fieldQ κ c δ T B ρ) 𝓕 P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < δ := hc.trans_le hcδ
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hNm : ∀ t, Measurable[(inferInstance : MeasurableSpace (ℂ × ℂ)).prod (𝓕 t)]
      (fun q : (ℂ × ℂ) × Ω => frozenPair κ c δ T B q.1.1 q.1.2 t q.2) := fun t =>
    @measurable_pair_of Ω (𝓕 t) _ (measurable_frozenField_joint hBc 𝓕 hBad hc T t) _
      (measurable_frozenKernel_joint hBc 𝓕 hBad hc T t)
  have hNm' : ∀ t, Measurable (fun q : (ℂ × ℂ) × Ω => frozenPair κ c δ T B q.1.1 q.1.2 t q.2) :=
    fun t => (hNm t).mono ((prodFiltration (α := ℂ × ℂ) 𝓕).le t) le_rfl
  have hbound : Integrable (fun p : ℂ × ℂ => |ρ p.1| * |ρ p.2| * (fzBound κ c T * fzBound κ c T)
      + |ρ p.1| * |ρ p.2| * greenH p.1 p.2) ((volume : Measure ℂ).prod volume) :=
    ((hρi.abs.mul_prod hρi.abs).mul_const _).add (integrable_rho_rho_greenH hρc hρs hδ hρδ)
  have hint : ∀ t, Integrable
      (fun q : (ℂ × ℂ) × Ω => ρ q.1.1 * ρ q.1.2 * frozenPair κ c δ T B q.1.1 q.1.2 t q.2)
      (((volume : Measure ℂ).prod volume).prod P) := by
    intro t
    refine Integrable.mono' (hbound.mul_prod (integrable_const (1 : ℝ)))
      (((hρc.measurable.comp measurable_fst.fst).mul
        (hρc.measurable.comp measurable_fst.snd)).mul (hNm' t)).aestronglyMeasurable ?_
    filter_upwards [ae_ne_diag_prod P] with q hq
    rw [mul_one]
    exact norm_rho_rho_pair_le hBc hc hcδ hρδ hq T t q.2
  refine ItoLite.martingale_of_setIntegral_eq_nnreal (fun t => ?_)
    (fun t => (hint t).integral_prod_right) ?_
  · exact (@measurable_integral_mul_joint (ℂ × ℂ) Ω _ (𝓕 t) ((volume : Measure ℂ).prod volume) _
      (fun p => ρ p.1 * ρ p.2) ((hρc.measurable.comp measurable_fst).mul
        (hρc.measurable.comp measurable_snd))
      (fun q => frozenPair κ c δ T B q.1.1 q.1.2 t q.2) (hNm t)).stronglyMeasurable
  · intro s t hst A hA
    have e1 := setIntegral_integral_swap'
      (f := fun (p : ℂ × ℂ) (ω : Ω) => ρ p.1 * ρ p.2 * frozenPair κ c δ T B p.1 p.2 s ω) (hint s) A
    have e2 := setIntegral_integral_swap'
      (f := fun (p : ℂ × ℂ) (ω : Ω) => ρ p.1 * ρ p.2 * frozenPair κ c δ T B p.1 p.2 t ω) (hint t) A
    beta_reduce at e1 e2
    unfold fieldQ
    rw [e1, e2]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_diag] with p hp
    simp only [integral_const_mul]
    by_cases ha : p.1.im < δ
    · simp [hρδ _ ha]
    by_cases hb : p.2.im < δ
    · simp [hρδ _ hb]
    push Not at ha hb
    rw [(frozenPair_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ ha hb hp T).setIntegral_eq hst hA]

/-- **MF-3 (second martingale).** `(X^δ)² + V^δ` is a martingale. -/
theorem fieldXV_martingale (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ) {ρ : ℂ → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T : ℝ≥0) :
    Martingale (fun t ω => fieldX κ c δ T B ρ t ω ^ 2 + fieldV κ c δ T B ρ t ω) 𝓕 P := by
  have e : (fun t ω => fieldX κ c δ T B ρ t ω ^ 2 + fieldV κ c δ T B ρ t ω) =
      fieldQ κ c δ T B ρ := by
    funext t ω; exact fieldX_sq_add_fieldV hBc 𝓕 hBad hc hcδ hρc hρs hρδ T t ω
  rw [e]
  exact fieldQ_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ hρc hρs hρδ T

end Fields

/-! ## E. MF-4, integrated bounds -/

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

theorem abs_fieldX_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0)
    (T t : ℝ≥0) (ω : Ω) :
    |fieldX κ c δ T B ρ t ω| ≤ (∫ a, |ρ a|) * fzBound κ c T := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  unfold fieldX
  rw [← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hρi.abs.mul_const _) (ae_of_all _ fun a => ?_)
  by_cases h : a.im < δ
  · simp [hρδ a h]
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_frozenField_le hBc hc (not_lt.1 h) T t ω)
      (abs_nonneg _)

/-- **MF-4, field increments.** `|X^δ_{t'} − X^δ_t| ≤ ‖ρ‖₁ ((2/δ) osc_{[t,t']} B + K (t' − t))`. -/
theorem abs_fieldX_sub_le (hBc : ∀ ω, Continuous (B · ω)) (𝓕 : Filtration ℝ≥0 mΩ)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ)
    {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T : ℝ≥0) (ω : Ω) {t t' : ℝ≥0} (htt : t ≤ t') :
    |fieldX κ c δ T B ρ t' ω - fieldX κ c δ T B ρ t ω| ≤
      (∫ a, |ρ a|) * (2 / δ * bmOsc B t (t' - t) ω
        + (2 / Real.sqrt κ * (2 / c) / δ + |chiC κ| * (2 / c ^ 2)) * ((t' : ℝ) - t)) := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hi : ∀ s, Integrable (fun a => ρ a * frozenField κ c δ T B a s ω) := fun s =>
    integrable_rho_mul hρc hρs hρδ
      ((measurable_frozenField_amb (κ := κ) (δ := δ) hBc 𝓕 hBad hc T s).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (fun a ha => abs_frozenField_le hBc hc ha T s ω)
  unfold fieldX
  rw [← integral_sub (hi t') (hi t), ← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hρi.abs.mul_const _) (ae_of_all _ fun a => ?_)
  by_cases h : a.im < δ
  · simp [hρδ a h]
  · show ‖ρ a * frozenField κ c δ T B a t' ω - ρ a * frozenField κ c δ T B a t ω‖ ≤ |ρ a| * _
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_frozenField_sub_le hBc hκ hc hcδ (not_lt.1 h) T ω htt)
      (abs_nonneg _)

/-- **MF-4, variance increments.** `|V^δ_{t'} − V^δ_t| ≤ ‖ρ‖₁² (4/δ²)(t' − t)`. -/
theorem abs_fieldV_sub_le (hBc : ∀ ω, Continuous (B · ω)) (𝓕 : Filtration ℝ≥0 mΩ)
    (hBad : ∀ t, Measurable[𝓕 t] (B t)) {κ c δ : ℝ} (hc : 0 < c) (hcδ : c ≤ δ)
    {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T : ℝ≥0) (ω : Ω) {t t' : ℝ≥0} (htt : t ≤ t') :
    |fieldV κ c δ T B ρ t' ω - fieldV κ c δ T B ρ t ω| ≤
      (∫ a, |ρ a|) ^ 2 * (4 / δ ^ 2 * ((t' : ℝ) - t)) := by
  have hδ : 0 < δ := hc.trans_le hcδ
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hi : ∀ s, Integrable
      (fun p : ℂ × ℂ => ρ p.1 * ρ p.2 * frozenKernel κ c δ T B p.1 p.2 s ω)
      ((volume : Measure ℂ).prod volume) := fun s =>
    integrable_rho_rho_mul hρc hρs hδ hρδ (C := 0)
      ((measurable_frozenKernel_amb (κ := κ) (δ := δ) hBc 𝓕 hBad hc T s).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (fun p hne ha hb => by
        rw [zero_add, abs_of_nonneg (frozenKernel_nonneg (κ := κ) hBc hc hcδ ha hb hne T s ω)]
        exact frozenKernel_le_greenH (κ := κ) hBc hc hcδ ha hb hne T s ω)
  have hsq : (∫ a, |ρ a|) ^ 2 =
      ∫ p, |ρ p.1| * |ρ p.2| ∂((volume : Measure ℂ).prod volume) := by
    rw [integral_prod_mul (fun a => |ρ a|) (fun a => |ρ a|), sq]
  rw [hsq]
  unfold fieldV
  rw [← integral_sub (hi t') (hi t), ← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((hρi.abs.mul_prod hρi.abs).mul_const _) ?_
  filter_upwards [ae_ne_diag] with p hp
  by_cases ha : p.1.im < δ
  · simp [hρδ _ ha]
  by_cases hb : p.2.im < δ
  · simp [hρδ _ hb]
  push Not at ha hb
  show ‖ρ p.1 * ρ p.2 * frozenKernel κ c δ T B p.1 p.2 t' ω
      - ρ p.1 * ρ p.2 * frozenKernel κ c δ T B p.1 p.2 t ω‖ ≤ |ρ p.1| * |ρ p.2| * _
  rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_frozenKernel_sub_le hBc hc hcδ ha hb hp T ω htt)
    (by positivity)

/-- **MF-4, variance bound.** `|V^δ_t| ≤ ∬ |ρ(a)||ρ(b)| G(a,b)`. -/
theorem abs_fieldV_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) (hcδ : c ≤ δ)
    {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T t : ℝ≥0) (ω : Ω) :
    |fieldV κ c δ T B ρ t ω| ≤
      ∫ p, |ρ p.1| * |ρ p.2| * greenH p.1 p.2 ∂((volume : Measure ℂ).prod volume) := by
  have hδ : 0 < δ := hc.trans_le hcδ
  unfold fieldV
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (integrable_rho_rho_greenH hρc hρs hδ hρδ) ?_
  filter_upwards [ae_ne_diag] with p hp
  by_cases ha : p.1.im < δ
  · simp [hρδ _ ha]
  by_cases hb : p.2.im < δ
  · simp [hρδ _ hb]
  push Not at ha hb
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (frozenKernel_nonneg (κ := κ) hBc hc hcδ ha hb hp T t ω)]
  exact mul_le_mul_of_nonneg_left (frozenKernel_le_greenH (κ := κ) hBc hc hcδ ha hb hp T t ω)
    (by positivity)

end Bounds

/-! ## F. MF-5: the frozen exponential identity -/

/-- Martingales are stable under modification by strongly adapted a.e.-equal processes. -/
theorem martingale_of_ae_eq {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 m} {f g : ℝ≥0 → Ω → ℝ} (hf : Martingale f 𝓕 P)
    (hg : StronglyAdapted 𝓕 g) (hfg : ∀ t, g t =ᵐ[P] f t) : Martingale g 𝓕 P :=
  ⟨hg, fun i j hij => (condExp_congr_ae (hfg j)).trans ((hf.2 i j hij).trans (hfg i).symm)⟩

theorem cube_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

theorem rpow_three_halves_eq {s : ℝ} (hs : 0 ≤ s) : s ^ (((3 : ℕ) : ℝ) / 2) = s * Real.sqrt s := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hs (by norm_num)]
  norm_num

section MF5

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem fieldX_zero (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) (ρ : ℂ → ℝ)
    (T : ℝ≥0) {ω : Ω} (hω : B 0 ω = 0) :
    fieldX κ c δ T B ρ 0 ω = ∫ a, ρ a * h0fwd κ a := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  unfold fieldX
  congr 1
  funext a
  unfold frozenField fzPhi fzU fzZ fzA
  rw [min_eq_left zero_le, NNReal.coe_zero, tamedA_eq, intervalIntegral.integral_same,
    tamedZ, tamedUnc_zero hW hc, drive_zero hω]
  simp

theorem fieldV_zero (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) (ρ : ℂ → ℝ)
    (T : ℝ≥0) (ω : Ω) :
    fieldV κ c δ T B ρ 0 ω =
      ∫ p, ρ p.1 * ρ p.2 * greenH p.1 p.2 ∂((volume : Measure ℂ).prod volume) := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  unfold fieldV
  congr 1
  funext p
  unfold frozenKernel fzZ
  rw [min_eq_left zero_le, NNReal.coe_zero, tamedZ, tamedZ, tamedUnc_zero hW hc,
    tamedUnc_zero hW hc, FwdClock.greenH_sub_ofReal]

/-- **MF-5.** `E exp(i X^δ_T − V^δ_T/2) = exp(i (𝔥₀, ρ) − E₀(ρ)/2)`, with
`(𝔥₀, ρ) = ∫ ρ h0fwd κ` and `E₀(ρ) = ∬ ρ(a) ρ(b) G(a,b)`. -/
theorem integral_exp_fieldX_fieldV (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ) {ρ : ℂ → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρδ : ∀ a : ℂ, a.im < δ → ρ a = 0) (T : ℝ≥0) :
    ∫ ω, Complex.exp (Complex.I * (fieldX κ c δ T B ρ T ω : ℂ)
        - (fieldV κ c δ T B ρ T ω : ℂ) / 2) ∂P =
      Complex.exp (Complex.I * ((∫ a, ρ a * h0fwd κ a : ℝ) : ℂ)
        - ((∫ p, ρ p.1 * ρ p.2 * greenH p.1 p.2 ∂((volume : Measure ℂ).prod volume) : ℝ) : ℂ)
          / 2) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < δ := hc.trans_le hcδ
  have hBm : ∀ r, Measurable (B r) := fun r => (hBad r).mono (𝓕.le r) le_rfl
  set x₀ : ℝ := ∫ a, ρ a * h0fwd κ a with hx₀
  set v₀ : ℝ := ∫ p, ρ p.1 * ρ p.2 * greenH p.1 p.2 ∂((volume : Measure ℂ).prod volume)
    with hv₀
  set L : ℝ := ∫ a, |ρ a| with hL
  set E : ℝ := ∫ p, |ρ p.1| * |ρ p.2| * greenH p.1 p.2 ∂((volume : Measure ℂ).prod volume)
    with hE
  set K1 : ℝ := 2 / Real.sqrt κ * (2 / c) / δ + |chiC κ| * (2 / c ^ 2) with hK1
  have hL0 : 0 ≤ L := integral_nonneg fun a => abs_nonneg _
  have hK10 : 0 ≤ K1 := by
    have : 0 < c ^ 2 := pow_pos hc 2
    positivity
  set S : Set Ω := {ω | B 0 ω = 0} with hS
  have hS0 : MeasurableSet[𝓕 0] S := (hBad 0) (measurableSet_singleton (0 : ℝ))
  have hSt : ∀ t, MeasurableSet[𝓕 t] S := fun t => 𝓕.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hS0
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := hB.eval_zero_ae_eq_zero
  set X := fieldX κ c δ T B ρ with hX
  set V := fieldV κ c δ T B ρ with hV
  set X' : ℝ≥0 → Ω → ℝ := fun t ω => S.indicator (X t) ω + Sᶜ.indicator (fun _ => x₀) ω
    with hX'
  have hX'mem : ∀ t ω, ω ∈ S → X' t ω = X t ω := fun t ω hω => by simp [hX', hω]
  have hX'nmem : ∀ t ω, ω ∉ S → X' t ω = x₀ := fun t ω hω => by simp [hX', hω]
  have hXae : ∀ t, X' t =ᵐ[P] X t := fun t => by
    filter_upwards [hSae] with ω hω using hX'mem t ω hω
  have hXm := fieldX_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ hρc hρs hρδ T
  have hQm := fieldXV_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ hρc hρs hρδ T
  have hX'ad : StronglyAdapted 𝓕 X' := fun t =>
    ((hXm.1 t).indicator (hSt t)).add (stronglyMeasurable_const.indicator (hSt t).compl)
  have hVad : StronglyAdapted 𝓕 V := fun t => by
    have := (hQm.1 t).sub ((hXm.1 t).pow 2)
    convert this using 1
    funext ω; simp [hV]
  have hX'm : Martingale X' 𝓕 P := martingale_of_ae_eq hXm hX'ad hXae
  have hQ'm : Martingale (fun t ω => X' t ω ^ 2 + V t ω) 𝓕 P :=
    martingale_of_ae_eq hQm (fun t => ((hX'ad t).pow 2).add (hVad t)) (fun t => by
      filter_upwards [hXae t] with ω hω
      show X' t ω ^ 2 + V t ω = X t ω ^ 2 + V t ω
      rw [hω])
  -- bounds
  have hXb : ∀ t ω, |X t ω| ≤ L * fzBound κ c T := fun t ω =>
    abs_fieldX_le (κ := κ) (δ := δ) hBc hc hρc hρs hρδ T t ω
  have hX'b : ∀ t ω, |X' t ω| ≤ L * fzBound κ c T + |x₀| := fun t ω => by
    by_cases hω : ω ∈ S
    · rw [hX'mem t ω hω]; linarith [hXb t ω, abs_nonneg x₀]
    · rw [hX'nmem t ω hω]; linarith [(abs_nonneg _).trans (hXb t ω)]
  have hΔ : ∀ (t s : ℝ≥0) ω, |X' (t + s) ω - X' t ω| ≤
      L * (2 / δ * bmOsc B t s ω + K1 * s) := fun t s ω => by
    have h := abs_fieldX_sub_le hBc 𝓕 hBad hκ hc hcδ hρc hρs hρδ T ω (le_self_add : t ≤ t + s)
    rw [add_tsub_cancel_left, NNReal.coe_add, add_sub_cancel_left] at h
    by_cases hω : ω ∈ S
    · rw [hX'mem _ ω hω, hX'mem _ ω hω]; exact h
    · rw [hX'nmem _ ω hω, hX'nmem _ ω hω, sub_self, abs_zero]
      exact (abs_nonneg _).trans h
  set K : ℝ := max E (L ^ 2 * (4 / δ ^ 2)) with hK
  have hVb : ∀ t ω, |V t ω| ≤ K := fun t ω =>
    (abs_fieldV_le (κ := κ) hBc hc hcδ hρc hρs hρδ T t ω).trans (le_max_left _ _)
  have hVinc : ∀ (t s : ℝ≥0) ω, |V (t + s) ω - V t ω| ≤ K * s := fun t s ω => by
    have h := abs_fieldV_sub_le (κ := κ) hBc 𝓕 hBad hc hcδ hρc hρs hρδ T ω (le_self_add : t ≤ t + s)
    rw [NNReal.coe_add, add_sub_cancel_left] at h
    calc _ ≤ _ := h
      _ = L ^ 2 * (4 / δ ^ 2) * s := by ring
      _ ≤ K * s := mul_le_mul_of_nonneg_right (le_max_right _ _) s.coe_nonneg
  have hX'meas : ∀ t, StronglyMeasurable (X' t) := fun t => (hX'ad t).mono (𝓕.le t)
  have hXint : ∀ t s : ℝ≥0, Integrable (fun ω => |X' (t + s) ω - X' t ω| ^ 3) P := by
    intro t s
    refine Integrable.of_bound (((hX'meas (t + s)).sub (hX'meas t)).norm.pow 3).aestronglyMeasurable
      ((2 * (L * fzBound κ c T + |x₀|)) ^ 3) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 3
    calc _ ≤ |X' (t + s) ω| + |X' t ω| := abs_sub _ _
      _ ≤ _ := by linarith [hX'b (t + s) ω, hX'b t ω]
  obtain ⟨Cosc, hCosc⟩ := bm_osc_moment hB hBm hBc 3
  have hX3 : ∀ t s : ℝ≥0, s ≤ 1 → ∫ ω, |X' (t + s) ω - X' t ω| ^ 3 ∂P ≤
      (4 * L ^ 3 * ((2 / δ) ^ 3 * Cosc + K1 ^ 3)) * ((s : ℝ) * Real.sqrt s) := by
    intro t s hs1
    have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
    have hs1' : (s : ℝ) ≤ 1 := by exact_mod_cast hs1
    have hosc := integrable_bmOsc_pow hB hBm hBc t s 3
    have hg : Integrable (fun ω => 4 * L ^ 3 * ((2 / δ) ^ 3 * bmOsc B t s ω ^ 3
        + K1 ^ 3 * (s : ℝ) ^ 3)) P :=
      ((hosc.const_mul _).add (integrable_const _)).const_mul _
    have hpt : ∀ ω, |X' (t + s) ω - X' t ω| ^ 3 ≤
        4 * L ^ 3 * ((2 / δ) ^ 3 * bmOsc B t s ω ^ 3 + K1 ^ 3 * (s : ℝ) ^ 3) := fun ω => by
      have ho := bmOsc_nonneg' (hBc ω) t s
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hΔ t s ω) 3
      have h2 := cube_add_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / δ) ho)
        (mul_nonneg hK10 hs0)
      calc _ ≤ (L * (2 / δ * bmOsc B t s ω + K1 * s)) ^ 3 := h1
        _ = L ^ 3 * (2 / δ * bmOsc B t s ω + K1 * s) ^ 3 := by ring
        _ ≤ L ^ 3 * (4 * ((2 / δ * bmOsc B t s ω) ^ 3 + (K1 * s) ^ 3)) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hL0 3)
        _ = _ := by ring
    have hint_le := integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) hg
      (ae_of_all _ hpt)
    have hcomp : ∫ ω, 4 * L ^ 3 * ((2 / δ) ^ 3 * bmOsc B t s ω ^ 3 + K1 ^ 3 * (s : ℝ) ^ 3) ∂P =
        4 * L ^ 3 * ((2 / δ) ^ 3 * ∫ ω, bmOsc B t s ω ^ 3 ∂P + K1 ^ 3 * (s : ℝ) ^ 3) := by
      rw [integral_const_mul, integral_add (hosc.const_mul _) (integrable_const _),
        integral_const_mul]
      simp
    have hmom := hCosc t s
    rw [rpow_three_halves_eq hs0] at hmom
    have hss : (s : ℝ) ^ 3 ≤ s * Real.sqrt s := by
      have hsq : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1'
      have hA : (s : ℝ) * Real.sqrt s ≤ 1 := by nlinarith [Real.sqrt_nonneg s]
      have hB' : (s : ℝ) ^ 3 = (s * Real.sqrt s) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hs0]; ring
      rw [hB']
      nlinarith [mul_nonneg hs0 (Real.sqrt_nonneg s)]
    refine hint_le.trans ?_
    rw [hcomp]
    have hL3 : 0 ≤ 4 * L ^ 3 := by positivity
    have h2δ : 0 ≤ (2 / δ) ^ 3 := by positivity
    have hK3 : 0 ≤ K1 ^ 3 := pow_nonneg hK10 3
    calc 4 * L ^ 3 * ((2 / δ) ^ 3 * ∫ ω, bmOsc B t s ω ^ 3 ∂P + K1 ^ 3 * (s : ℝ) ^ 3)
        ≤ 4 * L ^ 3 * ((2 / δ) ^ 3 * (Cosc * (s * Real.sqrt s)) + K1 ^ 3 * (s * Real.sqrt s)) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hmom h2δ)
            (mul_le_mul_of_nonneg_left hss hK3)) hL3
      _ = _ := by ring
  have hX'0 : ∀ ω, X' 0 ω = x₀ := fun ω => by
    by_cases hω : ω ∈ S
    · rw [hX'mem 0 ω hω]; exact fieldX_zero hBc hc ρ T hω
    · exact hX'nmem 0 ω hω
  have hV0 : ∀ ω, V 0 ω = v₀ := fun ω => fieldV_zero hBc hc ρ T ω
  have key := ItoLite.il6_integral_exp_eq (P := P) (ℱ := 𝓕) T hX'm hQ'm hX'0 hV0 hVb hVinc
    hXint hX3
  rw [← key]
  refine integral_congr_ae ?_
  filter_upwards [hXae T] with ω hω
  rw [hω]

end MF5

end FieldMart
end QuantumZipper
