/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux104Path
import InteractingSLE.Spec.Ito.Measurability
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Sec2.AssemblyUnique
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Aux. lemma 104: no common-seed entrance with opposite-sign Jacobi parameters

Packet PROVE-STRIPSYS3. **`Aux104.ae_lifetime_eq_zero`** (Aux. lemma 104, `source/spec/p337-384.md` L308–L345):
let `B` be a Brownian motion of a filtration `𝓕`, and let `W, V^L, V^R` be adapted before a lifetime `T` and satisfy
(IN1) on `[0, T)` almost surely (`IsSeedEntrance`: seeds `V^L_0 = V^R_0 = 0`, an extra drift `|e| ≤ C`, ordered marks,
null collision sets, integrable reciprocal gaps). If `a = ρ_L + 2 > 0 > b = ρ_R + 2` or `b > 0 > a`, then `T = 0`
almost surely.

Proof (the source's, in physical time; the restart at the first time `D = e^{−n}` is replaced by the cutoff `ψ` of
`Aux104Calc`). Put `m = min(a, −b)`, `c = m/4`, fix `d > 0` with `C d ≤ 2m`, a level `R` for `|B|` and a horizon `t₀`.
Stop at `σ = min(τ_d, τ_R, T, t₀)` (`τ_d`: `D` exceeds `d`; `τ_R`: `|B|` exceeds `R`). By the localized Itô formula
(`Ito.martingale_itoLocalized`) `Φ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} gen` is a martingale; the generator is nonnegative
(`IsSeedEntrance.itoGen_nonneg`) and `Φ(Λ₀, B₀) = 0`, so `E Φ_σ ≥ 0`. Since `Φ ≤ 1 + c`, and `Φ ≤ 1 − c(log d + n)`
on `{τ_d < min(T, τ_R, t₀)}`, `c (n + log d) P(τ_d < min(T, τ_R, t₀)) ≤ 1 + c` for every `n`: that event is null
((IN5)). By (IN2) `D_t² ≥ 16 t`, a lifetime `T > d²/16` makes `D` exceed `d` before `T`; letting `R → ∞` and
`d → 0` gives `T = 0` almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux104

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Stopped values of a process that agrees with an adapted one strictly before the stop -/

/-- **Stopped values.** Let `σ` be a finite stopping time of `𝓖`, and let `X` agree with an adapted `K` strictly
before `σ` and at time `0`, and be continuous on `[0, σ]`. Then `ω ↦ X_{t∧σ(ω)}(ω)` is `𝓖_t`-measurable. -/
theorem measurable_stopped_of_agree_lt {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓖 : Filtration ℝ≥0 mΩ} {K X : ℝ≥0 → Ω → β} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) (hK : ∀ s, Measurable[𝓖 s] (K s))
    (hKX : ∀ ω s, (s < σ ω ∨ s = 0) → K s ω = X s ω)
    (hXc : ∀ ω, ContinuousOn (X · ω) (Iic (σ ω))) (t : ℝ≥0) :
    Measurable[𝓖 t] fun ω => X (min t (σ ω)) ω := by
  -- the stopped time `t ∧ σ` is `𝓖_t`-measurable
  have hm : Measurable[𝓖 t] fun ω => min t (σ ω) := by
    refine measurable_of_Iic (mδ := 𝓖 t) fun x => ?_
    by_cases hx : t ≤ x
    · have : (fun ω => min t (σ ω)) ⁻¹' Iic x = univ := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (min_le_left _ _).trans hx
      rw [this]; exact @MeasurableSet.univ _ (𝓖 t)
    · push Not at hx
      have : (fun ω => min t (σ ω)) ⁻¹' Iic x = {ω | (σ ω : WithTop ℝ≥0) ≤ x} := by
        ext ω
        simp only [mem_preimage, mem_Iic, min_le_iff, mem_ofPred_eq, WithTop.coe_le_coe]
        exact ⟨fun h => h.resolve_left (not_le.2 hx), Or.inr⟩
      rw [this]
      exact 𝓖.mono hx.le _ (hσ x)
  set u : Ω → ℝ := fun ω => ((min t (σ ω) : ℝ≥0) : ℝ) with hu
  have hum : Measurable[𝓖 t] u := measurable_coe_nnreal_real.comp hm
  set arg : ℕ → Ω → ℝ := fun n ω => max (u ω - 1 / ((n : ℝ) + 1)) 0 with harg
  have hargm : ∀ n, Measurable[𝓖 t] (arg n) := fun n =>
    (hum.sub measurable_const).max measurable_const
  set idx : ℕ → Ω → ℕ := fun n ω => Girsanov.stepIdx n (arg n ω) with hidx
  have hidxm : ∀ n, Measurable[𝓖 t] (idx n) := fun n => (Girsanov.measurable_stepIdx n).comp (hargm n)
  set sn : ℕ → Ω → ℝ≥0 := fun n ω => Girsanov.grid n (idx n ω) with hsn
  have harg0 : ∀ n ω, 0 ≤ arg n ω := fun n ω => le_max_right _ _
  have hsn_le_arg : ∀ n ω, (sn n ω : ℝ) ≤ arg n ω := fun n ω => Girsanov.coe_grid_stepIdx_le (harg0 n ω)
  have hu0 : ∀ ω, 0 ≤ u ω := fun ω => NNReal.coe_nonneg _
  have hsn_le : ∀ n ω, sn n ω ≤ min t (σ ω) := fun n ω => by
    have : (sn n ω : ℝ) ≤ u ω := (hsn_le_arg n ω).trans (max_le (by
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith) (hu0 ω))
    exact_mod_cast this
  have hsn_cases : ∀ n ω, sn n ω < σ ω ∨ sn n ω = 0 := fun n ω => by
    by_cases h : u ω - 1 / ((n : ℝ) + 1) ≤ 0
    · right
      have h1 : arg n ω = 0 := max_eq_right h
      have h2 := hsn_le_arg n ω
      rw [h1] at h2
      exact le_antisymm (by exact_mod_cast h2) bot_le
    · left
      push Not at h
      have h1 : arg n ω = u ω - 1 / ((n : ℝ) + 1) := max_eq_left h.le
      have h2 := hsn_le_arg n ω
      rw [h1] at h2
      have h3 : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have h4 : (sn n ω : ℝ) < ((min t (σ ω) : ℝ≥0) : ℝ) := by simp only [hu] at h2; linarith
      exact lt_of_lt_of_le (by exact_mod_cast h4) (min_le_right _ _)
  have hsn_tendsto : ∀ ω, Tendsto (fun n => sn n ω) atTop (𝓝 (min t (σ ω))) := fun ω => by
    rw [← NNReal.tendsto_coe]
    have hlow : ∀ n : ℕ, u ω - 1 / ((n : ℝ) + 1) - 1 / 2 ^ n ≤ (sn n ω : ℝ) := fun n => by
      have h1 := Girsanov.lt_coe_grid_stepIdx_add (n := n) (arg n ω)
      have h2 : u ω - 1 / ((n : ℝ) + 1) ≤ arg n ω := le_max_left _ _
      simp only [hsn, hidx] at h1 ⊢
      linarith
    have hup : ∀ n : ℕ, (sn n ω : ℝ) ≤ u ω := fun n => by exact_mod_cast hsn_le n ω
    have hl1 : Tendsto (fun n : ℕ => u ω - 1 / ((n : ℝ) + 1) - 1 / 2 ^ n) atTop (𝓝 (u ω)) := by
      have a1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have a2 : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
        simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa using (tendsto_const_nhds.sub a1).sub a2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl1 tendsto_const_nhds hlow hup
  set f : ℕ → Ω → β := fun n ω => K (min (Girsanov.grid n (idx n ω)) t) ω with hf
  have hfm : ∀ n, Measurable[𝓖 t] (f n) := fun n => by
    refine @Ito.measurable_comp_index Ω β (𝓖 t) _ (fun ω k => K (min (Girsanov.grid n k) t) ω)
      (fun k => ?_) (idx n) (hidxm n)
    exact (hK _).mono (𝓖.mono (min_le_right _ _)) le_rfl
  refine @measurable_of_tendsto_metrizable Ω β (𝓖 t) _ _ _ _ f _ hfm (tendsto_pi_nhds.2 fun ω => ?_)
  have heq : ∀ n, f n ω = X (sn n ω) ω := fun n => by
    have e : min (Girsanov.grid n (idx n ω)) t = sn n ω := min_eq_left ((hsn_le n ω).trans (min_le_left _ _))
    simp only [hf]
    rw [e]
    exact hKX ω _ (hsn_cases n ω)
  simp_rw [heq]
  have hmem : min t (σ ω) ∈ Iic (σ ω) := mem_Iic.2 (min_le_right _ _)
  exact ((hXc ω) _ hmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hsn_tendsto ω,
    Eventually.of_forall fun n => mem_Iic.2 ((hsn_le n ω).trans (min_le_right _ _))⟩)

/-! ### Stopping times -/

section Stop

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W VL VR B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}

/-- A lifetime before which a process is adapted is a stopping time. -/
theorem isStoppingTime_lifetime (hW : AdaptedBefore 𝓕 T W) :
    IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0) := by
  intro t
  have h := (hW t univ MeasurableSet.univ).compl
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, mem_compl_iff, mem_univ, and_true, not_lt]
  rfl

/-- The rational hitting time of `{d < V^R − V^L}` before `T` is a stopping time of a right-continuous filtration
containing `𝓕`. -/
theorem isStoppingTime_hitCross {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] (h𝓕𝓖 : 𝓕 ≤ 𝓖)
    (hVL : AdaptedBefore 𝓕 T VL) (hVR : AdaptedBefore 𝓕 T VR) (d : ℝ) :
    IsStoppingTime 𝓖 fun ω => (Band.hitTime (fun s => d < VR s ω - VL s ω) (T ω) : WithTop ℝ≥0) := by
  refine Band.isStoppingTime_hitTime fun s => h𝓕𝓖 s _ ?_
  have e : {ω | (s : ℝ≥0∞) < T ω ∧ d < VR s ω - VL s ω} = {ω | (s : ℝ≥0∞) < T ω} ∩
      {ω | d < Girsanov.killed T VR s ω - Girsanov.killed T VL s ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1] at h2⟩
  rw [e]
  have hT : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < T ω} := by simpa using hVR s univ MeasurableSet.univ
  have hf : Measurable[𝓕 s] fun ω => Girsanov.killed T VR s ω - Girsanov.killed T VL s ω :=
    (Girsanov.measurable_killed hVR s).sub (Girsanov.measurable_killed hVL s)
  exact hT.inter (hf measurableSet_Ioi)

/-- The rational hitting time of `{R < |B|}` is a stopping time of a right-continuous filtration containing `𝓕`. -/
theorem isStoppingTime_hitAbs {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] (h𝓕𝓖 : 𝓕 ≤ 𝓖)
    (hB : ∀ t, Measurable[𝓕 t] (B t)) (R : ℝ) :
    IsStoppingTime 𝓖 fun ω => (Band.hitTime (fun s => R < |B s ω|) ⊤ : WithTop ℝ≥0) := by
  refine Band.isStoppingTime_hitTime fun s => h𝓕𝓖 s _ ?_
  have e : {ω | (s : ℝ≥0∞) < (⊤ : ℝ≥0∞) ∧ R < |B s ω|} = {ω | R < |B s ω|} := by
    ext ω; simp
  rw [e]
  exact (continuous_abs.measurable.comp (hB s)) measurableSet_Ioi

end Stop

/-! ### (IN4)–(IN5): the optional-stopping bound -/

section Core

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ ρL ρR C : ℝ}
  {W VL VR B e : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}

open scoped Classical in
/-- **The optional-stopping bound (IN4)–(IN5)** for fixed `d`, `R`, `t₀` and `n` with `e^{−n} ≤ d`: on a good set `G`
of full measure, `c (log d + n) P(τ_d < min(T, τ_R, t₀)) ≤ 1 + c` with `c = m/4`. -/
theorem mul_measure_hitEvent_le (hB : IsFilteredBrownianReal 𝓕 B P) (hW : AdaptedBefore 𝓕 T W)
    (hVL : AdaptedBefore 𝓕 T VL) (hVR : AdaptedBefore 𝓕 T VR) (hC : 0 ≤ C) {G : Set Ω} (hGm : MeasurableSet G)
    (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsSeedEntrance κ ρL ρR C (W · ω) (VL · ω) (VR · ω) (B · ω) (e · ω) (T ω) ∧
      Continuous (B · ω) ∧ B 0 ω = 0)
    {m : ℝ} (hm : 0 < m) (ha : m ≤ ρL + 2) (hb : m ≤ -(ρR + 2))
    {d : ℝ} (hd : 0 < d) (hCd : C * d ≤ 2 * m) (R t₀ : ℝ≥0) (n : ℕ) (hβd : beta n ≤ d) :
    m / 4 * (Real.log d + n) * (P (G ∩ {ω | Band.hitTime (fun s => d < VR s ω - VL s ω) (T ω) <
      min (T ω) (min (Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤) (t₀ : ℝ≥0∞))})).toReal ≤ 1 + m / 4 := by
  have hP := hB.isProbabilityMeasure'
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hB𝓖 := Ito.isFilteredBrownianReal_usualAugmentation hB
  have h𝓕𝓖 : 𝓕 ≤ 𝓖 := Ito.le_usualAugmentation 𝓕 P
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
    rwa [compl_compl] at this
  obtain ⟨hB'', hB''c⟩ := Ito.isFilteredBrownianReal_modify hB𝓖 hGm hGc fun ω hω => (hG ω hω).2.1
  rw [Ito.nullAugmented_usualAugmentation] at hB''
  set B'' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then B t ω else 0 with hB''def
  -- stopping times
  set τd : Ω → ℝ≥0∞ := fun ω => Band.hitTime (fun s => d < VR s ω - VL s ω) (T ω) with hτd
  set τR : Ω → ℝ≥0∞ := fun ω => Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤ with hτR
  set σE : Ω → ℝ≥0∞ := fun ω => min (τd ω) (min (T ω) (min (τR ω) t₀)) with hσE
  have hσEt : ∀ ω, σE ω ≤ t₀ := fun ω =>
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hσEfin : ∀ ω, σE ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (hσEt ω)
  set σ : Ω → ℝ≥0 := fun ω => (σE ω).toNNReal with hσdef
  have hσcoe : ∀ ω, (σ ω : ℝ≥0∞) = σE ω := fun ω => ENNReal.coe_toNNReal (hσEfin ω)
  have hσst : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0) := by
    have h1 := isStoppingTime_hitCross (𝓖 := 𝓖) h𝓕𝓖 hVL hVR d
    have h2 : IsStoppingTime 𝓖 fun ω => (T ω : WithTop ℝ≥0) := fun i => h𝓕𝓖 i _ (isStoppingTime_lifetime hW i)
    have h3 := isStoppingTime_hitAbs (𝓖 := 𝓖) h𝓕𝓖 (fun t => hB.2.1 t) R
    have h4 := isStoppingTime_const 𝓖 t₀
    have := h1.min (h2.min (h3.min h4))
    convert this using 2 with ω
    exact hσcoe ω
  have hσT : ∀ ω, (σ ω : ℝ≥0∞) ≤ T ω := fun ω => by
    rw [hσcoe]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hστd : ∀ ω, (σ ω : ℝ≥0∞) ≤ τd ω := fun ω => by rw [hσcoe]; exact min_le_left _ _
  have hστR : ∀ ω, (σ ω : ℝ≥0∞) ≤ τR ω := fun ω => by
    rw [hσcoe]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσt₀ : ∀ ω, σ ω ≤ t₀ := fun ω => by
    have := hσEt ω; rw [← hσcoe] at this; exact_mod_cast this
  -- pathwise facts on `G`
  have hdd : ∀ ω ∈ G, ∀ t : ℝ≥0, t < σ ω → VR t ω - VL t ω ≤ d := fun ω hω t ht =>
    le_of_lt_hitTime (hG ω hω).1.continuousOn_crossGap (lt_of_lt_of_le (by exact_mod_cast ht) (hσT ω))
      (lt_of_lt_of_le (by exact_mod_cast ht) (hστd ω))
  have hint : ∀ ω ∈ G, IntervalIntegrable (dens ρL ρR (W · ω) (VL · ω) (VR · ω) (e · ω) (T ω)) volume 0 (σ ω) ∧
      ∫ s in (0 : ℝ)..(σ ω), ‖dens ρL ρR (W · ω) (VL · ω) (VR · ω) (e · ω) (T ω) s‖ ≤
        (|ρL + 2| + |ρR| + 2) / 2 * d + C * t₀ := fun ω hω => by
    obtain ⟨h1, h2⟩ := (hG ω hω).1.intervalIntegrable_dens hC (hσT ω) hd.le (hdd ω hω)
    exact ⟨h1, h2.trans (by gcongr; exact_mod_cast hσt₀ ω)⟩
  have hstate : ∀ ω ∈ G, ∀ t : ℝ≥0, t ≤ σ ω →
      (coord ρL ρR (W · ω) (VL · ω) (VR · ω) (e · ω) (T ω) t, B t ω) ∈ stateSet κ d R := fun ω hω t ht =>
    (hG ω hω).1.mem_stateSet hC (hG ω hω).2.1 (hG ω hω).2.2 hd.le R.coe_nonneg (hσT ω) (hστd ω) (hστR ω) ht
  -- the coordinates, their density, and an adapted version
  set Λ : ℝ≥0 → Ω → ℝ × ℝ := fun t ω =>
    if ω ∈ G then coord ρL ρR (W · ω) (VL · ω) (VR · ω) (e · ω) (T ω) t else 0 with hΛdef
  set lam : ℝ → Ω → ℝ × ℝ := fun s ω =>
    if ω ∈ G then dens ρL ρR (W · ω) (VL · ω) (VR · ω) (e · ω) (T ω) s else 0 with hlamdef
  set K : ℝ≥0 → Ω → ℝ × ℝ := fun s ω => if ω ∈ G ∧ (s : ℝ≥0∞) < T ω then
      (Girsanov.killed T W s ω - Real.sqrt κ * B s ω - Girsanov.killed T VL s ω,
        Girsanov.killed T VR s ω - Girsanov.killed T VL s ω) else 0 with hKdef
  have hKm : ∀ s, Measurable[𝓖 s] (K s) := fun s => by
    have hT : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < T ω} := by simpa using hVR s univ MeasurableSet.univ
    refine Measurable.ite ((𝓖.mono (zero_le : (0 : ℝ≥0) ≤ s) _ hG0).inter (h𝓕𝓖 s _ hT)) ?_ measurable_const
    have hWk := (Girsanov.measurable_killed hW s).mono (h𝓕𝓖 s) le_rfl
    have hLk := (Girsanov.measurable_killed hVL s).mono (h𝓕𝓖 s) le_rfl
    have hRk := (Girsanov.measurable_killed hVR s).mono (h𝓕𝓖 s) le_rfl
    have hBk := (hB.2.1 s).mono (h𝓕𝓖 s) le_rfl
    exact ((hWk.sub (hBk.const_mul _)).sub hLk).prodMk (hRk.sub hLk)
  have hKX : ∀ ω s, (s < σ ω ∨ s = 0) → K s ω = Λ s ω := by
    intro ω s hs
    by_cases hω : ω ∈ G
    · have hcase : (s : ℝ≥0∞) < T ω ∨ (s = 0 ∧ ¬ (s : ℝ≥0∞) < T ω) := by
        rcases hs with hs | hs
        · exact Or.inl (lt_of_lt_of_le (by exact_mod_cast hs) (hσT ω))
        · by_cases h0 : (s : ℝ≥0∞) < T ω
          · exact Or.inl h0
          · exact Or.inr ⟨hs, h0⟩
      rcases hcase with hsT | ⟨rfl, h0⟩
      · simp only [hKdef, hΛdef, hω, hsT, and_self, ↓reduceIte, Girsanov.killed_of_lt hsT]
        rw [(hG ω hω).1.coord_eq hsT]
      · simp only [hKdef, hΛdef, hω, h0, and_false, ↓reduceIte]
        simp [coord]
    · simp only [hKdef, hΛdef, hω, false_and, ↓reduceIte]
  have hXc : ∀ ω, ContinuousOn (Λ · ω) (Iic (σ ω)) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hΛdef, hω, ↓reduceIte]
      have hF := intervalIntegral.continuousOn_primitive_interval' (hint ω hω).1 left_mem_uIcc
      rw [uIcc_of_le (σ ω).coe_nonneg] at hF
      exact hF.comp NNReal.continuous_coe.continuousOn fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht⟩
    · simp only [hΛdef, hω, ↓reduceIte]; exact continuousOn_const
  have hΛm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω :=
    measurable_stopped_of_agree_lt hσst hKm hKX hXc
  have hlam : ∀ ω, IntervalIntegrable (lam · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hlamdef, hω, ↓reduceIte]; exact (hint ω hω).1
    · simp only [hlamdef, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω := fun ω t _ => by
    by_cases hω : ω ∈ G
    · simp only [hΛdef, hlamdef, hω, ↓reduceIte, coord, NNReal.coe_zero, intervalIntegral.integral_same,
        zero_add]
    · simp only [hΛdef, hlamdef, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  set Kb : ℝ := (|ρL + 2| + |ρR| + 2) / 2 * d + C * t₀ with hKbdef
  have hKb0 : 0 ≤ Kb := by positivity
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖lam s ω‖ ≤ Kb := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hlamdef, hω, ↓reduceIte]; exact (hint ω hω).2
    · simp only [hlamdef, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]; exact hKb0
  set Kc : Set ((ℝ × ℝ) × ℝ) :=
    (Icc (-(d + Real.sqrt κ * R)) (d + Real.sqrt κ * R) ×ˢ Icc 0 d) ×ˢ Icc (-(R : ℝ)) R with hKcdef
  have hKcc : IsCompact Kc := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω → (Λ t ω, B'' t ω) ∈ Kc := fun ω t ht => by
    by_cases hω : ω ∈ G
    · simp only [hΛdef, hB''def, hω, ↓reduceIte]
      exact stateSet_subset κ d R hd.le (hstate ω hω t ht)
    · simp only [hΛdef, hB''def, hω, ↓reduceIte]
      have hs := Real.sqrt_nonneg κ
      have hR := R.coe_nonneg
      refine ⟨⟨⟨?_, ?_⟩, ⟨le_rfl, hd.le⟩⟩, ⟨?_, ?_⟩⟩ <;> simp <;> nlinarith
  set Φ := phi κ (m / 4) (alpha n) (beta n) n with hΦdef
  have hMart := Ito.martingale_itoLocalized hB'' hB''c isOpen_univ
    ((contDiff_phi (κ := κ) (c := m / 4) (n := (n : ℝ)) (alpha_pos n) (alpha_lt_beta n)).contDiffOn)
    hKcc (subset_univ _) hσst hΛm hlam hΛ hKb hK
  -- the end value `F`, the integrated generator `I`, and `E[F − I] = 0`
  have hmin : ∀ ω, min t₀ (σ ω) = σ ω := fun ω => min_eq_right (hσt₀ ω)
  set F : Ω → ℝ := fun ω => Φ (Λ (σ ω) ω, B'' (σ ω) ω) with hFdef
  set I : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..(σ ω),
    Ito.itoGen Φ (Λ s.toNNReal ω, B'' s.toNNReal ω) (lam s ω) with hIdef
  have hΛ0 : ∀ ω, Λ 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G <;> simp [hΛdef, hω, coord]
  have hΦ0 : ∀ x : ℝ, Φ ((0 : ℝ × ℝ), x) = 0 := fun x => by
    simp [hΦdef, phi, g1, g2, cut_eq_zero (alpha_lt_beta n) (alpha_pos n).le]
  have hmin0 : ∀ ω, min (0 : ℝ≥0) (σ ω) = 0 := fun ω => min_eq_left bot_le
  have hset := hMart.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t₀) (MeasurableSet.univ (m := 𝓖 0))
  simp only [Measure.restrict_univ] at hset
  have hint0 : ∫ ω, (F ω - I ω) ∂P = 0 := by
    refine Eq.trans ?_ (hset.symm.trans ?_)
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hFdef, hIdef, hmin]
      rfl
    · refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (Eventually.of_forall fun ω => ?_)).trans (by simp)
      simp only [hmin0, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
      rw [hΛ0]
      exact hΦ0 _
  have hMint := hMart.integrable t₀
  simp only [hmin] at hMint
  have hΦc : Continuous Φ := (contDiff_phi (k := 0) (κ := κ) (c := m / 4) (n := (n : ℝ)) (alpha_pos n)
    (alpha_lt_beta n)).continuous
  have hBst : Measurable[𝓖 t₀] fun ω => B'' (min t₀ (σ ω)) ω :=
    measurable_stopped_of_agree_lt hσst (fun s => hB''.2.1 s) (fun ω s _ => rfl)
      (fun ω => (hB''c ω).continuousOn) t₀
  have hFm : Measurable F := by
    have := hΦc.measurable.comp (((hΛm t₀).prodMk hBst).mono (𝓖.le t₀) le_rfl)
    have e : F = Φ ∘ fun ω => (Λ (min t₀ (σ ω)) ω, B'' (min t₀ (σ ω)) ω) := by
      funext ω; simp only [Function.comp, hFdef, hmin]
    rw [e]; exact this
  set Lg : ℝ := Real.log d + n with hLgdef
  have hLg : 0 ≤ Lg := by
    have h1 : Real.log (beta n) ≤ Real.log d := Real.log_le_log (Real.exp_pos _) hβd
    have h2 := log_beta_add n
    rw [hLgdef]; linarith
  have hc : 0 ≤ m / 4 := by positivity
  have hFb : ∀ ω, -(m / 4 * max 0 Lg) ≤ F ω ∧ F ω ≤ 1 + m / 4 := fun ω => by
    by_cases hω : ω ∈ G
    · obtain ⟨h1, h2, h3, -⟩ := hstate ω hω (σ ω) le_rfl
      simp only [hFdef, hΛdef, hB''def, hω, ↓reduceIte]
      exact ⟨le_phi n hc h1 h2 h3, phi_le_one_add n hc h1 h2⟩
    · simp only [hFdef, hΛdef, hB''def, hω, ↓reduceIte, hΦ0]
      exact ⟨by have := le_max_left 0 Lg; nlinarith, by linarith⟩
  have hFint : Integrable F P := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (1 + m / 4 + m / 4 * max 0 Lg)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := hFb ω
    have := le_max_left 0 Lg
    constructor <;> nlinarith
  have hIint : Integrable I P := by
    refine (hFint.sub hMint).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, hFdef, hIdef]; ring
  have hI0 : ∀ᵐ ω ∂P, 0 ≤ I ω := by
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
    filter_upwards [hGae] with ω hω
    simp only [hIdef, hΛdef, hB''def, hlamdef, hω, ↓reduceIte]
    refine intervalIntegral.integral_nonneg_of_ae_restrict (σ ω).coe_nonneg ?_
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (σ ω : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (hG ω hω).1.ae_gap_pos,
      ae_restrict_of_ae hne] with s hs hgap hsne
    have hsσ : s < σ ω := lt_of_le_of_ne hs.2 hsne
    have hsσ' : s.toNNReal < σ ω := (Real.toNNReal_lt_iff_lt_coe hs.1).2 hsσ
    have hsT : (s.toNNReal : ℝ≥0∞) < T ω := lt_of_lt_of_le (by exact_mod_cast hsσ') (hσT ω)
    obtain ⟨hL, hR⟩ := hgap hs.1 hsT
    exact (hG ω hω).1.itoGen_nonneg (alpha_pos n) (alpha_lt_beta n) hm ha hb hCd (by rw [log_beta_add])
      hsT hL hR (hdd ω hω _ hsσ')
  have hFpos : 0 ≤ ∫ ω, F ω ∂P := by
    have h1 := integral_sub hFint hIint
    rw [hint0] at h1
    have h2 := integral_nonneg_of_ae hI0
    linarith
  -- comparison on the success event
  set E₂ : Set Ω := {ω | F ω ≤ 1 + m / 4 - m / 4 * Lg} with hE₂def
  have hE₂m : MeasurableSet E₂ := measurableSet_le hFm measurable_const
  have hEE₂ : G ∩ {ω | τd ω < min (T ω) (min (τR ω) t₀)} ⊆ E₂ := by
    rintro ω ⟨hω, hlt⟩
    have hσeq : (σ ω : ℝ≥0∞) = τd ω := by rw [hσcoe]; exact min_eq_left hlt.le
    have hσT' : (σ ω : ℝ≥0∞) < T ω := by rw [hσeq]; exact lt_of_lt_of_le hlt (min_le_left _ _)
    have hdD : d ≤ VR (σ ω) ω - VL (σ ω) ω :=
      le_of_hitTime_eq (hG ω hω).1.continuousOn_crossGap hσeq hσT'
    have hWR := (hG ω hω).1.w_le_vR _ hσT'
    show F ω ≤ _
    simp only [hFdef, hΛdef, hB''def, hω, ↓reduceIte]
    rw [(hG ω hω).1.coord_eq hσT']
    have := phi_le_of_le (κ := κ) n hc hβd hdD (l := W (σ ω) ω - Real.sqrt κ * B (σ ω) ω - VL (σ ω) ω)
      (x := B (σ ω) ω) (by linarith)
    simp only [hΦdef]
    linarith
  have hbound : ∀ ω, F ω ≤ (1 + m / 4) - m / 4 * Lg * E₂.indicator 1 ω := fun ω => by
    by_cases hω : ω ∈ E₂
    · rw [indicator_of_mem hω, Pi.one_apply, mul_one]; exact hω
    · rw [indicator_of_notMem hω, mul_zero, sub_zero]; exact (hFb ω).2
  have hind : Integrable (E₂.indicator (1 : Ω → ℝ)) P := (integrable_const (1 : ℝ)).indicator hE₂m
  have hint_le : ∫ ω, F ω ∂P ≤ (1 + m / 4) - m / 4 * Lg * P.real E₂ := by
    calc ∫ ω, F ω ∂P ≤ ∫ ω, ((1 + m / 4) - m / 4 * Lg * E₂.indicator 1 ω) ∂P :=
          integral_mono hFint ((integrable_const _).sub (hind.const_mul _)) hbound
      _ = (1 + m / 4) - m / 4 * Lg * P.real E₂ := by
          rw [integral_sub (integrable_const _) (hind.const_mul _), integral_const, integral_const_mul,
            integral_indicator_one hE₂m]
          simp
  have hPE : (P (G ∩ {ω | τd ω < min (T ω) (min (τR ω) t₀)})).toReal ≤ P.real E₂ :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hEE₂)
  have hcL : 0 ≤ m / 4 * Lg := mul_nonneg hc hLg
  calc m / 4 * Lg * (P (G ∩ {ω | τd ω < min (T ω) (min (τR ω) t₀)})).toReal ≤ m / 4 * Lg * P.real E₂ :=
        mul_le_mul_of_nonneg_left hPE hcL
    _ ≤ 1 + m / 4 := by linarith

/-- **(IN5)**: letting `n → ∞`, the event that `D` exceeds `d` before `T`, before `|B|` exceeds `R` and before `t₀`
is null on the good set. -/
theorem measure_hitEvent_eq_zero (hB : IsFilteredBrownianReal 𝓕 B P) (hW : AdaptedBefore 𝓕 T W)
    (hVL : AdaptedBefore 𝓕 T VL) (hVR : AdaptedBefore 𝓕 T VR) (hC : 0 ≤ C) {G : Set Ω} (hGm : MeasurableSet G)
    (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsSeedEntrance κ ρL ρR C (W · ω) (VL · ω) (VR · ω) (B · ω) (e · ω) (T ω) ∧
      Continuous (B · ω) ∧ B 0 ω = 0)
    {m : ℝ} (hm : 0 < m) (ha : m ≤ ρL + 2) (hb : m ≤ -(ρR + 2))
    {d : ℝ} (hd : 0 < d) (hCd : C * d ≤ 2 * m) (R t₀ : ℝ≥0) :
    P (G ∩ {ω | Band.hitTime (fun s => d < VR s ω - VL s ω) (T ω) <
      min (T ω) (min (Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤) (t₀ : ℝ≥0∞))}) = 0 := by
  have hP := hB.isProbabilityMeasure'
  by_contra hne
  have hp : 0 < (P (G ∩ {ω | Band.hitTime (fun s => d < VR s ω - VL s ω) (T ω) <
      min (T ω) (min (Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤) (t₀ : ℝ≥0∞))})).toReal :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (-Real.log d)
  have hcp := mul_pos (show 0 < m / 4 by positivity) hp
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 + m / 4) / (m / 4 * (P (G ∩ {ω | Band.hitTime
    (fun s => d < VR s ω - VL s ω) (T ω) < min (T ω) (min (Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤)
      (t₀ : ℝ≥0∞))})).toReal) + n₀)
  have hX0 : 0 ≤ (1 + m / 4) / (m / 4 * (P (G ∩ {ω | Band.hitTime
      (fun s => d < VR s ω - VL s ω) (T ω) < min (T ω) (min (Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤)
        (t₀ : ℝ≥0∞))})).toReal) := by positivity
  have hβ : beta n ≤ d := by
    rw [beta, ← Real.exp_log hd]
    exact Real.exp_le_exp.2 (by linarith)
  have key := mul_measure_hitEvent_le hB hW hVL hVR hC hGm hGc hG hm ha hb hd hCd R t₀ n hβ
  have hX : (1 + m / 4) / (m / 4 * (P (G ∩ {ω | Band.hitTime
      (fun s => d < VR s ω - VL s ω) (T ω) < min (T ω) (min (Band.hitTime (fun s => (R : ℝ) < |B s ω|) ⊤)
        (t₀ : ℝ≥0∞))})).toReal) < Real.log d + n := by linarith
  rw [div_lt_iff₀ hcp] at hX
  nlinarith

end Core

/-! ### Aux. lemma 104 -/

section Main

variable {κ ρL ρR C : ℝ} {w vL vR b e : ℝ≥0 → ℝ} {T₀ : ℝ≥0∞}

/-- The hypotheses are monotone in the drift bound. -/
theorem IsSeedEntrance.mono_C (h : IsSeedEntrance κ ρL ρR C w vL vR b e T₀) {C' : ℝ} (hCC : C ≤ C') :
    IsSeedEntrance κ ρL ρR C' w vL vR b e T₀ :=
  { h with abs_e_le := fun t ht => (h.abs_e_le t ht).trans hCC }

/-- **Reflection** `x ↦ −x` exchanges the two sides (and the two weights). -/
theorem IsSeedEntrance.reflect (h : IsSeedEntrance κ ρL ρR C w vL vR b e T₀) :
    IsSeedEntrance κ ρR ρL C (fun t => -w t) (fun t => -vR t) (fun t => -vL t) (fun t => -b t) (fun t => -e t)
      T₀ where
  vL_le_w t ht := neg_le_neg (h.w_le_vR t ht)
  w_le_vR t ht := neg_le_neg (h.vL_le_w t ht)
  integrable_gapL t ht := by simpa only [neg_sub_neg] using h.integrable_gapR t ht
  integrable_gapR t ht := by simpa only [neg_sub_neg] using h.integrable_gapL t ht
  integrable_e t ht := (h.integrable_e t ht).neg
  abs_e_le t ht := by simpa only [abs_neg] using h.abs_e_le t ht
  w_eq t ht := by
    rw [h.w_eq t ht]
    have e1 : (fun s : ℝ => ρR / (-w s.toNNReal - -vR s.toNNReal) + ρL / (-w s.toNNReal - -vL s.toNNReal) +
        -e s.toNNReal) = fun s => -(ρL / (w s.toNNReal - vL s.toNNReal) + ρR / (w s.toNNReal - vR s.toNNReal) +
          e s.toNNReal) := by
      funext s
      rw [show -w s.toNNReal - -vR s.toNNReal = -(w s.toNNReal - vR s.toNNReal) by ring,
        show -w s.toNNReal - -vL s.toNNReal = -(w s.toNNReal - vL s.toNNReal) by ring, div_neg, div_neg]
      ring
    rw [e1, intervalIntegral.integral_neg]
    ring
  vL_eq t ht := by
    rw [h.vR_eq t ht]
    have e1 : (fun s : ℝ => 2 / (-vR s.toNNReal - -w s.toNNReal)) =
        fun s => -(2 / (vR s.toNNReal - w s.toNNReal)) := by
      funext s; rw [show -vR s.toNNReal - -w s.toNNReal = -(vR s.toNNReal - w s.toNNReal) by ring, div_neg]
    rw [e1, intervalIntegral.integral_neg]
  vR_eq t ht := by
    rw [h.vL_eq t ht]
    have e1 : (fun s : ℝ => 2 / (-vL s.toNNReal - -w s.toNNReal)) =
        fun s => -(2 / (vL s.toNNReal - w s.toNNReal)) := by
      funext s; rw [show -vL s.toNNReal - -w s.toNNReal = -(vL s.toNNReal - w s.toNNReal) by ring, div_neg]
    rw [e1, intervalIntegral.integral_neg]
  volume_collisionL := by simpa only [neg_inj] using h.volume_collisionR
  volume_collisionR := by simpa only [neg_inj] using h.volume_collisionL

end Main

section Theorem

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ ρL ρR C : ℝ}
  {W VL VR B e : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}

/-- **Aux. lemma 104, the case `a = ρ_L + 2 > 0 > b = ρ_R + 2`.** -/
theorem ae_lifetime_eq_zero_of_pos_of_neg (hB : IsFilteredBrownianReal 𝓕 B P) (hW : AdaptedBefore 𝓕 T W)
    (hVL : AdaptedBefore 𝓕 T VL) (hVR : AdaptedBefore 𝓕 T VR) (ha : 0 < ρL + 2) (hb : ρR + 2 < 0)
    (hpath : ∀ᵐ ω ∂P, IsSeedEntrance κ ρL ρR C (W · ω) (VL · ω) (VR · ω) (B · ω) (e · ω) (T ω)) :
    ∀ᵐ ω ∂P, T ω = 0 := by
  have hP := hB.isProbabilityMeasure'
  set m := min (ρL + 2) (-(ρR + 2)) with hmdef
  have hm : 0 < m := lt_min ha (by linarith)
  have ham : m ≤ ρL + 2 := min_le_left _ _
  have hbm : m ≤ -(ρR + 2) := min_le_right _ _
  set C' := max C 0 with hC'def
  have hC' : 0 ≤ C' := le_max_right _ _
  -- the good set
  set good : Ω → Prop := fun ω => IsSeedEntrance κ ρL ρR C' (W · ω) (VL · ω) (VR · ω) (B · ω) (e · ω) (T ω) ∧
    Continuous (B · ω) ∧ B 0 ω = 0 with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hB.1.cont, hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h1 h2 h3
    exact ⟨h1.mono_C (le_max_left _ _), h2, h3⟩
  obtain ⟨G, hGm, hGc, hG⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  -- the levels `d_k → 0` with `C' d_k ≤ 2m`, and the horizons
  set d₀ : ℝ := 2 * m / (C' + 1) with hd₀
  have hd₀pos : 0 < d₀ := by positivity
  have hCd₀ : C' * d₀ ≤ 2 * m := by
    rw [hd₀, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  set dk : ℕ → ℝ := fun k => min d₀ (1 / ((k : ℝ) + 1)) with hdk
  have hdk_pos : ∀ k, 0 < dk k := fun k => lt_min hd₀pos (by positivity)
  have hdk_le : ∀ k, dk k ≤ 1 / ((k : ℝ) + 1) := fun k => min_le_right _ _
  have hCdk : ∀ k, C' * dk k ≤ 2 * m := fun k =>
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hC').trans hCd₀
  set t₀ : ℕ → ℝ≥0 := fun k => (dk k ^ 2 / 16 + 1).toNNReal with ht₀
  have hnull : ∀ k R : ℕ, P (G ∩ {ω | Band.hitTime (fun s => dk k < VR s ω - VL s ω) (T ω) <
      min (T ω) (min (Band.hitTime (fun s => ((R : ℝ≥0) : ℝ) < |B s ω|) ⊤) (t₀ k : ℝ≥0∞))}) = 0 :=
    fun k R => measure_hitEvent_eq_zero hB hW hVL hVR hC' hGm hGc hG hm ham hbm (hdk_pos k) (hCdk k) R (t₀ k)
  -- a positive lifetime makes `D` exceed some `d_k` early
  have hcover : G ∩ {ω | T ω ≠ 0} ⊆ ⋃ k : ℕ, ⋃ R : ℕ, G ∩ {ω | Band.hitTime (fun s => dk k < VR s ω - VL s ω)
      (T ω) < min (T ω) (min (Band.hitTime (fun s => ((R : ℝ≥0) : ℝ) < |B s ω|) ⊤) (t₀ k : ℝ≥0∞))} := by
    rintro ω ⟨hω, hT0⟩
    obtain ⟨hE, hBc, -⟩ := hG ω hω
    have hTpos : 0 < T ω := pos_iff_ne_zero.2 hT0
    -- a level whose square is small against `T`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (((dk k ^ 2 / 16 : ℝ)).toNNReal : ℝ≥0∞) < T ω := by
      rcases eq_or_ne (T ω) ⊤ with htop | htop
      · exact ⟨0, by rw [htop]; exact ENNReal.coe_lt_top⟩
      · have hTr : 0 < (T ω).toReal := ENNReal.toReal_pos hT0 htop
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hTr
        refine ⟨k, ?_⟩
        rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity)]
        refine (ENNReal.ofReal_lt_ofReal_iff hTr).2 (lt_of_le_of_lt ?_ hk)
        have h1 := hdk_le k
        have h2 := (hdk_pos k).le
        have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
        nlinarith
    have hab : (((dk k ^ 2 / 16 : ℝ)).toNNReal : ℝ≥0∞) < min (T ω) (t₀ k : ℝ≥0∞) := by
      refine lt_min hk ?_
      exact_mod_cast (Real.toNNReal_lt_toNNReal_iff (by positivity)).2 (by linarith)
    obtain ⟨q₂, -, haq₂, hq₂b⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hab
    obtain ⟨q₁, -, haq₁, hq₁q₂⟩ := ENNReal.lt_iff_exists_rat_btwn.1 haq₂
    have hs₁T : ((Real.toNNReal q₁ : ℝ≥0) : ℝ≥0∞) < T ω := hq₁q₂.trans (hq₂b.trans_le (min_le_left _ _))
    -- (IN2) at `s₁`
    have h16 := hE.sixteen_mul_le_sq hs₁T
    have hds : dk k ^ 2 / 16 < (Real.toNNReal q₁ : ℝ) := by
      have := haq₁
      rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe (by positivity)] at this
      exact this
    have hD0 : 0 ≤ VR (Real.toNNReal q₁) ω - VL (Real.toNNReal q₁) ω := by
      have := hE.vL_le_w _ hs₁T; have := hE.w_le_vR _ hs₁T; linarith
    have hdD : dk k < VR (Real.toNNReal q₁) ω - VL (Real.toNNReal q₁) ω := by
      have hsq : dk k ^ 2 < (VR (Real.toNNReal q₁) ω - VL (Real.toNNReal q₁) ω) ^ 2 := by linarith
      exact (pow_lt_pow_iff_left₀ (hdk_pos k).le hD0 two_ne_zero).1 hsq
    have hτd : Band.hitTime (fun s => dk k < VR s ω - VL s ω) (T ω) ≤ (Real.toNNReal q₁ : ℝ≥0) :=
      Band.hitTime_le (p := fun s => dk k < VR s ω - VL s ω) hs₁T hdD
    -- a bound for `|B|` on `[0, s₂]`
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := Real.toNNReal q₂)).exists_bound_of_continuousOn
      (f := fun s => B s ω) hBc.continuousOn
    refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨⌈M⌉₊, hω, ?_⟩⟩
    have hτR : ((Real.toNNReal q₂ : ℝ≥0) : ℝ≥0∞) ≤
        Band.hitTime (fun s => ((⌈M⌉₊ : ℝ≥0) : ℝ) < |B s ω|) ⊤ := by
      refine Band.le_hitTime fun s hs _ => not_lt.2 ?_
      have hsle : s ≤ Real.toNNReal q₂ := (by exact_mod_cast hs : s < Real.toNNReal q₂).le
      have := hM s ⟨zero_le, hsle⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (by simpa using Nat.le_ceil M)
    refine lt_of_le_of_lt hτd (lt_of_lt_of_le hq₁q₂ (le_min ?_ (le_min hτR ?_)))
    · exact (hq₂b.trans_le (min_le_left _ _)).le
    · exact (hq₂b.trans_le (min_le_right _ _)).le
  have hzero : P (G ∩ {ω | T ω ≠ 0}) = 0 :=
    measure_mono_null hcover (measure_iUnion_null fun k => measure_iUnion_null fun R => hnull k R)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_union_null hzero hGc)
  by_cases h : ω ∈ G
  · exact Or.inl ⟨h, hω⟩
  · exact Or.inr h

/-- **Aux. lemma 104** (No common-seed entrance with opposite-sign Jacobi parameters; Specification p. 350). Let `B`
be a Brownian motion of `𝓕`, let `W, V^L, V^R` be adapted before a lifetime `T` and satisfy, almost surely, (IN1) on
`[0, T)` with `W_0 = V^L_0 = V^R_0 = 0` (up to `√κ B_0`), an extra drift `e` bounded by `C`, nonnegative gaps with
null zero sets and integrable reciprocals (`IsSeedEntrance`). If `a = ρ_L + 2` and `b = ρ_R + 2` have opposite
signs (`a > 0 > b` or `b > 0 > a`), then `T = 0` almost surely: there is no positive-lifetime solution. -/
theorem ae_lifetime_eq_zero (hB : IsFilteredBrownianReal 𝓕 B P) (hW : AdaptedBefore 𝓕 T W)
    (hVL : AdaptedBefore 𝓕 T VL) (hVR : AdaptedBefore 𝓕 T VR)
    (hab : (0 < ρL + 2 ∧ ρR + 2 < 0) ∨ (0 < ρR + 2 ∧ ρL + 2 < 0))
    (hpath : ∀ᵐ ω ∂P, IsSeedEntrance κ ρL ρR C (W · ω) (VL · ω) (VR · ω) (B · ω) (e · ω) (T ω)) :
    ∀ᵐ ω ∂P, T ω = 0 := by
  rcases hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact ae_lifetime_eq_zero_of_pos_of_neg hB hW hVL hVR ha hb hpath
  · refine ae_lifetime_eq_zero_of_pos_of_neg (κ := κ) (ρL := ρR) (ρR := ρL) (C := C) (W := -W) (VL := -VR)
      (VR := -VL) (B := -B) (e := -e) hB.neg hW.neg hVR.neg hVL.neg hb ha ?_
    filter_upwards [hpath] with ω h
    exact h.reflect

end Theorem

end Aux104

end Sec7

end InteractingSLE
