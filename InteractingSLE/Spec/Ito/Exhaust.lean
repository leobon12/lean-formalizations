import InteractingSLE.Spec.Ito.ExhaustPath
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# The natural localizing sequence of the Itô core

Packet PROVE-T11-ITO2 (Specification §3.3 L496–L550: "(3.15)–(3.17) … continuous local martingales … up to `T_* ∧
τ(z)`; these localizations exhaust every compact time interval"). For an integrated `SLE_κ(ρ)` evolution, finitely
many distinct points `z_i ∈ ℍ`, and a stopping time `σ₀` of the usual augmentation with `σ₀ < ζ` almost surely, the
exit times `ρ_n` of the level-`n` protection region (`Im f_t(z_i) ≥ m/(n+1)`, `|W|, |B|, |V| ≤ n + C₀`, `t ≤ n`,
`|f_t(z_i) − f_t(z_j)| ≥ e/(n+1)`, `t ≤ σ₀`) are stopping times of the usual augmentation (the failure set of each
path is a right neighbourhood of each of its points, so `{ρ_n < t}` is a countable union of the events `{the condition
fails at d}`, `d < t` in a countable dense set, each adapted by `measurableSet_isProtectedAt`, and the filtration is
right-continuous); they increase with `n`, they are protected, and they exhaust every horizon `t ≤ σ₀` at which the
points are alive (`exists_localizingSeq`).

With `σ₀ = τ ∧ N` for a stopping time `τ < ζ` (e.g. a stopping time of Theorem 1.1, or an announcing time of `T_*`),
this is the statement that (3.15)–(3.17) are local martingales up to `σ₀ ∧ τ(z)`; see `Spec/Ito/ExhaustMart.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Measurability of the protection event -/

theorem fwdMap_eq_zero_of_not {W : ℝ → ℝ} {T : ℝ} {z : ℂ} (h : ¬ ∃ u, IsForwardSol W z T u) :
    fwdMap W T z = 0 := by
  simp only [fwdMap, h, ↓reduceDIte]

section Measurability

variable {𝓖 : Filtration ℝ≥0 mΩ} {nL nR k : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {zs : Fin k → ℂ}

/-- On `G ∩ {s < ζ}`, the killed Loewner map is the Loewner map. -/
theorem killedFwdMap_eq {s : ℝ≥0} {z : ℂ} {ω : Ω} (hω : ω ∈ G) (hs : (s : ℝ≥0∞) < ζ ω) :
    (if ω ∈ aliveSet W ζ G z s then fwdMap (rpath (W · ω)) s z else 0) = fwdMap (rpath (W · ω)) s z := by
  by_cases h : ∃ u, IsForwardSol (rpath (W · ω)) z s u
  · have : ω ∈ aliveSet W ζ G z s := ⟨hω, hs, h⟩
    simp only [this, ↓reduceIte]
  · have : ω ∉ aliveSet W ζ G z s := fun h' => h h'.2.2
    simp only [this, ↓reduceIte, fwdMap_eq_zero_of_not h]

/-- The closed set of values defining the protection condition (apart from its order conditions). -/
def protectedValues (δ ε R : ℝ) :
    Set ((Fin k → ℂ) × ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  {x | (∀ i, δ ≤ (x.1 i).im) ∧ |x.2.1| ≤ R ∧ |x.2.2.1| ≤ R ∧ (∀ i, |x.2.2.2.1 i| ≤ R) ∧
    (∀ i, |x.2.2.2.2 i| ≤ R) ∧ ∀ i j, i ≠ j → ε ≤ ‖x.1 i - x.1 j‖}

theorem isClosed_protectedValues (δ ε R : ℝ) :
    IsClosed (protectedValues (k := k) (nL := nL) (nR := nR) δ ε R) := by
  have habs : ∀ {f : (Fin k → ℂ) × ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}, Continuous f →
      IsClosed {x | |f x| ≤ R} := fun hf => isClosed_le (continuous_abs.comp hf) continuous_const
  simp only [protectedValues, ofPred_and, ofPred_forall]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const
      (Complex.continuous_im.comp ((continuous_apply i).comp continuous_fst))) ?_
  refine IsClosed.inter (habs (continuous_fst.comp continuous_snd)) ?_
  refine IsClosed.inter (habs (continuous_fst.comp (continuous_snd.comp continuous_snd))) ?_
  refine IsClosed.inter (isClosed_iInter fun i => habs ((continuous_apply i).comp
    (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))) ?_
  refine IsClosed.inter (isClosed_iInter fun i => habs ((continuous_apply i).comp
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))) ?_
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le continuous_const
      (by fun_prop : Continuous fun x : (Fin k → ℂ) × ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
        ‖x.1 i - x.1 j‖)

/-- **The protection event is adapted**: `{ω ∈ G : the protection condition holds at time d}` is
`𝓖_d`-measurable. -/
theorem measurableSet_isProtectedAt (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (hB : Adapted 𝓖 B)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (hz : ∀ i, 0 < (zs i).im) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) (δ ε R N : ℝ) (d : ℝ≥0) :
    MeasurableSet[𝓖 d] {ω | ω ∈ G ∧ IsProtectedAt zs δ ε R N (σ₀ ω) (ζ ω) (W · ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) d} := by
  set S : Set Ω := {ω | ω ∈ G ∧ (d : ℝ≥0∞) < ζ ω} with hS
  have hSm : MeasurableSet[𝓖 d] S := by
    have h1 := hW d univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h1
    exact (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ d) _ hG).inter h1
  have hσm : MeasurableSet[𝓖 d] {ω | d ≤ σ₀ ω} := by
    have := (hσ₀.measurableSet_lt d).compl
    convert this using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_lt_coe, not_lt]
  set Fbar : Ω → (Fin k → ℂ) × ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    (fun i => if ω ∈ aliveSet W ζ G (zs i) d then fwdMap (rpath (W · ω)) d (zs i) else 0,
      Girsanov.killed ζ W d ω, B d ω, fun i => Girsanov.killed ζ (VL i) d ω,
      fun i => Girsanov.killed ζ (VR i) d ω) with hFbar
  have hFm : Measurable[𝓖 d] Fbar :=
    (@Measurable.of_eval Ω (Fin k) (fun _ => ℂ) (𝓖 d) _ _ fun i =>
      measurable_fwdMap_alive hW hGc hG (hz i) d).prodMk
      ((Girsanov.measurable_killed hW d).prodMk ((hB d).prodMk
        ((@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 d) _ _ fun i =>
          Girsanov.measurable_killed (hVL i) d).prodMk
        (@Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 d) _ _ fun i =>
          Girsanov.measurable_killed (hVR i) d))))
  have heq : {ω | ω ∈ G ∧ IsProtectedAt zs δ ε R N (σ₀ ω) (ζ ω) (W · ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) d} =
      S ∩ {ω | d ≤ σ₀ ω} ∩ {_ω | (d : ℝ) ≤ N} ∩ Fbar ⁻¹' protectedValues δ ε R := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, hS]
    constructor
    · rintro ⟨hω, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      refine ⟨⟨⟨⟨hω, h1⟩, h2⟩, h3⟩, ?_⟩
      simp only [hFbar, protectedValues, mem_ofPred_eq, killedFwdMap_eq hω h1, Girsanov.killed, h1,
        ↓reduceIte]
      exact ⟨h4, h5, h6, h7, h8, h9⟩
    · rintro ⟨⟨⟨⟨hω, h1⟩, h2⟩, h3⟩, h⟩
      simp only [hFbar, protectedValues, mem_ofPred_eq, killedFwdMap_eq hω h1, Girsanov.killed, h1,
        ↓reduceIte] at h
      exact ⟨hω, h1, h2, h3, h⟩
  rw [heq]
  exact ((hSm.inter hσm).inter (MeasurableSet.const _)).inter
    (hFm (isClosed_protectedValues δ ε R).measurableSet)

end Measurability

/-! ### The localizing sequence -/

section Sequence

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A bound for the initial force-point positions, `C₀ = ∑ |x^{i,L}| + ∑ |x^{i,R}|`. -/
def initBound (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : ℝ := ∑ i, |xL i| + ∑ i, |xR i|

theorem initBound_nonneg : 0 ≤ initBound xL xR := by
  unfold initBound; positivity

theorem abs_le_initBound_left (i : Fin nL) : |xL i| ≤ initBound xL xR :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (xL j)) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => abs_nonneg (xR j)))

theorem abs_le_initBound_right (i : Fin nR) : |xR i| ≤ initBound xL xR :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (xR j)) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => abs_nonneg (xL j)))

/-- **The natural localizing sequence** for finitely many distinct points `z_i ∈ ℍ`
(`Im z_i ≥ m > 0`, `|z_i − z_j| ≥ e > 0`) below a nondecreasing sequence of stopping times `σ₀ n < ζ` of the usual
augmentation: the level-`n` exit times `ρ_n` (thresholds `Im f ≥ m/(n+1)`, `|f(z_i) − f(z_j)| ≥ e/(n+1)`,
`|W|, |B|, |V| ≤ n + C₀`, `t ≤ n`, `t ≤ σ₀ n`) are stopping times of the usual augmentation, `ρ_n ≤ σ₀ n`,
nondecreasing in `n`, protected (the protection condition of level `n` holds at every `s ≤ ρ_n`), and they exhaust
every horizon `t ≤ σ₀ m` (any `m`) at which the points are alive. With `σ₀ n` announcing `ζ` this exhausts
`[0, ζ ∧ τ(z))`. -/
theorem exists_localizingSeq_of_seq (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k : ℕ}
    {zs : Fin k → ℂ} (hz : ∀ i, 0 < (zs i).im) {m e : ℝ} (hm : 0 < m) (hzm : ∀ i, m ≤ (zs i).im)
    (he : 0 < e) (hze : ∀ i j, i ≠ j → e ≤ ‖zs i - zs j‖) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ∀ s ≤ ρ n ω, IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1))
        ((n : ℝ) + initBound xL xR) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) s) ∧
      ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
        (∀ i, ∃ u, IsForwardSol (rpath (W · ω)) (zs i) t u) → ∀ᶠ n in atTop, t ≤ ρ n ω := by
  obtain ⟨hB, hWa, hVLa, hVRa, hpath⟩ := isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hinj : Function.Injective zs := fun i j hij => by
    by_contra hne
    have := hze i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧
    B 0 ω = 0 ∧ ∀ n, (σ₀ n ω : ℝ≥0∞) < ζ ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hB.1.cont, hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero,
      ae_all_iff.2 hσ₀ζ] with
      ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG : ∀ t, MeasurableSet[𝓖 t] G := fun t => by
    have := (measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set C := initBound xL xR with hC
  set ρ : ℕ → Ω → ℝ≥0 := fun n ω => if ω ∈ G then protectedExitTime zs (m / ((n : ℝ) + 1))
    (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (B · ω) else 0 with hρ
  have hcont : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      (∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ Continuous (B · ω) :=
    fun ω hω => ⟨(hGgood ω hω).1.2.2.2.1, (hGgood ω hω).1.2.2.2.2.1, (hGgood ω hω).1.2.2.2.2.2.1,
      (hGgood ω hω).2.1⟩
  have hδ : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  have h0 : ∀ ω ∈ G, ∀ n : ℕ, IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1))
      ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) 0 := by
    intro ω hω n
    obtain ⟨hP, -, hB0, hσζ'⟩ := hGgood ω hω
    have hσζ := hσζ' n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    have hC0 : 0 ≤ C := initBound_nonneg
    have hnC : C ≤ (n : ℝ) + C := by linarith [n.cast_nonneg (α := ℝ)]
    refine isProtectedAt_zero hz hP.1 hB0 (lt_of_le_of_lt (by exact_mod_cast zero_le) hσζ)
      (fun i => (div_le_self hm.le hn1).trans (hzm i))
      (fun i j hij => (div_le_self he.le hn1).trans (hze i j hij)) (hC0.trans hnC)
      (fun i => ?_) (fun i => ?_) n.cast_nonneg
    · rw [show VL i 0 ω = xL i from hP.2.1 i]; exact (abs_le_initBound_left i).trans hnC
    · rw [show VR i 0 ω = xR i from hP.2.2.1 i]; exact (abs_le_initBound_right i).trans hnC
  refine ⟨ρ, fun n => ?_, fun n ω => ?_, fun ω => ?_, fun n => ?_, ?_⟩
  · -- stopping times
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
    have heq : {ω | ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0)} =
        (⋃ d ∈ D ∩ Iio t, G \ {ω | ω ∈ G ∧ IsProtectedAt zs (m / ((n : ℝ) + 1))
          (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (B · ω) d}) ∪ (Gᶜ ∩ {_ω | (0 : ℝ≥0) < t}) := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion, mem_inter_iff, Set.mem_sdiff,
        mem_Iio, exists_prop, mem_compl_iff]
      by_cases hω : ω ∈ G
      · obtain ⟨hwc, hvLc, hvRc, hbc⟩ := hcont ω hω
        simp only [hρ, hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
        rw [protectedExitTime_lt_iff hwc hvLc hvRc hbc hz (hδ n) hDd]
        constructor
        · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, hnp⟩
        · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, hnp⟩
      · simp only [hρ, hω, ↓reduceIte, false_and, and_false, exists_false, false_or, not_false_eq_true,
          true_and]
    rw [heq]
    refine MeasurableSet.union (MeasurableSet.biUnion (hDc.mono inter_subset_left) fun d hd => ?_)
      ((hG t).compl.inter (MeasurableSet.const _))
    exact 𝓖.mono hd.2.le _ ((hG d).diff (measurableSet_isProtectedAt hWa hVLa hVRa hB.2.1
      (fun ω hω => (hcont ω hω).1) (hG 0) hz (hσ₀ n) _ _ _ _ d))
  · -- below σ₀
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]; exact protectedExitTime_le_sigma
    · simp only [hρ, hω, ↓reduceIte]; exact zero_le
  · -- monotone
    intro n n' hnn'
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]
      have hn : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
      exact (protectedExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith))
        (div_le_div_of_nonneg_left he.le (by positivity) (by linarith)) (by linarith) hn).trans
        (protectedExitTime_mono_sigma (hσ₀m ω hnn'))
    · simp only [hρ, hω, ↓reduceIte]; exact le_rfl
  · -- protection
    filter_upwards [hGae] with ω hω s hs
    simp only [hρ, hω, ↓reduceIte] at hs
    obtain ⟨hwc, hvLc, hvRc, hbc⟩ := hcont ω hω
    exact isProtectedAt_of_le_protectedExitTime hwc hvLc hvRc hbc hz (hδ n) ((hGgood ω hω).2.2.2 n)
      (h0 ω hω n) hs
  · -- exhaustion
    filter_upwards [hGae] with ω hω j t htσ halive
    obtain ⟨hwc, hvLc, hvRc, hbc⟩ := hcont ω hω
    have hev := eventually_le_protectedExitTime hwc hvLc hvRc hbc hz hinj m e C htσ
      (lt_of_le_of_lt (by exact_mod_cast htσ) ((hGgood ω hω).2.2.2 j)) halive
    filter_upwards [hev, eventually_ge_atTop j] with n hn hjn
    simp only [hρ, hω, ↓reduceIte]
    exact hn.trans (protectedExitTime_mono_sigma (hσ₀m ω hjn))

/-- **The natural localizing sequence below one stopping time `σ₀ < ζ`** (`exists_localizingSeq_of_seq` with the
constant sequence). -/
theorem exists_localizingSeq (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {k : ℕ}
    {zs : Fin k → ℂ} (hz : ∀ i, 0 < (zs i).im) {m e : ℝ} (hm : 0 < m) (hzm : ∀ i, m ≤ (zs i).im)
    (he : 0 < e) (hze : ∀ i j, i ≠ j → e ≤ ‖zs i - zs j‖) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ∀ s ≤ ρ n ω, IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1))
        ((n : ℝ) + initBound xL xR) n (σ₀ ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) s) ∧
      ∀ᵐ ω ∂P, ∀ t ≤ σ₀ ω, (∀ i, ∃ u, IsForwardSol (rpath (W · ω)) (zs i) t u) →
        ∀ᶠ n in atTop, t ≤ ρ n ω := by
  obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := exists_localizingSeq_of_seq hE hz hm hzm he hze
    (σ₀ := fun _ => σ₀) (fun _ => hσ₀) (fun _ => monotone_const) (fun _ => hσ₀ζ)
  exact ⟨ρ, h1, h2, h3, h4, h5.mono fun ω h t ht => h 0 t ht⟩

end Sequence

end Ito

end InteractingSLE
