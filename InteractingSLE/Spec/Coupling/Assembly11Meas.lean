import InteractingSLE.Spec.Coupling.Assembly11Path

/-!
# Measurability of the tested mean and energy for any filtration adapted to the driver

Packet PROVE-T11-ASM (obligation 5 of `planning/handoffs/PROVE-T11-L312.md` §4: "it needs `E` and `cfAt τ · 1_E` to
be measurable for the **driving** filtration's `𝓕_τ`"). For any filtration `𝓖` in which the driver and the marks are
adapted before `ζ`, and a good set `G ∈ 𝓖₀` of continuous paths:

* `measurableSet_safeSet`: the safe event at a fixed time `s` (the support of `φ` alive at `s` with `Im f_s ≥ δ`) is
  `𝓖_s`-measurable;
* `measurable_meanK`, `measurable_energyK`: on that event, the tested mean `∫ 𝔥_s φ` and the energy `E_s(φ)` are
  `𝓖_s`-measurable (the integrands are jointly measurable by Carathéodory's criterion, since the forward map and
  `log f_s'` are continuous on `supp φ` and adapted at each point);
* `measurable_stoppedPair`: at a `𝓖`-stopping time `ρ` at which `supp φ` is safe on `G`, the pair
  `(∫ 𝔥_ρ φ, E_ρ(φ))` is measurable for the stopped σ-algebra `𝓖_ρ`.

No Brownian motion and no stochastic calculus enter: only the path regularity and the adaptedness of the driver.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {nL nR : ℕ}

/-! ### Generic measurability of the two integrals -/

section Generic

variable {α : Type*} [MeasurableSpace α] {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {φ : ℂ → ℝ}

theorem measurable_meanHarmonic_prod (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable (fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ => meanHarmonic κ ρL ρR p.1 p.2.1 p.2.2) := by
  unfold meanHarmonic
  have hA := Complex.measurable_arg
  fun_prop

/-- The tested mean, from jointly measurable ingredients. -/
theorem measurable_meanIntegral_of {S : Set α} (hS : MeasurableSet S) (hφ : Measurable φ)
    {f L : ℂ → α → ℂ} (hf : Measurable fun p : ℂ × α => f p.1 p.2)
    (hL : Measurable fun p : ℂ × α => L p.1 p.2) {a : α → Fin nL → ℝ} (ha : Measurable a)
    {b : α → Fin nR → ℝ} (hb : Measurable b) :
    Measurable fun x => ∫ z, (if x ∈ S then (meanHarmonic κ ρL ρR (a x) (b x) (f z x) -
      chiC κ * (L z x).im) * φ z else 0) := by
  refine measurable_integral_param ?_
  refine Measurable.ite (measurable_snd hS) ?_ measurable_const
  refine Measurable.mul ?_ (hφ.comp measurable_fst)
  refine ((measurable_meanHarmonic_prod κ ρL ρR).comp ((ha.comp measurable_snd).prodMk
    ((hb.comp measurable_snd).prodMk hf))).sub (measurable_const.mul (Complex.measurable_im.comp hL))

/-- The energy, from a jointly measurable forward map. -/
theorem measurable_energyIntegral_of {S : Set α} (hS : MeasurableSet S) (hφ : Measurable φ)
    {f : ℂ → α → ℂ} (hf : Measurable fun p : ℂ × α => f p.1 p.2) :
    Measurable fun x => ∫ y, ∫ z, (if x ∈ S then φ y * greenH (f y x) (f z x) * φ z else 0) := by
  have hin : Measurable fun q : ℂ × α => ∫ z, (if q.2 ∈ S then
      φ q.1 * greenH (f q.1 q.2) (f z q.2) * φ z else 0) := by
    refine measurable_integral_param (f := fun z (q : ℂ × α) => if q.2 ∈ S then
      φ q.1 * greenH (f q.1 q.2) (f z q.2) * φ z else 0) ?_
    refine Measurable.ite (measurable_snd.snd hS) ?_ measurable_const
    have h1 : Measurable fun p : ℂ × (ℂ × α) => f p.2.1 p.2.2 := hf.comp measurable_snd
    have h2 : Measurable fun p : ℂ × (ℂ × α) => f p.1 p.2.2 :=
      hf.comp (measurable_fst.prodMk measurable_snd.snd)
    exact ((hφ.comp measurable_snd.fst).mul (measurable_greenH.comp (h1.prodMk h2))).mul
      (hφ.comp measurable_fst)
  exact measurable_integral_param (f := fun y x => ∫ z, (if x ∈ S then
    φ y * greenH (f y x) (f z x) * φ z else 0)) hin

end Generic

/-! ### The safe event and the adapted forward map at a fixed time -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {φ : ℂ → ℝ} {δ : ℝ}

/-- The safe event at the fixed time `s`: `ω ∈ G` and `supp φ` is alive at `s < ζ` with `Im f_s ≥ δ`. -/
def safeSet (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (φ : ℂ → ℝ) (δ : ℝ) (s : ℝ≥0) : Set Ω :=
  {ω | ω ∈ G ∧ IsSafeAt (tsupport φ) δ s s (ζ ω) (W · ω) s}

/-- The forward map at `s` on `safeSet × supp φ`, and `i` elsewhere. -/
def fwdSafe (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (φ : ℂ → ℝ) (δ : ℝ) (s : ℝ≥0) (y : ℂ)
    (ω : Ω) : ℂ :=
  if ω ∈ safeSet W ζ G φ δ s ∧ y ∈ tsupport φ then fwdMap (rpath (W · ω)) s y else Complex.I

/-- `log f_s'` at `s` on `safeSet × supp φ`, and `0` elsewhere. -/
def logSafe (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (φ : ℂ → ℝ) (δ : ℝ) (s : ℝ≥0) (y : ℂ)
    (ω : Ω) : ℂ :=
  if ω ∈ safeSet W ζ G φ δ s ∧ y ∈ tsupport φ then logDerivFwd (rpath (W · ω)) s y else 0

section Fixed

variable (hWa : AdaptedBefore 𝓖 ζ W)
  (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
  (hG : MeasurableSet[𝓖 0] G) (hφH : tsupport φ ⊆ H) (hδ : 0 < δ)

include hWa hGc hG hφH hδ in
theorem measurableSet_safeSet (s : ℝ≥0) : MeasurableSet[𝓖 s] (safeSet W ζ G φ δ s) := by
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (tsupport φ)).exists_countable_dense_subset
  have hst : IsStoppingTime 𝓖 fun _ : Ω => ((s : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓖 s
  have h := measurableSet_isSafeAt hWa hGc hG hDc (hDK.trans hφH) (σ₀ := fun _ => s) hst δ s s
  convert h using 1
  ext ω
  simp only [safeSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hω, h⟩; exact ⟨hω, h.subset hDK⟩
  · rintro ⟨hω, h⟩; exact ⟨hω, h.of_dense (hGc ω hω) hφH hKD hDK hδ⟩

theorem mem_aliveSet_of_mem_safeSet {s : ℝ≥0} {ω : Ω} (hω : ω ∈ safeSet W ζ G φ δ s) {y : ℂ}
    (hy : y ∈ tsupport φ) : ω ∈ aliveSet W ζ G y s :=
  ⟨hω.1, hω.2.1, (hω.2.2.2.2 y hy).1⟩

include hWa hGc hG hφH hδ in
theorem measurable_fwdSafe (s : ℝ≥0) :
    Measurable[(borel ℂ).prod (𝓖 s)] (fun p : ℂ × Ω => fwdSafe W ζ G φ δ s p.1 p.2) := by
  refine @measurable_uncurry_of_continuousOn ℂ Ω ℂ _ _ _ (borel ℂ) _ (𝓖 s) _ _ _ _
    _ (isClosed_tsupport φ) (fun y ω => fwdSafe W ζ G φ δ s y ω) Complex.I
    (fun ω => ?_) (fun y hy => ?_) (fun y hy ω => by simp [fwdSafe, hy])
  · by_cases hω : ω ∈ safeSet W ζ G φ δ s
    · exact (hω.2.continuousOn_fwdMap (hGc ω hω.1) hφH le_rfl).congr fun y hy => by
        simp [fwdSafe, hω, hy]
    · exact (continuousOn_const (c := Complex.I)).congr fun y _ => by simp [fwdSafe, hω]
  · have hS := measurableSet_safeSet hWa hGc hG hφH hδ s
    have hf := measurable_fwdMap_alive hWa hGc hG (hφH hy) s
    have e : (fun ω => fwdSafe W ζ G φ δ s y ω) = (safeSet W ζ G φ δ s).piecewise
        (fun ω => if ω ∈ aliveSet W ζ G y s then fwdMap (rpath (W · ω)) s y else 0)
        fun _ => Complex.I := by
      funext ω
      by_cases hω : ω ∈ safeSet W ζ G φ δ s
      · simp [fwdSafe, Set.piecewise, hω, hy, mem_aliveSet_of_mem_safeSet hω hy]
      · simp [fwdSafe, Set.piecewise, hω]
    rw [e]
    exact Measurable.piecewise hS hf measurable_const

include hWa hGc hG hφH hδ in
theorem measurable_logSafe (s : ℝ≥0) :
    Measurable[(borel ℂ).prod (𝓖 s)] (fun p : ℂ × Ω => logSafe W ζ G φ δ s p.1 p.2) := by
  refine @measurable_uncurry_of_continuousOn ℂ Ω ℂ _ _ _ (borel ℂ) _ (𝓖 s) _ _ _ _
    _ (isClosed_tsupport φ) (fun y ω => logSafe W ζ G φ δ s y ω) 0
    (fun ω => ?_) (fun y hy => ?_) (fun y hy ω => by simp [logSafe, hy])
  · by_cases hω : ω ∈ safeSet W ζ G φ δ s
    · exact (hω.2.continuousOn_logDerivFwd (hGc ω hω.1) hφH le_rfl).congr fun y hy => by
        simp [logSafe, hω, hy]
    · exact (continuousOn_const (c := (0 : ℂ))).congr fun y _ => by simp [logSafe, hω]
  · have hS := measurableSet_safeSet hWa hGc hG hφH hδ s
    have hf := measurable_logDerivFwd_alive hWa hGc hG (hφH hy) s
    have e : (fun ω => logSafe W ζ G φ δ s y ω) = (safeSet W ζ G φ δ s).piecewise
        (fun ω => if ω ∈ aliveSet W ζ G y s then logDerivFwd (rpath (W · ω)) s y else 0)
        fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ safeSet W ζ G φ δ s
      · simp [logSafe, Set.piecewise, hω, hy, mem_aliveSet_of_mem_safeSet hω hy]
      · simp [logSafe, Set.piecewise, hω]
    rw [e]
    exact Measurable.piecewise hS hf measurable_const

/-- The tested mean on the safe event at the fixed time `s` (zero off it). -/
def meanK (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω)
    (φ : ℂ → ℝ) (δ : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ safeSet W ζ G φ δ s then
    ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * φ z else 0

/-- The energy on the safe event at the fixed time `s` (zero off it). -/
def energyK (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (φ : ℂ → ℝ) (δ : ℝ) (s : ℝ≥0)
    (ω : Ω) : ℝ :=
  if ω ∈ safeSet W ζ G φ δ s then loewnerGreenEnergy (rpath (W · ω)) s φ else 0

include hWa hGc hG hφH hδ in
theorem measurable_meanK (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hφ : Measurable φ) (s : ℝ≥0) :
    Measurable[𝓖 s] (meanK κ ρL ρR W VL VR ζ G φ δ s) := by
  set a : Ω → Fin nL → ℝ := fun ω i => Girsanov.killed ζ (VL i) s ω - Girsanov.killed ζ W s ω
  set b : Ω → Fin nR → ℝ := fun ω i => Girsanov.killed ζ (VR i) s ω - Girsanov.killed ζ W s ω
  have ha : Measurable[𝓖 s] a := @Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 s) _ a fun i =>
    (Girsanov.measurable_killed (hVLa i) s).sub (Girsanov.measurable_killed hWa s)
  have hb : Measurable[𝓖 s] b := @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 s) _ b fun i =>
    (Girsanov.measurable_killed (hVRa i) s).sub (Girsanov.measurable_killed hWa s)
  have h := @measurable_meanIntegral_of nL nR Ω (𝓖 s) κ ρL ρR φ _
    (measurableSet_safeSet hWa hGc hG hφH hδ s) hφ _ _ (measurable_fwdSafe hWa hGc hG hφH hδ s)
    (measurable_logSafe hWa hGc hG hφH hδ s) a ha b hb
  convert h using 1
  funext ω
  by_cases hω : ω ∈ safeSet W ζ G φ δ s
  · simp only [meanK, hω, ↓reduceIte]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · simp only [meanCan, fwdSafe, logSafe, hω, hz, and_self, ↓reduceIte, a, b,
        Girsanov.killed_of_lt hω.2.1]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · simp [meanK, hω]

include hWa hGc hG hφH hδ in
theorem measurable_energyK (hφ : Measurable φ) (s : ℝ≥0) :
    Measurable[𝓖 s] (energyK W ζ G φ δ s) := by
  have h := @measurable_energyIntegral_of Ω (𝓖 s) φ _
    (measurableSet_safeSet hWa hGc hG hφH hδ s) hφ _ (measurable_fwdSafe hWa hGc hG hφH hδ s)
  convert h using 1
  funext ω
  by_cases hω : ω ∈ safeSet W ζ G φ δ s
  · simp only [energyK, hω, ↓reduceIte, loewnerGreenEnergy]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hy : y ∈ tsupport φ
    · by_cases hz : z ∈ tsupport φ
      · simp only [fwdSafe, hω, hy, hz, and_self, ↓reduceIte]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [energyK, hω]

end Fixed

/-! ### Stopped values -/

/-- A function that agrees on `{ρ ≤ t}` with a `𝓖_t`-measurable function, for every `t`, is measurable for the
stopped σ-algebra of the finite stopping time `ρ`. -/
theorem measurable_stoppingTime_of_forall {β : Type*} [MeasurableSpace β] {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓖 fun ω => (ρ ω : WithTop ℝ≥0)) {Y : Ω → β} {Y' : ℝ≥0 → Ω → β}
    (hY' : ∀ t, Measurable[𝓖 t] (Y' t)) (hYY : ∀ t ω, ρ ω ≤ t → Y' t ω = Y ω) :
    Measurable[hρ.measurableSpace] Y := by
  intro B hB
  have hpiece : ∀ t : ℝ≥0, Y ⁻¹' B ∩ {ω | (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      Y' t ⁻¹' B ∩ {ω | (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := fun t => by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, WithTop.coe_le_coe]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hYY t ω h2).symm ▸ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hYY t ω h2) ▸ h1, h2⟩
  have hmeas : ∀ t : ℝ≥0, MeasurableSet[𝓖 t]
      (Y ⁻¹' B ∩ {ω | (ρ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}) := fun t => by
    rw [hpiece t]; exact (hY' t hB).inter (hρ t)
  rw [IsStoppingTime.measurableSet]
  refine ⟨?_, fun t => ?_⟩
  · have hU : Y ⁻¹' B = ⋃ n : ℕ, (Y ⁻¹' B ∩ {ω | (ρ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
      ext ω
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_ofPred_eq, WithTop.coe_le_coe]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge (ρ ω)
        exact ⟨n, h, hn⟩
      · rintro ⟨n, h, -⟩; exact h
    rw [hU]
    exact MeasurableSet.iUnion fun n => (le_iSup (fun t => 𝓖 t) (n : ℝ≥0)) _ (hmeas n)
  · exact hmeas t

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The tested mean and energy at a safe stop are measurable for the stopped σ-algebra.** -/
theorem measurable_stoppedPair (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hGv : ∀ ω ∈ G, (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφH : tsupport φ ⊆ H) (hδ : 0 < δ) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓖 fun ω => (ρ ω : WithTop ℝ≥0)) {N : ℝ} {σ₀ : Ω → ℝ≥0}
    (hsafe : ∀ ω ∈ G, IsSafeAt (tsupport φ) δ N (σ₀ ω) (ζ ω) (W · ω) (ρ ω)) :
    Measurable[hρ.measurableSpace] fun ω => if ω ∈ G then
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ ω) z * φ z),
        loewnerGreenEnergy (rpath (W · ω)) (ρ ω) φ) else ((0 : ℝ), (0 : ℝ)) := by
  set X : ℝ≥0 → Ω → ℝ × ℝ := fun s ω =>
    ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * φ z),
      loewnerGreenEnergy (rpath (W · ω)) s φ) with hX
  set Kp : ℝ≥0 → Ω → ℝ × ℝ := fun s ω =>
    (meanK κ ρL ρR W VL VR ζ G φ δ s ω, energyK W ζ G φ δ s ω) with hKp
  have hK : ∀ s, Measurable[𝓖 s] (Kp s) := fun s =>
    (measurable_meanK hWa hGc hG hφH hδ κ ρL ρR hVLa hVRa hφc.measurable s).prodMk
      (measurable_energyK hWa hGc hG hφH hδ hφc.measurable s)
  have hmem : ∀ ω ∈ G, ∀ s ≤ ρ ω, ω ∈ safeSet W ζ G φ δ s := fun ω hω s hs => by
    have h := (hsafe ω hω).anti (hGc ω hω) hφH hs
    exact ⟨hω, h.1, le_rfl, le_rfl, h.2.2.2⟩
  have hagree : ∀ ω ∈ G, ∀ s ≤ ρ ω, Kp s ω = X s ω := fun ω hω s hs => by
    simp only [hKp, hX, meanK, energyK, hmem ω hω s hs, ↓reduceIte]
  have hcont : ∀ ω ∈ G, ContinuousOn (X · ω) (Iic (ρ ω)) := fun ω hω =>
    ((hsafe ω hω).continuousOn_meanInt hφc hφs (hGc ω hω) (hGv ω hω).1 (hGv ω hω).2 hφH hδ).prodMk
      ((hsafe ω hω).continuousOn_loewnerGreenEnergy hφc hφs (hGc ω hω) hφH hδ)
  have hst := measurable_stopped_of_agree hρ hK hG ((0 : ℝ), (0 : ℝ)) hagree hcont
  refine measurable_stoppingTime_of_forall hρ hst fun t ω hρt => ?_
  simp only [min_eq_right hρt, hX]

end Coupling

end InteractingSLE
