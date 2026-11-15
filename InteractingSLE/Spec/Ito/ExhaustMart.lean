import InteractingSLE.Spec.Ito.Exhaust
import InteractingSLE.Spec.Ito.Filtration

/-!
# (3.15)–(3.17) as local martingales up to `ζ ∧ τ(z)`

Packet PROVE-T11-ITO2 (Specification §3.3 L500–L513: "`𝔥_t(z)` is a continuous local martingale … (3.15) … (3.17)").
For an integrated `SLE_κ(ρ)` evolution on any filtration `𝓕` and a nondecreasing sequence of stopping times `σ₀ n` of
the usual augmentation `usualAugmentation 𝓕 P` with `σ₀ n < ζ` almost surely, the natural localizing sequence `ρ_n` of
`exists_localizingSeq_of_seq` (stopping times of the usual augmentation, `ρ_n ≤ σ₀ n`, nondecreasing, exhausting every
`t ≤ σ₀ j` at which the points are alive) makes the following processes martingales of the usual augmentation when
stopped at `ρ_n`:

* `exists_localizing_couplingMean`: **(3.15)** `𝔥_t(z)`, and `𝔥_t(z)² − ∫ Im(2/f_s(z))² ds`,
  `𝔥_t(z) B_t − ∫ Im(2/f_s(z)) ds` (so `d𝔥_t(z) = Im(2/f_t(z)) dB_t`);
* `exists_localizing_couplingMean_mul_add_greenH`: **(3.17)** `𝔥_t(y) 𝔥_t(z) + G(f_t(y), f_t(z))` for `y ≠ z`, together
  with (3.15) at `y` and at `z`, with one common sequence;
* `exists_localizing_log_fwdMap`: the Itô derivative of `log f_t(z)`;
* `exists_localizing_coordObs`: Itô's formula for any `C³` function of the Loewner coordinates.

For one stopping time `τ < ζ` of the frozen `drivingFiltration` (a stopping time of Theorem 1.1) take the constant
sequence `σ₀ n = truncTime τ N = τ ∧ N` (`isStoppingTime_truncTime_of_drivingFiltration`, `truncTime_lt`); then the
`ρ_n` exhaust `[0, τ ∧ N] ∩ [0, τ(z))`. For an announcing sequence `T_n ↑ T_* = ζ`, `T_n < ζ`, take
`σ₀ n = truncTime T_n n`; then the `ρ_n` exhaust `[0, ζ ∧ τ(z))`, which is the source's "local martingale up to
`T_* ∧ τ(z)`". To localize several processes by one common sequence, apply `exists_localizingSeq_of_seq` once and feed
`protection_of_isProtectedAt` / `protection₂_of_isProtectedAt` to the `…_usualAugmentation` theorems.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### From the protection condition to the protection hypotheses of the Itô core -/

section Protection

variable {nL nR k : ℕ} {zs : Fin k → ℂ} {δ ε R N : ℝ} {σ₀ σ : ℝ≥0} {ζ : ℝ≥0∞} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- The one-point protection hypothesis of the Itô core, from the protection condition up to `σ`. -/
theorem protection_of_isProtectedAt (hδ : 0 < δ)
    (h : ∀ s ≤ σ, IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s) (i : Fin k) :
    (σ : ℝ≥0∞) < ζ ∧ (∃ u, IsForwardSol (rpath w) (zs i) σ u) ∧
      δ ≤ (fwdMap (rpath w) σ (zs i)).im ∧ (σ : ℝ) ≤ N ∧
      ∀ s ≤ σ, |w s| ≤ R ∧ |b s| ≤ R ∧ (∀ i, |vL i s| ≤ R) ∧ ∀ i, |vR i s| ≤ R := by
  obtain ⟨h1, -, h3, h4, -⟩ := h σ le_rfl
  exact ⟨h1, exists_isForwardSol_of_im_pos (hδ.trans_le (h4 i)), h4 i, h3, fun s hs =>
    ⟨(h s hs).2.2.2.2.1, (h s hs).2.2.2.2.2.1, (h s hs).2.2.2.2.2.2.1, (h s hs).2.2.2.2.2.2.2.1⟩⟩

/-- The two-point protection hypothesis of (3.17), from the protection condition up to `σ`. -/
theorem protection₂_of_isProtectedAt (hδ : 0 < δ)
    (h : ∀ s ≤ σ, IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s) {i j : Fin k} (hij : i ≠ j) :
    (σ : ℝ≥0∞) < ζ ∧ (∃ u, IsForwardSol (rpath w) (zs i) σ u) ∧
      (∃ u, IsForwardSol (rpath w) (zs j) σ u) ∧ δ ≤ (fwdMap (rpath w) σ (zs i)).im ∧
      δ ≤ (fwdMap (rpath w) σ (zs j)).im ∧ (σ : ℝ) ≤ N ∧
      (∀ s ≤ σ, |w s| ≤ R ∧ |b s| ≤ R ∧ (∀ i, |vL i s| ≤ R) ∧ ∀ i, |vR i s| ≤ R) ∧
      ∀ s ≤ σ, ε ≤ ‖fwdMap (rpath w) s (zs i) - fwdMap (rpath w) s (zs j)‖ := by
  obtain ⟨h1, hi, h4i, h3, hb⟩ := protection_of_isProtectedAt hδ h i
  obtain ⟨-, hj, h4j, -, -⟩ := protection_of_isProtectedAt hδ h j
  exact ⟨h1, hi, hj, h4i, h4j, h3, hb, fun s hs => (h s hs).2.2.2.2.2.2.2.2 i j hij⟩

end Protection

/-! ### Truncated stopping times -/

/-- `τ ∧ N` as an `ℝ≥0`-valued time. -/
def truncTime (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0) (ω : Ω) : ℝ≥0 := min ((τ ω).untopD N) N

theorem coe_truncTime (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0) (ω : Ω) :
    ((truncTime τ N ω : ℝ≥0) : WithTop ℝ≥0) = min (τ ω) N := by
  unfold truncTime
  cases τ ω with
  | top => simp only [WithTop.untopD_top, min_self]; exact (min_eq_right le_top).symm
  | coe a => simp only [WithTop.untopD_coe, WithTop.coe_min]

theorem isStoppingTime_truncTime {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) (N : ℝ≥0) :
    IsStoppingTime 𝓖 fun ω => ((truncTime τ N ω : ℝ≥0) : WithTop ℝ≥0) := by
  simp only [coe_truncTime]
  exact hτ.min_const N

theorem truncTime_lt {τ : Ω → WithTop ℝ≥0} {ζ : Ω → ℝ≥0∞} {ω : Ω} (h : (τ ω : ℝ≥0∞) < ζ ω)
    (N : ℝ≥0) : ((truncTime τ N ω : ℝ≥0) : ℝ≥0∞) < ζ ω := by
  have h' : ((truncTime τ N ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
    rw [coe_truncTime]; exact min_le_left _ _
  exact lt_of_le_of_lt h' h

/-! ### The localized martingales -/

section Localized

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A stopping time of the frozen driving filtration, truncated at `N`, is a stopping time of the usual augmentation
of the evolution's filtration. -/
theorem isStoppingTime_truncTime_of_drivingFiltration
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (N : ℝ≥0) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => ((truncTime τ N ω : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_truncTime (isStoppingTime_usualAugmentation_of_drivingFiltration hE hX hτ) N

/-- **(3.15) as a local martingale up to `sup σ₀ ∧ τ(z)`**, with its brackets: for a nondecreasing sequence of
stopping times `σ₀ n < ζ` of the usual augmentation, there are stopping times `ρ_n ≤ σ₀ n` of the usual augmentation,
nondecreasing, with `ρ_n < ζ` and `z` alive at `ρ_n`, exhausting every `t ≤ σ₀ j` at which `z` is alive, such that
`𝔥_{t∧ρ_n}(z)`, `𝔥_{t∧ρ_n}(z)² − ∫₀^{t∧ρ_n} Im(2/f_s(z))² ds` and
`𝔥_{t∧ρ_n}(z) B_{t∧ρ_n} − ∫₀^{t∧ρ_n} Im(2/f_s(z)) ds` agree almost surely, at every time, with martingales of the
usual augmentation. -/
theorem exists_localizing_couplingMean
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω ∧ ∃ v, IsForwardSol (rpath (W · ω)) z (ρ n ω) v) ∧
      (∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω → (∃ v, IsForwardSol (rpath (W · ω)) z t v) →
        ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      ∀ n,
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
            (u ω (min t (ρ n ω))) z) ∧
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
              (u ω (min t (ρ n ω))) z ^ 2 -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0),
              ((2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) ^ 2) ∧
        ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
              (u ω (min t (ρ n ω))) z * B (min t (ρ n ω)) ω -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0),
              (2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im := by
  obtain ⟨ρ, hst, hle, hmono, hprot, hex⟩ := exists_localizingSeq_of_seq hE (zs := fun _ : Fin 1 => z)
    (fun _ => hz) (m := z.im) hz (fun _ => le_rfl) one_pos
    (fun i j hij => absurd (Subsingleton.elim i j) hij) hσ₀ hσ₀m hσ₀ζ
  have hδ : ∀ n : ℕ, 0 < z.im / ((n : ℝ) + 1) := fun n => by positivity
  have hp := fun n : ℕ => (hprot n).mono fun ω h => protection_of_isProtectedAt (hδ n) h 0
  refine ⟨ρ, hst, hle, hmono, fun n => (hp n).mono fun ω h => ⟨h.1, h.2.1⟩,
    hex.mono fun ω h j t ht hal => h j t ht fun _ => hal, fun n => ⟨?_, ?_, ?_⟩⟩
  · exact exists_martingale_couplingMean_usualAugmentation hE hκ hz (hst n) (hδ n) (hp n) u hu
  · exact exists_martingale_couplingMean_sq_usualAugmentation hE hκ hz (hst n) (hδ n) (hp n) u hu
  · exact exists_martingale_couplingMean_mul_B_usualAugmentation hE hκ hz (hst n) (hδ n) (hp n) u hu

/-- **(3.17) as a local martingale up to `sup σ₀ ∧ τ(y) ∧ τ(z)`**, together with (3.15) at both points and one
common localizing sequence: for `y ≠ z` in `ℍ` and a nondecreasing sequence of stopping times `σ₀ n < ζ` of the usual
augmentation. -/
theorem exists_localizing_couplingMean_mul_add_greenH
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {y z : ℂ}
    (hy : 0 < y.im) (hz : 0 < z.im) (hyz : y ≠ z)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω ∧ (∃ v, IsForwardSol (rpath (W · ω)) y (ρ n ω) v) ∧
        ∃ v, IsForwardSol (rpath (W · ω)) z (ρ n ω) v) ∧
      (∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω → (∃ v, IsForwardSol (rpath (W · ω)) y t v) →
        (∃ v, IsForwardSol (rpath (W · ω)) z t v) → ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      ∀ n,
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
              (u ω (min t (ρ n ω))) y *
              couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
                (u ω (min t (ρ n ω))) z +
            greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
              (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z)) ∧
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
            (u ω (min t (ρ n ω))) y) ∧
        ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
            (u ω (min t (ρ n ω))) z := by
  have hz2 : ∀ i, 0 < ((![y, z] : Fin 2 → ℂ) i).im := by
    intro i; fin_cases i
    · exact hy
    · exact hz
  have hm2 : ∀ i, min y.im z.im ≤ ((![y, z] : Fin 2 → ℂ) i).im := by
    intro i; fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have he2 : ∀ i j, i ≠ j → ‖y - z‖ ≤ ‖(![y, z] : Fin 2 → ℂ) i - (![y, z] : Fin 2 → ℂ) j‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact le_rfl
    · exact (norm_sub_rev y z).le
    · exact absurd rfl hij
  obtain ⟨ρ, hst, hle, hmono, hprot, hex⟩ := exists_localizingSeq_of_seq hE (zs := ![y, z]) hz2
    (lt_min hy hz) hm2 (norm_pos_iff.2 (sub_ne_zero.2 hyz)) he2 hσ₀ hσ₀m hσ₀ζ
  have hδ : ∀ n : ℕ, 0 < min y.im z.im / ((n : ℝ) + 1) := fun n => by
    have := lt_min hy hz; positivity
  have hε : ∀ n : ℕ, 0 < ‖y - z‖ / ((n : ℝ) + 1) := fun n => by
    have := norm_pos_iff.2 (sub_ne_zero.2 hyz); positivity
  have hp₂ := fun n : ℕ => (hprot n).mono fun ω h =>
    protection₂_of_isProtectedAt (hδ n) h (i := 0) (j := 1) (by decide)
  have hpy := fun n : ℕ => (hprot n).mono fun ω h => protection_of_isProtectedAt (hδ n) h 0
  have hpz := fun n : ℕ => (hprot n).mono fun ω h => protection_of_isProtectedAt (hδ n) h 1
  refine ⟨ρ, hst, hle, hmono, fun n => (hp₂ n).mono fun ω h => ⟨h.1, h.2.1, h.2.2.1⟩,
    hex.mono fun ω h j t ht haly halz => h j t ht fun i => ?_, fun n => ⟨?_, ?_, ?_⟩⟩
  · fin_cases i
    · exact haly
    · exact halz
  · exact exists_martingale_couplingMean_mul_add_greenH_usualAugmentation hE hκ hy hz (hst n) (hδ n)
      (hε n) (hp₂ n) u hu
  · exact exists_martingale_couplingMean_usualAugmentation hE hκ hy (hst n) (hδ n) (hpy n) u hu
  · exact exists_martingale_couplingMean_usualAugmentation hE hκ hz (hst n) (hδ n) (hpz n) u hu

/-- **The Itô derivative of `log f_t(z)`, localized up to `sup σ₀ ∧ τ(z)`** (`exists_martingale_log_fwdMap`). -/
theorem exists_localizing_log_fwdMap
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω ∧ ∃ v, IsForwardSol (rpath (W · ω)) z (ρ n ω) v) ∧
      (∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω → (∃ v, IsForwardSol (rpath (W · ω)) z t v) →
        ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      ∀ n,
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = Real.log ‖fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z‖ -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0),
              ((4 - κ) / (2 * fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
                (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
                  fwdMap (fun s : ℝ => W s.toNNReal ω) s z).re) ∧
        ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = Complex.arg (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z) -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0),
              ((4 - κ) / (2 * fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
                (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
                  fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im := by
  obtain ⟨ρ, hst, hle, hmono, hprot, hex⟩ := exists_localizingSeq_of_seq hE (zs := fun _ : Fin 1 => z)
    (fun _ => hz) (m := z.im) hz (fun _ => le_rfl) one_pos
    (fun i j hij => absurd (Subsingleton.elim i j) hij) hσ₀ hσ₀m hσ₀ζ
  have hδ : ∀ n : ℕ, 0 < z.im / ((n : ℝ) + 1) := fun n => by positivity
  have hp := fun n : ℕ => (hprot n).mono fun ω h => protection_of_isProtectedAt (hδ n) h 0
  exact ⟨ρ, hst, hle, hmono, fun n => (hp n).mono fun ω h => ⟨h.1, h.2.1⟩,
    hex.mono fun ω h j t ht hal => h j t ht fun _ => hal, fun n =>
      exists_martingale_log_fwdMap_usualAugmentation hE hκ hz (hst n) (hδ n) (hp n)⟩

/-- **Itô's formula for the Loewner coordinates, localized up to `sup σ₀ ∧ τ(z)`**, for every `C³` observable, with one
sequence for all observables (`exists_martingale_coordObs`). -/
theorem exists_localizing_coordObs
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {z : ℂ} (hz : 0 < z.im)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω ∧ ∃ v, IsForwardSol (rpath (W · ω)) z (ρ n ω) v) ∧
      (∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω → (∃ v, IsForwardSol (rpath (W · ω)) z t v) →
        ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      ∀ n, ∀ Φ : Coord nL nR × ℝ → ℝ, ContDiffOn ℝ 3 Φ (obsRegion κ) →
        ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = Φ (coordProc κ z W VL VR B (min t (ρ n ω)) ω, B (min t (ρ n ω)) ω) -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0), itoGen Φ
              (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
              (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) := by
  obtain ⟨ρ, hst, hle, hmono, hprot, hex⟩ := exists_localizingSeq_of_seq hE (zs := fun _ : Fin 1 => z)
    (fun _ => hz) (m := z.im) hz (fun _ => le_rfl) one_pos
    (fun i j hij => absurd (Subsingleton.elim i j) hij) hσ₀ hσ₀m hσ₀ζ
  have hδ : ∀ n : ℕ, 0 < z.im / ((n : ℝ) + 1) := fun n => by positivity
  have hp := fun n : ℕ => (hprot n).mono fun ω h => protection_of_isProtectedAt (hδ n) h 0
  exact ⟨ρ, hst, hle, hmono, fun n => (hp n).mono fun ω h => ⟨h.1, h.2.1⟩,
    hex.mono fun ω h j t ht hal => h j t ht fun _ => hal, fun n _ hΦ =>
      exists_martingale_coordObs_usualAugmentation hE hz (hst n) (hδ n) (hp n) hΦ⟩

end Localized

end Ito

end InteractingSLE
