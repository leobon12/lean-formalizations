import InteractingSLE.WangWu.Defs
import InteractingSLE.Spec.Ito.ExhaustMart
import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# Wang–Wu at `κ = 4`: the explicit harmonic mean and the Loewner differentials (Lemmas 3.1–3.2)

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemmas 3.1 and 3.2
(ruling R31). These are the `κ = 4` cases of the specification's Theorem 1.1 machinery (`InteractingSLE/Spec/Ito/*`,
PROVE-T11-ITO/ITO2), reused here, not re-derived:

* **Lemma 3.1.** `isBoundedHarmonicExtension_condMean` (the explicit mean (3.2) is the bounded harmonic function
  with the prescribed force-point boundary data), `eqOn_condMean` (uniqueness, Poisson extension),
  `tendsto_condMean_right`, `tendsto_condMean_left` (the boundary values `λ(1 + S_{j,R})`, `−λ(1 + S_{j,L})`), the
  bound `abs_condMean_le` (`Defs`), and **(3.4)** in martingale-problem form, localized up to `σ₀ ∧ s(z)`:
  `exists_localizing_meanAt` (`η_t(z)`, `η_t(z)² − ∫ σ²`, `η_t(z) B_t − ∫ σ` are martingales of the usual
  augmentation, `σ_t(z) = Im(2/f_t(z))`; Revuz–Yor IV: this is `dη = σ dB`).
* **Lemma 3.2.** **(3.5)**: `exists_localizing_meanAt_mul_add_greenH` (`η_t(y) η_t(z) + G_t(y,z)` is a local
  martingale, i.e. `d⟨η(y), η(z)⟩ = −dG_t(y,z)`) and the pathwise `dG_t(y,z) = −σ_t(y) σ_t(z) dt`
  (`greenH_fwdMap_eq_sub_integral'`, with `G_t(y,z) = G_ℍ(g_t y, g_t z) = G_ℍ(f_t y, f_t z)`,
  `greenH_gt_eq`); **(3.6)**: `log_confRadius_eq` (`log r_t(z) = log (2 Im z) − ∫₀ᵗ σ_s(z)² ds`),
  `antitoneOn_confRadius`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

/-! ### Lemma 3.1: the explicit mean is the bounded harmonic extension -/

/-- For centred positions `vL ≤ 0 ≤ vR`, `condMean` is the explicit extension `Impl.forceExt` of PROVE-T11-COMP. -/
theorem condMean_eq_forceExt (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) :
    condMean ρL ρR vL vR = Impl.forceExt 4 (Ito.weightWord ρL ρR) vL vR := funext fun w => by
  rw [condMean_eq_meanHarmonic, Ito.forceExt_eq_meanHarmonic 4 ρL ρR hvL hvR]

/-- **Lemma 3.1 (harmonic part).** The explicit mean (3.2) is a bounded harmonic extension of the force-point
boundary data (`−λ(1 + S_{j,L})`, `λ(1 + S_{j,R})` on the intervals between marks). -/
theorem isBoundedHarmonicExtension_condMean (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ}
    {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) :
    IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR vL vR) (forceJumpSet vL vR)
      (condMean ρL ρR vL vR) := by
  rw [condMean_eq_forceExt ρL ρR hvL hvR]
  exact Impl.isBoundedHarmonicExtension_forceExt 4 (Ito.weightWord ρL ρR) vL vR

/-- **Lemma 3.1 (uniqueness)**: every bounded harmonic extension of the data equals the explicit mean on `ℍ`. -/
theorem eqOn_condMean {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR vL vR) (forceJumpSet vL vR) u) :
    EqOn u (condMean ρL ρR vL vR) QuantumZipper.H := fun w hw => by
  rw [Ito.eqOn_meanHarmonic hvL hvR hu hw, condMean_eq_meanHarmonic]

/-- **Lemma 3.1 (boundary values, right)**: at a boundary point `x ≥ 0` off the marks, the mean tends to
`λ (1 + ∑_{v_{i,R} ≤ x} ρ_{i,R})` (`= λ(1 + S_{j,R})` on `(v_{j,R}, v_{j+1,R})`). -/
theorem tendsto_condMean_right {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) {x : ℝ} (hx : 0 ≤ x) (hxS : x ∉ forceJumpSet vL vR) :
    Tendsto (condMean ρL ρR vL vR) (𝓝[QuantumZipper.H] (x : ℂ))
      (𝓝 (wwLambda * (1 + ∑ i ∈ Finset.univ.filter (fun i => vR i ≤ x), ρR i))) := by
  have h := (isBoundedHarmonicExtension_condMean ρL ρR hvL hvR).2.2 x hxS
  rwa [show forceBoundaryData 4 ρL ρR vL vR x = boundaryData ρL ρR vL vR x from rfl,
    boundaryData_of_nonneg _ _ _ _ hx] at h

/-- **Lemma 3.1 (boundary values, left)**: at a boundary point `x < 0` off the marks, the mean tends to
`−λ (1 + ∑_{x < v_{i,L}} ρ_{i,L})` (`= −λ(1 + S_{j,L})` on `(v_{j+1,L}, v_{j,L})`). -/
theorem tendsto_condMean_left {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) {x : ℝ} (hx : x < 0) (hxS : x ∉ forceJumpSet vL vR) :
    Tendsto (condMean ρL ρR vL vR) (𝓝[QuantumZipper.H] (x : ℂ))
      (𝓝 (-wwLambda * (1 + ∑ i ∈ Finset.univ.filter (fun i => x < vL i), ρL i))) := by
  have h := (isBoundedHarmonicExtension_condMean ρL ρR hvL hvR).2.2 x hxS
  rwa [show forceBoundaryData 4 ρL ρR vL vR x = boundaryData ρL ρR vL vR x from rfl,
    boundaryData_of_neg _ _ _ _ hx] at h

/-! ### Lemma 3.1: the stochastic differential (3.4), localized -/

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The explicit bounded harmonic extensions of the transported data, at every state (`Impl.forceExt`). -/
def stateExt (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ≥0) : ℂ → ℝ :=
  Impl.forceExt 4 (Ito.weightWord ρL ρR) (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)

theorem isBoundedHarmonicExtension_stateExt (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData 4 ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (stateExt ρL ρR W VL VR ω s) :=
  Impl.isBoundedHarmonicExtension_forceExt 4 (Ito.weightWord ρL ρR) _ _

theorem isForwardSol_of_le {W' : ℝ → ℝ} {z : ℂ} {T t : ℝ} {u : ℝ → ℂ} (h : IsForwardSol W' z T u)
    (htT : t ≤ T) : IsForwardSol W' z t u :=
  ⟨h.1.mono (Icc_subset_Icc_right htT), fun s hs => h.2 s ⟨hs.1, hs.2.trans htT⟩⟩

/-- Along a path of the chain, at a time `r < ζ` at which `z` is alive, the frozen `couplingMean 4` (with any
bounded harmonic extension) is the document's mean `meanAt`. -/
theorem couplingMean_eq_meanAt_of_path {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ₀) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < ζ₀) {z : ℂ} (hz : 0 < z.im) (hsol : ∃ v, IsForwardSol (Ito.rpath w) z r v)
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR (fun i => vL i r - w r)
      (fun i => vR i r - w r)) (forceJumpSet (fun i => vL i r - w r) (fun i => vR i r - w r)) u) :
    couplingMean 4 (Ito.rpath w) r u z = meanAt ρL ρR w vL vR r z := by
  obtain ⟨-, hpos, -, -⟩ := Ito.fwdMap_facts hP hr hz hsol
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := hP
  exact couplingMean_four_eq (fun i => sub_nonpos.2 (hvLw r hr i)) (fun i => sub_nonneg.2 (hwvR r hr i)) hu
    (hpos r ⟨r.coe_nonneg, le_rfl⟩)

/-- **Lemma 3.1, (3.4) `dη_t(z) = σ_t(z) dB_t`, localized** (the specification's (3.15) at `κ = 4`). For a
nondecreasing sequence of stopping times `σ₀ n < ζ` of the usual augmentation, there are stopping times
`ρ_n ≤ σ₀ n`, nondecreasing, at which `z` is alive and which exhaust every `t ≤ σ₀ j` at which `z` is alive, such
that `η_{t∧ρ_n}(z)`, `η_{t∧ρ_n}(z)² − ∫₀^{t∧ρ_n} σ_s(z)² ds` and `η_{t∧ρ_n}(z) B_{t∧ρ_n} − ∫₀^{t∧ρ_n} σ_s(z) ds`
agree almost surely with martingales; `σ_s(z) = Im(2/f_s(z))`. -/
theorem exists_localizing_meanAt (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {z : ℂ} (hz : 0 < z.im)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω ∧ ∃ v, IsForwardSol (Ito.rpath (W · ω)) z (ρ n ω) v) ∧
      (∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω → (∃ v, IsForwardSol (Ito.rpath (W · ω)) z t v) →
        ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      ∀ n,
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z) ∧
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z ^ 2 -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0),
              ((2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) ^ 2) ∧
        ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z *
              B (min t (ρ n ω)) ω -
            ∫ s in (0 : ℝ)..(min t (ρ n ω) : ℝ≥0), (2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im := by
  obtain ⟨ρ, hst, hle, hmono, hprot, hex, hM⟩ := Ito.exists_localizing_couplingMean hE (by norm_num) hz
    hσ₀ hσ₀m hσ₀ζ (stateExt ρL ρR W VL VR) (isBoundedHarmonicExtension_stateExt ρL ρR W VL VR)
  refine ⟨ρ, hst, hle, hmono, hprot, hex, fun n => ?_⟩
  -- on almost every path the frozen mean at `t ∧ ρ_n` is `meanAt`
  have hgood : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, couplingMean 4 (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
      (stateExt ρL ρR W VL VR ω (min t (ρ n ω))) z =
      meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z := by
    filter_upwards [hE.2.2.2.2, hprot n] with ω hP hpr t
    obtain ⟨hlt, v, hv⟩ := hpr
    have hr : ((min t (ρ n ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hlt
    exact couplingMean_eq_meanAt_of_path hP hr hz
      ⟨v, isForwardSol_of_le hv (by exact_mod_cast min_le_right _ _)⟩
      (isBoundedHarmonicExtension_stateExt ρL ρR W VL VR ω _)
  obtain ⟨⟨M₁, hM₁, hM₁e⟩, ⟨M₂, hM₂, hM₂e⟩, ⟨M₃, hM₃, hM₃e⟩⟩ := hM n
  refine ⟨⟨M₁, hM₁, ?_⟩, ⟨M₂, hM₂, ?_⟩, ⟨M₃, hM₃, ?_⟩⟩
  · filter_upwards [hM₁e, hgood] with ω h1 h2 t
    rw [h1 t, h2 t]
  · filter_upwards [hM₂e, hgood] with ω h1 h2 t
    rw [h1 t, h2 t]
  · filter_upwards [hM₃e, hgood] with ω h1 h2 t
    rw [h1 t, h2 t]

/-- **Lemma 3.2, (3.5) in martingale form, localized** (the specification's (3.17) at `κ = 4`):
`η_t(y) η_t(z) + G_t(y, z)` with `G_t(y, z) = G_ℍ(f_t y, f_t z)` is a local martingale up to `σ₀ ∧ s(y) ∧ s(z)`,
with one common localizing sequence for it and for `η(y)`, `η(z)`. -/
theorem exists_localizing_meanAt_mul_add_greenH (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {y z : ℂ} (hy : 0 < y.im) (hz : 0 < z.im) (hyz : y ≠ z) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω ∧ (∃ v, IsForwardSol (Ito.rpath (W · ω)) y (ρ n ω) v) ∧
        ∃ v, IsForwardSol (Ito.rpath (W · ω)) z (ρ n ω) v) ∧
      (∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω → (∃ v, IsForwardSol (Ito.rpath (W · ω)) y t v) →
        (∃ v, IsForwardSol (Ito.rpath (W · ω)) z t v) → ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      ∀ n,
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) y *
              meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z +
            greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
              (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z)) ∧
        (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) y) ∧
        ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
          M t ω = meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z := by
  obtain ⟨ρ, hst, hle, hmono, hprot, hex, hM⟩ := Ito.exists_localizing_couplingMean_mul_add_greenH hE
    (by norm_num) hy hz hyz hσ₀ hσ₀m hσ₀ζ (stateExt ρL ρR W VL VR)
    (isBoundedHarmonicExtension_stateExt ρL ρR W VL VR)
  refine ⟨ρ, hst, hle, hmono, hprot, hex, fun n => ?_⟩
  have hgood : ∀ x : ℂ, 0 < x.im → ∀ᵐ ω ∂P,
      (∃ v, IsForwardSol (Ito.rpath (W · ω)) x (ρ n ω) v) → ∀ t : ℝ≥0,
      couplingMean 4 (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0)
        (stateExt ρL ρR W VL VR ω (min t (ρ n ω))) x =
      meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) x := by
    intro x hx
    filter_upwards [hE.2.2.2.2, hprot n] with ω hP hpr hal t
    obtain ⟨v, hv⟩ := hal
    have hr : ((min t (ρ n ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hpr.1
    exact couplingMean_eq_meanAt_of_path hP hr hx
      ⟨v, isForwardSol_of_le hv (by exact_mod_cast min_le_right _ _)⟩
      (isBoundedHarmonicExtension_stateExt ρL ρR W VL VR ω _)
  obtain ⟨⟨M₁, hM₁, hM₁e⟩, ⟨M₂, hM₂, hM₂e⟩, ⟨M₃, hM₃, hM₃e⟩⟩ := hM n
  refine ⟨⟨M₁, hM₁, ?_⟩, ⟨M₂, hM₂, ?_⟩, ⟨M₃, hM₃, ?_⟩⟩
  · filter_upwards [hM₁e, hgood y hy, hgood z hz, hprot n] with ω h1 h2 h3 hpr t
    rw [h1 t, h2 hpr.2.1 t, h3 hpr.2.2 t]
  · filter_upwards [hM₂e, hgood y hy, hprot n] with ω h1 h2 hpr t
    rw [h1 t, h2 hpr.2.1 t]
  · filter_upwards [hM₃e, hgood z hz, hprot n] with ω h1 h2 hpr t
    rw [h1 t, h2 hpr.2.2 t]

end Martingale

/-! ### Lemma 3.2: the Green kernel and the conformal radius along the flow (deterministic) -/

section Deterministic

variable {W : ℝ → ℝ} {y z : ℂ} {t : ℝ}

/-- `G_t(y, z) = G_ℍ(g_t y, g_t z) = G_ℍ(f_t y, f_t z)`: the Green function is invariant under the real
translation `g_t = f_t + W_t`. -/
theorem greenH_gt_eq (x x' : ℂ) (r : ℝ) : greenH (x + r) (x' + r) = greenH x x' := by
  have := FwdClock.greenH_sub_ofReal (x + r) (x' + r) r
  simp only [add_sub_cancel_right] at this
  exact this.symm

/-- **(3.5), integrated**: `G_t(y, z) = G_ℍ(y, z) − ∫₀ᵗ σ_s(y) σ_s(z) ds` for distinct `y, z` alive at `t`
(the specification's (3.16), `Ito.greenH_fwdMap_eq_sub_integral`). -/
theorem greenH_fwdMap_eq_sub_integral' (hW : Continuous W) (ht : 0 ≤ t) (hy : y ∈ H \ fwdHull W t)
    (hz : z ∈ H \ fwdHull W t) (hyz : y ≠ z) :
    greenH (fwdMap W t y) (fwdMap W t z) =
      greenH y z - ∫ s in (0 : ℝ)..t, (2 / fwdMap W s y).im * (2 / fwdMap W s z).im :=
  Ito.greenH_fwdMap_eq_sub_integral hW ht hy hz hyz

/-- The conformal radius of `D_t` at a point of the real-time flow: `2 Im f_t(z) exp(−Re log f_t′(z))`. -/
def confRadiusR (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  2 * (fwdMap W t z).im * Real.exp (-(logDerivFwd W t z).re)

theorem confRadius_eq_confRadiusR (w : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) :
    confRadius w t z = confRadiusR (Ito.rpath w) t z := rfl

theorem log_confRadiusR_eq_fwdLogCR (hpos : 0 < (fwdMap W t z).im) :
    Real.log (confRadiusR W t z) = Real.log 2 + FwdClock.fwdLogCR W t z := by
  rw [confRadiusR, FwdClock.fwdLogCR, Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (by norm_num) hpos.ne', Real.log_exp]
  ring

theorem sq_im_two_div (w : ℂ) : ((2 / w).im) ^ 2 = 4 * w.im ^ 2 / ‖w‖ ^ 4 := by
  rw [FwdClock.im_two_div]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · have : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    field_simp
    ring

/-- **(3.6)**: `log r_t(z) = log (2 Im z) − ∫₀ᵗ σ_s(z)² ds` for `z` alive at `t` (`r_0(z) = 2 Im z`,
`d log r_t(z) = −σ_t(z)² dt`), for a continuous driver. -/
theorem log_confRadiusR_eq (hW : Continuous W) (ht : 0 ≤ t) (hz : z ∈ H \ fwdHull W t) :
    Real.log (confRadiusR W t z) =
      Real.log (2 * z.im) - ∫ s in (0 : ℝ)..t, ((2 / fwdMap W s z).im) ^ 2 := by
  have hsol := Ito.exists_isForwardSol_of_mem ht hz
  have hd : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun r => FwdClock.fwdLogCR W r z)
      (-((2 / fwdMap W s z).im) ^ 2) (Icc 0 t) s := fun s hs => by
    rw [sq_im_two_div]
    have := FwdClock.hasDerivWithinAt_fwdLogCR hW hz.1 hsol hs
    convert this using 1
    ring
  have hc : ContinuousOn (fun s => -((2 / fwdMap W s z).im) ^ 2) (Icc 0 t) := by
    refine (Complex.continuous_im.comp_continuousOn ?_).pow 2 |>.neg
    exact continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW ht hz) fun s hs =>
      Ito.fwdMap_ne_zero hW ht hz hs
  have hFTC := Ito.integral_eq_sub_of_hasDerivWithinAt_Icc hd hc ht le_rfl
  have h0 : FwdClock.fwdLogCR W 0 z = Real.log z.im := by
    have hz0 : fwdMap W 0 z = z - W 0 := by
      have := Ito.fwdMap_eq_sub_add_integral hW ht hz (s := 0) ⟨le_rfl, ht⟩
      simpa using this
    simp [FwdClock.fwdLogCR, logDerivFwd, hz0]
  have hpos : 0 < (fwdMap W t z).im := Ito.im_fwdMap_pos hW ht hz ⟨ht, le_rfl⟩
  rw [log_confRadiusR_eq_fwdLogCR hpos, Real.log_mul (by norm_num) hz.1.ne']
  rw [intervalIntegral.integral_neg, h0] at hFTC
  linarith

/-- The conformal radius is nonincreasing along the flow (`d log r = −σ² dt ≤ 0`). -/
theorem antitoneOn_confRadiusR (hW : Continuous W) (hz : z ∈ H \ fwdHull W t) :
    AntitoneOn (fun s => confRadiusR W s z) (Icc 0 t) := by
  intro a ha b hb hab
  have hza := Ito.mem_diff_fwdHull_of_le hz ha.2
  have hzb := Ito.mem_diff_fwdHull_of_le hz hb.2
  have hpa : 0 < confRadiusR W a z := by
    have := Ito.im_fwdMap_pos hW ha.1 hza ⟨ha.1, le_rfl⟩
    unfold confRadiusR; positivity
  have hpb : 0 < confRadiusR W b z := by
    have := Ito.im_fwdMap_pos hW hb.1 hzb ⟨hb.1, le_rfl⟩
    unfold confRadiusR; positivity
  rw [← Real.log_le_log_iff hpb hpa, log_confRadiusR_eq hW hb.1 hzb, log_confRadiusR_eq hW ha.1 hza]
  have hint : IntervalIntegrable (fun s => ((2 / fwdMap W s z).im) ^ 2) volume 0 b := by
    refine ContinuousOn.intervalIntegrable_of_Icc hb.1 ?_
    refine (Complex.continuous_im.comp_continuousOn ?_).pow 2
    exact continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW hb.1 hzb) fun s hs =>
      Ito.fwdMap_ne_zero hW hb.1 hzb hs
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint.mono_set (by
    rw [uIcc_of_le ha.1, uIcc_of_le hb.1]; exact Icc_subset_Icc_right hab))
    (hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hb.1]; exact Icc_subset_Icc_left ha.1))]
  have : 0 ≤ ∫ s in a..b, ((2 / fwdMap W s z).im) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  linarith

end Deterministic

end WangWu

end InteractingSLE
