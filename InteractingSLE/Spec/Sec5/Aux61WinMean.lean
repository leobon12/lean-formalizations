/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofMean

/-!
# Aux. lemma 62's mean identity for a general actual mean (piece R3 of Theorem 1.2's (E1))

Packet PROVE-AUX61-WIN. Specification Aux. lemmas 61–62 (`source/spec/p241-288.md` L427–L465, pp. 261–263) and
Astra's follow-up 4 §§1.2–1.3 (`source/external/AstraIG1/ig1_followup4_audited.txt` L150–L262, ruling R71).

In the restart chart (current tip at `0`, original target at `∞`) the actual conditional mean `M` of the field is a
harmonic function on `ℍ` with the canonical flow-line jump at the seed (`q = M − M₀` vanishes near `0`) and
**unidentified elsewhere** (old kissing points). Aux. lemma 61 ((PC1)) describes the mean at a stop `t` of the
restarted path before its first new contact: `M_t = M⁰_t + q − 𝓗_t(q|γ)`, `M⁰_t` the canonical one-line mean
(`couplingMean κ w t u₀`, `u₀` the basic word `−λ | λ`) and `𝓗_t(q|γ)` the bounded harmonic function on `ℍ ∖ K_t`
with values `q` on the slit and `0` on `ℝ`. For every smooth odd cutoff `F` with `F.f = q` near `closure K_t` and
`Δ F.f = 0` there, the Cameron–Martin projection identity `P_{ℍ∖K_t} F.f = F.f − 𝓗_t(F.f|γ) = G_{ℍ∖K_t}(1_ℍ gD F.f)`
gives `𝓗_t(q|γ) = F.f − G_{ℍ∖K_t}(1_ℍ gD F.f)`. Against a test function `φ` off `K_t` this is the **cutoff form**

  `∫ M_t φ = ∫ M⁰_t φ − E_t(φ, F.src) + ∫ (q − F.f) φ`                                    (`IsPC1`)

(`E_t` the Loewner Green cross energy, `F.src = −1_ℍ gD F.f`). It is the form produced by the Cameron–Martin tilt
(`Restart.FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel`) and consumed by the reference kernel
(`Coupling.MartMeans.IsCouplingCharFun`), and it needs no Poisson integral on `ℍ ∖ K_t`.

* `CMCut.add`, `CMCut.src_add`: cutoffs add, and so do their sources;
* `greenCross_add_right`: the cross energy is additive in its source slot;
* `IsCutoffOn F q N O₀`: `F` is a cutoff of `q` on the open set `N` (harmonic on `N`, equal to `q` on `N ∩ ℍ`, real
  points of `N` in the real window `O₀`);
* **`IsPC1`**: (PC1) in cutoff form at one time (the output of Aux. lemma 61, piece R2);
* **`integral_mean_shift_eq`** (R3, Aux. lemma 62's mean identity, Astra L242–L246): if the actual mean satisfies
  (PC1) with `q`, the reference mean `M̂_t` satisfies (PC1) with `q̂`, and `F` is a cutoff of `v = q̂ − q` near the
  hull, then `∫ M_t φ − E_t(φ, F.src) + ∫ (v − F.f) φ = ∫ M̂_t φ` — the tilted actual kernel is the reference kernel;
* **`isPC1_couplingMean_ref`**: every finite-word reference mean satisfies (PC1) with `q̂` the bounded harmonic
  extension of the difference of the data (from L1-CMI's `integral_couplingMean_shift_eq`, the basic word as `b`).

Deterministic. Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61Win

open QuantumZipper (H Hbar fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross)
open Restart.FlowStopIdentCMI (CMCut)

/-! ### Sums of cutoffs -/

namespace CutSum

/-- **The sum of two cutoffs.** -/
def add (F G : CMCut) : CMCut where
  f := fun z => F.f z + G.f z
  smooth := F.smooth.add G.smooth
  compact := F.compact.add G.compact
  odd := fun z => by rw [F.odd, G.odd]; ring

@[simp] theorem add_f (F G : CMCut) (z : ℂ) : (add F G).f z = F.f z + G.f z := rfl

theorem greenDensity_add (F G : CMCut) (z : ℂ) :
    QuantumZipper.K3.greenDensity (add F G).f z =
      QuantumZipper.K3.greenDensity F.f z + QuantumZipper.K3.greenDensity G.f z := by
  have e : (add F G).f = F.f + G.f := rfl
  have h2 : ∀ K : CMCut, ContDiffAt ℝ 2 K.f z := fun K => (K.smooth.of_le (by simp)).contDiffAt
  simp only [QuantumZipper.K3.greenDensity, e, (h2 F).laplacian_add (h2 G)]
  ring

/-- **Sources add.** -/
theorem src_add (F G : CMCut) (z : ℂ) : (add F G).src z = F.src z + G.src z := by
  by_cases hz : z ∈ H
  · rw [CMCut.src_of_mem _ hz, CMCut.src_of_mem _ hz, CMCut.src_of_mem _ hz, greenDensity_add]
    ring
  · rw [CMCut.src_of_notMem _ hz, CMCut.src_of_notMem _ hz, CMCut.src_of_notMem _ hz, add_zero]

end CutSum

/-! ### Additivity of the cross energy in the source slot -/

section Cross

variable {W : ℝ → ℝ} {t : ℝ}

theorem crossKer_add_right (φ ψ₁ ψ₂ : ℂ → ℝ) (p : ℂ × ℂ) :
    LocalExt.crossKer W t φ (fun z => ψ₁ z + ψ₂ z) p =
      LocalExt.crossKer W t φ ψ₁ p + LocalExt.crossKer W t φ ψ₂ p := by
  simp only [LocalExt.crossKer]
  ring

/-- **The cross energy is additive in its second slot** (for Green tests). -/
theorem greenCross_add_right (hW : Continuous W) (ht : 0 ≤ t) {φ ψ₁ ψ₂ : ℂ → ℝ} (hφ : IsGreenTest W t φ)
    (hψ₁ : IsGreenTest W t ψ₁) (hψ₂ : IsGreenTest W t ψ₂) :
    greenCross W t φ (fun z => ψ₁ z + ψ₂ z) = greenCross W t φ ψ₁ + greenCross W t φ ψ₂ := by
  have hψ : IsGreenTest W t fun z => ψ₁ z + ψ₂ z := by
    simpa only [one_mul] using hψ₁.combo hψ₂ 1 1
  rw [LocalExt.greenCross_eq_integral_crossKer hW ht hφ hψ, LocalExt.greenCross_eq_integral_crossKer hW ht hφ hψ₁,
    LocalExt.greenCross_eq_integral_crossKer hW ht hφ hψ₂, ← integral_add
      (LocalExt.integrable_crossKer hW ht hφ hψ₁) (LocalExt.integrable_crossKer hW ht hφ hψ₂)]
  exact integral_congr_ae (ae_of_all _ fun p => crossKer_add_right φ ψ₁ ψ₂ p)

end Cross

/-! ### Cutoffs of a harmonic function near a hull, and (PC1) in cutoff form -/

/-- **`F` is a cutoff of `q` on `N`**: `N` is open, its real points lie in the real window `O₀`, `F.f = q` on
`N ∩ ℍ`, and `F.f` is harmonic on `N` (`gD F.f = 0`). -/
structure IsCutoffOn (F : CMCut) (q : ℂ → ℝ) (N : Set ℂ) (O₀ : Set ℝ) : Prop where
  isOpen : IsOpen N
  real : ∀ z ∈ N, z.im = 0 → z.re ∈ O₀
  eq : ∀ z ∈ N, z ∈ H → F.f z = q z
  harmonic : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0

/-- The source of a cutoff on `N ⊇ K` vanishes on `K`, so it is a Green test at every time whose hull lies in `N`. -/
theorem IsCutoffOn.isGreenTest_src {F : CMCut} {q : ℂ → ℝ} {N : Set ℂ} {O₀ : Set ℝ} (hF : IsCutoffOn F q N O₀)
    {W : ℝ → ℝ} {t : ℝ} (hKN : closure (fwdHull W t) ⊆ N) : IsGreenTest W t F.src := by
  refine F.isGreenTest_src (Set.disjoint_left.2 fun z hz hzK => ?_)
  have hzN : z ∈ N := hKN (subset_closure hzK)
  -- `gD F.f` vanishes on the open set `N`, so `z` is not in its topological support
  have hloc : ∀ᶠ y in 𝓝 z, QuantumZipper.K3.greenDensity F.f y = 0 :=
    Filter.eventually_of_mem (hF.isOpen.mem_nhds hzN) hF.harmonic
  exact (notMem_tsupport_iff_eventuallyEq.2 hloc) hz

/-- **(PC1) in cutoff form** (the output of Aux. lemma 61 at one time `t` of the restarted driver `w`): for every
cutoff `F` of `q` on an open `N` whose real points lie in `O₀` and which contains the seed `0` and `closure K_t`,
and every test
function `φ` off `K_t`, `∫ M_t φ = ∫ M⁰_t φ − E_t(φ, F.src) + ∫ (q − F.f) φ`, where `M⁰_t = couplingMean κ w t u₀`. -/
def IsPC1 (κ : ℝ) (u₀ : ℂ → ℝ) (w : ℝ → ℝ) (t : ℝ) (q : ℂ → ℝ) (O₀ : Set ℝ) (Mt : ℂ → ℝ) : Prop :=
  ∀ (F : CMCut) (N : Set ℂ), IsCutoffOn F q N O₀ → (0 : ℂ) ∈ N → closure (fwdHull w t) ⊆ N →
    ∀ φ : TestOn upperHalfPlaneOpens, Disjoint (tsupport φ) (fwdHull w t) →
      (∫ z, Mt z * φ z) =
        (∫ z, couplingMean κ w t u₀ z * φ z) - greenCross w t φ F.src + ∫ z, (q z - F.f z) * φ z

/-- (PC1) is monotone in the real window. -/
theorem IsPC1.mono {κ : ℝ} {u₀ : ℂ → ℝ} {w : ℝ → ℝ} {t : ℝ} {q : ℂ → ℝ} {O₀ O₁ : Set ℝ} {Mt : ℂ → ℝ}
    (h : IsPC1 κ u₀ w t q O₁ Mt) (hO : O₀ ⊆ O₁) : IsPC1 κ u₀ w t q O₀ Mt :=
  fun F N hF h0 hKN φ hφ => h F N ⟨hF.isOpen, fun z hz h0 => hO (hF.real z hz h0), hF.eq, hF.harmonic⟩ h0 hKN φ hφ

/-! ### The explicit mean of one cutoff -/

/-- **The (PC1) mean read through one cutoff** `F` of `q`: `M⁰_t + G_{ℍ∖K_t}(1_ℍ gD F.f) + (q − F.f)`, the
pointwise form of `M⁰_t + q − 𝓗_t(q|γ)` (Aux. lemma 61) when `F.f = q` near `closure K_t`. -/
def meanF (κ : ℝ) (u₀ q : ℂ → ℝ) (F : CMCut) (w : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  couplingMean κ w t u₀ z + GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t z + (q z - F.f z)

/-- The cross energy against a cutoff's source is minus the Green potential paired with the test (no integrability
needed: pointwise rewriting under the integrals). -/
theorem greenCross_src_eq (F : CMCut) (w : ℝ → ℝ) (t : ℝ) (φ : ℂ → ℝ) :
    greenCross w t φ F.src =
      -∫ y, GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t y * φ y := by
  rw [LocalExt.greenCross_eq_integral_mul, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have e : (fun z => greenH (fwdMap w t y) (fwdMap w t z) * F.src z) =
      fun z => -(greenH (fwdMap w t y) (fwdMap w t z) * H.indicator (QuantumZipper.K3.greenDensity F.f) z) := by
    funext z
    simp only [CMCut.src]
    ring
  simp only [e, integral_neg, GB7a.greenPot]
  ring

/-- **The Green-potential term is integrable against a test off the hull** (from the product integrability of the
cross kernel). -/
theorem integrable_greenPot_mul {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {F : CMCut}
    (hF : IsGreenTest w t F.src) (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull w t)) :
    Integrable fun y => GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t y * φ y := by
  have hφG := LocalExt.isGreenTest_of_testOn φ hφ
  have hI := (LocalExt.integrable_crossKer hw ht hφG hF).integral_prod_left
  refine (hI.neg).congr (ae_of_all _ fun y => ?_)
  simp only [Pi.neg_apply]
  have e : ∀ z, LocalExt.crossKer w t φ F.src (y, z) =
      φ y * greenH (fwdMap w t y) (fwdMap w t z) * F.src z := fun z =>
    (LocalExt.crossKer_eq hφG.alive hF.alive y z).symm
  simp only [e]
  have e2 : (fun z => φ y * greenH (fwdMap w t y) (fwdMap w t z) * F.src z) =
      fun z => -(φ y * (greenH (fwdMap w t y) (fwdMap w t z) *
        H.indicator (QuantumZipper.K3.greenDensity F.f) z)) := by
    funext z
    simp only [CMCut.src]
    ring
  rw [e2, integral_neg, integral_const_mul, neg_neg, GB7a.greenPot]
  ring

/-- **The explicit mean satisfies the cutoff identity of (PC1) for its own cutoff.** -/
theorem integral_meanF_eq {κ : ℝ} {u₀ q : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hq : ContinuousOn q H) {F : CMCut} {w' : ℝ≥0 → ℝ} (hw' : Continuous w') {t : ℝ≥0}
    (hF : IsGreenTest (Ito.rpath w') t F.src) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    (∫ z, meanF κ u₀ q F (Ito.rpath w') t z * φ z) =
      (∫ z, couplingMean κ (Ito.rpath w') t u₀ z * φ z) - greenCross (Ito.rpath w') t φ F.src +
        ∫ z, (q z - F.f z) * φ z := by
  have hw : Continuous (Ito.rpath w') := hw'.comp continuous_real_toNNReal
  have i₁ := LocalExt.integrable_couplingMean_mul (κ := κ) hw.continuousOn hu₀ hφ
  have i₂ := integrable_greenPot_mul hw t.coe_nonneg hF φ hφ
  have i₃ : Integrable fun z => (q z - F.f z) * φ z :=
    LocalExt.integrable_mul_testOn (u₀ := fun z => q z - F.f z) (hq.sub F.smooth.continuous.continuousOn) φ
  have i₁₂ : Integrable fun z => couplingMean κ (Ito.rpath w') t u₀ z * φ z +
      GB7a.greenPot (Ito.rpath w') (H.indicator (QuantumZipper.K3.greenDensity F.f)) t z * φ z := i₁.add i₂
  rw [greenCross_src_eq, sub_neg_eq_add, ← integral_add i₁ i₂, ← integral_add i₁₂ i₃]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [meanF]
  ring

/-! ### R3: the tilted actual mean is the reference mean -/

/-- **Aux. lemma 62's mean identity for a general actual mean** (piece R3; Astra's follow-up 4 L242–L246, spec p. 263:
"Applying (PC1) to the actual and the reference canonical means, and using `f = v` on the range and in its buffer, shows
that the weighted mean agrees […] with `M̂_A`"). If the actual mean `M_t` satisfies (PC1) with `q`, the reference mean
`M̂_t` satisfies (PC1) with `qR`, `q` has some cutoff near `closure K_t`, and `F` is a cutoff of `v = qR − q` near
`closure K_t`, then for every test `φ` off `K_t`: `∫ M_t φ − E_t(φ, F.src) + ∫ (v − F.f) φ = ∫ M̂_t φ`. -/
theorem integral_mean_shift_eq {κ : ℝ} {u₀ : ℂ → ℝ} {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {q qR Mt MR : ℂ → ℝ} {O₀ : Set ℝ} (hq : ContinuousOn q H) (hqR : ContinuousOn qR H)
    (hM : IsPC1 κ u₀ W t q O₀ Mt) (hMR : IsPC1 κ u₀ W t qR O₀ MR)
    {Fq : CMCut} {Nq : Set ℂ} (hFq : IsCutoffOn Fq q Nq O₀) (h0q : (0 : ℂ) ∈ Nq)
    (hKq : closure (fwdHull W t) ⊆ Nq) {F : CMCut} {N : Set ℂ} (hF : IsCutoffOn F (fun z => qR z - q z) N O₀)
    (h0N : (0 : ℂ) ∈ N) (hKN : closure (fwdHull W t) ⊆ N)
    (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull W t)) :
    (∫ z, Mt z * φ z) - greenCross W t φ F.src + ∫ z, ((qR z - q z) - F.f z) * φ z = ∫ z, MR z * φ z := by
  set FR : CMCut := CutSum.add Fq F with hFR
  have hFRc : IsCutoffOn FR qR (Nq ∩ N) O₀ := by
    refine ⟨hFq.isOpen.inter hF.isOpen, fun z hz h0 => hFq.real z hz.1 h0, fun z hz hzH => ?_, fun z hz => ?_⟩
    · rw [hFR, CutSum.add_f, hFq.eq z hz.1 hzH, hF.eq z hz.2 hzH]
      ring
    · rw [hFR, CutSum.greenDensity_add, hFq.harmonic z hz.1, hF.harmonic z hz.2, add_zero]
  have hKNR : closure (fwdHull W t) ⊆ Nq ∩ N := subset_inter hKq hKN
  have e₁ := hM Fq Nq hFq h0q hKq φ hφ
  have e₂ := hMR FR (Nq ∩ N) hFRc ⟨h0q, h0N⟩ hKNR φ hφ
  -- the cross energies add
  have hsrc : FR.src = fun z => Fq.src z + F.src z := funext fun z => CutSum.src_add Fq F z
  have hcross : greenCross W t φ FR.src = greenCross W t φ Fq.src + greenCross W t φ F.src := by
    rw [hsrc]
    exact greenCross_add_right hW ht (LocalExt.isGreenTest_of_testOn φ hφ) (hFq.isGreenTest_src hKq)
      (hF.isGreenTest_src hKN)
  -- the shift integrals add
  have hc₁ : ContinuousOn (fun z => q z - Fq.f z) H := hq.sub Fq.smooth.continuous.continuousOn
  have hc₂ : ContinuousOn (fun z => (qR z - q z) - F.f z) H := (hqR.sub hq).sub F.smooth.continuous.continuousOn
  have i₁ := LocalExt.integrable_mul_testOn hc₁ φ
  have i₂ := LocalExt.integrable_mul_testOn hc₂ φ
  have hshift : (∫ z, (qR z - FR.f z) * φ z) =
      (∫ z, (q z - Fq.f z) * φ z) + ∫ z, ((qR z - q z) - F.f z) * φ z := by
    rw [← integral_add i₁ i₂]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hFR, CutSum.add_f]
    ring
  rw [e₂, hcross, hshift, e₁]
  ring

/-! ### The finite-word reference mean satisfies (PC1) -/

/-- (PC1) only reads the canonical mean through `u₀` on `ℍ`. -/
theorem IsPC1.congr_u₀ {κ : ℝ} {u₀ u₀' : ℂ → ℝ} {w : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hw : ContinuousOn w (Icc 0 t))
    {q : ℂ → ℝ} {O₀ : Set ℝ} {Mt : ℂ → ℝ} (h : IsPC1 κ u₀ w t q O₀ Mt) (he : EqOn u₀ u₀' H) :
    IsPC1 κ u₀' w t q O₀ Mt := by
  intro F N hF h0 hKN φ hφ
  rw [h F N hF h0 hKN φ hφ]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp [hz]
  have hzA : z ∈ H \ fwdHull w t :=
    ⟨φ.tsupport_subset (subset_tsupport _ hz), fun hK => Set.disjoint_left.1 hφ (subset_tsupport _ hz) hK⟩
  have hfH : fwdMap w t z ∈ H :=
    Ito.im_fwdMap_pos_of_continuousOn ht hw hzA.1 (Ito.exists_isForwardSol_of_mem ht hzA) ⟨ht, le_rfl⟩
  simp only [couplingMean, he hfH]

section Ref

open Restart.FlowStopIdentCMI (geomL geomR)

variable {κ : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ} [DecidablePred (· ∈ O)]

/-- **The finite-word reference mean satisfies (PC1)** in the chart of its seed (`y = 0`): for words `b`, `bR` agreeing
on the open real window `O ∋ 0`, `q̂` the bounded harmonic extension of `bR − b`, a continuous driver `w′` from `0` with
generating trace `η`, and `t > 0`: the coupling mean `M^{bR}_t` satisfies (PC1) with `q̂` and the `b`-word's mean
`u₀` (L1-CMI's `integral_couplingMean_shift_eq`). With `b` the basic word `−λ | λ` this is (PC1) for the reference. -/
theorem isPC1_couplingMean_ref (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) (h0O : (0 : ℝ) ∈ O)
    (θ : ℝ) {qR : ℂ → ℝ} (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) qR)
    {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0) {t : ℝ≥0} (ht : 0 < t) {η : ℝ → ℂ}
    (hηc : ContinuousOn η (Icc 0 t)) (hfill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') s = fillH (η '' Icc 0 s))
    {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ 0 θ) (flowLineRhoR κ bR Ĵ 0 θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ 0 i)) (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ 0 j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL b J 0 i)) (fun j => geomR (Ito.rpath w') t (flowLineXR b J 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL b J 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR b J 0 j))) u) :
    IsPC1 κ u (Ito.rpath w') t qR O (couplingMean κ (Ito.rpath w') t uR) := by
  intro F N hF h0 hKN φ hφ
  have hKN' : closure (fwdHull (Ito.rpath w') t) ⊆ (fun z => z + ((0 : ℝ) : ℂ)) ⁻¹' N := by
    intro z hz
    simpa only [mem_preimage, Complex.ofReal_zero, add_zero] using hKN hz
  have hF0 : ∀ z ∈ N, z ∈ H → F.f z = qR z := hF.eq
  have h0N : ((0 : ℝ) : ℂ) ∈ N := by simpa only [Complex.ofReal_zero] using h0
  have e := Restart.FlowStopIdentCMI.integral_couplingMean_shift_eq hκ hb hbR hO hbO h0O θ hq hF.isOpen hF.real
    hF0 hF.harmonic h0N hw' hw0 ht hηc hfill hKN' huR hu φ hφ
  have hg : QuantumZipper.K3.greenDensity (F.shift 0).f = QuantumZipper.K3.greenDensity F.f := funext fun z => by
    rw [Restart.FlowStopIdentCMI.CMCut.greenDensity_shift, Complex.ofReal_zero, add_zero]
  have hsrc : (F.shift 0).src = F.src := funext fun z => by simp only [CMCut.src, hg]
  have hqc : ContinuousOn (fun z => qR (z + ((0 : ℝ) : ℂ)) - (F.shift 0).f z) H := by
    have h1 : ContinuousOn qR H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
    refine (h1.comp (continuousOn_id.add continuousOn_const) fun z hz => Exist.add_real_mem_H hz 0).sub
      (F.shift 0).smooth.continuous.continuousOn
  have hT : Restart.FlowStopIdentCMI.chartShift F qR 0 φ = ∫ z, (qR z - F.f z) * φ z := by
    rw [Restart.FlowStopIdentCMI.chartShift, SupercriticalConformalCovariance.GM24.smoothDist_apply hqc φ]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Restart.FlowStopIdentCMI.CMCut.shift_f, Complex.ofReal_zero, add_zero]
    ring
  rw [hsrc, hT] at e
  linarith

/-- **(PC1) for the finite-word reference at time `0`** (no hull; every cutoff works). -/
theorem isPC1_couplingMean_ref_zero (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) (h0O : (0 : ℝ) ∈ O)
    (θ : ℝ) {qR : ℂ → ℝ} (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) qR)
    {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0) {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ 0 θ) (flowLineRhoR κ bR Ĵ 0 θ)
        (fun i => geomL (Ito.rpath w') 0 (flowLineXL bR Ĵ 0 i)) (fun j => geomR (Ito.rpath w') 0 (flowLineXR bR Ĵ 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') 0 (flowLineXL bR Ĵ 0 i))
        (fun j => geomR (Ito.rpath w') 0 (flowLineXR bR Ĵ 0 j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (fun i => geomL (Ito.rpath w') 0 (flowLineXL b J 0 i)) (fun j => geomR (Ito.rpath w') 0 (flowLineXR b J 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') 0 (flowLineXL b J 0 i))
        (fun j => geomR (Ito.rpath w') 0 (flowLineXR b J 0 j))) u) :
    IsPC1 κ u (Ito.rpath w') ((0 : ℝ≥0) : ℝ) qR O (couplingMean κ (Ito.rpath w') ((0 : ℝ≥0) : ℝ) uR) := by
  intro F N hF h0 hKN φ hφ
  have e := Restart.FlowStopIdentCMI.integral_couplingMean_shift_eq_zero hκ hb hbR hO hbO h0O θ F hq hw' hw0
    (by simpa only [NNReal.coe_zero] using huR) (by simpa only [NNReal.coe_zero] using hu) φ
  have hg : QuantumZipper.K3.greenDensity (F.shift 0).f = QuantumZipper.K3.greenDensity F.f := funext fun z => by
    rw [Restart.FlowStopIdentCMI.CMCut.greenDensity_shift, Complex.ofReal_zero, add_zero]
  have hsrc : (F.shift 0).src = F.src := funext fun z => by simp only [CMCut.src, hg]
  have hqc : ContinuousOn (fun z => qR (z + ((0 : ℝ) : ℂ)) - (F.shift 0).f z) H := by
    have h1 : ContinuousOn qR H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
    refine (h1.comp (continuousOn_id.add continuousOn_const) fun z hz => Exist.add_real_mem_H hz 0).sub
      (F.shift 0).smooth.continuous.continuousOn
  have hT : Restart.FlowStopIdentCMI.chartShift F qR 0 φ = ∫ z, (qR z - F.f z) * φ z := by
    rw [Restart.FlowStopIdentCMI.chartShift, SupercriticalConformalCovariance.GM24.smoothDist_apply hqc φ]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Restart.FlowStopIdentCMI.CMCut.shift_f, Complex.ofReal_zero, add_zero]
    ring
  rw [hsrc, hT] at e
  simp only [NNReal.coe_zero] at e ⊢
  linarith

end Ref

/-- **R3 with the actual mean given through one cutoff** (`meanF`): the tilted actual mean is the reference mean. -/
theorem integral_meanF_shift_eq {κ : ℝ} {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    {w' : ℝ≥0 → ℝ} (hw' : Continuous w') {t : ℝ≥0} {q qR MR : ℂ → ℝ} {O₀ : Set ℝ} (hq : ContinuousOn q H)
    (hqR : ContinuousOn qR H) (hMR : IsPC1 κ u₀ (Ito.rpath w') t qR O₀ MR) {O₁ : Set ℝ}
    {Fq : CMCut} {Nq : Set ℂ} (hFq : IsCutoffOn Fq q Nq O₁) (h0q : (0 : ℂ) ∈ Nq)
    (hKq : closure (fwdHull (Ito.rpath w') t) ⊆ Nq) {F : CMCut} {N : Set ℂ}
    (hF : IsCutoffOn F (fun z => qR z - q z) N O₀) (h0N : (0 : ℂ) ∈ N)
    (hKN : closure (fwdHull (Ito.rpath w') t) ⊆ N) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    (∫ z, meanF κ u₀ q Fq (Ito.rpath w') t z * φ z) - greenCross (Ito.rpath w') t φ F.src +
      ∫ z, ((qR z - q z) - F.f z) * φ z = ∫ z, MR z * φ z := by
  have hw : Continuous (Ito.rpath w') := hw'.comp continuous_real_toNNReal
  set FR : CMCut := CutSum.add Fq F with hFR
  have hFRc : IsCutoffOn FR qR (Nq ∩ N) O₀ := by
    refine ⟨hFq.isOpen.inter hF.isOpen, fun z hz h0 => hF.real z hz.2 h0, fun z hz hzH => ?_, fun z hz => ?_⟩
    · rw [hFR, CutSum.add_f, hFq.eq z hz.1 hzH, hF.eq z hz.2 hzH]
      ring
    · rw [hFR, CutSum.greenDensity_add, hFq.harmonic z hz.1, hF.harmonic z hz.2, add_zero]
  have e₁ := integral_meanF_eq (κ := κ) hu₀ hq hw' (hFq.isGreenTest_src hKq) φ hφ
  have e₂ := hMR FR (Nq ∩ N) hFRc ⟨h0q, h0N⟩ (subset_inter hKq hKN) φ hφ
  have hsrc : FR.src = fun z => Fq.src z + F.src z := funext fun z => CutSum.src_add Fq F z
  have hcross : greenCross (Ito.rpath w') t φ FR.src =
      greenCross (Ito.rpath w') t φ Fq.src + greenCross (Ito.rpath w') t φ F.src := by
    rw [hsrc]
    exact greenCross_add_right hw t.coe_nonneg (LocalExt.isGreenTest_of_testOn φ hφ) (hFq.isGreenTest_src hKq)
      (hF.isGreenTest_src hKN)
  have hc₁ : ContinuousOn (fun z => q z - Fq.f z) H := hq.sub Fq.smooth.continuous.continuousOn
  have hc₂ : ContinuousOn (fun z => (qR z - q z) - F.f z) H := (hqR.sub hq).sub F.smooth.continuous.continuousOn
  have hshift : (∫ z, (qR z - FR.f z) * φ z) =
      (∫ z, (q z - Fq.f z) * φ z) + ∫ z, ((qR z - q z) - F.f z) * φ z := by
    rw [← integral_add (LocalExt.integrable_mul_testOn hc₁ φ) (LocalExt.integrable_mul_testOn hc₂ φ)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hFR, CutSum.add_f]
    ring
  rw [e₂, hcross, hshift, e₁]
  ring

end InteractingSLE.Sec5.Aux61Win
