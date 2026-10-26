import SupercriticalConformalCovariance.BiLip.Assembly
import SupercriticalConformalCovariance.BiLip.Tight
import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SupercriticalConformalCovariance.BiLip.Port.Inverse
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalLQGUniqueness.B2.QPos.QPosClosure

/-!
# Lemma 2.1 (bi-Lipschitz comparison), paper l. 90–148, assembled

**Lemma 2.1.** There exists a deterministic `C = C(ξ) ≥ 1`, independent of `U` and `φ`, such that almost
surely `C⁻¹ d(u, v) ≤ e(u, v) ≤ C d(u, v)` for `u, v ∈ U`.

Forward convention (l. 32–40): `h` is (the restriction to `U` of) a normalized whole-plane GFF,
`d = D_h(·,·;U)`, and `e(u, v) = D_{h^φ}(φ u, φ v; V)` for the target field
`h^φ = h ∘ φ⁻¹ + Q log |(φ⁻¹)′|` on `V` (`confPullbackField Q hψ (h|_U)`, `ψ = φ⁻¹`), given through a
realization `h^φ = g₀|_V + k` (`IsDomainRealization`) on the same probability space, the domain metric being
`domainMetric ξ D V g₀ k` (working copies of the statement candidates in `SupercriticalConformalCovariance.BiLip.Cand` / `SupercriticalConformalCovariance.Domain.Cand`).

`lemma21_of_inputs` proves the lemma from two explicitly stated inputs, which are the parts of the printed
proof NOT proved here:
* `TargetTightUniform ξ Q D` — step 2 (l. 108–127), the marginal tightness of the pulled-back metric,
  uniformly over all `(U, φ)` (this is where `C` becomes independent of `U` and `φ`);
* `GoodEventsLocal ξ Q D` — step 4 (l. 136–138), "the events are local modulo an additive constant", i.e.
  both good events are annulus-local (`AEEventIn` of `localSigma`).
Everything else is proved: step 1 (the sealed annulus tail bounds, `source_tails`), step 3 (`prob_lt_of_tails`),
the good covers and Borel–Cantelli, the loop chaining with the repaired `l4_chain` and the endpoint
closure by Lemma 1.2 (`le_of_goodCovers`), both directions, on one almost-sure event.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale IsStrongLQGMetric IsLFPPExponent
  IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails (nrm)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization
  domainMetric)
open SupercriticalConformalCovariance.Cover (localSigma)
open LQGMetric (DistC restrictTo)
open LQGMetric.Blueprint (AEEventIn)

/-- The data of one instance of Lemma 2.1: domains `U, V`, a conformal bijection `φ : U → V`, a normalized
whole-plane GFF `h`, and a realization `(g₀, k)` of the target field
`h^φ = h ∘ φ⁻¹ + Q log |(φ⁻¹)′| = confPullbackField Q (φ⁻¹) (h|_U)` on `V`, all on one probability space. -/
def IsInstance (Q : ℝ) (U V : Opens ℂ) {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)) :
    Prop :=
  IsNormalizedWholePlaneGFF h P ∧
    IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) (restrictTo U (h ω)))
      g₀ k

/-- the two normalized target tails at `(z, r)` at level `M` are at most `δ` (`ρ = r |φ′(z)|`):
`P[e(around A_{9ρ/8,15ρ/8}(φ z)) > M m_{z,r}] ≤ δ` and `P[e(across cl A_{5ρ/8,7ρ/8}(φ z)) < M⁻¹ m_{z,r}] ≤ δ` -/
def TargetTailsLE (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) {V : Opens ℂ} (φ : ℂ → ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ))
    (M δ : ℝ) (z : ℂ) (r : ℝ) : Prop :=
  P {ω | ENNReal.ofReal M * nrm ξ Q (h ω) r z <
      tAround (D (g₀ ω)) ξ (k ω) (φ z) (9 / 8 * (r * ‖deriv φ z‖)) (15 / 8 * (r * ‖deriv φ z‖))} ≤
      ENNReal.ofReal δ ∧
    P {ω | tAcr (D (g₀ ω)) ξ (k ω) (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖)) <
      ENNReal.ofReal M⁻¹ * nrm ξ Q (h ω) r z} ≤ ENNReal.ofReal δ

/-- **Step 2, uniform form** (l. 108–127): the marginal tightness of the pulled-back metric, normalized by
the SOURCE circle average `m_{z,r} = r^{ξQ} e^{ξ h_r(z)}`, with one `M` for every instance (chosen before
`(U, φ)`), uniformly over `z ∈ L` compact and small `r`. -/
def TargetTightUniform (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 0 < M ∧
    ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
      ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
        TargetTailsLE ξ Q D φ P h g₀ k M δ z r

/-- **Step 4** (l. 136–138, transported locality): for every instance and every `K`, both good events are,
on small scales around every compact `L ⊆ U`, almost surely events of the field on the enlarged annulus
modulo its circle average (`localSigma`). -/
def GoodEventsLocal (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
  ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
    ∀ K : ℝ≥0∞, 0 < K → K < ∞ →
    ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
      AEEventIn P (localSigma h z r) (goodEvent₁ D ξ φ h g₀ k K z r) ∧
        AEEventIn P (localSigma h z r) (goodEvent₂ D ξ φ h g₀ k K z r)

theorem tails_mono {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X Y m : Ω → ℝ≥0∞) {M M' δ : ℝ}
    (hM : 0 < M) (hMM : M ≤ M')
    (hX : P {ω | ENNReal.ofReal M * m ω < X ω} ≤ ENNReal.ofReal δ)
    (hY : P {ω | Y ω < ENNReal.ofReal M⁻¹ * m ω} ≤ ENNReal.ofReal δ) :
    P {ω | ENNReal.ofReal M' * m ω < X ω} ≤ ENNReal.ofReal δ ∧
      P {ω | Y ω < ENNReal.ofReal M'⁻¹ * m ω} ≤ ENNReal.ofReal δ := by
  constructor
  · refine le_trans (measure_mono fun ω (hω : ENNReal.ofReal M' * m ω < X ω) => ?_) hX
    exact lt_of_le_of_lt (mul_le_mul_left (ENNReal.ofReal_le_ofReal hMM) _) hω
  · refine le_trans (measure_mono fun ω (hω : Y ω < ENNReal.ofReal M'⁻¹ * m ω) => ?_) hY
    exact lt_of_lt_of_le hω (mul_le_mul_left (ENNReal.ofReal_le_ofReal (inv_anti₀ hM hMM)) _)

/-- **Lemma 2.1** (l. 90–148), from the two open inputs. There is a deterministic `C ≥ 1`, depending only
on `(ξ, Q, D)` and chosen BEFORE `U` and `φ`, such that for every instance, almost surely, simultaneously for
all `u, v ∈ U`, `C⁻¹ d(u, v) ≤ e(u, v) ≤ C d(u, v)`, with `d = D_h(·,·;U)` and
`e(u, v) = D_{h^φ}(φ u, φ v; V)` the domain metric of the target realization. -/
theorem lemma21_of_inputs (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (hT : TargetTightUniform ξ Q D) (hloc : GoodEventsLocal ξ Q D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
        ∀ᵐ ω ∂P, ∀ u v : U,
          ENNReal.ofReal C⁻¹ * (D (h ω)).internal U (u, v) ≤
              domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
                (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
            domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
                (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
              ENNReal.ofReal C * (D (h ω)).internal U (u, v) := by
  have hQpos : 0 < Q :=
    SupercriticalLQGUniqueness.B2.QPos.dg20ExponentPositive_proved ξ Q hQ
  have hW := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  obtain ⟨p, hp0, hp1, Hasm⟩ := bilip_assembly
  set δ : ℝ := (1 - p) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδp : ENNReal.ofReal p ≤ ENNReal.ofReal (1 - 2 * δ) :=
    ENNReal.ofReal_le_ofReal (by rw [hδdef]; linarith)
  obtain ⟨Ms, hMs, hsrc⟩ := source_tails ξ Q hQpos D hW δ hδ
  obtain ⟨Mt, hMt, htgt⟩ := hT δ hδ
  set M : ℝ := max (max Ms Mt) 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMsM : Ms ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMtM : Mt ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨2 * M ^ 2, by nlinarith, ?_⟩
  intro U V φ hφ Ω _ P _ h g₀ k hI
  obtain ⟨hh, hR⟩ := hI
  set K : ℝ≥0∞ := ENNReal.ofReal (2 * M ^ 2) with hKdef
  have hK0 : K ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
  -- the geometry of `φ`
  have hφU : MapsTo φ U V := hφ.2.mapsTo
  have hψc : ContinuousOn (Function.invFunOn φ U) V :=
    (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ).1.continuousOn
  -- the sample event
  have hhc : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh.1
  have hsample : ∀ᵐ ω ∂P, IsGoodSample D ξ (h ω) (g₀ ω) := by
    filter_upwards [SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P h hhc,
      SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₀ hR.2.1] with ω h₁ h₀
    exact ⟨h₁.1, h₀.1, h₀.2.1, h₀.2.2⟩
  -- (4) in both directions, from steps 1 and 2
  have hprob : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z ∈ L,
      ∀ r ∈ Ioc (0 : ℝ) r₀,
      (AEEventIn P (localSigma h z r) (goodEvent₁ D ξ φ h g₀ k K z r) ∧
        ENNReal.ofReal p ≤ P (goodEvent₁ D ξ φ h g₀ k K z r)) ∧
      (AEEventIn P (localSigma h z r) (goodEvent₂ D ξ φ h g₀ k K z r) ∧
        ENNReal.ofReal p ≤ P (goodEvent₂ D ξ φ h g₀ k K z r)) := by
    intro L hL hLU
    obtain ⟨r₁, hr₁, ht⟩ := htgt U V φ hφ P h g₀ k ⟨hh, hR⟩ L hL hLU
    obtain ⟨r₂, hr₂, hl⟩ := hloc U V φ hφ P h g₀ k ⟨hh, hR⟩ K
      (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top L hL hLU
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz r hr => ?_⟩
    have hr0 : 0 < r := hr.1
    have hr₁' : r ∈ Ioc (0 : ℝ) r₁ := ⟨hr0, hr.2.trans (min_le_left _ _)⟩
    have hr₂' : r ∈ Ioc (0 : ℝ) r₂ := ⟨hr0, hr.2.trans (min_le_right _ _)⟩
    obtain ⟨hsA, hsB⟩ := hsrc P h hh z r hr0
    obtain ⟨hsA', hsB'⟩ := tails_mono P _ _ _ hMs hMsM hsA hsB
    obtain ⟨htA, htB⟩ := ht z hz r hr₁'
    obtain ⟨htA', htB'⟩ := tails_mono P _ _ _ hMt hMtM htA htB
    have hm : ∀ ω, 0 < nrm ξ Q (h ω) r z ∧ nrm ξ Q (h ω) r z < ∞ := fun ω =>
      nrm_pos_lt_top ξ Q (h ω) hr0 z
    obtain ⟨hl₁, hl₂⟩ := hl z hz r hr₂'
    refine ⟨⟨hl₁, hδp.trans ?_⟩, ⟨hl₂, hδp.trans ?_⟩⟩
    · exact prob_lt_of_tails P _ _ _ hm hM0 hδ.le htA' hsB'
    · exact prob_lt_of_tails P _ _ _ hm hM0 hδ.le hsA' htB'
  have hmain := Hasm D ξ (le_of_lt ξ.2) U.isOpen V.isOpen hφ.1 hφ.2.injOn hφ.2.image_eq hψc P h g₀ k
    hh.1 hsample hK0 hKtop hprob
  filter_upwards [hmain, hsample] with ω hω hs u v
  obtain ⟨h₁, h₂⟩ := hω u u.2 v v.2
  -- identify `e` and `d`
  have he : domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
      (⟨φ u, hφU u.2⟩, ⟨φ v, hφU v.2⟩) = eT (D (g₀ ω)) ξ (k ω) φ u v :=
    SupercriticalConformalCovariance.Domain.weylScaleOn_eq_dV hs.2.1 (k ω) _
  have hd : (D (h ω)).internal U (u, v) = pathInf (D (h ω)) U u v := rfl
  rw [he, hd]
  refine ⟨?_, h₁⟩
  -- `C⁻¹ d ≤ e` from `d ≤ C e`
  have hCC : ENNReal.ofReal (2 * M ^ 2)⁻¹ * K = 1 := by
    rw [hKdef, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  calc ENNReal.ofReal (2 * M ^ 2)⁻¹ * pathInf (D (h ω)) U u v
      ≤ ENNReal.ofReal (2 * M ^ 2)⁻¹ * (K * eT (D (g₀ ω)) ξ (k ω) φ u v) := by gcongr
    _ = eT (D (g₀ ω)) ξ (k ω) φ u v := by rw [← mul_assoc, hCC, one_mul]

end SupercriticalConformalCovariance.BiLip
