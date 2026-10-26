import SupercriticalLQGUniqueness.Frozen.Exists_strongLQGMetric_lfppLimit
import SupercriticalLQGUniqueness.B2.Median.LFPPMetric
import SupercriticalLQGUniqueness.B2.Polylog.P4Event
import SupercriticalLFPPAS.Field.LocalizedApproximation

/-!
# Local comparisons: shared objects and generic probability lemmas (packet P32)

Objects of `source/almost-sure-supercritical-lfpp.txt` §§2.2–3.1 (planning audit
`planning/audits/SB1-sections-1-3.md`, A10–A13 and the statement shapes of its §(c)):

* `IsLFPPLimit ξ m D`: `D` is the limit in probability of `𝔞_ε⁻¹ D^ε_h` for every GFF plus a
  bounded continuous function (DG Theorems 1.3 and 1.8; obtained once from the sealed
  `exists_strongLQGMetric_lfppLimit` by `exists_isStrongLQGMetric_isLFPPLimit`);
* the annuli `V = {1/2 ≤ |z| ≤ 3}` (`srcV`) and `U = {1/8 ≤ |z| ≤ 16}` (`tgtU`) of Lemma 3.2 and its
  event `Lemma32Event` ((3.1)–(3.2) for all `|u| = 1`, `|v| = 2`), with the unit-adjusted variant
  `Lemma32EventU` (lengths and errors in units `e^{ξ h_1(0)}`, Lemma 3.2's last sentence);
* the localized LFPP metric `Y_{δ,L}` (`locMetric`, cutoff radius `δL`);
* the generic lemmas turning "every sequence has a subsequence along which the event holds
  eventually, almost surely" into "probability tending to one" (SB1 A11), for null-measurable
  events.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-! ### The limiting metric -/

/-- `D` is the limit of normalized LFPP for the normalizer `m`, in the sense of DG
Theorems 1.3 and 1.8: for every whole-plane GFF plus a bounded continuous function and every family
of heat versions, `𝔞_ε⁻¹ D^ε_h → D_h` in probability for the lower semicontinuous topology. -/
def IsLFPPLimit (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    LQGMetric.IsGFFPlusBddCont h P → ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ ε, IsHeatSmoothing P h ε (X ε)) →
      LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
        (fun ω => (D (h ω)).toLSCFun.1)

/-- The strong LQG metric of the sealed `exists_strongLQGMetric_lfppLimit` is an LFPP limit for
every normalizer. -/
theorem exists_isStrongLQGMetric_isLFPPLimit (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) :
    ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
      ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        IsLFPPLimit ξ m D := by
  obtain ⟨D, hD, hlim⟩ := exists_strongLQGMetric_lfppLimit ξ Q hQ
  exact ⟨D, hD, fun m hm Ω _ P _ h hh X hX => hlim m hm P h hh X hX⟩

/-! ### Generic probability lemmas (SB1 A11) -/

/-- If almost every sample eventually avoids the null-measurable events `A i` along a countably
generated filter, their probabilities tend to zero. -/
theorem tendsto_measure_of_ae_eventually_not_mem {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {l : Filter ι} [l.IsCountablyGenerated]
    {A : ι → Set Ω} (hA : ∀ i, NullMeasurableSet (A i) P)
    (hae : ∀ᵐ ω ∂P, ∀ᶠ i in l, ω ∉ A i) :
    Tendsto (fun i => P (A i)) l (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  let B : ℕ → Set Ω := fun N => ⋃ n, ⋃ (_ : N ≤ n), A (x n)
  have hBm : ∀ N, NullMeasurableSet (B N) P := fun N =>
    NullMeasurableSet.iUnion fun n => NullMeasurableSet.iUnion fun _ => hA (x n)
  have hBanti : Antitone B := by
    intro N N' hNN' ω hω
    simp only [B, mem_iUnion] at hω ⊢
    obtain ⟨n, hn, hωn⟩ := hω
    exact ⟨n, hNN'.trans hn, hωn⟩
  have hlim := tendsto_measure_iInter_atTop hBm hBanti ⟨0, measure_ne_top P _⟩
  have hzero : P (⋂ N, B N) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hx.eventually hω)
    intro hmem
    have hωN := mem_iInter.1 hmem N
    simp only [B, mem_iUnion] at hωN
    obtain ⟨n, hn, hωn⟩ := hωN
    exact hN n hn hωn
  rw [hzero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun N => ?_)
  refine measure_mono fun ω hω => ?_
  simp only [B, mem_iUnion]
  exact ⟨N, le_rfl, hω⟩

/-- **The subsequence criterion** (SB1 A11): if the events `E δ` are null-measurable and every
sequence `δ_n → 0` has a subsequence along which almost surely `ω ∈ E δ` eventually, then
`P (E δ)ᶜ → 0` as `δ → 0`. -/
theorem tendsto_measure_compl_of_subseq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {E : Set.Ioi (0 : ℝ) → Set Ω} (hE : ∀ δ, NullMeasurableSet (E δ) P)
    (hsub : ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∈ E (ε (φ k))) :
    Tendsto (fun δ => P (E δ)ᶜ) (comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hns' : Tendsto (fun n => (ns n : ℝ)) atTop (𝓝 0) := tendsto_comap_iff.1 hns
  obtain ⟨φ, -, hae⟩ := hsub ns hns'
  refine ⟨φ, ?_⟩
  refine tendsto_measure_of_ae_eventually_not_mem (l := atTop)
    (A := fun k => (E (ns (φ k)))ᶜ) (fun k => (hE _).compl) ?_
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with k hk
  exact fun hc => hc hk

/-- The subsequence criterion for events contained in null-measurable events: if every sequence
has a subsequence along which almost surely `ω ∉ F δ` eventually, with `F δ` null-measurable and
`G δ ⊆ F δ`, then the outer measure of `G δ` tends to zero. -/
theorem tendsto_measure_of_subseq_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {F G : Set.Ioi (0 : ℝ) → Set Ω} (hF : ∀ δ, NullMeasurableSet (F δ) P)
    (hGF : ∀ δ, G δ ⊆ F δ)
    (hsub : ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ F (ε (φ k))) :
    Tendsto (fun δ => P (G δ)) (comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  have h := tendsto_measure_compl_of_subseq (E := fun δ => (F δ)ᶜ) (fun δ => (hF δ).compl)
    (by simpa only [mem_compl_iff] using hsub)
  simp only [compl_compl] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun δ => measure_mono (hGF δ))

/-- An eventually-small property along `comap Subtype.val (𝓝 0)` holds below a positive radius. -/
theorem exists_pos_of_eventually_comap {p : Set.Ioi (0 : ℝ) → Prop}
    (hp : ∀ᶠ δ in comap Subtype.val (𝓝 (0 : ℝ)), p δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ : Set.Ioi (0 : ℝ), (δ : ℝ) < r → p δ := by
  obtain ⟨t, ht, hts⟩ := mem_comap.1 hp
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨r, hr, fun δ hδ => hts (hrt ?_)⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos δ.2]
  exact hδ

/-! ### The annuli and the event of Lemma 3.2 -/

/-- The source annulus `V = {1/2 ≤ |z| ≤ 3}` of Lemma 3.2. -/
def srcV : Set ℂ := {z | 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3}

/-- The target annulus `U = {1/8 ≤ |z| ≤ 16}` of Lemma 3.2. -/
def tgtU : Set ℂ := {z | 1 / 8 ≤ ‖z‖ ∧ ‖z‖ ≤ 16}

/-- One direction of Lemma 3.2 ((3.1) with `S = D`, `T = X_δ`, or (3.2) with the roles exchanged):
for all `|u| = 1`, `|v| = 2` with `S(u, v; V) ≤ M`,
`T(B_η(u), B_η(v); U) ≤ S(u, v; V) + ν`. -/
def OneWayCompare (S T : LSCMetric) (η ν M : ℝ) : Prop :=
  ∀ u v : srcV, ‖(u : ℂ)‖ = 1 → ‖(v : ℂ)‖ = 2 →
    S.internal srcV (u, v) ≤ ENNReal.ofReal M →
    T.internalSetDist tgtU {x | (x : ℂ) ∈ ball (u : ℂ) η} {x | (x : ℂ) ∈ ball (v : ℂ) η} ≤
      S.internal srcV (u, v) + ENNReal.ofReal ν

/-- The event of Lemma 3.2: both (3.1) and (3.2), simultaneously for `|u| = 1`, `|v| = 2`. -/
def Lemma32Event (S T : LSCMetric) (η ν M : ℝ) : Prop :=
  OneWayCompare S T η ν M ∧ OneWayCompare T S η ν M

/-- Lemma 3.2's event with the height cutoff and the additive error expressed in units `t`
(the paper's `e^{ξ h_1(0)}`), as in the locality clause of Lemma 3.2. -/
def Lemma32EventU (S T : LSCMetric) (η ν M t : ℝ) : Prop :=
  Lemma32Event S T η (ν * t) (M * t)

theorem OneWayCompare.mono {S T : LSCMetric} {η η' ν ν' M M' : ℝ}
    (h : OneWayCompare S T η ν M) (hη : η ≤ η') (hν : ν ≤ ν') (hM : M' ≤ M) :
    OneWayCompare S T η' ν' M' := by
  intro u v hu hv hM'
  have hsub : ∀ c : ℂ, {x : tgtU | (x : ℂ) ∈ ball c η} ⊆ {x : tgtU | (x : ℂ) ∈ ball c η'} :=
    fun c x hx => ball_subset_ball hη hx
  calc T.internalSetDist tgtU {x | (x : ℂ) ∈ ball (u : ℂ) η'} {x | (x : ℂ) ∈ ball (v : ℂ) η'}
      ≤ T.internalSetDist tgtU {x | (x : ℂ) ∈ ball (u : ℂ) η} {x | (x : ℂ) ∈ ball (v : ℂ) η} := by
        unfold LSCMetric.internalSetDist
        exact iInf₂_mono' fun x hx => ⟨x, hsub _ hx, iInf₂_mono' fun y hy =>
          ⟨y, hsub _ hy, le_rfl⟩⟩
    _ ≤ S.internal srcV (u, v) + ENNReal.ofReal ν :=
        h u v hu hv (hM'.trans (ENNReal.ofReal_le_ofReal hM))
    _ ≤ S.internal srcV (u, v) + ENNReal.ofReal ν' := by
        gcongr

theorem Lemma32Event.mono {S T : LSCMetric} {η η' ν ν' M M' : ℝ}
    (h : Lemma32Event S T η ν M) (hη : η ≤ η') (hν : ν ≤ ν') (hM : M' ≤ M) :
    Lemma32Event S T η' ν' M' :=
  ⟨h.1.mono hη hν hM, h.2.mono hη hν hM⟩

/-- For `t = 1` the unit-adjusted event is the plain event. -/
theorem lemma32EventU_one (S T : LSCMetric) (η ν M : ℝ) :
    Lemma32EventU S T η ν M 1 ↔ Lemma32Event S T η ν M := by
  simp only [Lemma32EventU, mul_one]

/-! ### The localized LFPP metric -/

/-- `Y_{δ,L} = 𝔞_δ⁻¹ D_{H_{δ,L}}`, the normalized LFPP metric of the field `H_{δ,L}` localized at
cutoff radius `δL` (paper (2.3)–(2.4)). `H_{δ,L}` is the PL localized mollification with exponent
`q = log L / log log δ⁻¹` (`Field.uniformLocalizedHeatField`); its cutoff radius is exactly `δL`
when `1 < log δ⁻¹ ≤ L` (`Field.plRad_uniform_eq`). -/
def locMetric (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (δ L : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (g : DistC) : LSCMetric :=
  B2.Polylog.plLocMetric ξ (Field.uniformLocalizationExponent δ L) m δ hδ g

end SupercriticalLFPPAS.Local
