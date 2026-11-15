/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.GFF.LocalSets.Prop38Version

/-!
# A measurable version of a fibre-constant random function, through the conditional kernel

Packet PROVE-T14-WALKMEAN. The union mean of Theorem 1.4's two walks must be a function of the joined retained past
`𝒥` (the measurability clause of `WalkLaw.WalkUnionMeanRegAEStatement`). The follow-up note (A–E, D.5) obtains this
from an explicit Borel construction of the classified word and of the hydrodynamic maps. Here it is obtained from a
general principle instead: a random function that is **constant on the fibres of the past** (it is a function of the
retained runs, which agree on almost every fibre of the past) and that is the almost-sure value of a **jointly
measurable** random function (bump pairings of the local-set mean) has a `𝒥`-measurable version — its average under
the regular conditional kernel given `𝒥`.

* `kerAvg 𝒥 P M ω z = ∫ M (ω', z) d(condExpKernel P 𝒥 ω)(ω')`;
* `stronglyMeasurable_kerAvg`: `(ω, z) ↦ kerAvg 𝒥 P M ω z` is measurable for `𝒥 ⊗ Borel`;
* `measurable_integral_kerAvg_mul`: `ω ↦ ∫ kerAvg 𝒥 P M ω z * ψ z dz` is `𝒥`-measurable for measurable `ψ`;
* **`ae_kerAvg_eq`**: if almost surely the kernel fibres carry the same value `ρ` and, almost surely, `M (ω, ·)`
  agrees with `Φ (ρ ω)` on `U (ρ ω)`, then almost surely `kerAvg 𝒥 P M ω` agrees with `Φ (ρ ω)` on `U (ρ ω)`;
* `bumpLim`: the limit of normalized bump pairings of a random distribution (plus a deterministic function on `ℍ`);
  `measurable_bumpLim`, **`bumpLim_eq_of_harmonic`** (its value on an open set where the distribution has a harmonic
  representative).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace InteractingSLE.Theorem14.WalkMean

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

/-! ### The kernel average -/

section Kernel

variable {Ω : Type*} {𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

variable (P 𝒥) in
/-- The average of the random function `M (ω', ·)` under the regular conditional kernel given `𝒥` at `ω`. -/
def kerAvg (M : Ω × ℂ → ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  ∫ ω', M (ω', z) ∂(condExpKernel P 𝒥 ω)

/-- The kernel average is jointly measurable for `𝒥 ⊗ Borel`. -/
theorem stronglyMeasurable_kerAvg {M : Ω × ℂ → ℝ} (hM : Measurable M) :
    StronglyMeasurable[𝒥.prod inferInstance] fun p : Ω × ℂ => kerAvg 𝒥 P M p.1 p.2 := by
  have hfst : Measurable[𝒥.prod inferInstance, 𝒥] (Prod.fst : Ω × ℂ → Ω) := measurable_fst
  let κ' := Kernel.comap (mγ := 𝒥.prod inferInstance) (condExpKernel P 𝒥) Prod.fst hfst
  have : IsSFiniteKernel κ' := Kernel.IsSFiniteKernel.comap (condExpKernel P 𝒥) hfst
  have hg : Measurable[(𝒥.prod inferInstance).prod mΩ, mΩ.prod inferInstance]
      (fun q : (Ω × ℂ) × Ω => (q.2, q.1.2)) :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hf : StronglyMeasurable[(𝒥.prod inferInstance).prod mΩ] (fun q : (Ω × ℂ) × Ω => M (q.2, q.1.2)) :=
    (hM.comp hg).stronglyMeasurable
  exact hf.integral_kernel_prod_right' (κ := κ')

/-- The pairing of the kernel average with a measurable function is `𝒥`-measurable. -/
theorem measurable_integral_kerAvg_mul {M : Ω × ℂ → ℝ} (hM : Measurable M) {ψ : ℂ → ℝ} (hψ : Measurable ψ) :
    Measurable[𝒥] fun ω => ∫ z, kerAvg 𝒥 P M ω z * ψ z := by
  have h1 := stronglyMeasurable_kerAvg (P := P) (𝒥 := 𝒥) hM
  have hsnd : Measurable[𝒥.prod inferInstance] (Prod.snd : Ω × ℂ → ℂ) := measurable_snd
  have h2 : StronglyMeasurable[𝒥.prod inferInstance] fun p : Ω × ℂ => ψ p.2 :=
    (hψ.comp hsnd).stronglyMeasurable
  let F : Ω × ℂ → ℝ := fun p => kerAvg 𝒥 P M p.1 p.2 * ψ p.2
  have hFm : StronglyMeasurable[𝒥.prod inferInstance] F := h1.mul h2
  have h3 : StronglyMeasurable[𝒥] fun ω => ∫ z, F (ω, z) := by
    let _ : MeasurableSpace Ω := 𝒥
    exact hFm.integral_prod_right'
  exact h3.measurable

/-- **The kernel average is the fibre value.** If almost surely the regular conditional law given `𝒥` lives on the
fibre of `ρ`, and almost surely `M (ω, ·)` agrees with `Φ (ρ ω)` on `U (ρ ω)`, then almost surely the kernel average
agrees with `Φ (ρ ω)` on `U (ρ ω)`. -/
theorem ae_kerAvg_eq (h𝒥 : 𝒥 ≤ mΩ) {X : Type*} {ρ : Ω → X}
    (hfib : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒥 ω₀), ρ ω = ρ ω₀) {M : Ω × ℂ → ℝ} {U : X → Set ℂ}
    {Φ : X → ℂ → ℝ} (hMΦ : ∀ᵐ ω ∂P, ∀ z ∈ U (ρ ω), M (ω, z) = Φ (ρ ω) z) :
    ∀ᵐ ω ∂P, ∀ z ∈ U (ρ ω), kerAvg 𝒥 P M ω z = Φ (ρ ω) z := by
  have hk := KernelTower.ae_ae_condExpKernel_of_ae (P := P) h𝒥 hMΦ
  filter_upwards [hfib, hk] with ω₀ hf hk' z hz
  have e : ∀ᵐ ω ∂(condExpKernel P 𝒥 ω₀), M (ω, z) = Φ (ρ ω₀) z := by
    filter_upwards [hf, hk'] with ω h1 h2
    rw [← h1] at hz
    rw [h2 z hz, h1]
  rw [kerAvg, integral_congr_ae e, integral_const, probReal_univ, one_smul]

end Kernel

/-! ### Limits of normalized bump pairings -/

section Bump

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The radius `1/(n+1)` of the `n`-th bump. -/
def bumpRad (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem bumpRad_pos (n : ℕ) : 0 < bumpRad n := by
  unfold bumpRad
  positivity

theorem tendsto_bumpRad : Tendsto bumpRad atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The limit (`limsup`) of the normalized bump pairings of a random distribution `T` at `z`, plus `u z` on `ℍ`. -/
def bumpLim (T : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (p : Ω × ℂ) : ℝ :=
  limsup (fun n => LocalSets.bumpPair T (bumpRad n) (bumpRad_pos n) p /
    (bumpRad n ^ 2 * GFF.bumpMass)) atTop + H.indicator u p.2

theorem measurable_bumpLim {T : Ω → DistOn upperHalfPlaneOpens} (hT : Measurable T) {u : ℂ → ℝ}
    (hu : ContinuousOn u H) : Measurable (bumpLim T u) := by
  classical
  refine Measurable.add ?_ ?_
  · exact Measurable.limsup fun n =>
      (LocalSets.measurable_bumpPair hT (bumpRad_pos n)).div_const _
  · have hHm : MeasurableSet H := QuantumZipper.isOpen_H.measurableSet
    have : Measurable (H.indicator u) := by
      rw [← piecewise_eq_indicator]
      exact hu.measurable_piecewise continuousOn_const hHm
    exact this.comp measurable_snd

omit [MeasurableSpace Ω] in
/-- **The bump limit on a harmonic patch**: if `T ω` is represented on an open `V ⊆ ℍ` by `v` harmonic there, then
at every `z ∈ V` the bump limit is `v z + u z`. -/
theorem bumpLim_eq_of_harmonic {T : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {ω : Ω} {V : Set ℂ}
    (hV : IsOpen V) (hVH : V ⊆ H) {v : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v V)
    (hTv : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ V → T ω φ = ∫ z, v z * φ z) {z : ℂ} (hz : z ∈ V) :
    bumpLim T u (ω, z) = v z + u z := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV z hz
  have hev : ∀ᶠ n in atTop, LocalSets.bumpPair T (bumpRad n) (bumpRad_pos n) (ω, z) /
      (bumpRad n ^ 2 * GFF.bumpMass) = v z := by
    have := (tendsto_order.1 tendsto_bumpRad).2 r hr
    filter_upwards [this] with n hn
    refine LocalSets.bumpPair_eq_of_harmonic (bumpRad_pos n) hV hv hTv ?_ hVH
    exact (Metric.closedBall_subset_ball hn).trans hrV
  have hlim : limsup (fun n => LocalSets.bumpPair T (bumpRad n) (bumpRad_pos n) (ω, z) /
      (bumpRad n ^ 2 * GFF.bumpMass)) atTop = v z :=
    (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)).limsup_eq
  rw [bumpLim, hlim, indicator_of_mem (hVH hz)]

end Bump

end InteractingSLE.Theorem14.WalkMean
