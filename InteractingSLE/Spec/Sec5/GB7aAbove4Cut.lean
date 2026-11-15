/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux61Cutoff

/-!
# Aux. lemma 61's two-core cutoff with an asymmetric seed core

Packet PROVE-CFBARRIER2 (GB7a's pathwise half above `κ = 4`). PROVE-GB7A2's cutoff (`GB7a.CutParams`,
`Aux61Cutoff.lean`) has a seed core `(−a₀, a₀)` symmetric about the chart's starting point `0`; its energy bound
(`GB7a.exists_markDrift_energy_le`) asks the chart trace to meet `ℝ` only at `0`. Above `κ = 4` the chart trace at a
restart time touches the image of the past hull, a compact subset of an interval `(L, R) ∋ 0` that is free of marks
but in general not symmetric about `0`. This file redoes the cutoff with a seed core `(l₀, r₀)`, `l₀ < 0 < r₀`:

* `SeedCut`, `SeedCut.Valid`: the parameters (seed core `(l₀, r₀)`, target core `(a₁, b₁)`, margin `μ`, radius `R`);
* `seedChi`: the smooth cutoff, `1` on the buffer `seedN`, vanishing near the real points off the cores;
* `SeedConfig`, `seedF = seedChi · GB7a.oddExt`: smooth (`contDiff_seedF`), harmonic on the buffer
  (`laplacian_seedF_eq_zero`);
* `fillH_subset_seedU`: a compact set in the inner buffer `seedU` whose real points lie over the shrunk seed core has
  its filling in `seedU`;
* `exists_markDrift_energy_le_seed`: **the energy bound** (Aux. lemmas 61–62 in the field-free form) for a chart trace
  whose real points lie over the shrunk seed core.

The generic parts (the odd extension `GB7a.oddExt`, its local holomorphy, the drift identity `GB7a.IdentHyp`,
`GB7a.srcDrift_eq_markDrift`, `GB7a.integral_srcDrift_sq_le`) are reused unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace Sec5.GB7aAbove4

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH fwdMapInv)
open GB7a

/-! ### Parameters and bumps -/

/-- The parameters: the seed core `(l₀, r₀)`, the target core `(a₁, b₁)`, the margin `μ` and the radius `R`. -/
structure SeedCut where
  l₀ : ℝ
  r₀ : ℝ
  a₁ : ℝ
  b₁ : ℝ
  μ : ℝ
  R : ℝ

/-- Admissible parameters. -/
structure SeedCut.Valid (P : SeedCut) : Prop where
  μ_pos : 0 < P.μ
  l₀_lt : P.l₀ < -(3 * P.μ)
  r₀_gt : 3 * P.μ < P.r₀
  r₀_lt : P.r₀ + P.μ < P.a₁ - P.μ
  core1 : P.a₁ + 3 * P.μ < P.b₁ - 3 * P.μ
  R_pos : 0 < P.R

/-- The interval bump: `1` on `[l + μ, r − μ]`, `0` off `(l, r)`. -/
def ibump (μ l r x : ℝ) : ℝ :=
  Real.smoothTransition ((x - l) / μ) * Real.smoothTransition ((r - x) / μ)

/-- The core bump. -/
def seedBump (P : SeedCut) (x : ℝ) : ℝ := ibump P.μ P.l₀ P.r₀ x + ibump P.μ P.a₁ P.b₁ x

/-- The height bump: `0` for `|y| ≤ μ`, `1` for `|y| ≥ 2μ`. -/
def hbump (μ y : ℝ) : ℝ := Real.smoothTransition ((y ^ 2 - μ ^ 2) / (3 * μ ^ 2))

/-- **The cutoff** `χ(z) = D(|z|) (A(Re z) + C(Im z) − A(Re z) C(Im z))`. -/
def seedChi (P : SeedCut) (z : ℂ) : ℝ :=
  LocalExt.cutoffFn P.R (P.R + 1) z *
    (seedBump P z.re + hbump P.μ z.im - seedBump P z.re * hbump P.μ z.im)

variable {P : SeedCut}

theorem contDiff_ibump {n : ℕ∞} (μ l r : ℝ) : ContDiff ℝ n (ibump μ l r) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem contDiff_hbump {n : ℕ∞} (μ : ℝ) : ContDiff ℝ n (hbump μ) :=
  Real.smoothTransition.contDiff.comp (((contDiff_id.pow 2).sub contDiff_const).div_const _)

theorem contDiff_seedChi {n : ℕ∞} : ContDiff ℝ n (seedChi P) := by
  have hre : ContDiff ℝ n fun z : ℂ => seedBump P z.re :=
    ((contDiff_ibump _ _ _).add (contDiff_ibump _ _ _)).comp Complex.reCLM.contDiff
  have him : ContDiff ℝ n fun z : ℂ => hbump P.μ z.im := (contDiff_hbump _).comp Complex.imCLM.contDiff
  exact LocalExt.contDiff_cutoffFn.mul ((hre.add him).sub (hre.mul him))

theorem ibump_eq_zero {μ l r : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : x ≤ l ∨ r ≤ x) : ibump μ l r x = 0 := by
  rcases hx with hx | hx
  · rw [ibump, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hμ.le), zero_mul]
  · have h : (r - x) / μ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hμ.le
    rw [ibump, Real.smoothTransition.zero_of_nonpos h, mul_zero]

theorem ibump_eq_one {μ l r : ℝ} (hμ : 0 < μ) {x : ℝ} (hx : x ∈ Icc (l + μ) (r - μ)) : ibump μ l r x = 1 := by
  have h1 : 1 ≤ (x - l) / μ := by rw [le_div_iff₀ hμ]; linarith [hx.1]
  have h2 : 1 ≤ (r - x) / μ := by rw [le_div_iff₀ hμ]; linarith [hx.2]
  rw [ibump, Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

theorem hbump_eq_zero {μ y : ℝ} (hy : |y| ≤ μ) : hbump μ y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ (by positivity))
  have : y ^ 2 ≤ μ ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  linarith

theorem hbump_eq_one {μ y : ℝ} (hμ : 0 < μ) (hy : 2 * μ ≤ |y|) : hbump μ y = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by positivity), one_mul]
  have : (2 * μ) ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (by positivity) hy 2
  nlinarith

theorem seedChi_conj (z : ℂ) : seedChi P (conj z) = seedChi P z := by
  simp only [seedChi, LocalExt.cutoffFn_conj, Complex.conj_re, Complex.conj_im, hbump, even_two.neg_pow]

/-! ### The buffer `N` where `χ = 1` -/

/-- **The buffer** `N`: the disc of radius `R`, above height `2μ` (in absolute value) or over the shrunk cores. -/
def seedN (P : SeedCut) : Set ℂ :=
  {z | ‖z‖ < P.R ∧ (2 * P.μ < |z.im| ∨ z.re ∈ Ioo (P.l₀ + P.μ) (P.r₀ - P.μ) ∨
    z.re ∈ Ioo (P.a₁ + P.μ) (P.b₁ - P.μ))}

theorem isOpen_seedN : IsOpen (seedN P) :=
  (isOpen_lt continuous_norm continuous_const).inter ((isOpen_lt continuous_const
    Complex.continuous_im.abs).union ((isOpen_Ioo.preimage Complex.continuous_re).union
      (isOpen_Ioo.preimage Complex.continuous_re)))

theorem seedChi_eq_one (hP : P.Valid) {z : ℂ} (hz : z ∈ seedN P) : seedChi P z = 1 := by
  obtain ⟨hR, h⟩ := hz
  have hμ := hP.μ_pos
  have hD : LocalExt.cutoffFn P.R (P.R + 1) z = 1 :=
    LocalExt.cutoffFn_eq_one hP.R_pos.le (by linarith) hR.le
  rw [seedChi, hD, one_mul]
  rcases h with h | h | h
  · rw [hbump_eq_one hμ h.le]; ring
  · have h1 : ibump P.μ P.a₁ P.b₁ z.re = 0 :=
      ibump_eq_zero hμ (Or.inl (by linarith [h.2, hP.r₀_lt]))
    rw [seedBump, ibump_eq_one hμ ⟨h.1.le, h.2.le⟩, h1]; ring
  · have h0 : ibump P.μ P.l₀ P.r₀ z.re = 0 :=
      ibump_eq_zero hμ (Or.inr (by linarith [h.1, hP.r₀_lt]))
    rw [seedBump, h0, ibump_eq_one hμ ⟨h.1.le, h.2.le⟩]; ring

theorem zero_mem_seedN (hP : P.Valid) : (0 : ℂ) ∈ seedN P :=
  ⟨by simpa using hP.R_pos, Or.inr (Or.inl ⟨by simp; linarith [hP.l₀_lt, hP.μ_pos],
    by simp; linarith [hP.r₀_gt, hP.μ_pos]⟩)⟩

/-- Near a real point off the closed cores, `χ` vanishes. -/
theorem seedChi_eq_zero_near (hP : P.Valid) {x : ℝ} (hx : x < P.l₀ ∨ P.r₀ < x) (hx1 : x < P.a₁ ∨ P.b₁ < x) :
    ∀ᶠ z in 𝓝 (x : ℂ), seedChi P z = 0 := by
  have hμ := hP.μ_pos
  have hre : ∀ {S : Set ℝ}, IsOpen S → x ∈ S → ∀ᶠ z in 𝓝 (x : ℂ), z.re ∈ S := fun hS hxS =>
    (Complex.continuous_re.tendsto _).eventually (hS.mem_nhds (by simpa using hxS))
  have h1 : ∀ᶠ z in 𝓝 (x : ℂ), z.re < P.l₀ ∨ P.r₀ < z.re :=
    hre ((isOpen_gt' P.l₀).union (isOpen_lt' P.r₀)) hx
  have h2 : ∀ᶠ z in 𝓝 (x : ℂ), z.re < P.a₁ ∨ P.b₁ < z.re :=
    hre ((isOpen_gt' P.a₁).union (isOpen_lt' P.b₁)) hx1
  have h3 : ∀ᶠ z in 𝓝 (x : ℂ), |z.im| < P.μ :=
    (Complex.continuous_im.abs.tendsto _).eventually (gt_mem_nhds (by simpa using hμ))
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [seedChi, seedBump, ibump_eq_zero hμ (hz1.imp le_of_lt le_of_lt),
    ibump_eq_zero hμ (hz2.imp le_of_lt le_of_lt), hbump_eq_zero hz3.le]
  ring

/-! ### The cutoff field `f = χ · oddExt` -/

section SeedF

variable {ι : Type*} [Fintype ι] {p c : ι → ℝ} {c₀ : ℝ}

/-- The configuration: the marks avoid the closed `μ`-neighbourhoods of both cores, and the boundary value of the arg
sum vanishes on both cores. -/
structure SeedConfig (P : SeedCut) (p c : ι → ℝ) (c₀ : ℝ) : Prop where
  avoid0 : ∀ j, p j < P.l₀ - P.μ ∨ P.r₀ + P.μ < p j
  avoid1 : ∀ j, p j < P.a₁ - P.μ ∨ P.b₁ + P.μ < p j
  seed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0
  core : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => P.b₁ + P.μ ≤ p j), c j = 0

/-- **The cutoff field** `f = χ · oddExt`. -/
def seedF (P : SeedCut) (p c : ι → ℝ) (c₀ : ℝ) (z : ℂ) : ℝ := seedChi P z * oddExt p c c₀ z

/-- The two core strips of a configuration. -/
theorem SeedConfig.local_hol (hP : P.Valid) (hC : SeedConfig P p c c₀) {w : ℂ}
    (hw : w.re ∈ Ioo (P.l₀ - P.μ) (P.r₀ + P.μ) ∨ w.re ∈ Ioo (P.a₁ - P.μ) (P.b₁ + P.μ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ oddExt p c c₀ =ᶠ[𝓝 w] fun u => (g u).im := by
  classical
  have hμ := hP.μ_pos
  rcases hw with h | h
  · have havoid : ∀ j, p j ≤ P.l₀ - P.μ ∨ P.r₀ + P.μ ≤ p j := fun j => (hC.avoid0 j).imp le_of_lt le_of_lt
    have hfilt : Finset.univ.filter (fun j => P.r₀ + P.μ ≤ p j) =
        Finset.univ.filter (fun j => 0 < p j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj; linarith [hP.r₀_gt]
      · intro hj
        rcases havoid j with h' | h'
        · linarith [hP.l₀_lt]
        · exact h'
    have hdata : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => P.r₀ + P.μ ≤ p j), c j = 0 := by
      rw [hfilt]; exact hC.seed
    obtain ⟨ha, he⟩ := oddExt_eventuallyEq_core havoid hdata h.1 h.2
    exact ⟨_, ha, he⟩
  · have havoid : ∀ j, p j ≤ P.a₁ - P.μ ∨ P.b₁ + P.μ ≤ p j := fun j => (hC.avoid1 j).imp le_of_lt le_of_lt
    obtain ⟨ha, he⟩ := oddExt_eventuallyEq_core havoid hC.core h.1 h.2
    exact ⟨_, ha, he⟩

/-- **The cutoff field is smooth.** -/
theorem contDiff_seedF (hP : P.Valid) (hC : SeedConfig P p c c₀) {n : ℕ∞} :
    ContDiff ℝ n (seedF P p c c₀) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  have hμ := hP.μ_pos
  have hol : ∀ {g : ℂ → ℂ}, AnalyticAt ℂ g z → oddExt p c c₀ =ᶠ[𝓝 z] (fun u => (g u).im) →
      ContDiffAt ℝ n (seedF P p c c₀) z := fun {g} hg he => by
    have hgd : ContDiffAt ℝ n (fun u => (g u).im) z :=
      Complex.imCLM.contDiff.contDiffAt.comp z (hg.contDiffAt.restrict_scalars ℝ)
    exact ((contDiff_seedChi (P := P)).contDiffAt.mul hgd).congr_of_eventuallyEq
      (he.mono fun u hu => by simp only [seedF, hu])
  by_cases hz : z.im ≠ 0
  · obtain ⟨g, hg, he⟩ := oddExt_eventuallyEq_off (p := p) (c := c) (c₀ := c₀) hz
    exact hol hg he
  · push Not at hz
    by_cases hcore : z.re ∈ Ioo (P.l₀ - P.μ) (P.r₀ + P.μ) ∨ z.re ∈ Ioo (P.a₁ - P.μ) (P.b₁ + P.μ)
    · obtain ⟨g, hg, he⟩ := hC.local_hol hP hcore
      exact hol hg he
    · push Not at hcore
      obtain ⟨h1, h2⟩ := hcore
      have hx : z.re < P.l₀ ∨ P.r₀ < z.re := by
        by_contra h'
        push Not at h'
        exact h1 ⟨by linarith [h'.1], by linarith [h'.2]⟩
      have hx1 : z.re < P.a₁ ∨ P.b₁ < z.re := by
        by_contra h'
        push Not at h'
        exact h2 ⟨by linarith [h'.1], by linarith [h'.2]⟩
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
      have hev := seedChi_eq_zero_near hP hx hx1
      rw [← hzr] at hev
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with u hu
      simp only [seedF, hu, zero_mul]

theorem hasCompactSupport_seedF (hP : P.Valid) : HasCompactSupport (seedF P p c c₀) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (P.R + 1)) fun z hz => by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    simp only [seedF, seedChi, LocalExt.cutoffFn_eq_zero hP.R_pos.le (by linarith) hz.le, zero_mul]

theorem seedF_conj (z : ℂ) : seedF P p c c₀ (conj z) = -seedF P p c c₀ z := by
  simp only [seedF, seedChi_conj, oddExt_conj, mul_neg]

theorem seedF_eq_of_mem_seedN (hP : P.Valid) {z : ℂ} (hz : z ∈ seedN P) :
    seedF P p c c₀ z = oddExt p c c₀ z := by
  rw [seedF, seedChi_eq_one hP hz, one_mul]

/-- **The source vanishes on the buffer**: `Δ f = 0` on `N`. -/
theorem laplacian_seedF_eq_zero (hP : P.Valid) (hC : SeedConfig P p c c₀) {z : ℂ} (hz : z ∈ seedN P) :
    Laplacian.laplacian (seedF P p c c₀) z = 0 := by
  have hμ := hP.μ_pos
  have heq : seedF P p c c₀ =ᶠ[𝓝 z] oddExt p c c₀ := by
    filter_upwards [isOpen_seedN.mem_nhds hz] with w hw using seedF_eq_of_mem_seedN hP hw
  have harm : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ oddExt p c c₀ =ᶠ[𝓝 z] fun u => (g u).im := by
    by_cases him : z.im ≠ 0
    · exact oddExt_eventuallyEq_off him
    · push Not at him
      refine hC.local_hol hP ?_
      obtain ⟨-, h⟩ := hz
      rcases h with h | h | h
      · rw [him, abs_zero] at h; linarith
      · left; exact ⟨by linarith [h.1], by linarith [h.2]⟩
      · right; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨g, hg, he⟩ := harm
  have hH := hg.harmonicAt_im
  rw [(InnerProductSpace.laplacian_congr_nhds (heq.trans he)).eq_of_nhds, hH.2.eq_of_nhds, Pi.zero_apply]

end SeedF

/-! ### The inner buffer and the fillings of curves in it -/

/-- **The inner buffer** `U`: the disc of radius `R − μ`, above height `3μ` or over the cores shrunk by `2μ`. -/
def seedU (P : SeedCut) : Set ℂ :=
  {z | ‖z‖ < P.R - P.μ ∧ (3 * P.μ < z.im ∨ z.re ∈ Ioo (P.l₀ + 2 * P.μ) (P.r₀ - 2 * P.μ) ∨
    z.re ∈ Ioo (P.a₁ + 2 * P.μ) (P.b₁ - 2 * P.μ))}

/-- The closure of the inner buffer, intersected with `ℍ̄`, lies in the buffer. -/
theorem closure_seedU_inter_subset (hP : P.Valid) : closure (seedU P) ∩ Hbar ⊆ seedN P := by
  have hcl : closure (seedU P) ⊆ {z | ‖z‖ ≤ P.R - P.μ ∧ (3 * P.μ ≤ z.im ∨
      z.re ∈ Icc (P.l₀ + 2 * P.μ) (P.r₀ - 2 * P.μ) ∨ z.re ∈ Icc (P.a₁ + 2 * P.μ) (P.b₁ - 2 * P.μ))} := by
    refine closure_minimal (fun z hz => ⟨hz.1.le, ?_⟩) ?_
    · rcases hz.2 with h | h | h
      · exact Or.inl h.le
      · exact Or.inr (Or.inl ⟨h.1.le, h.2.le⟩)
      · exact Or.inr (Or.inr ⟨h.1.le, h.2.le⟩)
    · exact (isClosed_le continuous_norm continuous_const).inter ((isClosed_le continuous_const
        Complex.continuous_im).union ((isClosed_Icc.preimage Complex.continuous_re).union
          (isClosed_Icc.preimage Complex.continuous_re)))
  rintro z ⟨hz, hzH⟩
  obtain ⟨h1, h2⟩ := hcl hz
  have hμ := hP.μ_pos
  have him : 0 ≤ z.im := hzH
  refine ⟨by linarith, ?_⟩
  rcases h2 with h | h | h
  · exact Or.inl (by rw [abs_of_nonneg him]; linarith)
  · exact Or.inr (Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩)
  · exact Or.inr (Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩)

/-- **A compact set in the inner buffer whose real points lie over the shrunk seed core has its filling in the inner
buffer.** -/
theorem fillH_subset_seedU (hP : P.Valid) {C : Set ℂ} (hCc : IsCompact C) (hCU : C ⊆ seedU P) (hCH : C ⊆ Hbar)
    (hCR : ∀ z ∈ C, z.im = 0 → z.re ∈ Ioo (P.l₀ + 2 * P.μ) (P.r₀ - 2 * P.μ)) : fillH C ⊆ seedU P := by
  have hμ := hP.μ_pos
  intro z hz
  have hzH : 0 < z.im := hz.1
  by_contra hzU
  have hCcl : closure C = C := hCc.isClosed.closure_eq
  suffices ∃ S : Set ℂ, z ∈ S ∧ IsPreconnected S ∧ S ⊆ H \ C ∧ ¬ Bornology.IsBounded S by
    obtain ⟨S, hzS, hS, hSsub, hSb⟩ := this
    rw [← hCcl] at hSsub
    exact (subset_H_diff_fillH_of_isPreconnected hCc.isBounded hS hSsub hSb hzS).2 hz
  by_cases hfar : P.R - P.μ ≤ ‖z‖
  · -- the radial ray
    refine ⟨(fun t : ℝ => (t : ℂ) * z) '' Ici 1, ⟨1, mem_Ici.2 le_rfl, by simp⟩,
      (isPreconnected_Ici.image _ (by fun_prop)), ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      have ht1 : (1 : ℝ) ≤ t := ht
      refine ⟨show 0 < ((t : ℂ) * z).im by simp; positivity, fun hC => ?_⟩
      have hn := (hCU hC).1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hn
      nlinarith [norm_nonneg z]
    · intro hb
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => by rw [h, Complex.zero_im] at hzH; exact lt_irrefl 0 hzH
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨1, mem_Ici.2 le_rfl, rfl⟩)
      have h1 : (1 : ℝ) ≤ M / ‖z‖ + 1 := by
        have : 0 ≤ M / ‖z‖ := by positivity
        linarith
      have := hM _ ⟨M / ‖z‖ + 1, h1, rfl⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
        div_mul_cancel₀ _ hz0.ne'] at this
      linarith
  · -- near the real line off the cores
    push Not at hfar
    have hlow3 : z.re ∉ Ioo (P.a₁ + 2 * P.μ) (P.b₁ - 2 * P.μ) := fun h => hzU ⟨hfar, Or.inr (Or.inr h)⟩
    have hlow2 : z.re ∉ Ioo (P.l₀ + 2 * P.μ) (P.r₀ - 2 * P.μ) := fun h => hzU ⟨hfar, Or.inr (Or.inl h)⟩
    have hlow1 : z.im ≤ 3 * P.μ := by
      by_contra h; exact hzU ⟨hfar, Or.inl (not_le.1 h)⟩
    -- the direction: right if `z` is right of the seed core, left otherwise
    set dirR : Prop := P.r₀ - 2 * P.μ ≤ z.re with hdirR
    have hleft : ¬ dirR → z.re ≤ P.l₀ + 2 * P.μ := fun hn => by
      by_contra h
      exact hlow2 ⟨not_le.1 h, not_le.1 hn⟩
    have hvert : ∀ y : ℝ, 0 < y → y ≤ z.im → ((z.re : ℂ) + y * Complex.I) ∉ C := by
      intro y hy hyz hC
      have hU := (hCU hC).2
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, zero_add, Complex.add_re, Complex.mul_re, sub_zero, add_zero] at hU
      rcases hU with h | h | h
      · linarith
      · exact hlow2 h
      · exact hlow3 h
    classical
    have hside : ∃ h₀ > 0, ∀ w ∈ C, (if dirR then z.re ≤ w.re else w.re ≤ z.re) → h₀ ≤ w.im := by
      set D : Set ℂ := C ∩ {w | if dirR then z.re ≤ w.re else w.re ≤ z.re} with hD
      have hDc : IsCompact D := by
        refine hCc.inter_right ?_
        split_ifs
        · exact isClosed_le continuous_const Complex.continuous_re
        · exact isClosed_le Complex.continuous_re continuous_const
      have hDpos : ∀ w ∈ D, 0 < w.im := by
        intro w hw
        have hwH : 0 ≤ w.im := hCH hw.1
        rcases hwH.lt_or_eq with h | h
        · exact h
        · have hw0 := hCR w hw.1 h.symm
          have hw2 := hw.2
          simp only [Set.mem_ofPred_eq] at hw2
          split_ifs at hw2 with hpos
          · exact absurd (hw2.trans_lt hw0.2) (not_lt.2 hpos)
          · exact absurd (hw0.1.trans_le hw2) (not_lt.2 (hleft hpos))
      rcases D.eq_empty_or_nonempty with hDe | hDn
      · refine ⟨1, one_pos, fun w hw hw' => ?_⟩
        exact absurd (show w ∈ D from ⟨hw, hw'⟩) (by rw [hDe]; exact Set.notMem_empty w)
      · obtain ⟨w₀, hw₀, hmin⟩ := hDc.exists_isMinOn hDn Complex.continuous_im.continuousOn
        exact ⟨w₀.im, hDpos w₀ hw₀, fun w hw hw' => hmin ⟨hw, hw'⟩⟩
    obtain ⟨h₀, hh₀, hh₀C⟩ := hside
    set h : ℝ := min (h₀ / 2) z.im with hh
    have hhpos : 0 < h := lt_min (by positivity) hzH
    have hhz : h ≤ z.im := min_le_right _ _
    have hhh₀ : h < h₀ := (min_le_left _ _).trans_lt (by linarith)
    set σ : ℝ := if dirR then 1 else -1 with hσ
    set vert : Set ℂ := (fun y : ℝ => (z.re : ℂ) + y * Complex.I) '' Icc h z.im
    set horiz : Set ℂ := (fun t : ℝ => ((z.re + σ * t : ℝ) : ℂ) + h * Complex.I) '' Ici 0
    have hjoin : ((z.re : ℂ) + h * Complex.I) ∈ vert ∩ horiz :=
      ⟨⟨h, ⟨le_rfl, hhz⟩, rfl⟩, ⟨0, mem_Ici.2 le_rfl, by simp⟩⟩
    refine ⟨vert ∪ horiz, Or.inl ⟨z.im, ⟨hhz, le_rfl⟩, Complex.ext (by simp) (by simp)⟩,
      (isPreconnected_Icc.image _ (by fun_prop)).union _ hjoin.1 hjoin.2
        (isPreconnected_Ici.image _ (by fun_prop)), ?_, ?_⟩
    · rintro w (⟨y, hy, rfl⟩ | ⟨t, ht, rfl⟩)
      · refine ⟨show 0 < ((z.re : ℂ) + y * Complex.I).im by simp; linarith [hy.1], ?_⟩
        exact hvert y (hhpos.trans_le hy.1) hy.2
      · refine ⟨show 0 < (((z.re + σ * t : ℝ) : ℂ) + h * Complex.I).im by simp; exact hhpos, fun hC => ?_⟩
        have hside := hh₀C _ hC (by
          have ht0 : (0 : ℝ) ≤ t := ht
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
            Complex.I_im, mul_zero]
          split_ifs with hpos
          · simp only [hσ, hpos, ↓reduceIte, one_mul]; linarith
          · simp only [hσ, hpos, ↓reduceIte]; linarith)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re, mul_one, mul_zero, zero_add] at hside
        linarith
    · intro hb
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
      have hσ1 : |σ| = 1 := by simp only [hσ]; split_ifs <;> simp
      have hpos' : (0 : ℝ) ≤ M + |z.re| + 1 := by
        have : 0 ≤ M := (norm_nonneg _).trans (hM _ (Or.inr ⟨0, mem_Ici.2 le_rfl, rfl⟩))
        positivity
      have ht := hM _ (Or.inr ⟨M + |z.re| + 1, mem_Ici.2 hpos', rfl⟩)
      have hre := (Complex.abs_re_le_norm _).trans ht
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, add_zero, mul_one, sub_self] at hre
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (Or.inr ⟨0, mem_Ici.2 le_rfl, rfl⟩))
      have : M + 1 ≤ |z.re + σ * (M + |z.re| + 1)| := by
        have h1 : |σ * (M + |z.re| + 1)| = M + |z.re| + 1 := by
          rw [abs_mul, hσ1, one_mul, abs_of_nonneg (by positivity)]
        have key := abs_add_le (z.re + σ * (M + |z.re| + 1)) (-z.re)
        rw [show z.re + σ * (M + |z.re| + 1) + -z.re = σ * (M + |z.re| + 1) by ring, h1, abs_neg] at key
        linarith
      linarith

/-! ### The energy bound for the asymmetric two-core cutoff -/

/-- **The energy bound of the comparison with an asymmetric seed core** (Aux. lemmas 61–62 in the field-free form;
`GB7a.exists_markDrift_energy_le` with the seed core `(l₀, r₀)`): for a configuration admissible for the parameters
there is a constant `C` such that, for every driver whose trace up to time `t` stays in the inner buffer and meets `ℝ`
only over the shrunk seed core, and whose marks are alive through `[0, t]`, `∫₀ˢ markDrift² ≤ C` for `s ≤ t`. -/
theorem exists_markDrift_energy_le_seed {ι : Type*} [Fintype ι] {P : SeedCut} (hP : P.Valid) {p c : ι → ℝ}
    {c₀ : ℝ} (hC : SeedConfig P p c c₀) :
    ∃ C : ℝ, ∀ (W : ℝ → ℝ) (t : ℝ) (η : ℝ → ℂ), Continuous W → W 0 = 0 → 0 < t →
      ContinuousOn η (Icc 0 t) → (∀ s ∈ Ioc (0 : ℝ) t, fwdHull W s = fillH (η '' Icc 0 s)) →
      η '' Icc 0 t ⊆ seedU P →
      (∀ s ∈ Icc (0 : ℝ) t, η s ∈ Hbar ∧ ((η s).im = 0 → (η s).re ∈ Ioo (P.l₀ + 2 * P.μ) (P.r₀ - 2 * P.μ))) →
      MarksAlive W p t → ∀ s ∈ Icc (0 : ℝ) t, ∫ u in (0 : ℝ)..s, markDrift W p c u ^ 2 ≤ C := by
  classical
  set f := seedF P p c c₀ with hf
  set v : ℂ → ℝ := H.indicator (QuantumZipper.K3.greenDensity f) with hv
  have hf2 : ContDiff ℝ 2 f := contDiff_seedF hP hC
  have hfc : HasCompactSupport f := hasCompactSupport_seedF hP
  have hvc : Continuous (QuantumZipper.K3.greenDensity f) := continuous_greenDensity hf2
  have hvs : HasCompactSupport (QuantumZipper.K3.greenDensity f) := hasCompactSupport_greenDensity hfc
  obtain ⟨Cv₀, hCv₀⟩ := hvs.exists_bound_of_continuous hvc
  set Cv := max Cv₀ 0 with hCv
  have hHm : MeasurableSet H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hvb : ∀ z, |v z| ≤ Cv := fun z => by
    by_cases hz : z ∈ H
    · rw [hv, Set.indicator_of_mem hz, ← Real.norm_eq_abs]; exact (hCv₀ z).trans (le_max_left _ _)
    · rw [hv, Set.indicator_of_notMem hz, abs_zero]; exact le_max_right _ _
  have hΔN : ∀ z ∈ seedN P, QuantumZipper.K3.greenDensity f z = 0 := fun z hz => by
    rw [QuantumZipper.K3.greenDensity, laplacian_seedF_eq_zero hP hC hz, mul_zero]
  have hvN : ∀ z, v z ≠ 0 → z ∉ seedN P := fun z hz hzN => by
    apply hz
    by_cases hzH : z ∈ H
    · rw [hv, Set.indicator_of_mem hzH, hΔN z hzN]
    · rw [hv, Set.indicator_of_notMem hzH]
  have htsupN : Disjoint (tsupport (QuantumZipper.K3.greenDensity f)) (seedN P) := by
    rw [Set.disjoint_right]
    intro z hzN hzt
    have hev : QuantumZipper.K3.greenDensity f =ᶠ[𝓝 z] 0 := by
      filter_upwards [isOpen_seedN.mem_nhds hzN] with w hw
      rw [hΔN w hw, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hzt
  have hvH : ∀ z, v z ≠ 0 → z ∈ H := fun z hz => by
    by_contra hzH; exact hz (by rw [hv, Set.indicator_of_notMem hzH])
  have hvt : ∀ z, v z ≠ 0 → z ∈ tsupport (QuantumZipper.K3.greenDensity f) ∩ Hbar := fun z hz =>
    ⟨subset_tsupport _ fun h0 => hz (by rw [hv, Set.indicator_of_mem (hvH z hz), h0]),
      show (0 : ℝ) ≤ z.im from le_of_lt (hvH z hz)⟩
  have hsupR : ∀ z, v z ≠ 0 → ‖z‖ ≤ P.R + 1 := fun z hz => by
    have h1 := QuantumZipper.K3.tsupport_greenDensity_subset f (hvt z hz).1
    have hsub : tsupport f ⊆ closedBall 0 (P.R + 1) :=
      closure_minimal (fun w hw => by
        by_contra hwb
        rw [mem_closedBall, dist_zero_right, not_le] at hwb
        exact hw (by simp only [hf, seedF, seedChi,
          LocalExt.cutoffFn_eq_zero hP.R_pos.le (by linarith) hwb.le, zero_mul])) isClosed_closedBall
    have := hsub h1
    rwa [mem_closedBall, dist_zero_right] at this
  refine ⟨2 * IsSrc.greenBound Cv (P.R + 1) * ∫ z, |v z|, ?_⟩
  intro W t η hW hW0 ht hηc hfill hηU hηH hp s hs
  have hKt : fwdHull W t = fillH (η '' Icc 0 t) := hfill t ⟨ht, le_rfl⟩
  have hcpt : IsCompact (η '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hηc
  have hKU : fwdHull W t ⊆ seedU P := by
    rw [hKt]
    refine fillH_subset_seedU hP hcpt hηU ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩; exact (hηH r hr).1
    · rintro _ ⟨r, hr, rfl⟩ h0; exact (hηH r hr).2 h0
  have hKN : closure (fwdHull W t) ⊆ seedN P := by
    intro z hz
    refine closure_seedU_inter_subset hP ⟨closure_mono hKU hz, ?_⟩
    have : closure (fwdHull W t) ⊆ Hbar := by
      rw [← closure_H]; exact closure_mono (QuantumZipper.fwdHull_mono.2 t)
    exact this hz
  have halive : ∀ z ∈ tsupport (QuantumZipper.K3.greenDensity f) ∩ Hbar, ∃ u, IsForwardSol W z t u := by
    rintro z ⟨hzt, hzH⟩
    have hzN : z ∉ seedN P := Set.disjoint_left.1 htsupN hzt
    rcases (show (0 : ℝ) ≤ z.im from hzH).lt_or_eq with hpos | hzero
    · exact Ito.exists_isForwardSol_of_mem ht.le ⟨hpos, fun hK => hzN (hKN (subset_closure hK))⟩
    · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hz0 : z.re ≠ 0 := fun h => hzN (by rw [hzr, h, Complex.ofReal_zero]; exact zero_mem_seedN hP)
      have hzcl : z ∉ closure (fwdHull W t) := fun h => hzN (hKN h)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hzcl
      have hd : Disjoint (ball ((z.re : ℝ) : ℂ) r) (fwdHull W t) := by
        rw [← hzr]
        exact Set.disjoint_left.2 fun w hw hwK => hball hw (subset_closure hwK)
      obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hz0 ht.le hr hd
      exact ⟨u, by rw [hzr]; exact hu⟩
  obtain ⟨m, hm, hmfar⟩ := exists_far hW ht.le ((hvs.isCompact).inter_right
    (isClosed_le continuous_const Complex.continuous_im)) halive
  have hsrc : IsSrc W v t Cv (P.R + 1) m :=
    { meas := hvc.measurable.indicator hHm
      bound := hvb
      m_pos := hm
      alive := fun z hz => ⟨hvH z hz, fun hK => hvN z hz (hKN (subset_closure hK))⟩
      norm_le := hsupR
      far := fun z hz u hu => hmfar z (hvt z hz) u hu }
  have hp0 : ∀ j, (p j : ℂ) ≠ 0 := fun j => by
    obtain ⟨u, hu⟩ := hp j
    exact ne_zero_of_isForwardSol hW0 ht.le hu
  have hI : IdentHyp W t η p c c₀ v Cv (P.R + 1) m f (seedN P) :=
    { cont := hW
      zero := hW0
      t_pos := ht
      trace_cont := hηc
      fill := hfill
      marks := hp
      seed := hC.seed
      src := hsrc
      open_N := isOpen_seedN
      hull_N := hKN
      zero_N := zero_mem_seedN hP
      src_N := hvN
      green := fun y _ => integral_greenH_mul_indicator_greenDensity hf2 hfc (fun z => seedF_conj z) y
      f_eq := fun y ⟨hyN, hyH⟩ => by
        have hy0 : y ≠ 0 := fun h => by
          have : (0 : ℝ) < y.im := hyH
          rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
        rw [hf, seedF_eq_of_mem_seedN hP hyN, oddExt_of_pos hyH, argSum0, argSum, fwdMap_zero_time hW hW0 hy0]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fwdMap_zero_time hW hW0 (hp0 j)] }
  have heq : ∫ u in (0 : ℝ)..s, markDrift W p c u ^ 2 = ∫ u in (0 : ℝ)..s, srcDrift W v u ^ 2 := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs.1] at hu
    rw [srcDrift_eq_markDrift hI ⟨hu.1, hu.2.trans hs.2⟩]
  rw [heq]
  exact integral_srcDrift_sq_le hW hsrc hs

end Sec5.GB7aAbove4

end InteractingSLE
