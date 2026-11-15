import InteractingSLE.Foundations.SLE.Transience
import InteractingSLE.Foundations.SLE.SpaceFilling.Density
import QuantumZipper.Proofs.Probability.GermZeroOne
import QuantumZipper.Proofs.Thm11.NonSwallowing
import InteractingSLE.Foundations.Topology.Jordan.Crossing
import InteractingSLE.Foundations.Topology.Jordan.Brouwer

/-!
# Rohde–Schramm, Lemma 7.3 and Corollary 7.4: half-neighbourhoods in the hull, space filling

Packet `planning/packets/PROVE-RS05-74.md`; external inputs `EXT-RS05-Lem7.3`, `EXT-RS05-Cor7.4` of
`planning/EXT-INV.md`. Source: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161
(2005), arXiv:math/0106036v4, pinned LaTeX `source/external/RS05/arxiv-latex/SLEcont.tex`:
Lemma 7.3 (`lem-7.3`, lines 2304–2308, proof 2310–2375), Corollary 7.4 (`cor-7.4`, lines
2406–2409, proof 2411–2416) and the update after it (lines 2418–2423).

* **Lemma 7.3** ([RS05], `κ > 4`, `κ ≠ 8`; `κ = 8` by the update): for `t > 0`, almost surely
  `K_t ⊇ {z ∈ ℍ : |z| < ε}` for some `ε > 0`. The specification (proof of Proposition 5.13,
  `source/spec/p145-192.md` line 102) uses it simultaneously for all `t > 0`.
* **Corollary 7.4** (`κ > 8`; `κ = 8` by the update): almost surely `γ[0,∞) = \overline{ℍ}`.

## What is proved here

* `HullContainsHalfBall W t`: the event of Lemma 7.3 at time `t` (`K_t ⊇ ℍ ∩ B(0,ε)`, `ε > 0`).
* **The zero-one step of the proof of Lemma 7.3** ([RS05] p. 33: "By scale invariance, `δ` does not
  depend on `t`. Since these events are monotone in `t` … By Blumenthal's 0-1 law it therefore
  follows that `δ = 1`"): `measure_hullContainsHalfBall_eq` (scale invariance; the probability is a
  law quantity), `ae_forall_hullContainsHalfBall_of_measure_ne_zero` (positivity at one time gives
  the event a.s. for all `t > 0`, the specification's form) and `hullContainsHalfBall_dichotomy`.
  Measurability for the Brownian past: `measurableSet_hullContainsHalfBall`.
* **The arc criterion** (the "topological considerations" of [Law] Prop. 6.10, p. 128):
  `exists_le_norm_of_arc`, `hullContainsHalfBall_of_arc` — if the trace runs, in
  `\overline{ℍ} \ {0}`, from one real half-axis to the other, the hull contains a half-neighbourhood
  of `0` (crossing lemma of the Jordan-curve port, in log-coordinates). Hence Lemma 7.3 follows from
  positivity of the arc event (`ae_forall_sleHull_halfBall_of_arc`, `κ ≠ 8`;
  `ae_forall_sleHull_halfBall_eight_of_arc`, `κ = 8` under the SLE₈ anchor's statement).
* **Corollary 7.4**: the deterministic step `image_Ici_eq_Hbar_of_tendsto_norm`; the density of the
  trace for `κ > 8` (`ae_mem_closure_sleTrace_of_eight_lt`, from `SpaceFilling/Density.lean`); and
  `ae_sleTrace_image_eq_Hbar_of_eight_lt_of_measure_ne_zero`: for `κ > 8`, Corollary 7.4 follows from positivity in
  Lemma 7.3 alone. At `κ = 8`: `ae_sleTrace_image_eq_Hbar_eight_of_density` (conditional on the SLE₈
  anchor, positivity and density).

Not proved here (see `planning/handoffs/PROVE-RS05-74.md`): positivity in Lemma 7.3 (equivalently,
by the dichotomy, Lemma 7.3 itself), whose proofs in [RS05] use Lemma 6.6 and the strong Markov
property at a swallowing time (`4 < κ < 8`) or Theorem 6.4, Lemma 6.5 and Corollary 5.3 (`κ > 8`);
and the density at `κ = 8`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### The event of [RS05, Lemma 7.3] -/

/-- **The event of [RS05, Lemma 7.3] at time `t`**: the hull `K_t` contains the upper
half-neighbourhood `{z ∈ ℍ : |z| < ε}` of the starting point `0` for some `ε > 0`. -/
def HullContainsHalfBall (W : ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull W t

/-- The event of Lemma 7.3 is monotone in time (hulls increase). -/
theorem HullContainsHalfBall.mono {W : ℝ → ℝ} {s t : ℝ} (h : HullContainsHalfBall W s)
    (hst : s ≤ t) : HullContainsHalfBall W t := by
  obtain ⟨ε, hε, h⟩ := h
  exact ⟨ε, hε, fun z hz hzε => (QuantumZipper.fwdHull_mono (W := W)).1 hst (h z hz hzε)⟩

/-- **Brownian scaling of the event of Lemma 7.3.** With `W^a(s) = W(a² s)/a`,
`K_t(W^a) = a⁻¹ K_{a² t}(W)` (`LoewnerAlgebra.mem_fwdHull_scale_iff`). -/
theorem hullContainsHalfBall_scale_iff (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) :
    HullContainsHalfBall (fun s => W (a ^ 2 * s) / a) t ↔ HullContainsHalfBall W (a ^ 2 * t) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hnorm : ‖(a : ℂ)‖ = a := Complex.norm_of_nonneg ha.le
  have him : ∀ z : ℂ, ((a : ℂ) * z).im = a * z.im := fun z => by
    simp [Complex.mul_im]
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨a * ε, mul_pos ha hε, fun z hz hzε => ?_⟩
    have hz' : (a : ℂ)⁻¹ * z ∈ H := by
      have e : ((a : ℂ)⁻¹ * z).im = a⁻¹ * z.im := by
        rw [← Complex.ofReal_inv]
        simp [Complex.mul_im]
      show 0 < ((a : ℂ)⁻¹ * z).im
      rw [e]
      exact mul_pos (inv_pos.2 ha) hz
    have hzε' : ‖(a : ℂ)⁻¹ * z‖ < ε := by
      rw [norm_mul, norm_inv, hnorm, inv_mul_lt_iff₀ ha]
      exact hzε
    have h1 := (LoewnerAlgebra.mem_fwdHull_scale_iff W ha ht _).1 (h _ hz' hzε')
    rwa [← mul_assoc, mul_inv_cancel₀ ha', one_mul] at h1
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε / a, div_pos hε ha, fun z hz hzε => (LoewnerAlgebra.mem_fwdHull_scale_iff W ha ht z).2
      (h _ ?_ ?_)⟩
    · show 0 < ((a : ℂ) * z).im
      rw [him]
      exact mul_pos ha hz
    · rw [norm_mul, hnorm]
      rw [lt_div_iff₀ ha] at hzε
      linarith

/-- **Countable form of the event.** Since `ℍ \ K_t` is open, `K_t ⊇ ℍ ∩ B(0,ε)` can be tested on
the points of a fixed dense sequence and radii `1/(n+1)`. -/
theorem hullContainsHalfBall_iff_denseSeq {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    HullContainsHalfBall W t ↔ ∃ n : ℕ, ∀ m : ℕ, TopologicalSpace.denseSeq ℂ m ∈ H →
      ‖TopologicalSpace.denseSeq ℂ m‖ < 1 / ((n : ℝ) + 1) →
        TopologicalSpace.denseSeq ℂ m ∈ fwdHull W t := by
  constructor
  · rintro ⟨ε, hε, h⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, fun m hm hmn => h _ hm (hmn.trans hn)⟩
  · rintro ⟨n, h⟩
    refine ⟨1 / ((n : ℝ) + 1), by positivity, fun z hz hzn => ?_⟩
    by_contra hzK
    have hU : IsOpen ((H \ fwdHull W t) ∩ ball 0 (1 / ((n : ℝ) + 1))) :=
      (FwdHolo.isOpen_compl_fwdHull hW ht).inter isOpen_ball
    obtain ⟨m, hm⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open hU
      ⟨z, ⟨hz, hzK⟩, by rwa [mem_ball, dist_zero_right]⟩
    obtain ⟨⟨hmH, hmK⟩, hmB⟩ := hm
    rw [mem_ball, dist_zero_right] at hmB
    exact hmK (h m hmH hmB)

section Measurability

variable {Ω : Type*}

/-- **Measurability of `{z ∈ K_t}` with respect to the driving past.** For a process `B` with
continuous paths, the event `z ∈ K_t(√κ B)` is measurable for every σ-algebra for which the
coordinates `B r`, `r ≤ t`, are measurable (QuantumZipper's tamed-flow description of the hull,
`NonSwallow.mem_fwdHull_iff_tamed`, and `measurable_tamed_drive`). -/
theorem measurableSet_mem_fwdHull_drive {m : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ t → Measurable[m] (B r)) (z : ℂ) :
    MeasurableSet[m] {ω | z ∈ fwdHull (drive κ B ω) t} := by
  have hdc : ∀ ω, Continuous (drive κ B ω) := fun ω => drive_continuous (hBc ω)
  have e : {ω | z ∈ fwdHull (drive κ B ω) t} = {ω : Ω | 0 < z.im} ∩
      ⋂ k : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t),
        {ω | (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z q).im < 2 * (1 / ((k : ℝ) + 1))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, exists_prop,
      NonSwallow.mem_fwdHull_iff_tamed (hdc ω) ht, and_assoc]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.iInter fun k =>
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
  have hmeas := (@measurable_tamed_drive Ω m κ (1 / ((k : ℝ) + 1)) (by positivity) B hBc (q : ℝ)
    hq.1 fun r hr => hBm r (hr.trans hq.2)).1
  exact measurableSet_lt (Complex.measurable_im.comp (hmeas.comp measurable_prodMk_left))
    measurable_const

/-- **Measurability of the event of Lemma 7.3 with respect to the driving past up to `t`.** -/
theorem measurableSet_hullContainsHalfBall {m : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ t → Measurable[m] (B r)) :
    MeasurableSet[m] {ω | HullContainsHalfBall (drive κ B ω) t} := by
  have e : {ω | HullContainsHalfBall (drive κ B ω) t} = ⋃ n : ℕ, ⋂ k : ℕ,
      ({ω : Ω | TopologicalSpace.denseSeq ℂ k ∈ H ∧
        ‖TopologicalSpace.denseSeq ℂ k‖ < 1 / ((n : ℝ) + 1)}ᶜ ∪
        {ω | TopologicalSpace.denseSeq ℂ k ∈ fwdHull (drive κ B ω) t}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      hullContainsHalfBall_iff_denseSeq (drive_continuous (hBc ω)) ht, not_and_or, imp_iff_not_or,
      or_assoc]
  rw [e]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun k =>
    (MeasurableSet.const _).compl.union (measurableSet_mem_fwdHull_drive hBc κ ht hBm _)

end Measurability

/-! ### Scale invariance and the zero-one law ([RS05], proof of Lemma 7.3, p. 33) -/

section ZeroOne

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The driver of `a⁻¹ B(a² ·)` is `s ↦ W(a² s)/a` (pathwise; as in
`QuantumZipper.RS.ae_sleTrace_scale`). -/
theorem drive_scale_eq (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {a : ℝ} (ha : 0 < a) :
    drive κ (fun t ω => (√((a ^ 2).toNNReal : ℝ))⁻¹ * B ((a ^ 2).toNNReal * t) ω) ω =
      fun r => drive κ B ω (a ^ 2 * r) / a := by
  funext r
  simp only [drive, Real.coe_toNNReal _ (sq_nonneg a), Real.sqrt_sq ha.le,
    Real.toNNReal_mul (sq_nonneg a)]
  field_simp

/-- The probability of the event of Lemma 7.3 for `B` is that of a Borel set of continuous paths
under the law of a continuous version `G` of `B`. -/
theorem measure_hullContainsHalfBall_eq_toCPath {G : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => G t ω) (hae : ∀ᵐ ω ∂P, ∀ t, G t ω = B t ω) (κ t : ℝ) :
    P {ω | HullContainsHalfBall (drive κ B ω) t} =
      P (toCPath G hc ⁻¹' {f : CPath | HullContainsHalfBall (drive κ canonBM f) t}) := by
  refine measure_congr (hae.mono fun ω h => ?_)
  have hdr : drive κ canonBM (toCPath G hc ω) = drive κ B ω :=
    funext fun s => by simp [drive, h]
  change HullContainsHalfBall (drive κ B ω) t = HullContainsHalfBall _ t
  rw [hdr]

/-- **The probability of the event of Lemma 7.3 is a law quantity**: it is the same for any two
Brownian motions (outer measures; the events are measurable for good versions). -/
theorem measure_hullContainsHalfBall_eq_of_isBrownianReal {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {B' : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P')
    (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | HullContainsHalfBall (drive κ B ω) t} =
      P' {ω | HullContainsHalfBall (drive κ B' ω) t} := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure P' :=
    hB'.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G, hGm, hGc, -, hGbr, hGeq⟩ := exists_good_version0 hB
  obtain ⟨G', hG'm, hG'c, -, hG'br, hG'eq⟩ := exists_good_version0 hB'
  have hS : MeasurableSet {f : CPath | HullContainsHalfBall (drive κ canonBM f) t} :=
    measurableSet_hullContainsHalfBall continuous_canonBM κ ht fun r _ => measurable_canonBM r
  rw [measure_hullContainsHalfBall_eq_toCPath hGc hGeq,
    measure_hullContainsHalfBall_eq_toCPath hG'c hG'eq, ← Measure.map_apply (measurable_toCPath hGm hGc) hS,
    ← Measure.map_apply (measurable_toCPath hG'm hG'c) hS,
    map_toCPath_eq hGbr.toIsPreBrownianReal hG'br.toIsPreBrownianReal hGm hG'm hGc hG'c]

/-- **Scale invariance** ([RS05] p. 33, "By scale invariance, `δ` does not depend on `t`"): for a
Brownian motion, `ℙ[K_t ⊇ ℍ ∩ B(0,ε) for some ε > 0]` is the same for all `t > 0`. -/
theorem measure_hullContainsHalfBall_eq (hB : IsBrownianReal B P) (κ : ℝ) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) :
    P {ω | HullContainsHalfBall (drive κ B ω) s} = P {ω | HullContainsHalfBall (drive κ B ω) t} := by
  set a : ℝ := √(t / s) with ha_def
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos ht hs)
  have ha2 : a ^ 2 * s = t := by
    rw [ha_def, Real.sq_sqrt (div_pos ht hs).le]
    field_simp
  have hc0 : (a ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have hBa := hB.smul hc0
  rw [measure_hullContainsHalfBall_eq_of_isBrownianReal hB hBa κ hs.le]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [drive_scale_eq κ B ω ha, hullContainsHalfBall_scale_iff _ ha hs.le, ha2]

/-- **Zero-one step of [RS05, Lemma 7.3]** (p. 33, "By Blumenthal's 0-1 law it therefore follows
that `δ = 1`"): if for one `t₀ > 0` the event `K_{t₀} ⊇ ℍ ∩ B(0,ε)` has positive probability, then
almost surely it holds for every `t > 0`. The events decrease to the germ event
`⋂ₙ E_{1/(n+1)}`, measurable for the Brownian germ σ-algebra, which is trivial by Blumenthal's
zero-one law (`QuantumZipper.GermZeroOne.isTrivialSigma_iInf_bmPast`); by scale invariance its
probability equals `ℙ[E_{t₀}] > 0`. -/
theorem ae_forall_hullContainsHalfBall_of_measure_ne_zero (hB : IsBrownianReal B P) (κ : ℝ)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hpos : P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t > 0, HullContainsHalfBall (drive κ B ω) t := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G, hGm, hGc, -, hGbr, hGeq⟩ := exists_good_version0 hB
  have hdrG : ∀ᵐ ω ∂P, drive κ G ω = drive κ B ω := hGeq.mono fun ω h =>
    funext fun s => by simp [drive, h]
  set A : ℕ → Set Ω := fun n => {ω | HullContainsHalfBall (drive κ G ω) (GermZeroOne.epsSeq n)}
    with hA
  have hεpos : ∀ n, (0 : ℝ) < GermZeroOne.epsSeq n := fun n =>
    NNReal.coe_pos.2 (GermZeroOne.epsSeq_pos n)
  -- measurability for the Brownian past
  have hApast : ∀ n, MeasurableSet[GermZeroOne.bmPast G (GermZeroOne.epsSeq n)] (A n) := fun n =>
    measurableSet_hullContainsHalfBall hGc κ (hεpos n).le fun r hr =>
      GermZeroOne.measurable_bmPast_coord (NNReal.coe_le_coe.1 hr)
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    GermZeroOne.bmPast_le hGm _ _ (hApast n)
  have hAanti : Antitone A := fun n k hnk ω hω =>
    HullContainsHalfBall.mono hω (NNReal.coe_le_coe.2 (GermZeroOne.epsSeq_antitone hnk))
  -- all the events have the same probability
  have hδ : ∀ n, P (A n) = P {ω | HullContainsHalfBall (drive κ B ω) t₀} := by
    intro n
    rw [measure_hullContainsHalfBall_eq hGbr κ (hεpos n) ht₀]
    exact measure_congr (hdrG.mono fun ω h => by
      change HullContainsHalfBall (drive κ G ω) t₀ = HullContainsHalfBall (drive κ B ω) t₀
      rw [h])
  have hinter : P (⋂ n, A n) = P {ω | HullContainsHalfBall (drive κ B ω) t₀} := by
    rw [hAanti.measure_iInter (fun n => (hAm n).nullMeasurableSet) ⟨0, measure_ne_top P _⟩]
    simp only [hδ, iInf_const]
  -- the intersection lies in the germ σ-algebra
  have hgerm : MeasurableSet[⨅ n, GermZeroOne.bmPast G (GermZeroOne.epsSeq n)] (⋂ n, A n) := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro k
    have e : (⋂ n, A n) = ⋂ n, A (n ⊔ k) := by
      refine Subset.antisymm (fun ω hω => mem_iInter.2 fun n => mem_iInter.1 hω _)
        (fun ω hω => mem_iInter.2 fun n => hAanti le_sup_left (mem_iInter.1 hω n))
    rw [e]
    exact MeasurableSet.iInter fun n => GermZeroOne.bmPast_mono
      (GermZeroOne.epsSeq_antitone le_sup_right) _ (hApast (n ⊔ k))
  rcases GermZeroOne.isTrivialSigma_iInf_bmPast hGbr hGm _ hgerm with h0 | h1
  · exact absurd (hinter.symm.trans h0) hpos
  · have hae : ∀ᵐ ω ∂P, ω ∈ ⋂ n, A n := by
      rw [ae_iff, ← compl_ofPred, ofPred_mem_eq, prob_compl_eq_zero_iff
        (MeasurableSet.iInter hAm)]
      exact h1
    filter_upwards [hae, hdrG] with ω hω hdr t ht
    obtain ⟨n, hn⟩ := (GermZeroOne.tendsto_epsSeq.eventually
      (gt_mem_nhds (show (0 : ℝ≥0) < t.toNNReal from Real.toNNReal_pos.2 ht))).exists
    have hle : (GermZeroOne.epsSeq n : ℝ) ≤ t := by
      have := NNReal.coe_le_coe.2 hn.le
      rwa [Real.coe_toNNReal _ ht.le] at this
    rw [← hdr]
    exact HullContainsHalfBall.mono (mem_iInter.1 hω n) hle

/-- **Zero-one law for the event of [RS05, Lemma 7.3].** For every `κ`, either the hull never
contains a half-neighbourhood of `0` with positive probability, or almost surely every hull
`K_t`, `t > 0`, contains one. -/
theorem hullContainsHalfBall_dichotomy (hB : IsBrownianReal B P) (κ : ℝ) :
    (∀ t > 0, P {ω | HullContainsHalfBall (drive κ B ω) t} = 0) ∨
      ∀ᵐ ω ∂P, ∀ t > 0, HullContainsHalfBall (drive κ B ω) t := by
  by_cases h : ∃ t₀ > 0, P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0
  · obtain ⟨t₀, ht₀, hpos⟩ := h
    exact Or.inr (ae_forall_hullContainsHalfBall_of_measure_ne_zero hB κ ht₀ hpos)
  · push Not at h
    exact Or.inl h

end ZeroOne

/-! ### Lemma 7.3 from positivity at one time -/

section Lemma73

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **[RS05, Lemma 7.3], conditional on positivity at one time** (the specification's form:
simultaneously for all `t > 0`). If for some `t₀ > 0` the hull `K_{t₀}` contains a
half-neighbourhood of `0` with positive probability, then almost surely every `K_t`, `t > 0`,
does. This is the zero-one part of the proof of Lemma 7.3; the positivity is the part of the
proof that uses [RS05, Lemma 6.6] (`4 < κ < 8`) or [RS05, Theorem 6.4, Lemma 6.5, Corollary 5.3]
(`κ > 8`), see the handoff `planning/handoffs/PROVE-RS05-74.md`. -/
theorem ae_forall_sleHull_halfBall_of_measure_ne_zero (hB : IsBrownianReal B P) (κ : ℝ)
    (hpos : ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B ω t := by
  obtain ⟨t₀, ht₀, h⟩ := hpos
  exact ae_forall_hullContainsHalfBall_of_measure_ne_zero hB κ ht₀ h

/-- Positivity at one time transfers between Brownian motions (the probability is a law
quantity, `measure_hullContainsHalfBall_eq_of_isBrownianReal`). -/
theorem exists_measure_hullContainsHalfBall_ne_zero_of {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {B' : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P')
    {κ : ℝ} (hpos : ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0) :
    ∃ t₀ > (0 : ℝ), P' {ω | HullContainsHalfBall (drive κ B' ω) t₀} ≠ 0 := by
  obtain ⟨t₀, ht₀, h⟩ := hpos
  exact ⟨t₀, ht₀, by rwa [← measure_hullContainsHalfBall_eq_of_isBrownianReal hB hB' κ ht₀.le]⟩

end Lemma73

/-! ### Corollary 7.4: the deterministic step -/

section Deterministic

/-- A curve on `[0,∞)` with `‖γ(t)‖ → ∞` has a closed range. -/
theorem isClosed_image_Ici_of_tendsto_norm {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0))
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) : IsClosed (γ '' Ici 0) := by
  refine closure_subset_iff_isClosed.1 fun p hp => ?_
  obtain ⟨T, hT⟩ := (htr.eventually_gt_atTop (‖p‖ + 1)).exists_forall_of_atTop
  set T' := max T 0 with hT'
  have hcomp : IsCompact (γ '' Icc 0 T') :=
    isCompact_Icc.image_of_continuousOn (hc.mono Icc_subset_Ici_self)
  have hsub : γ '' Ici 0 ⊆ γ '' Icc 0 T' ∪ {q : ℂ | ‖p‖ + 1 ≤ ‖q‖} := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases htT : t ≤ T'
    · exact Or.inl ⟨t, ⟨ht, htT⟩, rfl⟩
    · exact Or.inr (hT t (le_trans (le_max_left _ _) (not_le.1 htT).le)).le
  have hp' := closure_mono hsub hp
  rw [closure_union, hcomp.isClosed.closure_eq,
    (isClosed_le continuous_const continuous_norm).closure_eq] at hp'
  rcases hp' with h | h
  · exact image_mono Icc_subset_Ici_self h
  · exact absurd h (by simp)

/-- **Deterministic step of [RS05, Corollary 7.4]** ("Since `γ` is a.s. transient, `γ[0,∞)` is
closed in `ℂ`, and hence is equal to `\overline{ℍ}`"): a curve in `\overline{ℍ}` with
`‖γ(t)‖ → ∞` whose range is dense in `ℍ` has range `\overline{ℍ}`. -/
theorem image_Ici_eq_Hbar_of_tendsto_norm {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0))
    (hH : ∀ t, 0 ≤ t → γ t ∈ Hbar) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hdense : H ⊆ closure (γ '' Ici 0)) : γ '' Ici 0 = Hbar := by
  have hcl := isClosed_image_Ici_of_tendsto_norm hc htr
  refine Subset.antisymm (fun _ ⟨t, ht, h⟩ => h ▸ hH t ht) ?_
  have hHbar : Hbar = closure H := by
    simp only [Hbar, H, Complex.closure_setOfPred_lt_im]
  rw [hHbar, ← hcl.closure_eq]
  exact closure_mono (hdense.trans hcl.closure_eq.le)

/-- Density in `ℍ` from density at the points of a fixed dense sequence. -/
theorem subset_closure_of_denseSeq {S : Set ℂ}
    (h : ∀ m : ℕ, TopologicalSpace.denseSeq ℂ m ∈ H → TopologicalSpace.denseSeq ℂ m ∈ closure S) :
    H ⊆ closure S := by
  intro z hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨m, hmH, hmz⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open
    (isOpen_H.inter (isOpen_ball (x := z) (ε := ε / 2))) ⟨z, hz, mem_ball_self (by positivity)⟩
  obtain ⟨b, hb, hdb⟩ := Metric.mem_closure_iff.1 (h m hmH) (ε / 2) (by positivity)
  refine ⟨b, hb, ?_⟩
  rw [mem_ball] at hmz
  calc dist z b ≤ dist z (TopologicalSpace.denseSeq ℂ m) + dist (TopologicalSpace.denseSeq ℂ m) b :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm] at hmz; exact add_lt_add hmz hdb
    _ = ε := by ring

/-- The radial limit of `F_t(iy)` lies in `\overline{ℍ}`. -/
theorem trace_mem_Hbar_of_tendsto {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {p : ℂ}
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 p)) : p ∈ Hbar := by
  have hcl : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  refine hcl.mem_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hmem : 0 < (fwdMapInv W t (y * I)).im :=
    (fwdMapInv_mem_compl_fwdHull hW hW0 ht (mem_H_mul_I hy)).1
  exact hmem.le

end Deterministic

/-! ### Corollary 7.4 for `κ > 8` from Lemma 7.3 and density -/

section Corollary74

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **[RS05, Corollary 7.4] for `κ > 8`, conditional on its two probabilistic inputs**:
positivity in Lemma 7.3 (`hpos`, giving transience by `ae_tendsto_norm_sleTrace_of_interior`)
and the density of the trace at each fixed point of `ℍ` (`hdense`, [RS05, Lemma 6.3 and
(6.4)]: `Z(z) = ∞` a.s. for `κ ≥ 8`). Then almost surely `γ[0,∞) = \overline{ℍ}`. -/
theorem ae_sleTrace_image_eq_Hbar_of_eight_lt_of_density [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ)
    (hpos : ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0)
    (hdense : ∀ z ∈ H, ∀ᵐ ω ∂P, z ∈ closure (sleTrace κ B ω '' Ici 0)) :
    ∀ᵐ ω ∂P, sleTrace κ B ω '' Ici 0 = Hbar := by
  have hκ0 : 0 < κ := by linarith
  have htr := ae_tendsto_norm_sleTrace_of_interior hB hκ0 (by linarith) fun _ Ω' _ P' B' hB' =>
    (ae_forall_sleHull_halfBall_of_measure_ne_zero hB' κ
      (exists_measure_hullContainsHalfBall_ne_zero_of hB hB' hpos)).mono fun _ h => h 1 one_pos
  obtain ⟨δ, -, hgood⟩ := ae_sleTrace_good_of_eight_lt hB hκ
  have hden : ∀ᵐ ω ∂P, ∀ m : ℕ, TopologicalSpace.denseSeq ℂ m ∈ H →
      TopologicalSpace.denseSeq ℂ m ∈ closure (sleTrace κ B ω '' Ici 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : TopologicalSpace.denseSeq ℂ m ∈ H
    · exact (hdense _ hm).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => absurd h hm
  filter_upwards [htr, hgood, hden, ae_tendsto_fwdMapInv_of_ne_eight hB hκ0 (by linarith),
    hB.cont, hB.eval_zero_ae_eq_zero] with ω htrω hgω hdω hlim hc h0
  have hW := drive_continuous (κ := κ) hc
  have hW0 := drive_zero (κ := κ) h0
  exact image_Ici_eq_Hbar_of_tendsto_norm hgω.2.1
    (fun t ht => trace_mem_Hbar_of_tendsto hW hW0 ht (hlim t ht)) htrω
    (subset_closure_of_denseSeq hdω)

end Corollary74

/-! ### The arc criterion ("topological considerations", [Law] Prop. 6.10, p. 128) -/

section Arc

open InteractingSLE.Foundations.Jordan

/-- Log-coordinates `z ↦ (log |z|, arg z)` in the plane of the crossing lemma. -/
def logCoord (z : ℂ) : Arcs.Plane := Arcs.complexLIE (Complex.log z)

theorem logCoord_zero (z : ℂ) : (logCoord z).ofLp 0 = Real.log ‖z‖ := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (Complex.log z)
  rw [logCoord, show Arcs.complexLIE
      = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp [Complex.log_re]

theorem logCoord_one (z : ℂ) : (logCoord z).ofLp 1 = Complex.arg z := by
  have h := Complex.isometryOfOrthonormal_apply (EuclideanSpace.basisFun (Fin 2) ℝ) (Complex.log z)
  rw [logCoord, show Arcs.complexLIE
      = Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ) from rfl, h]
  simp [Complex.log_im]

theorem eq_of_logCoord_eq {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (h : logCoord z = logCoord w) :
    z = w := by
  have h' : Complex.log z = Complex.log w := Arcs.complexLIE.injective h
  rw [← Complex.exp_log hz, ← Complex.exp_log hw, h']

theorem continuousOn_log_Hbar_diff : ContinuousOn Complex.log (Hbar \ {0}) := by
  intro z hz
  by_cases hs : z ∈ Complex.slitPlane
  · exact (continuousAt_clog hs).continuousWithinAt
  · rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hs
    have hre : z.re < 0 := by
      rcases hs.1.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by simpa using h) (by simpa using hs.2)) hz.2
    exact (continuousWithinAt_log_of_re_neg_of_im_zero hre hs.2).mono fun w hw => hw.1

theorem continuousOn_logCoord : ContinuousOn logCoord (Hbar \ {0}) :=
  Arcs.complexLIE.continuous.comp_continuousOn continuousOn_log_Hbar_diff

theorem logCoord_mem_rect {u : ℂ} (hu : u ∈ Hbar) {lo hi : ℝ} (hlo : lo ≤ Real.log ‖u‖)
    (hhi : Real.log ‖u‖ ≤ hi) :
    (logCoord u).ofLp 0 ∈ Icc lo hi ∧ (logCoord u).ofLp 1 ∈ Icc 0 Real.pi := by
  rw [logCoord_zero, logCoord_one]
  exact ⟨⟨hlo, hhi⟩, Complex.arg_nonneg_iff.2 hu, Complex.arg_le_pi u⟩

theorem arg_eq_zero_of_real_pos {u : ℂ} (h : u.im = 0) (h' : 0 < u.re) : Complex.arg u = 0 := by
  have : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [h])
  rw [this, Complex.arg_ofReal_of_nonneg h'.le]

theorem arg_eq_pi_of_real_neg {u : ℂ} (h : u.im = 0) (h' : u.re < 0) : Complex.arg u = Real.pi := by
  have : u = (u.re : ℂ) := Complex.ext (by simp) (by simp [h])
  rw [this, Complex.arg_ofReal_of_neg h']

/-- **Arc criterion** (the "topological considerations" of [Law] Prop. 6.10, p. 128). Let `U ⊆ ℍ`
be open, connected and unbounded, and let `γ : [s₁, s₂] → \overline{ℍ} \ {0}` be continuous, with
`γ(s₁)` on the negative and `γ(s₂)` on the positive real half-axis. If `U` avoids `γ[s₁, s₂]`, then
`U` stays away from `0`. Proof: in log-coordinates `(log |z|, arg z)` the curve crosses the
rectangle `[log ε, log R] × [0, π]` from top to bottom, while a path in `U` from a point close to
`0` to a point far away crosses it from left to right; the crossing lemma (Maehara, via Brouwer)
makes them meet. -/
theorem exists_le_norm_of_arc {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) (hUH : U ⊆ H)
    (hUb : ¬ Bornology.IsBounded U) {γ : ℝ → ℂ} {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (hγc : ContinuousOn γ (Icc s₁ s₂)) (hγH : ∀ s ∈ Icc s₁ s₂, γ s ∈ Hbar)
    (h0 : ∀ s ∈ Icc s₁ s₂, γ s ≠ 0) (h1 : (γ s₁).im = 0) (h1' : (γ s₁).re < 0)
    (h2 : (γ s₂).im = 0) (h2' : 0 < (γ s₂).re) (hdisj : ∀ s ∈ Icc s₁ s₂, γ s ∉ U) :
    ∃ ε > (0 : ℝ), ∀ z ∈ U, ε ≤ ‖z‖ := by
  have hK : IsCompact (Icc s₁ s₂) := isCompact_Icc
  have hne : (Icc s₁ s₂).Nonempty := nonempty_Icc.2 hs
  obtain ⟨smin, hsmin, hmin⟩ := hK.exists_isMinOn hne (continuous_norm.comp_continuousOn hγc)
  obtain ⟨smax, hsmax, hmax⟩ := hK.exists_isMaxOn hne (continuous_norm.comp_continuousOn hγc)
  have hε₀ : 0 < ‖γ smin‖ := norm_pos_iff.2 (h0 _ hsmin)
  have hminv : ∀ s ∈ Icc s₁ s₂, ‖γ smin‖ ≤ ‖γ s‖ := fun s hs => hmin hs
  have hmaxv : ∀ s ∈ Icc s₁ s₂, ‖γ s‖ ≤ ‖γ smax‖ := fun s hs => hmax hs
  refine ⟨‖γ smin‖, hε₀, fun z hz => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨w, hw, hwR⟩ : ∃ w ∈ U, ‖γ smax‖ + 1 < ‖w‖ := by
    by_contra hcon
    push Not at hcon
    exact hUb (isBounded_iff_forall_norm_le.2 ⟨_, hcon⟩)
  have hj : JoinedIn U z w :=
    ((hU.isConnected_iff_isPathConnected).1 hUc).joinedIn z hz w hw
  set q : ℝ → ℂ := ⇑hj.somePath.extend with hq_def
  have hqc : Continuous q := hj.somePath.continuous_extend
  have hqU : ∀ τ ∈ Icc (0 : ℝ) 1, q τ ∈ U := fun τ hτ => by
    rw [hq_def, show τ = ((⟨τ, hτ⟩ : Icc (0 : ℝ) 1) : ℝ) from rfl, Path.extend_extends']
    exact hj.somePath_mem _
  have hq0 : q 0 = z := hj.somePath.extend_zero
  have hq1 : q 1 = w := hj.somePath.extend_one
  have hqpos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < ‖q τ‖ := fun τ hτ =>
    norm_pos_iff.2 fun h => by
      have := hUH (hqU τ hτ)
      simp [H, h] at this
  -- `a`: the last time with `‖q‖ ≤ ‖z‖`
  set A : Set ℝ := Icc 0 1 ∩ {τ | ‖q τ‖ ≤ ‖z‖} with hA_def
  have hAc : IsClosed A := isClosed_Icc.inter (isClosed_le (continuous_norm.comp hqc)
    continuous_const)
  have hAne : A.Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hq0]⟩
  have hAbdd : BddAbove A := ⟨1, fun τ hτ => hτ.1.2⟩
  set a := sSup A with ha_def
  have haA : a ∈ A := hAc.csSup_mem hAne hAbdd
  have hagt : ∀ τ ∈ Icc (0 : ℝ) 1, a < τ → ‖z‖ < ‖q τ‖ := fun τ hτ hat => by
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hAbdd ⟨hτ, hle⟩) (not_le.2 hat)
  -- `b`: the first time after `a` with `‖q‖ ≥ R`
  set Bs : Set ℝ := Icc a 1 ∩ {τ | ‖γ smax‖ + 1 ≤ ‖q τ‖} with hBs_def
  have hBc : IsClosed Bs := isClosed_Icc.inter (isClosed_le continuous_const
    (continuous_norm.comp hqc))
  have hBne : Bs.Nonempty := ⟨1, ⟨haA.1.2, le_rfl⟩, by simp only [mem_ofPred_eq, hq1]; exact hwR.le⟩
  have hBbdd : BddBelow Bs := ⟨a, fun τ hτ => hτ.1.1⟩
  set b := sInf Bs with hb_def
  have hbB : b ∈ Bs := hBc.csInf_mem hBne hBbdd
  have hblt : ∀ τ ∈ Icc a 1, τ < b → ‖q τ‖ < ‖γ smax‖ + 1 := fun τ hτ htb => by
    by_contra hle
    push Not at hle
    exact absurd (csInf_le hBbdd ⟨hτ, hle⟩) (not_le.2 htb)
  have hzγ : ‖z‖ < ‖γ smax‖ := hlt.trans_le (hminv smax hsmax)
  have hab : a < b := by
    rcases hbB.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hbB.2
      rw [← h] at h1
      have h2 := haA.2
      simp only [mem_ofPred_eq] at h1 h2
      linarith
  have ha01 : a ∈ Icc (0 : ℝ) 1 := haA.1
  have hb01 : b ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans hab.le, hbB.1.2⟩
  have hqa_pos : 0 < ‖q a‖ := hqpos a ha01
  have hnormab : ∀ τ ∈ Icc a b, ‖q a‖ ≤ ‖q τ‖ ∧ ‖q τ‖ ≤ ‖q b‖ := by
    intro τ hτ
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans hτ.1, hτ.2.trans hb01.2⟩
    constructor
    · rcases hτ.1.lt_or_eq with h | h
      · exact haA.2.trans (hagt τ hτ01 h).le
      · rw [h]
    · rcases hτ.2.lt_or_eq with h | h
      · exact (hblt τ ⟨hτ.1, hτ01.2⟩ h).le.trans hbB.2
      · rw [h]
  -- the two crossing paths
  set hp : ℝ → Arcs.Plane := fun σ => logCoord (q (a + (σ + 1) / 2 * (b - a))) with hhp
  set vp : ℝ → Arcs.Plane := fun τ => logCoord (γ (s₂ + (τ + 1) / 2 * (s₁ - s₂))) with hvp
  have hmapq : MapsTo (fun σ : ℝ => a + (σ + 1) / 2 * (b - a)) (Icc (-1) 1) (Icc a b) := by
    intro σ hσ
    have h1 : 0 ≤ (σ + 1) / 2 := by linarith [hσ.1]
    have h2 : (σ + 1) / 2 ≤ 1 := by linarith [hσ.2]
    constructor <;> nlinarith
  have hmapγ : MapsTo (fun τ : ℝ => s₂ + (τ + 1) / 2 * (s₁ - s₂)) (Icc (-1) 1) (Icc s₁ s₂) := by
    intro τ hτ
    have h1 : 0 ≤ (τ + 1) / 2 := by linarith [hτ.1]
    have h2 : (τ + 1) / 2 ≤ 1 := by linarith [hτ.2]
    constructor <;> nlinarith
  have hqab_mem : ∀ σ ∈ Icc (-1 : ℝ) 1, q (a + (σ + 1) / 2 * (b - a)) ∈ U := fun σ hσ =>
    hqU _ ⟨ha01.1.trans (hmapq hσ).1, (hmapq hσ).2.trans hb01.2⟩
  have hqH : ∀ σ ∈ Icc (-1 : ℝ) 1, q (a + (σ + 1) / 2 * (b - a)) ∈ Hbar \ {0} := fun σ hσ => by
    have hH : 0 < (q (a + (σ + 1) / 2 * (b - a))).im := hUH (hqab_mem σ hσ)
    refine ⟨show (0 : ℝ) ≤ _ from hH.le, fun h => ?_⟩
    rw [mem_singleton_iff] at h
    rw [h, Complex.zero_im] at hH
    exact lt_irrefl _ hH
  have hhpc : ContinuousOn hp (Icc (-1) 1) :=
    continuousOn_logCoord.comp (hqc.comp (by fun_prop)).continuousOn fun σ hσ => hqH σ hσ
  have hvpc : ContinuousOn vp (Icc (-1) 1) :=
    continuousOn_logCoord.comp (hγc.comp (by fun_prop : Continuous fun τ : ℝ =>
      s₂ + (τ + 1) / 2 * (s₁ - s₂)).continuousOn hmapγ) fun τ hτ =>
        ⟨hγH _ (hmapγ hτ), h0 _ (hmapγ hτ)⟩
  have hab_log : Real.log ‖q a‖ ≤ Real.log ‖q b‖ :=
    Real.log_le_log hqa_pos (hnormab b ⟨hab.le, le_rfl⟩).1
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := crossing Brouwer.brouwerFPT hab_log Real.pi_pos.le hp vp hhpc hvpc
    (fun σ hσ => by
      have hm := hnormab _ (hmapq hσ)
      have hpos := hqpos _ ⟨ha01.1.trans (hmapq hσ).1, (hmapq hσ).2.trans hb01.2⟩
      exact logCoord_mem_rect (hqH σ hσ).1 (Real.log_le_log hqa_pos hm.1)
        (Real.log_le_log hpos hm.2))
    (fun τ hτ => by
      have hs := hmapγ hτ
      have hpos : 0 < ‖γ (s₂ + (τ + 1) / 2 * (s₁ - s₂))‖ := norm_pos_iff.2 (h0 _ hs)
      refine logCoord_mem_rect (hγH _ hs) (Real.log_le_log hqa_pos ?_)
        (Real.log_le_log hpos ?_)
      · exact (haA.2.trans hlt.le).trans (hminv _ hs)
      · have := hmaxv _ hs
        have hb2 : ‖γ smax‖ + 1 ≤ ‖q b‖ := hbB.2
        linarith)
    (by simp only [hhp]; rw [logCoord_zero]; norm_num)
    (by simp only [hhp]; rw [logCoord_zero, show a + (1 + 1) / 2 * (b - a) = b by ring])
    (by simp only [hvp]; rw [logCoord_one]; norm_num; exact arg_eq_zero_of_real_pos h2 h2')
    (by simp only [hvp]; rw [logCoord_one]; norm_num; exact arg_eq_pi_of_real_neg h1 h1')
  have hqe := eq_of_logCoord_eq (hqH σ hσ).2 (h0 _ (hmapγ hτ)) heq
  exact hdisj _ (hmapγ hτ) (hqe ▸ hqab_mem σ hσ)


/-- **Hull form of the arc criterion.** Suppose `ℍ \ K_t` is an unbounded connected component of
`ℍ \ γ[0,t]` (the generation property of the trace). If on some `[s₁, s₂] ⊆ [0, t]` the curve
runs, in `\overline{ℍ} \ {0}`, from one real half-axis to the other, then `K_t` contains a
half-neighbourhood of `0`. -/
theorem hullContainsHalfBall_of_arc {W : ℝ → ℝ} (hW : Continuous W) {γ : ℝ → ℂ} {t s₁ s₂ : ℝ}
    (ht : 0 ≤ t)
    (hgen : ∃ z ∈ H \ fwdHull W t, connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t)
    (hunb : ¬ Bornology.IsBounded (H \ fwdHull W t)) (hs₁ : 0 ≤ s₁) (hs : s₁ ≤ s₂) (hs₂ : s₂ ≤ t)
    (hγc : ContinuousOn γ (Icc s₁ s₂)) (hγH : ∀ s ∈ Icc s₁ s₂, γ s ∈ Hbar)
    (h0 : ∀ s ∈ Icc s₁ s₂, γ s ≠ 0)
    (hreal : ((γ s₁).im = 0 ∧ (γ s₁).re < 0 ∧ (γ s₂).im = 0 ∧ 0 < (γ s₂).re) ∨
      ((γ s₂).im = 0 ∧ (γ s₂).re < 0 ∧ (γ s₁).im = 0 ∧ 0 < (γ s₁).re)) :
    HullContainsHalfBall W t := by
  obtain ⟨z₀, hz₀, hcomp⟩ := hgen
  set U := H \ fwdHull W t with hU_def
  have hUo : IsOpen U := FwdHolo.isOpen_compl_fwdHull hW ht
  have hz₀F : z₀ ∈ H \ γ '' Icc 0 t := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hcomp
    exact (hcomp ▸ hz₀ : z₀ ∈ (∅ : Set ℂ))
  have hUc : IsConnected U := hcomp ▸ isConnected_connectedComponentIn_iff.2 hz₀F
  have hUsub : U ⊆ H \ γ '' Icc 0 t := hcomp ▸ connectedComponentIn_subset _ _
  have hdisj : ∀ s ∈ Icc s₁ s₂, γ s ∉ U := fun s hs hU =>
    (hUsub hU).2 ⟨s, ⟨hs₁.trans hs.1, hs.2.trans hs₂⟩, rfl⟩
  have hUH : U ⊆ H := fun _ h => h.1
  have key : ∃ ε > (0 : ℝ), ∀ z ∈ U, ε ≤ ‖z‖ := by
    rcases hreal with ⟨h1, h1', h2, h2'⟩ | ⟨h1, h1', h2, h2'⟩
    · exact exists_le_norm_of_arc hUo hUc hUH hunb hs hγc hγH h0 h1 h1' h2 h2' hdisj
    · -- reverse the curve
      have hmap : MapsTo (fun s => s₁ + s₂ - s) (Icc s₁ s₂) (Icc s₁ s₂) := fun s hs =>
        ⟨by linarith [hs.2], by linarith [hs.1]⟩
      refine exists_le_norm_of_arc (γ := fun s => γ (s₁ + s₂ - s)) hUo hUc hUH hunb hs
        (hγc.comp (by fun_prop : Continuous fun s : ℝ => s₁ + s₂ - s).continuousOn hmap)
        (fun s hs => hγH _ (hmap hs)) (fun s hs => h0 _ (hmap hs)) ?_ ?_ ?_ ?_
        (fun s hs => hdisj _ (hmap hs))
      · simpa using h1
      · simpa using h1'
      · simpa using h2
      · simpa using h2'
  obtain ⟨ε, hε, hU⟩ := key
  refine ⟨ε, hε, fun z hz hzε => ?_⟩
  by_contra hzK
  exact absurd (hU z ⟨hz, hzK⟩) (not_le.2 hzε)

/-- The Rohde–Schramm form of the generation property (`ℍ \ K_t` is the component of
`ℍ \ γ[0,t]` containing `M i` for every `M > max ‖γ‖`) gives the hypotheses of
`hullContainsHalfBall_of_arc`. -/
theorem genForm_of_forall_bound {W : ℝ → ℝ} {γ : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hγc : ContinuousOn γ (Icc 0 t))
    (h : ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖γ s‖ < M) →
      H \ fwdHull W t = connectedComponentIn (H \ γ '' Icc 0 t) (M * I)) :
    (∃ z ∈ H \ fwdHull W t, connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t) ∧
      ¬ Bornology.IsBounded (H \ fwdHull W t) := by
  obtain ⟨smax, hsmax, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 ht)
    (continuous_norm.comp_continuousOn hγc)
  have hmaxv : ∀ s ∈ Icc 0 t, ‖γ s‖ ≤ ‖γ smax‖ := fun s hs => hmax hs
  have hmem : ∀ M : ℝ, ‖γ smax‖ < M → (M : ℂ) * I ∈ H \ fwdHull W t := by
    intro M hM
    have hM0 : 0 < M := (norm_nonneg _).trans_lt hM
    have hbd : ∀ s ∈ Icc 0 t, ‖γ s‖ < M := fun s hs => (hmaxv s hs).trans_lt hM
    rw [h M hbd]
    refine mem_connectedComponentIn ⟨mem_H_mul_I hM0, ?_⟩
    rintro ⟨s, hs, hseq⟩
    have := hbd s hs
    rw [hseq, norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg hM0.le] at this
    exact lt_irrefl _ this
  refine ⟨⟨_, hmem (‖γ smax‖ + 1) (by linarith), ?_⟩, fun hb => ?_⟩
  · rw [← h (‖γ smax‖ + 1) fun s hs => (hmaxv s hs).trans_lt (by linarith)]
  · obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
    set M := max (‖γ smax‖ + 1) (R + 1)
    have hM := hR _ (hmem M (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
    have hM0 : 0 < M := lt_of_lt_of_le (by linarith [norm_nonneg (γ smax)]) (le_max_left _ _)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg hM0.le] at hM
    linarith [le_max_right (‖γ smax‖ + 1) (R + 1)]

end Arc


/-! ### Lemma 7.3 from the arc event -/

section ArcEvent

/-- **The arc event** at time `t₀`: by time `t₀` the curve runs, inside `\overline{ℍ} \ {0}`, from one
real half-axis to the other. -/
def TraceArcEvent (γ : ℝ → ℂ) (t₀ : ℝ) : Prop :=
  ∃ s₁ s₂ : ℝ, 0 ≤ s₁ ∧ s₁ ≤ s₂ ∧ s₂ ≤ t₀ ∧ (∀ s ∈ Icc s₁ s₂, γ s ≠ 0) ∧
    (((γ s₁).im = 0 ∧ (γ s₁).re < 0 ∧ (γ s₂).im = 0 ∧ 0 < (γ s₂).re) ∨
      ((γ s₂).im = 0 ∧ (γ s₂).re < 0 ∧ (γ s₁).im = 0 ∧ 0 < (γ s₁).re))

/-- **[RS05, Lemma 7.3] for `κ ≠ 8` from the arc event** (the route of [Law] Prop. 6.10). If with
positive probability the SLE trace runs from one real half-axis to the other without passing
through `0` by some time `t₀ > 0`, then almost surely every hull `K_t`, `t > 0`, contains an upper
half-neighbourhood of `0`. Uses the generation of the hulls by the trace
(`QuantumZipper.RS.rohdeSchrammTraceGen_of_lt_eight`, `rohdeSchrammTraceGen_of_eight_lt`), the
arc criterion and the zero-one law. -/
theorem ae_forall_sleHull_halfBall_of_arc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≠ 8)
    (harc : ∃ t₀ > (0 : ℝ), P {ω | TraceArcEvent (sleTrace κ B ω) t₀} ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B ω t := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hgen : Blueprint.RohdeSchrammTraceGen κ := by
    rcases lt_or_gt_of_ne hκ8 with h | h
    · exact rohdeSchrammTraceGen_of_lt_eight hκ h
    · exact rohdeSchrammTraceGen_of_eight_lt h
  obtain ⟨t₀, ht₀, hpos⟩ := harc
  refine ae_forall_sleHull_halfBall_of_measure_ne_zero hB κ ⟨t₀, ht₀, fun h0 => hpos ?_⟩
  refine le_antisymm ((measure_mono_ae ?_).trans h0.le) bot_le
  filter_upwards [hgen P B hB, ae_tendsto_fwdMapInv_of_ne_eight hB hκ hκ8, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hg hlim hc h0' harcω
  obtain ⟨-, hcont, hcomp⟩ := hg
  obtain ⟨s₁, s₂, hs₁, hs, hs₂, hne, hreal⟩ := harcω
  have hW := drive_continuous (κ := κ) hc
  have hW0 := drive_zero (κ := κ) h0'
  obtain ⟨hgen', hunb⟩ := genForm_of_forall_bound ht₀.le (hcont.mono Icc_subset_Ici_self)
    (hcomp t₀ ht₀.le)
  exact hullContainsHalfBall_of_arc hW ht₀.le hgen' hunb hs₁ hs hs₂
    (hcont.mono fun s hs' => mem_Ici.2 (hs₁.trans hs'.1))
    (fun s hs' => trace_mem_Hbar_of_tendsto hW hW0 (hs₁.trans hs'.1) (hlim s (hs₁.trans hs'.1)))
    hne hreal


/-- The locally uniform radial limit `γ` of the SLE₈ anchor is the QuantumZipper trace. -/
theorem trace_eq_of_tendstoLocallyUniformly {W : ℝ → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : TendstoLocallyUniformly (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv W t (y * I)) γ (𝓝[>] 0))
    (t : ℝ≥0) : trace W t = γ t :=
  ((hγ.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ t)).limUnder_eq

/-- **[RS05, Lemma 7.3] at `κ = 8` from the arc event, conditional on the SLE₈ trace.** `h8` is the
conclusion of the frozen anchor `InteractingSLE.SLE8.ae_exists_continuous_trace` (SLE₈ note,
Theorem 1.1) for `B`. The update after [RS05, Corollary 7.4] states that the proofs at `κ = 8`
are otherwise the same. -/
theorem ae_forall_sleHull_halfBall_eight_of_arc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (h8 : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv (drive 8 B ω) t (y * Complex.I)) γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ H \ fwdHull (drive 8 B ω) t,
              connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull (drive 8 B ω) t) ∧
            ¬ Bornology.IsBounded (H \ fwdHull (drive 8 B ω) t))
    (harc : ∃ t₀ > (0 : ℝ), P {ω | TraceArcEvent (sleTrace 8 B ω) t₀} ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull 8 B ω t := by
  obtain ⟨t₀, ht₀, hpos⟩ := harc
  refine ae_forall_sleHull_halfBall_of_measure_ne_zero hB 8 ⟨t₀, ht₀, fun h0 => hpos ?_⟩
  refine le_antisymm ((measure_mono_ae ?_).trans h0.le) bot_le
  filter_upwards [h8, hB.cont] with ω hω hc harcω
  obtain ⟨γ, hγu, hγc, hγH, -, hgen⟩ := hω
  obtain ⟨s₁, s₂, hs₁, hs, hs₂, hne, hreal⟩ := harcω
  have htr : ∀ s : ℝ, 0 ≤ s → sleTrace 8 B ω s = γ s.toNNReal := fun s hs' => by
    rw [← trace_eq_of_tendstoLocallyUniformly hγu, Real.coe_toNNReal _ hs']
    rfl
  have himg : γ '' Icc 0 t₀.toNNReal = sleTrace 8 B ω '' Icc 0 t₀ := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, ⟨u.coe_nonneg, ?_⟩, ?_⟩
      · have := NNReal.coe_le_coe.2 hu.2
        rwa [Real.coe_toNNReal _ ht₀.le] at this
      · rw [htr _ u.coe_nonneg, Real.toNNReal_coe]
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hu.2⟩, (htr u hu.1).symm⟩
  obtain ⟨hgen', hunb⟩ := hgen t₀.toNNReal
  rw [Real.coe_toNNReal _ ht₀.le, himg] at hgen'
  rw [Real.coe_toNNReal _ ht₀.le] at hunb
  have hcont : ContinuousOn (sleTrace 8 B ω) (Icc s₁ s₂) :=
    (hγc.comp continuous_real_toNNReal).continuousOn.congr fun s hs' => htr s (hs₁.trans hs'.1)
  exact hullContainsHalfBall_of_arc (drive_continuous hc) ht₀.le hgen' hunb hs₁ hs hs₂ hcont
    (fun s hs' => by rw [htr s (hs₁.trans hs'.1)]; exact hγH _) hne hreal

end ArcEvent


/-! ### Density of the trace and Corollary 7.4 for `κ > 8` -/

section DensityCor

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Density of the SLE_κ trace for `κ > 8`** ([RS05, Lemma 6.3 with (6.4)]; [Law] Theorem 7.9):
for each fixed `a ∈ ℍ`, almost surely `a ∈ \overline{γ[0,∞)}`. The conformal radius of `a` tends to
`0` (`ae_exists_fwdLogCR_lt_of_eight_lt`, the one-point martingale), the Schwarz lemma bounds the
distance from `a` to `∂H_t` by twice the conformal radius, and `∂H_t ∩ ℍ ⊆ γ[0,t]` by the
generation of the hulls (`rohdeSchrammTraceGen_of_eight_lt`). -/
theorem ae_mem_closure_sleTrace_of_eight_lt [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) {a : ℂ} (ha : 0 < a.im) :
    ∀ᵐ ω ∂P, a ∈ closure (sleTrace κ B ω '' Ici 0) := by
  refine ae_drive_of_forall_canon hB κ (Q := fun W => a ∈ closure (trace W '' Ici 0))
    fun μ _ hμ => ?_
  filter_upwards [rohdeSchrammTraceGen_of_eight_lt hκ μ canonBM hμ,
    ae_exists_fwdLogCR_lt_of_eight_lt hμ hκ ha, hμ.cont] with f hg hsmall hc
  obtain ⟨-, hcont, hcomp⟩ := hg
  exact mem_closure_image_of_fwdLogCR (drive_continuous hc) hcont
    (fun t ht => (genForm_of_forall_bound ht (hcont.mono Icc_subset_Ici_self) (hcomp t ht)).1)
    ha hsmall

/-- **[RS05, Corollary 7.4] for `κ > 8`, conditional only on positivity in Lemma 7.3**: if for
some `t₀ > 0` the hull `K_{t₀}` contains a half-neighbourhood of `0` with positive probability,
then almost surely `γ[0,∞) = \overline{ℍ}`. -/
theorem ae_sleTrace_image_eq_Hbar_of_eight_lt_of_measure_ne_zero [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ)
    (hpos : ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0) :
    ∀ᵐ ω ∂P, sleTrace κ B ω '' Ici 0 = Hbar :=
  ae_sleTrace_image_eq_Hbar_of_eight_lt_of_density hB hκ hpos fun _ hz =>
    ae_mem_closure_sleTrace_of_eight_lt hB hκ hz


/-- **[RS05, Corollary 7.4] at `κ = 8` (the update after it), conditional.** `htrace` is the
conclusion of the frozen SLE₈ anchor `InteractingSLE.SLE8.ae_exists_continuous_trace` for Brownian
motions on spaces in `Type` (not yet proved); `hpos` is positivity in Lemma 7.3 at `κ = 8`; `hdense`
is the density of the trace at fixed points of `ℍ` at `κ = 8` ([RS05, Lemma 6.3]: `Z(z) = ∞` for
`κ ≥ 8`; the one-point martingale used for `κ > 8` degenerates at `κ = 8`). Then almost surely
`γ[0,∞) = \overline{ℍ}`. -/
theorem ae_sleTrace_image_eq_Hbar_eight_of_density {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (htrace : ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {B' : ℝ≥0 → Ω' → ℝ},
      IsBrownianReal B' P' →
      ∀ᵐ ω ∂P', ∃ γ : ℝ≥0 → ℂ,
        TendstoLocallyUniformly
            (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv (drive 8 B' ω) t (y * Complex.I)) γ (𝓝[>] 0) ∧
          Continuous γ ∧ (∀ t, γ t ∈ Hbar) ∧ γ 0 = 0 ∧
          ∀ t : ℝ≥0,
            (∃ z ∈ H \ fwdHull (drive 8 B' ω) t,
                connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull (drive 8 B' ω) t) ∧
              ¬ Bornology.IsBounded (H \ fwdHull (drive 8 B' ω) t))
    (hpos : ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive 8 B ω) t₀} ≠ 0)
    (hdense : ∀ z ∈ H, ∀ᵐ ω ∂P, z ∈ closure (sleTrace 8 B ω '' Ici 0)) :
    ∀ᵐ ω ∂P, sleTrace 8 B ω '' Ici 0 = Hbar := by
  have htr := ae_tendsto_norm_sleTrace_eight_of_interior hB htrace fun hB' =>
    (ae_forall_sleHull_halfBall_of_measure_ne_zero hB' 8
      (exists_measure_hullContainsHalfBall_ne_zero_of hB hB' hpos)).mono fun _ h => h 1 one_pos
  have hden : ∀ᵐ ω ∂P, ∀ m : ℕ, TopologicalSpace.denseSeq ℂ m ∈ H →
      TopologicalSpace.denseSeq ℂ m ∈ closure (sleTrace 8 B ω '' Ici 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : TopologicalSpace.denseSeq ℂ m ∈ H
    · exact (hdense _ hm).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => absurd h hm
  filter_upwards [htr, htrace hB, hden, hB.cont, hB.eval_zero_ae_eq_zero] with ω htrω h8 hdω hc h0
  obtain ⟨γ, hγu, hγc, -, -, -⟩ := h8
  obtain ⟨hcont, hlim⟩ := trace_good_of_tendstoLocallyUniformly hγu hγc
  have hW := drive_continuous (κ := 8) hc
  have hW0 := drive_zero (κ := 8) h0
  have hcontOn : ContinuousOn (sleTrace 8 B ω) (Ici 0) :=
    (hcont.comp continuous_real_toNNReal).continuousOn.congr fun t ht => by
      simp only [Function.comp, Real.coe_toNNReal _ (mem_Ici.1 ht)]
      rfl
  exact image_Ici_eq_Hbar_of_tendsto_norm hcontOn
    (fun t ht => trace_mem_Hbar_of_tendsto hW hW0 ht (hlim t ht)) htrω
    (subset_closure_of_denseSeq hdω)

end DensityCor

end InteractingSLE
