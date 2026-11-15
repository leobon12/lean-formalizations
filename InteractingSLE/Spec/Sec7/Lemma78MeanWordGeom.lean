/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanUntouched
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# The real boundary of the first-contact chart: the base `[a, b]` and the untouched correspondence

Packet PROVE-PRIMEEND2, item (a) of `planning/handoffs/PROVE-PRIMEEND.md` (the geometry of Lemma 7.8's boundary word,
spec pp. 292–293; Aux. 78). On the contact event, `K = η₁[0, s₀] ∪ η₂[0, t₀]` is a connected compact meeting `ℝ`; let
`[a, b]` be the hull of its real points (`baseL`, `baseR`). The first-contact chart `φ : D → ℍ` (inverse `ψ`,
continuous on `ℍ̄`) relates the real boundary as follows:

* a real point `x < a` (or `x > b`) has a ball free of `K` and of `fill K`, so it is an untouched accessible boundary
  point (`exists_ball_of_lt_baseL`, `exists_ball_of_baseR_lt`);
* a real point of `(a, b) \ K` is not accessible from `D` (`notMem_closure_D_of_mem_Ioo`; it is enclosed by `K`);
* for a real chart point `w`, `ψ(w)` is either in `K` or an untouched real point accessible from `D`
  (`inv_mem_K_or`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

section Geom

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- The real points of the first-contact compact. -/
def PairData.realK (d : PairData Ω) (ω : Ω) : Set ℝ := {x : ℝ | (x : ℂ) ∈ d.K ω}

/-- The left end `a` of the real base of `K`. -/
def PairData.baseL (d : PairData Ω) (ω : Ω) : ℝ := sInf (d.realK ω)

/-- The right end `b` of the real base of `K`. -/
def PairData.baseR (d : PairData Ω) (ω : Ω) : ℝ := sSup (d.realK ω)

/-- The path facts on the contact event. -/
theorem PairData.IsMeasGood.pathFacts (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    ContinuousOn (d.η₁ ω) (Icc 0 (d.s₀ ω)) ∧ ContinuousOn (d.η₂ ω) (Icc 0 (d.t₀ ω)) ∧
      MapsTo (d.η₁ ω) (Icc 0 (d.s₀ ω)) Hbar ∧ MapsTo (d.η₂ ω) (Icc 0 (d.t₀ ω)) Hbar ∧
      (d.η₁ ω 0).im = 0 ∧ (d.η₂ ω 0).im = 0 ∧ d.η₁ ω (d.s₀ ω) = d.η₂ ω (d.t₀ ω) := by
  have hg := hd.good ω hE.1
  have hfc := hd.isFirstContact hE
  refine ⟨?_, ?_, fun s hs => hg.2.2.1 s ((ENNReal.coe_le_coe.2 hs.2).trans hfc.1),
    fun t ht => hg.2.2.2.1 t ((ENNReal.coe_le_coe.2 ht.2).trans hfc.2.1), hg.2.2.2.2.1, hg.2.2.2.2.2.1,
    hfc.2.2.1⟩
  · rw [Icc_zero_eq_Iic]; exact hd.continuousOn₁ hE
  · rw [Icc_zero_eq_Iic]; exact hd.continuousOn₂ hE

theorem PairData.IsMeasGood.isCompact_realK (hd : d.IsMeasGood) (ω : Ω) : IsCompact (d.realK ω) :=
  Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage (hd.isCompact_K ω)

theorem PairData.IsMeasGood.nonempty_realK (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    (d.realK ω).Nonempty := by
  obtain ⟨-, -, -, -, h0, -, -⟩ := hd.pathFacts hE
  refine ⟨(d.η₁ ω 0).re, ?_⟩
  show (((d.η₁ ω 0).re : ℝ) : ℂ) ∈ d.K ω
  have e : (((d.η₁ ω 0).re : ℝ) : ℂ) = d.η₁ ω 0 := Complex.ext (by simp) (by simp [h0])
  rw [e, K_of_mem hE]
  exact Or.inl ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩

theorem PairData.IsMeasGood.baseL_mem (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : d.baseL ω ∈ d.realK ω :=
  (hd.isCompact_realK ω).sInf_mem (hd.nonempty_realK hE)

theorem PairData.IsMeasGood.baseR_mem (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : d.baseR ω ∈ d.realK ω :=
  (hd.isCompact_realK ω).sSup_mem (hd.nonempty_realK hE)

theorem PairData.IsMeasGood.baseL_le (hd : d.IsMeasGood) {ω : Ω} {x : ℝ} (hx : (x : ℂ) ∈ d.K ω) :
    d.baseL ω ≤ x :=
  csInf_le (hd.isCompact_realK ω).bddBelow hx

theorem PairData.IsMeasGood.le_baseR (hd : d.IsMeasGood) {ω : Ω} {x : ℝ} (hx : (x : ℂ) ∈ d.K ω) :
    x ≤ d.baseR ω :=
  le_csSup (hd.isCompact_realK ω).bddAbove hx

theorem PairData.IsMeasGood.baseL_le_baseR (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : d.baseL ω ≤ d.baseR ω :=
  hd.le_baseR (hd.baseL_mem hE)

/-- `dist z (Re z) = |Im z|`. -/
theorem dist_ofReal_re (z : ℂ) : dist z (z.re : ℂ) = |z.im| := by
  rw [Complex.dist_eq]
  have : z - (z.re : ℂ) = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **A real point beyond a compact's real points has a ball free of the compact and of its filling** (deterministic):
if every real point of the compact `K` is `≥ c` and `x < c`, then some `B(x, ρ)` misses `K` and `fill K` (a thin strip
along `(−∞, x)` connects the half-ball to `∞` off `K`). -/
theorem exists_ball_disjoint_of_lt {K : Set ℂ} (hK : IsCompact K) {x c : ℝ} (hxc : x < c)
    (hKc : ∀ z ∈ K, z.im = 0 → c ≤ z.re) :
    ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) K ∧ Disjoint (ball (x : ℂ) ρ) (fillH K) := by
  set x' : ℝ := (x + c) / 2 with hx'
  set F : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re ≤ x'} with hF
  have hFc : IsClosed F :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le Complex.continuous_re continuous_const)
  have hxF : (x : ℂ) ∈ F := ⟨by simp, by simp [hx']; linarith⟩
  have hKF : ∀ z ∈ K, z ∉ F := fun z hz hzF => by
    have := hKc z hz hzF.1
    linarith [hzF.2]
  -- a positive distance from `K` to `F`
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ infDist z F := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun z hz => by rw [hKe] at hz; exact absurd hz (notMem_empty z)⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt F).continuousOn
    exact ⟨infDist z₀ F, (hFc.notMem_iff_infDist_pos ⟨_, hxF⟩).1 (hKF z₀ hz₀), fun z hz => hmin hz⟩
  have hnotK : ∀ z, infDist z F < δ → z ∉ K := fun z hz hzK => (hδK z hzK).not_gt hz
  set ρ := min δ (x' - x) with hρ
  have hρpos : 0 < ρ := lt_min hδ (by rw [hx']; linarith)
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · refine Set.disjoint_left.2 fun z hz => hnotK z ?_
    calc infDist z F ≤ dist z (x : ℂ) := infDist_le_dist_of_mem hxF
      _ < ρ := hz
      _ ≤ δ := min_le_left _ _
  -- the strip
  set V : Set ℂ := {w : ℂ | w.re < x' ∧ 0 < w.im ∧ w.im < δ} with hV
  have hVconv : Convex ℝ V := by
    refine ((convex_halfSpace_lt (f := fun w : ℂ => w.re) Complex.reLm.isLinear x').inter
      ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
        (convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear δ)))
  have hVK : V ⊆ H \ K := fun w hw => ⟨hw.2.1, hnotK w (by
    calc infDist w F ≤ dist w (w.re : ℂ) := infDist_le_dist_of_mem ⟨by simp, by simp; exact hw.1.le⟩
      _ = |w.im| := dist_ofReal_re w
      _ = w.im := abs_of_pos hw.2.1
      _ < δ := hw.2.2)⟩
  have hVu : ¬ IsBounded V := by
    intro hb
    obtain ⟨C, hC⟩ := hb.subset_closedBall 0
    set t : ℝ := -(|x'| + |C| + 1) with ht
    have hmem : ((t : ℂ) + ((δ / 2 : ℝ) : ℂ) * I) ∈ V := by
      refine ⟨?_, ?_, ?_⟩ <;> simp [ht]
      · linarith [neg_abs_le x', abs_nonneg C]
      · exact hδ
      · linarith
    have h1 := mem_closedBall_zero_iff.1 (hC hmem)
    have h2 : |t| ≤ ‖(t : ℂ) + ((δ / 2 : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((t : ℂ) + ((δ / 2 : ℝ) : ℂ) * I)
      simpa using this
    have ht' : |t| = |x'| + |C| + 1 := by rw [ht, abs_neg, abs_of_pos (by positivity)]
    linarith [le_abs_self C, abs_nonneg x']
  have hVD := HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hK.isClosed hVconv.isPreconnected hVu hVK
  refine Set.disjoint_left.2 fun z hz hzF => ?_
  have hzH : z ∈ H := hzF.1
  have hzV : z ∈ V := by
    have hd' : dist z (x : ℂ) < ρ := hz
    have hre : |z.re - x| < ρ := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.dist_eq] at hd'
      simp only [sub_re, ofReal_re] at this
      linarith
    have him : |z.im| < ρ := by
      have := Complex.abs_im_le_norm (z - x)
      rw [Complex.dist_eq] at hd'
      simp only [sub_im, ofReal_im, sub_zero] at this
      linarith
    refine ⟨?_, hzH, ?_⟩
    · linarith [(abs_lt.1 hre).2, min_le_right δ (x' - x)]
    · linarith [(abs_lt.1 him).2, min_le_left δ (x' - x)]
  exact (hVD hzV).2 hzF

/-- The mirror image of `exists_ball_disjoint_of_lt`: if every real point of `K` is `≤ c` and `c < x`. -/
theorem exists_ball_disjoint_of_gt {K : Set ℂ} (hK : IsCompact K) {x c : ℝ} (hxc : c < x)
    (hKc : ∀ z ∈ K, z.im = 0 → z.re ≤ c) :
    ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) K ∧ Disjoint (ball (x : ℂ) ρ) (fillH K) := by
  set x' : ℝ := (x + c) / 2 with hx'
  set F : Set ℂ := {z : ℂ | z.im = 0 ∧ x' ≤ z.re} with hF
  have hFc : IsClosed F :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have hxF : (x : ℂ) ∈ F := ⟨by simp, by simp [hx']; linarith⟩
  have hKF : ∀ z ∈ K, z ∉ F := fun z hz hzF => by
    have := hKc z hz hzF.1
    linarith [hzF.2]
  -- a positive distance from `K` to `F`
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ infDist z F := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun z hz => by rw [hKe] at hz; exact absurd hz (notMem_empty z)⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_infDist_pt F).continuousOn
    exact ⟨infDist z₀ F, (hFc.notMem_iff_infDist_pos ⟨_, hxF⟩).1 (hKF z₀ hz₀), fun z hz => hmin hz⟩
  have hnotK : ∀ z, infDist z F < δ → z ∉ K := fun z hz hzK => (hδK z hzK).not_gt hz
  set ρ := min δ (x - x') with hρ
  have hρpos : 0 < ρ := lt_min hδ (by rw [hx']; linarith)
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · refine Set.disjoint_left.2 fun z hz => hnotK z ?_
    calc infDist z F ≤ dist z (x : ℂ) := infDist_le_dist_of_mem hxF
      _ < ρ := hz
      _ ≤ δ := min_le_left _ _
  -- the strip
  set V : Set ℂ := {w : ℂ | x' < w.re ∧ 0 < w.im ∧ w.im < δ} with hV
  have hVconv : Convex ℝ V := by
    refine ((convex_halfSpace_gt (f := fun w : ℂ => w.re) Complex.reLm.isLinear x').inter
      ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
        (convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear δ)))
  have hVK : V ⊆ H \ K := fun w hw => ⟨hw.2.1, hnotK w (by
    calc infDist w F ≤ dist w (w.re : ℂ) := infDist_le_dist_of_mem ⟨by simp, by simp; exact hw.1.le⟩
      _ = |w.im| := dist_ofReal_re w
      _ = w.im := abs_of_pos hw.2.1
      _ < δ := hw.2.2)⟩
  have hVu : ¬ IsBounded V := by
    intro hb
    obtain ⟨C, hC⟩ := hb.subset_closedBall 0
    set t : ℝ := |x'| + |C| + 1 with ht
    have hmem : ((t : ℂ) + ((δ / 2 : ℝ) : ℂ) * I) ∈ V := by
      refine ⟨?_, ?_, ?_⟩ <;> simp [ht]
      · linarith [le_abs_self x', abs_nonneg C]
      · exact hδ
      · linarith
    have h1 := mem_closedBall_zero_iff.1 (hC hmem)
    have h2 : |t| ≤ ‖(t : ℂ) + ((δ / 2 : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((t : ℂ) + ((δ / 2 : ℝ) : ℂ) * I)
      simpa using this
    have ht' : |t| = |x'| + |C| + 1 := by rw [ht, abs_of_pos (by positivity)]
    linarith [le_abs_self C, abs_nonneg x']
  have hVD := HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hK.isClosed hVconv.isPreconnected hVu hVK
  refine Set.disjoint_left.2 fun z hz hzF => ?_
  have hzH : z ∈ H := hzF.1
  have hzV : z ∈ V := by
    have hd' : dist z (x : ℂ) < ρ := hz
    have hre : |z.re - x| < ρ := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.dist_eq] at hd'
      simp only [sub_re, ofReal_re] at this
      linarith
    have him : |z.im| < ρ := by
      have := Complex.abs_im_le_norm (z - x)
      rw [Complex.dist_eq] at hd'
      simp only [sub_im, ofReal_im, sub_zero] at this
      linarith
    refine ⟨?_, hzH, ?_⟩
    · linarith [(abs_lt.1 hre).1, min_le_right δ (x - x')]
    · linarith [(abs_lt.1 him).2, min_le_left δ (x - x')]
  exact (hVD hzV).2 hzF

/-- The real point `↑(Re z)` of a real complex number. -/
theorem ofReal_re_eq {z : ℂ} (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz])

/-- **Real points left of the base are untouched**: a ball around them misses `K` and `fill K`. -/
theorem PairData.IsMeasGood.exists_ball_of_lt_baseL (hd : d.IsMeasGood) {ω : Ω} {x : ℝ} (hx : x < d.baseL ω) :
    ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (d.K ω) ∧ Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω)) :=
  exists_ball_disjoint_of_lt (hd.isCompact_K ω) hx fun z hz hz0 =>
    hd.baseL_le (show ((z.re : ℝ) : ℂ) ∈ d.K ω by rw [ofReal_re_eq hz0]; exact hz)

/-- **Real points right of the base are untouched.** -/
theorem PairData.IsMeasGood.exists_ball_of_baseR_lt (hd : d.IsMeasGood) {ω : Ω} {x : ℝ} (hx : d.baseR ω < x) :
    ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (d.K ω) ∧ Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω)) :=
  exists_ball_disjoint_of_gt (hd.isCompact_K ω) hx fun z hz hz0 =>
    hd.le_baseR (show ((z.re : ℝ) : ℂ) ∈ d.K ω by rw [ofReal_re_eq hz0]; exact hz)

omit [MeasurableSpace Ω] in
/-- A real point with a ball free of `fill K` is accessible from `D`. -/
theorem PairData.mem_closure_D_of_disjoint {ω : Ω} {x : ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hdis : Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω))) : (x : ℂ) ∈ closure (d.D ω) := by
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  set t : ℝ := min ε ρ / 2 with ht
  have htpos : 0 < t := by positivity
  have htl : t < min ε ρ := by rw [ht]; linarith [lt_min hε hρ]
  have hdist : dist (x : ℂ) ((x : ℂ) + (t : ℂ) * I) = t := by
    rw [Complex.dist_eq, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos htpos]
  have hH : (x : ℂ) + (t : ℂ) * I ∈ H := show 0 < ((x : ℂ) + (t : ℂ) * I).im by simpa using htpos
  refine ⟨(x : ℂ) + (t : ℂ) * I, ⟨hH, fun hF => Set.disjoint_left.1 hdis ?_ hF⟩, ?_⟩
  · rw [mem_ball, dist_comm, hdist]; exact htl.trans_le (min_le_right _ _)
  · rw [hdist]; exact htl.trans_le (min_le_left _ _)

/-- **Real points strictly inside the base and off `K` are not accessible from `D`** (they are enclosed by `K`). -/
theorem PairData.IsMeasGood.notMem_closure_D_of_mem_Ioo (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x : ℝ}
    (h1 : d.baseL ω < x) (h2 : x < d.baseR ω) (hxK : (x : ℂ) ∉ d.K ω) : (x : ℂ) ∉ closure (d.D ω) := by
  obtain ⟨hc₁, hc₂, hH₁, hH₂, -, -, hp⟩ := hd.pathFacts hE
  have hKζ : d.K ω = joinPath (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) '' Icc 0 ((d.s₀ ω : ℝ) + d.t₀ ω) := by
    rw [K_of_mem hE, image_joinPath hp]
  have hL : ((d.baseL ω : ℝ) : ℂ) ∈ d.K ω := hd.baseL_mem hE
  have hR : ((d.baseR ω : ℝ) : ℂ) ∈ d.K ω := hd.baseR_mem hE
  rw [hKζ] at hL hR hxK
  obtain ⟨u₁, hu₁, hζ₁⟩ := hL
  obtain ⟨u₂, hu₂, hζ₂⟩ := hR
  have hcl := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt (continuousOn_joinPath hc₁ hc₂ hp)
    (mapsTo_joinPath hH₁ hH₂) hu₁ hu₂ (by rw [hζ₁]; simp) (by rw [hζ₂]; simp) (by rw [hζ₁]; simpa using h1)
    (by rw [hζ₂]; simpa using h2) hxK
  rw [← hKζ] at hcl hxK
  intro hxD
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hd.isCompact_K ω).isClosed.isOpen_compl _ hxK
  have hdis : Disjoint (ball (x : ℂ) r) (d.K ω) := Set.disjoint_left.2 fun z hz hzK => hball hz hzK
  have hdF := disjoint_ball_fillH_of_mem_closure (hd.isCompact_K ω).isClosed hdis hxD
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ isOpen_ball (mem_ball_self hr)
  exact Set.disjoint_left.1 hdF hz1 hz2

/-- **The chart inverse at a real point**: `ψ(w)` lies on `K`, or it is an untouched real point accessible from
`D` (a non-real point off `K` and off `D` lies in a bounded pocket, an open set missing `D`). -/
theorem PairData.IsMeasGood.inv_mem_K_or (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (w : ℝ) :
    d.inv ω w ∈ d.K ω ∨ ((d.inv ω w).im = 0 ∧ d.inv ω w ∉ d.K ω ∧ d.inv ω w ∈ closure (d.D ω)) := by
  obtain ⟨-, hcl⟩ := hd.tendsto_inv_real hE w
  by_cases hK : d.inv ω w ∈ d.K ω
  · exact Or.inl hK
  refine Or.inr ⟨?_, hK, hcl⟩
  have hC := (hd.isFirstContactChart hE).2
  have hnD : d.inv ω w ∉ d.D ω := by
    rw [hd.D_of_mem hE]
    exact hC.2.2.2.1 w fun h => by simpa using (show (0 : ℝ) < (w : ℂ).im from h)
  have hHbar : d.inv ω w ∈ Hbar := by
    have := closure_mono (show d.D ω ⊆ H from sdiff_subset) hcl
    rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar] at this
  rcases mem_H_or_im_eq_zero hHbar with hH | h0
  · exfalso
    have hKc := (hd.isCompact_K ω).isClosed
    have hF : d.inv ω w ∈ fillH (d.K ω) := by
      by_contra h
      exact hnD ⟨hH, h⟩
    have hbd : IsBounded (connectedComponentIn (H \ d.K ω) (d.inv ω w)) := by
      have := hF.2.resolve_left (by rw [hKc.closure_eq]; exact hK)
      rwa [hKc.closure_eq] at this
    set C := connectedComponentIn (H \ d.K ω) (d.inv ω w) with hCdef
    have hCo : IsOpen C := (QuantumZipper.isOpen_H.sdiff hKc).connectedComponentIn
    have hmem : d.inv ω w ∈ C := mem_connectedComponentIn ⟨hH, hK⟩
    have hCD : Disjoint C (d.D ω) := by
      refine Set.disjoint_left.2 fun z hzC hzD => hzD.2 ⟨hzD.1, Or.inr ?_⟩
      rw [hKc.closure_eq, ← connectedComponentIn_eq hzC]
      exact hbd
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl C hCo hmem
    exact Set.disjoint_left.1 hCD hz1 hz2
  · exact h0

/-- **The boundary correspondence** at a real point: the real part of the limit of the chart `φ` there. -/
def PairData.bdry (d : PairData Ω) (ω : Ω) (x : ℝ) : ℝ := (limUnder (𝓝[d.D ω] (x : ℂ)) (d.fwd ω)).re

/-- **At an untouched accessible real point `x`, `φ → ℓ(x)` (real), `ψ(ℓ(x)) = x`, and `ℓ(x)` is the only preimage**
(the point is regular: `isUnboundedLinked_of_notMem`). -/
theorem PairData.IsMeasGood.bdry_spec (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x : ℝ}
    (hxK : (x : ℂ) ∉ d.K ω) (hxD : (x : ℂ) ∈ closure (d.D ω)) :
    Tendsto (d.fwd ω) (𝓝[d.D ω] (x : ℂ)) (𝓝 (d.bdry ω x : ℂ)) ∧ d.inv ω (d.bdry ω x) = x ∧
      ∀ w' ∈ Hbar, d.inv ω w' = x → w' = d.bdry ω x := by
  obtain ⟨hc₁, hc₂, -, -, h0₁, -, hp⟩ := hd.pathFacts hE
  have hC := (hd.isFirstContactChart hE).2
  have hDa := hd.D_of_mem hE
  have hreg : IsChartRegularPoint (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (x : ℂ) :=
    Or.inr (isUnboundedLinked_of_notMem hc₁ hc₂ h0₁ hp (by rw [← K_of_mem hE]; exact hxK))
  obtain ⟨w, hwH, hT, hψw, huniq⟩ := hC.2.2.2.2.2.2.2.2.2.2 (x : ℂ) (by rw [← hDa]; exact hxD) hreg
  rw [← hDa] at hT
  have hw0 : w.im = 0 := by
    rcases mem_H_or_im_eq_zero hwH with hH | h0
    · exfalso
      have hmem := hC.2.1.mapsTo hH
      rw [hψw, ← hDa] at hmem
      have h0 : (0 : ℝ) < (x : ℂ).im := hmem.1
      simp at h0
    · exact h0
  have hNe : (𝓝[d.D ω] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxD
  have hlim : limUnder (𝓝[d.D ω] (x : ℂ)) (d.fwd ω) = w := hT.limUnder_eq
  have hbw : (d.bdry ω x : ℂ) = w := by
    rw [PairData.bdry, hlim]; exact ofReal_re_eq hw0
  rw [hbw]
  exact ⟨hT, hψw, huniq⟩

/-- The bounded displacement of the chart inverse, `‖ψ(w) − w‖ ≤ M` on `ℍ̄`. -/
theorem PairData.IsMeasGood.exists_inv_sub_le (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    ∃ M : ℝ, ∀ w ∈ Hbar, ‖d.inv ω w - w‖ ≤ M :=
  (hd.isFirstContactChart hE).2.2.2.2.2.2.2.2.2.2.1

/-- **The boundary correspondence is locally the real part of the Schwarz reflection** of the mapping-out function
(minus the shift), at an untouched real point `x` with a ball free of `fill K`. -/
theorem PairData.IsMeasGood.eventually_bdry_eq (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x ρ : ℝ} (hρ : 0 < ρ)
    (hK : Disjoint (ball (x : ℂ) ρ) (d.K ω)) (hF : Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω))) :
    ∃ G : ℂ → ℂ, ContinuousAt (fun y : ℝ => (G y).re) x ∧
      ∀ᶠ y in 𝓝 x, d.bdry ω y = (G y).re - (d.shift ω).re := by
  have hA := hd.isHPHull ω
  have hg : IsMapOut (fillH (d.K ω)) (d.g ω) := ConformalImage.isMapOut_mapOut hA
  obtain ⟨G, hG⟩ := Sec7.exists_isBdryReflection hA hg hρ hF
  have hr := hG.pos
  have hGc : ContinuousOn G (ball (x : ℂ) (ρ / 2)) := hG.diff.continuousOn
  refine ⟨G, ?_, ?_⟩
  · have := (hGc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).comp
      Complex.continuous_ofReal.continuousAt
    exact Complex.continuous_re.continuousAt.comp this
  · have hball : ∀ᶠ y in 𝓝 x, y ∈ Ioo (x - ρ / 2) (x + ρ / 2) := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hball] with y hy
    have hyb : (y : ℂ) ∈ ball (x : ℂ) (ρ / 2) := by
      rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    -- a small ball around `y` inside `B(x, ρ/2)`
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isOpen_ball _ hyb
    have hyK : (y : ℂ) ∉ d.K ω := fun h =>
      Set.disjoint_left.1 hK (ball_subset_ball (by linarith) hyb) h
    have hyF : Disjoint (ball (y : ℂ) ε) (fillH (d.K ω)) :=
      hF.mono_left (hεb.trans (ball_subset_ball (by linarith)))
    have hyD := PairData.mem_closure_D_of_disjoint (d := d) hε hyF
    obtain ⟨hT, -, -⟩ := hd.bdry_spec hE hyK hyD
    have hNe : (𝓝[d.D ω] (y : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hyD
    have hT' : Tendsto (d.fwd ω) (𝓝[d.D ω] (y : ℂ)) (𝓝 (G y - d.shift ω)) := by
      have hGy : Tendsto G (𝓝[d.D ω] (y : ℂ)) (𝓝 (G y)) :=
        (hGc.continuousAt (isOpen_ball.mem_nhds hyb)).tendsto.mono_left nhdsWithin_le_nhds
      refine (hGy.sub_const (d.shift ω)).congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hyb)] with z hzD hzb
      show G z - d.shift ω = d.g ω z - d.shift ω
      rw [hG.eqOn ⟨hzb, hzD.1⟩]
    have heq := tendsto_nhds_unique hT hT'
    have := congrArg Complex.re heq
    simpa using this

/-- **The boundary correspondence is continuous on `(−∞, a)`.** -/
theorem PairData.IsMeasGood.continuousOn_bdry_Iio (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    ContinuousOn (d.bdry ω) (Iio (d.baseL ω)) := by
  intro x hx
  obtain ⟨ρ, hρ, hK, hF⟩ := hd.exists_ball_of_lt_baseL hx
  obtain ⟨G, hGc, hev⟩ := hd.eventually_bdry_eq hE hρ hK hF
  exact ((hGc.sub continuousAt_const).congr (hev.mono fun y hy => hy.symm)).continuousWithinAt

/-- **The boundary correspondence is continuous on `(b, ∞)`.** -/
theorem PairData.IsMeasGood.continuousOn_bdry_Ioi (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    ContinuousOn (d.bdry ω) (Ioi (d.baseR ω)) := by
  intro x hx
  obtain ⟨ρ, hρ, hK, hF⟩ := hd.exists_ball_of_baseR_lt hx
  obtain ⟨G, hGc, hev⟩ := hd.eventually_bdry_eq hE hρ hK hF
  exact ((hGc.sub continuousAt_const).congr (hev.mono fun y hy => hy.symm)).continuousWithinAt

/-- The boundary correspondence at an untouched point left of the base. -/
theorem PairData.IsMeasGood.bdry_spec_lt (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x : ℝ}
    (hx : x < d.baseL ω) :
    Tendsto (d.fwd ω) (𝓝[d.D ω] (x : ℂ)) (𝓝 (d.bdry ω x : ℂ)) ∧ d.inv ω (d.bdry ω x) = x ∧
      ∀ w' ∈ Hbar, d.inv ω w' = x → w' = d.bdry ω x := by
  obtain ⟨ρ, hρ, hK, hF⟩ := hd.exists_ball_of_lt_baseL hx
  exact hd.bdry_spec hE (fun h => Set.disjoint_left.1 hK (mem_ball_self hρ) h)
    (PairData.mem_closure_D_of_disjoint hρ hF)

/-- The boundary correspondence at an untouched point right of the base. -/
theorem PairData.IsMeasGood.bdry_spec_gt (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x : ℝ}
    (hx : d.baseR ω < x) :
    Tendsto (d.fwd ω) (𝓝[d.D ω] (x : ℂ)) (𝓝 (d.bdry ω x : ℂ)) ∧ d.inv ω (d.bdry ω x) = x ∧
      ∀ w' ∈ Hbar, d.inv ω w' = x → w' = d.bdry ω x := by
  obtain ⟨ρ, hρ, hK, hF⟩ := hd.exists_ball_of_baseR_lt hx
  exact hd.bdry_spec hE (fun h => Set.disjoint_left.1 hK (mem_ball_self hρ) h)
    (PairData.mem_closure_D_of_disjoint hρ hF)

omit [MeasurableSpace Ω] in
/-- `|ℓ(x) − x| ≤ M` at untouched accessible points. -/
theorem PairData.abs_bdry_sub_le {ω : Ω} {M : ℝ}
    (hM : ∀ w ∈ Hbar, ‖d.inv ω w - w‖ ≤ M) {x : ℝ} (hψ : d.inv ω (d.bdry ω x) = x) :
    |d.bdry ω x - x| ≤ M := by
  have h := hM (d.bdry ω x) (show (0 : ℝ) ≤ ((d.bdry ω x : ℝ) : ℂ).im by simp)
  rw [hψ, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at h
  exact h

/-- A continuous injective function with bounded displacement is increasing on an interval unbounded below. -/
theorem strictMonoOn_of_injOn_Iio {f : ℝ → ℝ} {a M : ℝ} (hc : ContinuousOn f (Iio a)) (hi : InjOn f (Iio a))
    (hM : ∀ x ∈ Iio a, |f x - x| ≤ M) : StrictMonoOn f (Iio a) := by
  intro x hx y hy hxy
  set z := min x (y - 2 * M - 1) with hz
  have hzx : z ≤ x := min_le_left _ _
  have hzy : z ≤ y := hzx.trans hxy.le
  have hsub : Icc z y ⊆ Iio a := fun t ht => lt_of_le_of_lt ht.2 hy
  rcases (hc.mono hsub).strictMonoOn_of_injOn_Icc' hzy (hi.mono hsub) with h | h
  · exact h ⟨hzx, hxy.le⟩ ⟨hzy, le_rfl⟩ hxy
  · exfalso
    rcases hzy.lt_or_eq with hlt | heq
    · have h1 := h ⟨le_rfl, hzy⟩ ⟨hzy, le_rfl⟩ hlt
      have h2 := abs_le.1 (hM z (hsub ⟨le_rfl, hzy⟩))
      have h3 := abs_le.1 (hM y hy)
      have h4 : z ≤ y - 2 * M - 1 := min_le_right _ _
      linarith [h2.2, h3.1]
    · have h4 : z ≤ y - 2 * M - 1 := min_le_right _ _
      have h3 := abs_le.1 (hM y hy)
      have : 0 ≤ M := (abs_nonneg _).trans (hM y hy)
      linarith

/-- A continuous injective function with bounded displacement is increasing on an interval unbounded above. -/
theorem strictMonoOn_of_injOn_Ioi {f : ℝ → ℝ} {a M : ℝ} (hc : ContinuousOn f (Ioi a)) (hi : InjOn f (Ioi a))
    (hM : ∀ x ∈ Ioi a, |f x - x| ≤ M) : StrictMonoOn f (Ioi a) := by
  intro x hx y hy hxy
  set z := max y (x + 2 * M + 1) with hz
  have hyz : y ≤ z := le_max_left _ _
  have hxz : x ≤ z := hxy.le.trans hyz
  have hsub : Icc x z ⊆ Ioi a := fun t ht => lt_of_lt_of_le hx ht.1
  rcases (hc.mono hsub).strictMonoOn_of_injOn_Icc' hxz (hi.mono hsub) with h | h
  · exact h ⟨le_rfl, hxz⟩ ⟨hxy.le, hyz⟩ hxy
  · exfalso
    have h4 : x + 2 * M + 1 ≤ z := le_max_right _ _
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
    have hxz' : x < z := by linarith
    have h1 := h ⟨le_rfl, hxz⟩ ⟨hxz, le_rfl⟩ hxz'
    have h2 := abs_le.1 (hM z (hsub ⟨hxz, le_rfl⟩))
    have h3 := abs_le.1 (hM x hx)
    linarith [h2.1, h3.2]

/-- **The boundary correspondence is increasing on `(−∞, a)`.** -/
theorem PairData.IsMeasGood.strictMonoOn_bdry_Iio (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    StrictMonoOn (d.bdry ω) (Iio (d.baseL ω)) := by
  obtain ⟨M, hM⟩ := hd.exists_inv_sub_le hE
  refine strictMonoOn_of_injOn_Iio (hd.continuousOn_bdry_Iio hE) (fun x hx y hy hxy => ?_)
    (fun x hx => PairData.abs_bdry_sub_le hM (hd.bdry_spec_lt hE hx).2.1)
  have h1 := (hd.bdry_spec_lt hE hx).2.1
  rw [hxy, (hd.bdry_spec_lt hE hy).2.1] at h1
  exact_mod_cast h1.symm

/-- **The boundary correspondence is increasing on `(b, ∞)`.** -/
theorem PairData.IsMeasGood.strictMonoOn_bdry_Ioi (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    StrictMonoOn (d.bdry ω) (Ioi (d.baseR ω)) := by
  obtain ⟨M, hM⟩ := hd.exists_inv_sub_le hE
  refine strictMonoOn_of_injOn_Ioi (hd.continuousOn_bdry_Ioi hE) (fun x hx y hy hxy => ?_)
    (fun x hx => PairData.abs_bdry_sub_le hM (hd.bdry_spec_gt hE hx).2.1)
  have h1 := (hd.bdry_spec_gt hE hx).2.1
  rw [hxy, (hd.bdry_spec_gt hE hy).2.1] at h1
  exact_mod_cast h1.symm

/-- **The left extreme chart position** `L = sup ℓ(−∞, a)` (the prime end of the left end `a` of the base). -/
def PairData.wordL (d : PairData Ω) (ω : Ω) : ℝ := sSup (d.bdry ω '' Iio (d.baseL ω))

/-- **The right extreme chart position** `R = inf ℓ(b, ∞)`. -/
def PairData.wordR (d : PairData Ω) (ω : Ω) : ℝ := sInf (d.bdry ω '' Ioi (d.baseR ω))

theorem PairData.IsMeasGood.bddAbove_bdry_Iio (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    BddAbove (d.bdry ω '' Iio (d.baseL ω)) := by
  obtain ⟨M, hM⟩ := hd.exists_inv_sub_le hE
  refine ⟨d.baseL ω + M, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := abs_le.1 (PairData.abs_bdry_sub_le hM (hd.bdry_spec_lt hE hx).2.1)
  have hx' : x < d.baseL ω := hx
  linarith

theorem PairData.IsMeasGood.bddBelow_bdry_Ioi (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    BddBelow (d.bdry ω '' Ioi (d.baseR ω)) := by
  obtain ⟨M, hM⟩ := hd.exists_inv_sub_le hE
  refine ⟨d.baseR ω - M, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := abs_le.1 (PairData.abs_bdry_sub_le hM (hd.bdry_spec_gt hE hx).2.1)
  have hx' : d.baseR ω < x := hx
  linarith

theorem PairData.IsMeasGood.bdry_lt_wordL (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x : ℝ}
    (hx : x < d.baseL ω) : d.bdry ω x < d.wordL ω := by
  have hx' : (x + d.baseL ω) / 2 < d.baseL ω := by linarith
  calc d.bdry ω x < d.bdry ω ((x + d.baseL ω) / 2) :=
        hd.strictMonoOn_bdry_Iio hE hx hx' (by linarith)
    _ ≤ d.wordL ω := le_csSup (hd.bddAbove_bdry_Iio hE) ⟨_, hx', rfl⟩

theorem PairData.IsMeasGood.wordR_lt_bdry (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x : ℝ}
    (hx : d.baseR ω < x) : d.wordR ω < d.bdry ω x := by
  have hx' : d.baseR ω < (x + d.baseR ω) / 2 := by linarith
  calc d.wordR ω ≤ d.bdry ω ((x + d.baseR ω) / 2) := csInf_le (hd.bddBelow_bdry_Ioi hE) ⟨_, hx', rfl⟩
    _ < d.bdry ω x := hd.strictMonoOn_bdry_Ioi hE hx' hx (by linarith)

/-- **Every chart point left of `L` is the image of an untouched point left of the base.** -/
theorem PairData.IsMeasGood.exists_bdry_eq_of_lt_wordL (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {w : ℝ}
    (hw : w < d.wordL ω) : ∃ x < d.baseL ω, d.bdry ω x = w := by
  obtain ⟨M, hM⟩ := hd.exists_inv_sub_le hE
  have hne : (d.bdry ω '' Iio (d.baseL ω)).Nonempty := ⟨_, ⟨d.baseL ω - 1, by simp, rfl⟩⟩
  obtain ⟨_, ⟨x₂, hx₂, rfl⟩, hw₂⟩ := exists_lt_of_lt_csSup hne hw
  set x₁ := min (d.baseL ω - 1) (w - M - 1) with hx₁
  have hx₁L : x₁ < d.baseL ω := (min_le_left _ _).trans_lt (by linarith)
  have h₁ : d.bdry ω x₁ < w := by
    have := abs_le.1 (PairData.abs_bdry_sub_le hM (hd.bdry_spec_lt hE hx₁L).2.1)
    have : x₁ ≤ w - M - 1 := min_le_right _ _
    linarith
  have hpre : IsPreconnected (d.bdry ω '' Iio (d.baseL ω)) :=
    isPreconnected_Iio.image _ (hd.continuousOn_bdry_Iio hE)
  obtain ⟨x, hx, hxw⟩ := hpre.Icc_subset ⟨x₁, hx₁L, rfl⟩ ⟨x₂, hx₂, rfl⟩ ⟨h₁.le, hw₂.le⟩
  exact ⟨x, hx, hxw⟩

/-- **Every chart point right of `R` is the image of an untouched point right of the base.** -/
theorem PairData.IsMeasGood.exists_bdry_eq_of_wordR_lt (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {w : ℝ}
    (hw : d.wordR ω < w) : ∃ x > d.baseR ω, d.bdry ω x = w := by
  obtain ⟨M, hM⟩ := hd.exists_inv_sub_le hE
  have hne : (d.bdry ω '' Ioi (d.baseR ω)).Nonempty := ⟨_, ⟨d.baseR ω + 1, by simp, rfl⟩⟩
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, hw₁⟩ := exists_lt_of_csInf_lt hne hw
  set x₂ := max (d.baseR ω + 1) (w + M + 1) with hx₂
  have hx₂R : d.baseR ω < x₂ := (by linarith : d.baseR ω < d.baseR ω + 1).trans_le (le_max_left _ _)
  have h₂ : w < d.bdry ω x₂ := by
    have := abs_le.1 (PairData.abs_bdry_sub_le hM (hd.bdry_spec_gt hE hx₂R).2.1)
    have : w + M + 1 ≤ x₂ := le_max_right _ _
    linarith
  have hpre : IsPreconnected (d.bdry ω '' Ioi (d.baseR ω)) :=
    isPreconnected_Ioi.image _ (hd.continuousOn_bdry_Ioi hE)
  obtain ⟨x, hx, hxw⟩ := hpre.Icc_subset ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂R, rfl⟩ ⟨hw₁.le, h₂.le⟩
  exact ⟨x, hx, hxw⟩

/-- The chart inverse sends `0` into `K` (to the contact point). -/
theorem PairData.IsMeasGood.inv_zero_mem_K (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : d.inv ω 0 ∈ d.K ω := by
  rw [(hd.isFirstContactChart hE).2.2.2.2.2.2.2.2.2.1, K_of_mem hE]
  exact Or.inl ⟨d.s₀ ω, ⟨zero_le, le_rfl⟩, rfl⟩

theorem PairData.IsMeasGood.wordL_nonpos (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : d.wordL ω ≤ 0 := by
  by_contra h
  obtain ⟨x, hx, hx0⟩ := hd.exists_bdry_eq_of_lt_wordL hE (not_le.1 h)
  have h1 := (hd.bdry_spec_lt hE hx).2.1
  rw [hx0] at h1
  obtain ⟨ρ, hρ, hK, -⟩ := hd.exists_ball_of_lt_baseL hx
  have := hd.inv_zero_mem_K hE
  rw [show ((0 : ℝ) : ℂ) = 0 by simp] at h1
  rw [h1] at this
  exact Set.disjoint_left.1 hK (mem_ball_self hρ) this

theorem PairData.IsMeasGood.wordR_nonneg (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : 0 ≤ d.wordR ω := by
  by_contra h
  obtain ⟨x, hx, hx0⟩ := hd.exists_bdry_eq_of_wordR_lt hE (not_le.1 h)
  have h1 := (hd.bdry_spec_gt hE hx).2.1
  rw [hx0] at h1
  obtain ⟨ρ, hρ, hK, -⟩ := hd.exists_ball_of_baseR_lt hx
  have := hd.inv_zero_mem_K hE
  rw [show ((0 : ℝ) : ℂ) = 0 by simp] at h1
  rw [h1] at this
  exact Set.disjoint_left.1 hK (mem_ball_self hρ) this

/-- **The chart inverse sends `[L, R]` into `K`** (the exposed sides of the two prefixes). -/
theorem PairData.IsMeasGood.inv_mem_K_of_mem_Icc (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {w : ℝ}
    (h1 : d.wordL ω ≤ w) (h2 : w ≤ d.wordR ω) : d.inv ω w ∈ d.K ω := by
  rcases hd.inv_mem_K_or hE w with h | ⟨hre, hK, hcl⟩
  · exact h
  exfalso
  set x : ℝ := (d.inv ω w).re with hxdef
  have hx : d.inv ω w = (x : ℂ) := (ofReal_re_eq hre).symm
  have hwH : (w : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (w : ℂ).im by simp
  rw [hx] at hK hcl
  rcases lt_trichotomy x (d.baseL ω) with hxa | hxa | hxa
  · have := (hd.bdry_spec_lt hE hxa).2.2 _ hwH hx
    have h3 := hd.bdry_lt_wordL hE hxa
    have h' : w = d.bdry ω x := by exact_mod_cast this
    rw [← h'] at h3
    exact (not_le.2 h3) h1
  · exact hK (hxa ▸ hd.baseL_mem hE)
  rcases lt_trichotomy x (d.baseR ω) with hxb | hxb | hxb
  · exact hd.notMem_closure_D_of_mem_Ioo hE hxa hxb hK hcl
  · exact hK (hxb ▸ hd.baseR_mem hE)
  · have := (hd.bdry_spec_gt hE hxb).2.2 _ hwH hx
    have h3 := hd.wordR_lt_bdry hE hxb
    have h' : w = d.bdry ω x := by exact_mod_cast this
    rw [← h'] at h3
    exact (not_le.2 h3) h2

/-- **Left of `L` the chart inverse is the inverse of the boundary correspondence.** -/
theorem PairData.IsMeasGood.inv_of_lt_wordL (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {w : ℝ}
    (hw : w < d.wordL ω) : ((d.inv ω w).re < d.baseL ω) ∧ d.inv ω w = ((d.inv ω w).re : ℂ) ∧
      d.bdry ω (d.inv ω w).re = w := by
  obtain ⟨x, hx, rfl⟩ := hd.exists_bdry_eq_of_lt_wordL hE hw
  rw [(hd.bdry_spec_lt hE hx).2.1]
  simp only [ofReal_re]
  exact ⟨hx, by simp, by simp⟩

/-- **Right of `R` the chart inverse is the inverse of the boundary correspondence.** -/
theorem PairData.IsMeasGood.inv_of_wordR_lt (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {w : ℝ}
    (hw : d.wordR ω < w) : (d.baseR ω < (d.inv ω w).re) ∧ d.inv ω w = ((d.inv ω w).re : ℂ) ∧
      d.bdry ω (d.inv ω w).re = w := by
  obtain ⟨x, hx, rfl⟩ := hd.exists_bdry_eq_of_wordR_lt hE hw
  rw [(hd.bdry_spec_gt hE hx).2.1]
  simp only [ofReal_re]
  exact ⟨hx, by simp, by simp⟩

end Geom

end Restart

end InteractingSLE
