/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3Pull

/-!
# A.2, part 3: the image-chart accumulation from a noncollision dichotomy and the contact geometry

Packet PROVE-ZHAN-A2P3. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L563–L594; R38, R53).

Condition on the small prefix at a deterministic time `q > 0`. In the chart of the conditional image law (relative to
the image source `src = g_q(0)`) the large curve is a local evolution, up to the image `ζ'` of its contact time, of
the image word with left marks (nearest first) `a₀ = g_q(x)`, …, the small tip `w = W₁(q)` and the seeds; the weights
are `largeG3ImgRhoL κ = [κ − 4, 2 − κ/2, −κ/2, κ − 6]` (marks `x`, `y⁺`, `w`, `y⁻`) and `largeEightImgRhoL κ =
[(κ − 4)/2, −κ/2, 2]` (marks `x⁺`, `w`, `x⁻`). Let `U` be the union of the image hulls before `ζ'`.

The source's argument (L563–L594) has two halves, stated here as two named propositions:

* **(I1) the retargeted noncollision dichotomy** (`ImageDichotomyG3Statement`, `ImageDichotomyEightStatement`; a
  statement about local evolutions of the image word only): retarget `w` to `∞` by
  `R(u) = 1/(x₂′ − w) − 1/(u − w)`; the retargeted word has all side partial sums `≥ κ/2 − 2` (left `x`, `y⁺`; right the
  old target `R(∞)` and `y⁻`, L574–L584, checked in `OuterBoundary.fourForce_*`), so by high-force noncollision the
  retargeted process never collides at a finite retargeted time. Pulled back: either the retargeted capacity at `ζ'` is
  infinite, and then (a hull in a disc has bounded capacity, L591–L593) `w` lies in the closure of `U`; or it is finite,
  and then `U` is bounded (`R(∞)` is protected) and its closure misses the real half-line `(−∞, a₀]` (the left
  protected marks and the two old-slit rays `(−∞, R(d₁)]`, `[R(c₁), ∞)` lie beyond protected marks, L586–L588).
* **(I2) the contact geometry** (`PairContactG3Statement`, `PairContactEightStatement`; a statement about the dual
  pair only, with `A = g_q(large hulls before contact)`, which equals the physical image hulls before `ζ'` by
  `iUnion_physHull_eq_of_imageChain`): the image process is maximal up to contact (L564–L571). At the contact time
  the large curve either meets the closed small hull — its image meets the old-hull interval `[c₁, d₁] ⊂ (−∞, a₀]` —
  or swallows the small hull wholesale — its image meets `(−∞, c₁)` — or swallows its mark `x` at the end of its strip
  life — its image meets `(−∞, a₀]`; if there is no contact the large hulls, hence their images (`g_q` moves points a
  bounded amount), are unbounded. So almost surely `w ∈ closure A`, or `A` is unbounded, or `closure A` meets
  `(−∞, a₀]`.

Together they give `LargeAccum…Statement` of `A2Part3Pull` (**`largeAccumG3Statement_of_split`**,
**`largeAccumEightStatement_of_split`**), hence A.2's part 3 (**`smallInHullG3Statement_of_split`**,
**`smallInHullEightStatement_of_split`**).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-! ### The image hulls in relative coordinates -/

/-- The union of the hulls of the centred driver `w` before `ζ`. -/
def imgHulls (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Set ℂ :=
  ⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ), fwdHull (Strip.extPath w) t

theorem iUnion_physHull_eq (src : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ), physHull src (Strip.extPath w) t) =
      (fun z : ℂ => z + src) '' imgHulls w ζ := by
  ext z
  simp only [imgHulls, physHull, mem_iUnion, mem_image]
  constructor
  · rintro ⟨t, ht, a, ha, rfl⟩
    exact ⟨a, ⟨t, ht, ha⟩, rfl⟩
  · rintro ⟨a, ⟨t, ht, ha⟩, rfl⟩
    exact ⟨t, ht, a, ha, rfl⟩

theorem mem_closure_image_add_iff {U : Set ℂ} {z c : ℂ} :
    z + c ∈ closure ((fun z : ℂ => z + c) '' U) ↔ z ∈ closure U := by
  have h := (Homeomorph.addRight c).image_closure U
  have hf : ⇑(Homeomorph.addRight c) = fun z : ℂ => z + c := rfl
  rw [hf] at h
  rw [← h]
  exact (add_left_injective c).mem_set_image

theorem isBounded_image_add {U : Set ℂ} (hU : IsBounded U) (c : ℂ) :
    IsBounded ((fun z : ℂ => z + c) '' U) := by
  obtain ⟨r, hr⟩ := hU.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := c) (r := r)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  have h := hr hz
  simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h ⊢
  simpa using h

/-- The `g_q`-images of the large hulls before contact (the set `A` of (I2)): the small curve starts at `x₁` with
driver `w₁`, the large curve at `0` with driver `w₂`, inner mark `v₂` and lifetime `ζ₂`. -/
def preContactImage (x₁ : ℝ) (w₁ w₂ v₂ : ℝ≥0 → ℝ) (ζ₂ : ℝ≥0∞) (q : ℝ≥0) : Set ℂ :=
  physMap x₁ (Strip.extPath w₁) q ''
    preContactHulls (Strip.extPath w₂) (contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂) x₁ (Strip.extPath w₁) q)

/-- **Pathwise combination of the two halves.** With `U` the image hulls (relative coordinates), `w` the tip mark and
`a₀` the protected mark: the dichotomy (I1) and the contact trichotomy (I2) (in physical coordinates, `src` the image
source) give the accumulation at the physical tip image `w + src`. -/
theorem mem_closure_of_dichotomy_of_contact {U : Set ℂ} {w a₀ src : ℝ}
    (h1 : (w : ℂ) ∈ closure U ∨ (IsBounded U ∧ ∀ u : ℝ, u ≤ a₀ → (u : ℂ) ∉ closure U))
    (h2 : ((w + src : ℝ) : ℂ) ∈ closure ((fun z : ℂ => z + src) '' U) ∨
      ¬ IsBounded ((fun z : ℂ => z + src) '' U) ∨
      ∃ u : ℝ, u ≤ a₀ + src ∧ (u : ℂ) ∈ closure ((fun z : ℂ => z + src) '' U)) :
    ((w + src : ℝ) : ℂ) ∈ closure ((fun z : ℂ => z + src) '' U) := by
  rcases h1 with hw | ⟨hb, hav⟩
  · rw [ofReal_add, mem_closure_image_add_iff]
    exact hw
  · rcases h2 with hw | hnb | ⟨u, hu, huc⟩
    · exact hw
    · exact absurd (isBounded_image_add hb _) hnb
    · refine absurd ?_ (hav (u - src) (by linarith))
      rw [← mem_closure_image_add_iff (c := (src : ℂ))]
      simpa using huc

/-! ### The nearest image mark is strictly left of the image source -/

/-- **The outer right mark stays strictly right of the driver, and the right marks keep a strict order** before the
lifetime, when the whole right word has total weight `≤ −2` (a collision of the outer mark with the driver would
put every right mark on the driver, which is the threshold): for `xR i < xR j`, `j` the outer mark, `vR i t < vR j t`
for every `t < ζ`. -/
theorem vR_lt_vR_outer {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hsum : ∑ k, ρR k ≤ -2) {i j : Fin nR}
    (hj : ∀ k, k ≤ j) (hij : xR i < xR j) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR i t < vR j t := by
  have hf := hp.isForcePath
  have hout : ∀ r ≤ t, w r < vR j r := by
    intro r hr
    have hrζ : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hr) ht
    refine lt_of_le_of_ne (hf.w_le_vR hrζ j) fun heq => hf.not_threshold hrζ (Or.inr ?_)
    have hall : ∀ k, vR k r = w r := fun k =>
      le_antisymm ((hf.monotone_vR hrζ (hj k)).trans heq.symm.le) (hf.w_le_vR hrζ k)
    have hfilt : Finset.univ.filter (fun k => vR k r = w r) = Finset.univ :=
      Finset.filter_true_of_mem fun k _ => hall k
    simpa [hfilt] using hsum
  have h := hf.reflect.vL_lt_vL_of_lt ht (i := i) (j := j) (by simpa using hij)
    (fun r hr => by simpa using hout r hr)
  simpa using h

/-- (G3) The image of `x` is strictly left of the image of `0` (`VR₁ 1 < VR₁ 2`) before the small lifetime. -/
theorem smallG3_vR_one_lt_two {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {y x : ℝ} (hx : x < 0) {w : ℝ≥0 → ℝ}
    {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 3 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR 1 t < vR 2 t := by
  refine vR_lt_vR_outer hp ?_ (fun k => by fin_cases k <;> decide) (by simp; linarith) ht
  rw [Fin.sum_univ_three]
  exact (smallG3_prefix hκ4 hκ8).2.2.2.le

/-- (Eight) The image of `x⁺` is strictly left of the image of `0` (`VR₁ 0 < VR₁ 1`) before the small lifetime. -/
theorem smallEight_vR_zero_lt_one {κ : ℝ} (hκ8 : 8 ≤ κ) {x : ℝ} (hx : x < 0) {w : ℝ≥0 → ℝ}
    {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR 0 t < vR 1 t := by
  refine vR_lt_vR_outer hp ?_ (fun k => by fin_cases k <;> decide) (by simp; linarith) ht
  rw [Fin.sum_univ_two]
  exact (smallEight_prefix hκ8).2.2.le

/-! ### (I1): the retargeted noncollision dichotomy -/

/-- **(I1), (G3)** (L572–L594): for `4 < κ < 8`, every local evolution, up to a random time `ζ'`, of an initially
measurable random word `ΘL` with the weights `largeG3ImgRhoL κ` (marks `x`, `y⁺`, the small tip `w`, `y⁻`, nearest
first; no right marks) whose nearest mark is almost surely strictly left of the source on the live event satisfies
almost surely on the live event: the tip mark `ΘL 2` lies in the closure of the hulls
before `ζ'`, or these hulls are bounded and their closure misses the real half-line `(−∞, ΘL 0]`. -/
def ImageDichotomyG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 →
    ∀ {Ω : Type u} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Set Ω) (ΘL : Ω → Fin 4 → ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin 4 → ℝ≥0 → Ω → ℝ) (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P 𝓔 F ΘL (fun _ => ![]) (largeG3ImgRhoL κ) ![] 𝓖 W' VL' VR'
          B' ζ' → (∀ᵐ ω ∂P, ω ∈ F → ΘL ω 0 < 0) →
        ∀ᵐ ω ∂P, ω ∈ F → ((ΘL ω 2 : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
          (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧
            ∀ u : ℝ, u ≤ ΘL ω 0 → (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))))

/-- **(I1), (Eight)** (L572–L594, three-force version L603–L605): for `κ ≥ 8`, the same with the weights
`largeEightImgRhoL κ` (marks `x⁺`, the small tip `w`, `x⁻`), nearest mark strictly left of the source: almost
surely on the live event, `ΘL 1` lies in the
closure of the hulls before `ζ'`, or these are bounded and their closure misses `(−∞, ΘL 0]`. -/
def ImageDichotomyEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ →
    ∀ {Ω : Type u} (𝓔 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Set Ω) (ΘL : Ω → Fin 3 → ℝ) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin 3 → ℝ≥0 → Ω → ℝ) (VR' : Fin 0 → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      Restart.StoppedK2.IsRandomWordEvolutionUpTo κ P 𝓔 F ΘL (fun _ => ![]) (largeEightImgRhoL κ) ![] 𝓖 W' VL' VR'
          B' ζ' → (∀ᵐ ω ∂P, ω ∈ F → ΘL ω 0 < 0) →
        ∀ᵐ ω ∂P, ω ∈ F → ((ΘL ω 1 : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
          (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧
            ∀ u : ℝ, u ≤ ΘL ω 0 → (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))))

/-! ### (I2): the contact geometry -/

/-- **(I2), (G3)** (L564–L571): for every (G3) dual pair and every deterministic time `q > 0`, almost surely on
`{q < ζ₁}`, the `g_q`-images `A` of the large hulls before contact (the hulls before the first meeting of their
closure with the closed small hull, capped by the end of the large strip life) accumulate at the small tip image
`y + W₁(q)`, or are unbounded, or their closure meets the real half-line `(−∞, y + VR₁ 1 q]` (left of the image `g_q(x)`
of the mark `x`). -/
def PairContactG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
          (y : ℂ) + (W₁ q ω : ℂ) ∈ closure (preContactImage y (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q) ∨
            ¬ IsBounded (preContactImage y (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q) ∨
            ∃ u : ℝ, u ≤ y + VR₁ 1 q ω ∧
              (u : ℂ) ∈ closure (preContactImage y (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q)

/-- **(I2), (Eight)** (L564–L571): the same for the (Eight) dual pair (small tip image `x + W₁(q)`, protected
half-line `(−∞, x + VR₁ 0 q]`, left of the image `g_q(x⁺)`). -/
def PairContactEightStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
      (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
      (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
        ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ₁ ω →
          (x : ℂ) + (W₁ q ω : ℂ) ∈ closure (preContactImage x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q) ∨
            ¬ IsBounded (preContactImage x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q) ∨
            ∃ u : ℝ, u ≤ x + VR₁ 0 q ω ∧
              (u : ℂ) ∈ closure (preContactImage x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q)

/-! ### The combination -/

/-- **Pathwise combination.** If the image hulls `U'` (physical, source `src`) of the image chain are `(·+src)`-images
of `U` and `g_q`-images of the large hulls before contact, then (I1) for `U` and (I2) for `A = U'` give the
accumulation of `A` at the physical tip image `w + src`. -/
theorem mem_closure_of_dichotomy_of_pair {U A : Set ℂ} {w a₀ src : ℝ}
    (hA : A = (fun z : ℂ => z + src) '' U)
    (h1 : (w : ℂ) ∈ closure U ∨ (IsBounded U ∧ ∀ u : ℝ, u ≤ a₀ → (u : ℂ) ∉ closure U))
    (h2 : ((w + src : ℝ) : ℂ) ∈ closure A ∨ ¬ IsBounded A ∨ ∃ u : ℝ, u ≤ a₀ + src ∧ (u : ℂ) ∈ closure A) :
    ((w + src : ℝ) : ℂ) ∈ closure A := by
  subst hA
  exact mem_closure_of_dichotomy_of_contact h1 h2

/-- **The large-hull accumulation, (G3)**, from (I1) and (I2). -/
theorem largeAccumG3Statement_of_split {κ : ℝ} (hD : ImageDichotomyG3Statement.{u} κ)
    (hC : PairContactG3Statement.{u} κ) : LargeAccumG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hE, hch⟩ := hpair.2.2.2 (fun _ => q) (isStoppingTime_const 𝓕₁ q)
  have hneg : ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) < ζ₁ ω} →
      (![VR₁ 1 q ω - VR₁ 2 q ω, VR₁ 0 q ω - VR₁ 2 q ω, W₁ q ω - VR₁ 2 q ω, VL₁ 0 q ω - VR₁ 2 q ω] : Fin 4 → ℝ) 0
        < 0 := by
    filter_upwards [hpair.2.1.2.2.2.2] with ω hp hq
    simpa using smallG3_vR_one_lt_two hκ4 hκ8 hx hp hq
  filter_upwards [hD hκ4 hκ8 _ P _ _ 𝓖 W' VL' VR' B' ζ' hE hneg, hch,
    hC hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0] with ω h1 hc h2 hq
  have h1' : ((W₁ q ω - VR₁ 2 q ω : ℝ) : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
      (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧ ∀ u : ℝ, u ≤ VR₁ 1 q ω - VR₁ 2 q ω →
        (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))) := h1 hq
  have hA : preContactImage y (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q =
      (fun z : ℂ => z + (y + VR₁ 2 q ω : ℝ)) '' imgHulls (W' · ω) (ζ' ω) := by
    rw [← iUnion_physHull_eq, iUnion_physHull_eq_of_imageChain (hc hq)]
    rfl
  have he1 : ((W₁ q ω - VR₁ 2 q ω) + (y + VR₁ 2 q ω) : ℝ) = y + W₁ q ω := by ring
  have he2 : (VR₁ 1 q ω - VR₁ 2 q ω) + (y + VR₁ 2 q ω) = y + VR₁ 1 q ω := by ring
  have h := mem_closure_of_dichotomy_of_pair hA h1' (by rw [he1, he2, ofReal_add]; exact h2 hq)
  rw [he1, ofReal_add] at h
  exact h

/-- **The large-hull accumulation, (Eight)**, from (I1) and (I2). -/
theorem largeAccumEightStatement_of_split {κ : ℝ} (hD : ImageDichotomyEightStatement.{u} κ)
    (hC : PairContactEightStatement.{u} κ) : LargeAccumEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hE, hch⟩ := hpair.2.2.2 (fun _ => q) (isStoppingTime_const 𝓕₁ q)
  have hneg : ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) < ζ₁ ω} →
      (![VR₁ 0 q ω - VR₁ 1 q ω, W₁ q ω - VR₁ 1 q ω, VL₁ 0 q ω - VR₁ 1 q ω] : Fin 3 → ℝ) 0 < 0 := by
    filter_upwards [hpair.2.1.2.2.2.2] with ω hp hq
    simpa using smallEight_vR_zero_lt_one hκ8 hx hp hq
  filter_upwards [hD hκ8 _ P _ _ 𝓖 W' VL' VR' B' ζ' hE hneg, hch,
    hC hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0] with ω h1 hc h2 hq
  have h1' : ((W₁ q ω - VR₁ 1 q ω : ℝ) : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
      (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧ ∀ u : ℝ, u ≤ VR₁ 0 q ω - VR₁ 1 q ω →
        (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))) := h1 hq
  have hA : preContactImage x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q =
      (fun z : ℂ => z + (x + VR₁ 1 q ω : ℝ)) '' imgHulls (W' · ω) (ζ' ω) := by
    rw [← iUnion_physHull_eq, iUnion_physHull_eq_of_imageChain (hc hq)]
    rfl
  have he1 : ((W₁ q ω - VR₁ 1 q ω) + (x + VR₁ 1 q ω) : ℝ) = x + W₁ q ω := by ring
  have he2 : (VR₁ 0 q ω - VR₁ 1 q ω) + (x + VR₁ 1 q ω) = x + VR₁ 0 q ω := by ring
  have h := mem_closure_of_dichotomy_of_pair hA h1' (by rw [he1, he2, ofReal_add]; exact h2 hq)
  rw [he1, ofReal_add] at h
  exact h

/-- **A.2, part 3, (G3)** (`A2SmallInHullG3Statement`) from (I1) and (I2). -/
theorem smallInHullG3Statement_of_split {κ : ℝ} (hD : ImageDichotomyG3Statement.{u} κ)
    (hC : PairContactG3Statement.{u} κ) : A2SmallInHullG3Statement.{u} κ :=
  smallInHullG3Statement_of_tip (tipInHullG3Statement_of_largeAccum (largeAccumG3Statement_of_split hD hC))

/-- **A.2, part 3, (Eight)** (`A2SmallInHullEightStatement`) from (I1) and (I2). -/
theorem smallInHullEightStatement_of_split {κ : ℝ} (hD : ImageDichotomyEightStatement.{u} κ)
    (hC : PairContactEightStatement.{u} κ) : A2SmallInHullEightStatement.{u} κ :=
  smallInHullEightStatement_of_tip (tipInHullEightStatement_of_largeAccum (largeAccumEightStatement_of_split hD hC))

end InteractingSLE.ZhanGT4.A2X.P3
