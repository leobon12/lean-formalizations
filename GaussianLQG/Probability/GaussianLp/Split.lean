import GaussianLQG.Probability.GaussianLp.Basic

/-!
# Splitting `ℝ^ℕ` into the first `n` coordinates and the rest

Blueprint Proposition `prop:gaussian-Lp`, steps "Projection to `n` coordinates" and "Limit".
Write `ω = (x, y)` with `x = (ω₀, …, ω_{n-1}) ∈ ℝⁿ`; then `P = γₙ ⊗ P` for the product Gaussian
measure `P = stdP` on `ℝ^ℕ`.

* `headN`, `tailN`, `joinN`: the splitting `ℝ^ℕ ≃ ℝⁿ × ℝ^ℕ` and `splitEquiv`.
* `measurePreserving_joinN`, `measurePreserving_splitEquiv`, `measurePreserving_headN`:
  `stdP = (γₙ ⊗ stdP) ∘ joinN⁻¹` (checked on measurable boxes, `Measure.eq_infinitePi`).
* `headFiltration`: the filtration `σ(ω₀, …, ω_{n-1})`; its supremum contains the product
  σ-algebra (`measurable_iSup_headFiltration`).
* `condExp_headFiltration`: `E[F | ω₀, …, ω_{n-1}] = ∫ F(x, y) dP(y)` at `x = headN n ω`.
* `tendsto_ae_integral_joinN`: **Lévy's upward theorem** for this filtration: for integrable `F`,
  `∫ F(headN n ω, y) dP(y) → F(ω)` for `P`-a.e. `ω`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

namespace GaussLp

/-! ### The splitting maps -/

/-- The first `n` coordinates `(ω₀, …, ω_{n-1})`. -/
def headN (n : ℕ) (ω : Coord) : Fin n → ℝ := fun i => ω i

/-- The remaining coordinates `(ω_n, ω_{n+1}, …)`, reindexed from `0`. -/
def tailN (n : ℕ) (ω : Coord) : Coord := fun k => ω (n + k)

/-- The concatenation of `x ∈ ℝⁿ` and `y ∈ ℝ^ℕ`. -/
def joinN (n : ℕ) (x : Fin n → ℝ) (y : Coord) : Coord :=
  fun i => if h : i < n then x ⟨i, h⟩ else y (i - n)

variable (n : ℕ)

lemma joinN_apply_of_lt (x : Fin n → ℝ) (y : Coord) {i : ℕ} (h : i < n) :
    joinN n x y i = x ⟨i, h⟩ := by
  simp [joinN, h]

lemma joinN_apply_of_le (x : Fin n → ℝ) (y : Coord) {i : ℕ} (h : n ≤ i) :
    joinN n x y i = y (i - n) := by
  simp [joinN, not_lt.2 h]

@[simp] lemma headN_joinN (x : Fin n → ℝ) (y : Coord) : headN n (joinN n x y) = x := by
  funext i
  simp [headN, joinN, i.isLt]

@[simp] lemma tailN_joinN (x : Fin n → ℝ) (y : Coord) : tailN n (joinN n x y) = y := by
  funext k
  simp [tailN, joinN]

@[simp] lemma joinN_headN_tailN (ω : Coord) : joinN n (headN n ω) (tailN n ω) = ω := by
  funext i
  by_cases h : i < n
  · simp [joinN, h, headN]
  · simp only [joinN, h, dite_false, tailN]
    congr 1
    omega

lemma measurable_headN : Measurable (headN n) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_tailN : Measurable (tailN n) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_joinN : Measurable fun z : (Fin n → ℝ) × Coord => joinN n z.1 z.2 := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i < n
  · simp only [joinN, h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [joinN, h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The measurable equivalence `ℝ^ℕ ≃ ℝⁿ × ℝ^ℕ`, `ω ↦ (headN n ω, tailN n ω)`. -/
def splitEquiv : Coord ≃ᵐ (Fin n → ℝ) × Coord where
  toFun ω := (headN n ω, tailN n ω)
  invFun z := joinN n z.1 z.2
  left_inv ω := joinN_headN_tailN n ω
  right_inv z := by simp
  measurable_toFun := (measurable_headN n).prodMk (measurable_tailN n)
  measurable_invFun := measurable_joinN n

@[simp] lemma splitEquiv_apply (ω : Coord) : splitEquiv n ω = (headN n ω, tailN n ω) := rfl

@[simp] lemma splitEquiv_symm_apply (z : (Fin n → ℝ) × Coord) :
    (splitEquiv n).symm z = joinN n z.1 z.2 := rfl

/-! ### Measure preservation -/

/-- The preimage of a measurable box under `joinN` is a product set. -/
lemma joinN_preimage_pi (s : Finset ℕ) (t : ℕ → Set ℝ) :
    (fun z : (Fin n → ℝ) × Coord => joinN n z.1 z.2) ⁻¹' (Set.pi ↑s t) =
      (Set.univ.pi fun i : Fin n => if (i : ℕ) ∈ s then t i else Set.univ) ×ˢ
        Set.pi ↑(s.preimage (fun k => n + k) (fun _ _ _ _ h => Nat.add_left_cancel h))
          (fun k => t (n + k)) := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
    true_implies]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · split_ifs with hi
      · have := h i hi
        rwa [joinN_apply_of_lt n x y i.isLt] at this
      · trivial
    · have := h (n + k) (Finset.mem_preimage.1 hk)
      rwa [joinN_apply_of_le n x y (Nat.le_add_right n k), Nat.add_sub_cancel_left] at this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hin : i < n
    · have := h1 ⟨i, hin⟩
      simp only [hi, ↓reduceIte] at this
      rwa [joinN_apply_of_lt n x y hin]
    · have hni : n ≤ i := not_lt.1 hin
      rw [joinN_apply_of_le n x y hni]
      have hk : n + (i - n) ∈ s := by rwa [Nat.add_sub_cancel' hni]
      have := h2 (i - n) (Finset.mem_preimage.2 hk)
      rwa [Nat.add_sub_cancel' hni] at this

/-- `stdP` is the image of `γₙ ⊗ stdP` under `joinN`. -/
theorem map_joinN : ((gaussPi n).prod stdP).map (fun z => joinN n z.1 z.2) = stdP := by
  change _ = Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  set g : ℕ → ℝ≥0∞ := fun i => gaussianReal 0 1 (t i) with hg
  rw [Measure.map_apply (measurable_joinN n) (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    joinN_preimage_pi, Measure.prod_prod, Measure.pi_pi]
  change _ * Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) _ = _
  rw [Measure.infinitePi_pi _ (fun k _ => ht _)]
  -- the first block
  have hA : ∏ i : Fin n, gaussianReal 0 1 (if (i : ℕ) ∈ s then t i else Set.univ) =
      ∏ i ∈ s with i < n, g i := by
    have e1 : ∀ i : Fin n, gaussianReal 0 1 (if (i : ℕ) ∈ s then t i else Set.univ) =
        (fun k : ℕ => if k ∈ s then g k else 1) i := by
      intro i
      by_cases hi : (i : ℕ) ∈ s <;> simp [hi, hg]
    rw [Finset.prod_congr rfl fun i _ => e1 i,
      Fin.prod_univ_eq_prod_range (fun k : ℕ => if k ∈ s then g k else 1) n,
      ← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext k
    simp [and_comm]
  -- the second block
  have hB : ∏ k ∈ s.preimage (fun k => n + k) (fun _ _ _ _ h => Nat.add_left_cancel h),
      gaussianReal 0 1 (t (n + k)) = ∏ i ∈ s with ¬i < n, g i := by
    rw [Finset.prod_filter]
    have e2 : ∀ k : ℕ, gaussianReal 0 1 (t (n + k)) =
        (fun i : ℕ => if ¬i < n then g i else 1) (n + k) := by
      intro k
      simp [hg]
    rw [Finset.prod_congr rfl fun k _ => e2 k]
    refine Finset.prod_preimage (fun k => n + k) s _ (fun i : ℕ => if ¬i < n then g i else 1) ?_
    intro i _ hi
    have hlt : i < n := by
      by_contra h
      exact hi ⟨i - n, by simp only; omega⟩
    simp [hlt]
  rw [hA, hB, Finset.prod_filter_mul_prod_filter_not]

theorem measurePreserving_joinN :
    MeasurePreserving (fun z : (Fin n → ℝ) × Coord => joinN n z.1 z.2) ((gaussPi n).prod stdP)
      stdP :=
  ⟨measurable_joinN n, map_joinN n⟩

theorem measurePreserving_splitEquiv_symm :
    MeasurePreserving (splitEquiv n).symm ((gaussPi n).prod stdP) stdP :=
  measurePreserving_joinN n

theorem measurePreserving_splitEquiv :
    MeasurePreserving (splitEquiv n) stdP ((gaussPi n).prod stdP) := by
  have h := (measurePreserving_splitEquiv_symm n).symm
  rwa [MeasurableEquiv.symm_symm] at h

theorem measurePreserving_headN : MeasurePreserving (headN n) stdP (gaussPi n) :=
  measurePreserving_fst.comp (measurePreserving_splitEquiv n)

lemma measurableEmbedding_joinN :
    MeasurableEmbedding fun z : (Fin n → ℝ) × Coord => joinN n z.1 z.2 :=
  (splitEquiv n).symm.measurableEmbedding

/-- Transport of an almost-sure property of `stdP` to `γₙ ⊗ stdP`. -/
lemma ae_joinN_of_ae {P : Coord → Prop} (h : ∀ᵐ ω ∂stdP, P ω) :
    ∀ᵐ z ∂(gaussPi n).prod stdP, P (joinN n z.1 z.2) :=
  (measurePreserving_joinN n).quasiMeasurePreserving.ae h

/-- Transport of an almost-sure property of `γₙ ⊗ stdP` to `stdP` (measurable property). -/
lemma ae_of_ae_joinN {P : Coord → Prop} (hP : MeasurableSet {ω | P ω})
    (h : ∀ᵐ z ∂(gaussPi n).prod stdP, P (joinN n z.1 z.2)) : ∀ᵐ ω ∂stdP, P ω := by
  rw [← map_joinN n]
  exact (ae_map_iff (measurable_joinN n).aemeasurable hP).2 h

/-! ### The filtration of the first coordinates -/

/-- The filtration `ℱₙ = σ(ω₀, …, ω_{n-1})`. -/
def headFiltration : Filtration ℕ (inferInstance : MeasurableSpace Coord) where
  seq n := MeasurableSpace.comap (headN n) inferInstance
  mono' n m hnm := by
    have h : headN n = (fun x : Fin m → ℝ => fun i : Fin n => x (Fin.castLE hnm i)) ∘ headN m :=
      rfl
    simp only
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Measurable.comap_le (Measurable.of_eval fun _ => measurable_pi_apply _))
  le' n := (measurable_headN n).comap_le

lemma headFiltration_apply : (headFiltration n : MeasurableSpace Coord) =
    MeasurableSpace.comap (headN n) inferInstance := rfl

/-- A measurable function on `ℝ^ℕ` is measurable for `⨆ₙ ℱₙ`. -/
theorem measurable_iSup_headFiltration {F : Coord → ℝ} (hF : Measurable F) :
    Measurable[⨆ n, headFiltration n] F := by
  have hid : @Measurable Coord Coord (⨆ n, headFiltration n) _ id := by
    refine @Measurable.of_eval Coord ℕ (fun _ => ℝ) (⨆ n, headFiltration n) _ id fun i => ?_
    have h1 : Measurable[headFiltration (i + 1)] fun ω : Coord => ω i := by
      have e : (fun ω : Coord => ω i) =
          (fun x : Fin (i + 1) → ℝ => x ⟨i, Nat.lt_succ_self i⟩) ∘ headN (i + 1) := rfl
      rw [e]
      exact (measurable_pi_apply _).comp (comap_measurable (headN (i + 1)))
    exact h1.mono (le_iSup (fun n => (headFiltration n : MeasurableSpace Coord)) (i + 1)) le_rfl
  exact hF.comp hid

/-! ### Conditional expectations and Lévy's upward theorem -/

/-- `E[F | ω₀, …, ω_{n-1}](ω) = ∫ F(headN n ω, y) dP(y)`. -/
theorem condExp_headFiltration {F : Coord → ℝ} (hF : Integrable F stdP)
    (hG : Measurable fun x => ∫ y, F (joinN n x y) ∂stdP) :
    (fun ω => ∫ y, F (joinN n (headN n ω) y) ∂stdP) =ᵐ[stdP] stdP[F | headFiltration n] := by
  set G : (Fin n → ℝ) → ℝ := fun x => ∫ y, F (joinN n x y) ∂stdP with hGdef
  have hprod : Integrable (fun z : (Fin n → ℝ) × Coord => F (joinN n z.1 z.2))
      ((gaussPi n).prod stdP) :=
    ((measurePreserving_joinN n).integrable_comp hF.aestronglyMeasurable).2 hF
  have hGi : Integrable G (gaussPi n) := hprod.integral_prod_left
  have hgi : Integrable (G ∘ headN n) stdP :=
    ((measurePreserving_headN n).integrable_comp hG.aestronglyMeasurable).2 hGi
  have hm := headFiltration.le n
  have : IsFiniteMeasure (stdP.trim hm) := isFiniteMeasure_trim hm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hF (fun s _ _ => hgi.integrableOn) ?_ ?_
  · intro s hs _
    rw [headFiltration_apply, MeasurableSpace.measurableSet_comap] at hs
    obtain ⟨A, hA, rfl⟩ := hs
    -- left side: transport along `headN`
    have hL : ∫ ω in headN n ⁻¹' A, G (headN n ω) ∂stdP = ∫ x in A, G x ∂gaussPi n := by
      rw [← (measurePreserving_headN n).map_eq, setIntegral_map hA
        ((measurePreserving_headN n).map_eq ▸ hG.aestronglyMeasurable)
        (measurable_headN n).aemeasurable]
    -- right side: transport along `joinN` and Fubini
    have hpre : (fun z : (Fin n → ℝ) × Coord => joinN n z.1 z.2) ⁻¹' (headN n ⁻¹' A) =
        A ×ˢ Set.univ := by
      ext ⟨x, y⟩
      simp
    have hR : ∫ ω in headN n ⁻¹' A, F ω ∂stdP = ∫ x in A, G x ∂gaussPi n := by
      rw [← (measurePreserving_joinN n).setIntegral_preimage_emb (measurableEmbedding_joinN n),
        hpre, setIntegral_prod _ hprod.integrableOn]
      simp only [Measure.restrict_univ]
      rfl
    exact hL.trans hR.symm
  · exact (hG.comp (comap_measurable (headN n))).stronglyMeasurable.aestronglyMeasurable

/-- **Lévy's upward theorem** for the first-coordinates filtration: for integrable measurable `F`,
`∫ F(headN n ω, y) dP(y) → F(ω)` for `P`-a.e. `ω`. -/
theorem tendsto_ae_integral_joinN {F : Coord → ℝ} (hFm : Measurable F) (hF : Integrable F stdP)
    (hG : ∀ n, Measurable fun x => ∫ y, F (joinN n x y) ∂stdP) :
    ∀ᵐ ω ∂stdP,
      Tendsto (fun n => ∫ y, F (joinN n (headN n ω) y) ∂stdP) atTop (𝓝 (F ω)) := by
  have h1 := hF.tendsto_ae_condExp (ℱ := headFiltration)
    (measurable_iSup_headFiltration hFm).stronglyMeasurable
  have h2 : ∀ᵐ ω ∂stdP, ∀ n, ∫ y, F (joinN n (headN n ω) y) ∂stdP =
      (stdP[F | headFiltration n]) ω :=
    ae_all_iff.2 fun n => condExp_headFiltration n hF (hG n)
  filter_upwards [h1, h2] with ω h1ω h2ω
  simp_rw [h2ω]
  exact h1ω

end GaussLp

end GaussianLQG
