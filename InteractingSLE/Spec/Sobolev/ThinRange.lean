import InteractingSLE.Spec.Sobolev.CondMean

/-!
# Support removal on a thin random range (toward Aux. lemma 13)

Source: `source/spec/p049-096.md`, proof of Aux. lemma 13 (`#aux-13-proof`, pp. 85–86): "To see this
without conditioning a random test, use a countable test family in each deterministic rational
ball `B ⋐ U` and the `𝒫`-measurable event `{A ∩ B̄ = ∅}`. … Thus `M_𝒥 - N` is supported on `A`.
Aux. lemma 12 makes this difference zero."

## Main results

* `testFam` : a countable family of test functions (dense sequences of `𝓓_{K}` for exhaustions of
  finite unions of rational balls);
* `eq_zero_off_of_testFam` : a distribution vanishing on the members of the family supported off a
  relatively closed set `A` vanishes on every test function supported off `A`;
* `ae_eq_of_ae_eq_off` : two random distributions, a.s. locally `H^{-ε}` through a countable family
  of cutoffs, that agree (test function by test function, a.s.) off a random relatively closed set
  satisfying (SR3), agree a.s.;
* `exists_curve_condMean` : the conditional mean given the finer history has a version that is a
  measurable function of the curve (Step 1 of the proof of Aux. lemma 13);
* `measure_eq_of_setIntegral_exp` : the joint law of (distribution, curve) is determined by
  `E[1_B(γ) e^{i⟨T, φ⟩}]`;
* `aux13_joint_law_eq` : **Aux. lemma 13**.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real Metric ProbabilityTheory
open scoped Distributions ContDiff ENNReal NNReal

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### A countable test family -/

/-- The rational ball `B((p₁, p₂), p₃)`. -/
def ratBall (p : ℚ × ℚ × ℚ) : Set ℂ := ball ⟨p.1, p.2.1⟩ p.2.2

/-- A finite union of rational balls, as an open set. -/
def ratUnion (S : Finset (ℚ × ℚ × ℚ)) : Opens ℂ :=
  ⟨⋃ p ∈ S, ratBall p, isOpen_biUnion fun _ _ => isOpen_ball⟩

/-- Indices of the test family: a finite union `V` of rational balls with `V ⊆ U`, an exhaustion
level `n` of `V` and an index `k` of a dense sequence of `𝓓_{K_n(V)}`. -/
def TestIdx (U : Opens ℂ) : Type :=
  {S : Finset (ℚ × ℚ × ℚ) // (ratUnion S : Set ℂ) ⊆ U} × ℕ × ℕ

instance (U : Opens ℂ) : Countable (TestIdx U) := by unfold TestIdx; infer_instance

/-- The countable test family. -/
def testFam {U : Opens ℂ} (i : TestIdx U) : TestOn U :=
  TestFunction.ofSupportedIn ((exhaustK_subset (ratUnion i.1.1) i.2.1).trans i.1.2)
    (denseSeqK (ratUnion i.1.1) i.2.1 i.2.2)

theorem tsupport_testFam_subset {U : Opens ℂ} (i : TestIdx U) :
    tsupport (testFam i) ⊆ ratUnion i.1.1 :=
  ((denseSeqK (ratUnion i.1.1) i.2.1 i.2.2).tsupport_subset).trans
    (exhaustK_subset (ratUnion i.1.1) i.2.1)

theorem exists_ratBall_subset {W : Set ℂ} (hW : IsOpen W) {x : ℂ} (hx : x ∈ W) :
    ∃ p : ℚ × ℚ × ℚ, x ∈ ratBall p ∧ ratBall p ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 hW x hx
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (half_pos hδ)
  obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_btwn (show x.re - r / 2 < x.re + r / 2 by
    have : (0 : ℝ) < r := by exact_mod_cast hr0
    linarith)
  obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_btwn (show x.im - r / 2 < x.im + r / 2 by
    have : (0 : ℝ) < r := by exact_mod_cast hr0
    linarith)
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hdist : ‖x - ⟨q₁, q₂⟩‖ < r := by
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have h1 : |x.re - q₁| < r / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have h2 : |x.im - q₂| < r / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  refine ⟨(q₁, q₂, r), ?_, fun y hy => hδW ?_⟩
  · rw [ratBall, mem_ball, dist_eq_norm]; exact hdist
  · rw [ratBall, mem_ball, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm]
    calc ‖y - x‖ = ‖(y - ⟨q₁, q₂⟩) - (x - ⟨q₁, q₂⟩)‖ := by ring_nf
      _ ≤ ‖y - ⟨q₁, q₂⟩‖ + ‖x - ⟨q₁, q₂⟩‖ := norm_sub_le _ _
      _ < r + r := add_lt_add hy hdist
      _ < δ := by linarith

variable {U : Opens ℂ}

/-- **The countable test family suffices**: if `T` vanishes on the members of `testFam` whose
rational union avoids `A` (`A` relatively closed in `U`), then `T` vanishes on every test function
supported off `A`. -/
theorem eq_zero_off_of_testFam {T : DistOn U} {A : Set ℂ} (hA : closure A ∩ U ⊆ A)
    (h : ∀ i : TestIdx U, Disjoint (ratUnion i.1.1 : Set ℂ) A → T (testFam i) = 0) :
    ∀ φ : TestOn U, Disjoint (tsupport φ) A → T φ = 0 := by
  intro φ hφ
  set K := tsupport φ
  have hK : IsCompact K := φ.hasCompactSupport
  set W := (U : Set ℂ) \ closure A
  have hWo : IsOpen W := U.isOpen.sdiff isClosed_closure
  have hKW : K ⊆ W := fun x hx => ⟨φ.tsupport_subset hx, fun hxA =>
    Set.disjoint_left.1 hφ hx (hA ⟨hxA, φ.tsupport_subset hx⟩)⟩
  choose p hxp hpW using fun x : W => exists_ratBall_subset hWo x.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : W => ratBall (p x)) (fun _ => isOpen_ball)
    fun x hx => mem_iUnion.2 ⟨⟨x, hKW hx⟩, hxp _⟩
  classical
  set S : Finset (ℚ × ℚ × ℚ) := t.image p
  have hSW : (ratUnion S : Set ℂ) ⊆ W := by
    intro y hy
    simp only [ratUnion, Opens.coe_mk, mem_iUnion, S, Finset.mem_image] at hy
    obtain ⟨q, ⟨x, -, rfl⟩, hyq⟩ := hy
    exact hpW x hyq
  have hSU : (ratUnion S : Set ℂ) ⊆ U := hSW.trans sdiff_subset
  have hSA : Disjoint (ratUnion S : Set ℂ) A :=
    Set.disjoint_left.2 fun y hy hyA => (hSW hy).2 (subset_closure hyA)
  have hKS : K ⊆ ratUnion S := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
    simp only [ratUnion, Opens.coe_mk, mem_iUnion, S, Finset.mem_image]
    exact ⟨p x, ⟨x, hx, rfl⟩, hyx⟩
  obtain ⟨n, hn⟩ := exists_exhaustK_superset (ratUnion S) hK hKS
  set V := ratUnion S
  have hKU : (exhaustK V n : Set ℂ) ⊆ U := (exhaustK_subset V n).trans hSU
  let f : 𝓓_{exhaustK V n}(ℂ, ℝ) := ContDiffMapSupportedIn.of_support_subset φ.contDiff
    (subset_tsupport _ |>.trans hn)
  have hfφ : TestFunction.ofSupportedIn hKU f = φ := TestFunction.ext fun _ => rfl
  have hcont : Continuous (fun g : 𝓓_{exhaustK V n}(ℂ, ℝ) => T (TestFunction.ofSupportedIn hKU g)) :=
    T.continuous.comp (TestFunction.continuous_ofSupportedIn hKU)
  have := (denseRange_denseSeqK V n).induction_on (p := fun g => T (TestFunction.ofSupportedIn hKU g) = 0)
    f (isClosed_eq hcont continuous_const) fun k => h (⟨⟨S, hSU⟩, n, k⟩) hSA
  rwa [hfφ] at this

theorem negSobolevSq_neg (ε : ℝ) (T : DistOn U) (ζ : TestOn U) :
    negSobolevSq ε (-T) ζ = negSobolevSq ε T ζ := by
  simp only [negSobolevSq, fourierSq_neg]

theorem negSobolevSq_sub_lt_top {ε : ℝ} {T S : DistOn U} {ζ : TestOn U}
    (hT : negSobolevSq ε T ζ < ⊤) (hS : negSobolevSq ε S ζ < ⊤) : negSobolevSq ε (T - S) ζ < ⊤ := by
  rw [sub_eq_add_neg]
  refine lt_of_le_of_lt (negSobolevSq_add_le ε T (-S) ζ) ?_
  rw [negSobolevSq_neg]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hT, ENNReal.mul_lt_top (by simp) hS⟩

/-- **Support removal** (proof of Aux. lemma 13: "`M_𝒥 - N` is supported on `A`. Aux. lemma 12
makes this difference zero"). Two random distributions on `U`, almost surely locally `H^{-ε}`
through a sequence of cutoffs `ζ_n = 1` on the exhaustion `K_n(U)`, which agree (for each test
function, almost surely) off a random relatively closed set `A` satisfying (SR3) almost surely,
agree almost surely. -/
theorem ae_eq_of_ae_eq_off {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M N : Ω → DistOn U}
    {A : Ω → Set ℂ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {ζ : ℕ → TestOn U}
    (hζ : ∀ n, EqOn (ζ n) 1 (exhaustK U n))
    (hM : ∀ᵐ o ∂P, ∀ n, negSobolevSq ε (M o) (ζ n) < ⊤)
    (hN : ∀ᵐ o ∂P, ∀ n, negSobolevSq ε (N o) (ζ n) < ⊤)
    (hAcl : ∀ᵐ o ∂P, closure (A o) ∩ U ⊆ A o)
    (hdim : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A o ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    (hoff : ∀ φ : TestOn U, ∀ᵐ o ∂P, Disjoint (tsupport φ) (A o) → M o φ = N o φ) :
    ∀ᵐ o ∂P, M o = N o := by
  have hoff' : ∀ᵐ o ∂P, ∀ i : TestIdx U, Disjoint (tsupport (testFam i)) (A o) →
      M o (testFam i) = N o (testFam i) := ae_all_iff.2 fun i => hoff (testFam i)
  filter_upwards [hM, hN, hAcl, hdim, hoff'] with o hMo hNo hAo hdo hoo
  have h0 : M o - N o = 0 := by
    refine eq_zero_of_cutoff_bound_of_dimH_lt hε0 hε1 hAo hdo (fun φ => ?_) ?_
    · obtain ⟨n, hn⟩ := exists_exhaustK_superset U φ.hasCompactSupport.isCompact φ.tsupport_subset
      exact ⟨ζ n, (hζ n).mono hn, negSobolevSq_sub_lt_top (hMo n) (hNo n)⟩
    · refine eq_zero_off_of_testFam hAo fun i hi => ?_
      rw [sub_apply, hoo i (Set.disjoint_of_subset_left (tsupport_testFam_subset i) hi), sub_self]
  exact sub_eq_zero.1 h0

/-! ### Conditional means given the finer history and given the curve -/

section Curve

variable {Ω Γ : Type*} {mΓ : MeasurableSpace Γ} {J mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- "On that event the `𝒥`-conditional mean is the prescribed `𝒫`-measurable function. Taking
conditional expectation onto `𝒫` preserves the same identity." -/
theorem condExp_eq_off_of_le {X : Ω → Γ} (hX : Measurable X)
    (hXJ : MeasurableSpace.comap X mΓ ≤ J) (hJ : J ≤ mΩ) {f : Ω → ℝ}
    {B : Set Γ} (hB : MeasurableSet B) {g : Γ → ℝ} (hg : Measurable g)
    (hJB : ∀ᵐ o ∂P, X o ∈ B → P[f | J] o = g (X o)) :
    ∀ᵐ o ∂P, X o ∈ B → P[f | MeasurableSpace.comap X mΓ] o = g (X o) := by
  set 𝓖 := MeasurableSpace.comap X mΓ
  have h𝓖 : 𝓖 ≤ mΩ := hX.comap_le
  have hs : MeasurableSet[𝓖] (X ⁻¹' B) := ⟨B, hB, rfl⟩
  have h1 : P[f | 𝓖] =ᵐ[P] P[P[f | J] | 𝓖] := (condExp_condExp_of_le hXJ hJ).symm
  have h2 : P[(X ⁻¹' B).indicator (P[f | J]) | 𝓖] =ᵐ[P] (X ⁻¹' B).indicator (P[P[f | J] | 𝓖]) :=
    condExp_indicator integrable_condExp hs
  have h3 : (X ⁻¹' B).indicator (P[f | J]) =ᵐ[P] (X ⁻¹' B).indicator (g ∘ X) := by
    filter_upwards [hJB] with o ho
    by_cases hb : X o ∈ B
    · rw [indicator_of_mem (show o ∈ X ⁻¹' B from hb), indicator_of_mem (show o ∈ X ⁻¹' B from hb),
        ho hb]; rfl
    · rw [indicator_of_notMem (show o ∉ X ⁻¹' B from hb),
        indicator_of_notMem (show o ∉ X ⁻¹' B from hb)]
  have hint : Integrable ((X ⁻¹' B).indicator (g ∘ X)) P :=
    (integrable_condExp.indicator (h𝓖 _ hs)).congr h3
  have hgX : StronglyMeasurable[𝓖] (g ∘ X) :=
    (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have h4 : P[(X ⁻¹' B).indicator (g ∘ X) | 𝓖] = (X ⁻¹' B).indicator (g ∘ X) :=
    condExp_of_stronglyMeasurable h𝓖 (hgX.indicator hs) hint
  have h5 : P[(X ⁻¹' B).indicator (P[f | J]) | 𝓖] =ᵐ[P] P[(X ⁻¹' B).indicator (g ∘ X) | 𝓖] :=
    condExp_congr_ae h3
  filter_upwards [h1, h2, h5] with o e1 e2 e5 hb
  have hb' : o ∈ X ⁻¹' B := hb
  have e6 : (X ⁻¹' B).indicator (P[P[f | J] | 𝓖]) o = P[P[f | J] | 𝓖] o := indicator_of_mem hb' _
  rw [e1, ← e6, ← e2, e5, h4, indicator_of_mem hb']
  rfl

variable {U : Opens ℂ}

/-- **Step 1 of Aux. lemma 13** (in one coupling): the conditional mean given the finer history
`𝒥` has a version that is a measurable function of the recorded curve, a.s. locally `H^{-ε}`, and
equal to the prescribed mean off the range. -/
theorem exists_curve_condMean {X : Ω → Γ} (hX : Measurable X) (hXJ : MeasurableSpace.comap X mΓ ≤ J)
    (hJ : J ≤ mΩ) {h : Ω → DistOn U} (hh : Measurable h)
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤)
    {A : Γ → Set ℂ} (hAcl : ∀ γ, closure (A γ) ∩ U ⊆ A γ)
    (hAm : ∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)})
    (hSR3 : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A (X o) ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {m : Γ → TestOn U → ℝ} (hm : ∀ φ, Measurable fun γ => m γ φ)
    (hmean : ∀ φ : TestOn U, ∀ᵐ o ∂P, Disjoint (tsupport φ) (A (X o)) →
      P[fun o => h o φ | J] o = m (X o) φ)
    {ζ : ℕ → TestOn U} (hζ : ∀ n, EqOn (ζ n) 1 (exhaustK U n)) :
    ∃ N : Ω → DistOn U, Measurable[MeasurableSpace.comap X mΓ] N ∧
      (∀ φ : TestOn U, P[fun o => h o φ | J] =ᵐ[P] fun o => N o φ) ∧
      (∀ᵐ o ∂P, ∀ n, negSobolevSq ε (N o) (ζ n) < ⊤) ∧
      (∀ φ : TestOn U, ∀ᵐ o ∂P, Disjoint (tsupport φ) (A (X o)) → N o φ = m (X o) φ) := by
  obtain ⟨M, -, hMv, hMr⟩ := exists_condMean_version hh hJ hint hε0 hε1 hSR1
  obtain ⟨N, hNm, hNv, hNr⟩ := exists_condMean_version hh hX.comap_le hint hε0 hε1 hSR1
  have hNoff : ∀ φ : TestOn U, ∀ᵐ o ∂P, Disjoint (tsupport φ) (A (X o)) → N o φ = m (X o) φ := by
    intro φ
    have hB := hAm (tsupport φ) φ.hasCompactSupport
    have h1 := condExp_eq_off_of_le hX hXJ hJ hB (hm φ) (hmean φ)
    filter_upwards [h1, hNv φ] with o e1 e2 hd
    rw [e2, e1 hd]
  have hMoff : ∀ φ : TestOn U, ∀ᵐ o ∂P, Disjoint (tsupport φ) (A (X o)) → M o φ = m (X o) φ := by
    intro φ
    filter_upwards [hmean φ, hMv φ] with o e1 e2 hd
    rw [e2, e1 hd]
  have hMN : ∀ᵐ o ∂P, M o = N o :=
    ae_eq_of_ae_eq_off hε0 hε1 hζ (ae_all_iff.2 fun n => hMr (ζ n))
      (ae_all_iff.2 fun n => hNr (ζ n)) (ae_of_all _ fun o => hAcl (X o)) hSR3
      fun φ => by
        filter_upwards [hMoff φ, hNoff φ] with o e1 e2 hd
        rw [e1 hd, e2 hd]
  refine ⟨N, hNm, fun φ => ?_, ae_all_iff.2 fun n => hNr (ζ n), hNoff⟩
  filter_upwards [hMv φ, hMN] with o e1 e2
  rw [← e1, e2]

end Curve

/-! ### The joint law is determined by the curve-conditional characteristic functions -/

section Law

variable {U : Opens ℂ}

/-- The evaluation map `T ↦ (T φ)_φ`. -/
def evalMap (T : DistOn U) : TestOn U → ℝ := fun φ => T φ

theorem measurable_evalMap : Measurable (evalMap (U := U)) := Measurable.of_comap_le le_rfl

theorem distOn_measurableSpace_eq :
    (inferInstance : MeasurableSpace (DistOn U)) =
      MeasurableSpace.generateFrom (Set.preimage (evalMap (U := U)) '' measurableCylinders
        (fun _ : TestOn U => ℝ)) := by
  rw [← MeasurableSpace.comap_generateFrom, generateFrom_measurableCylinders]
  rfl

/-- **The law of a (distribution, curve) pair is determined by `E[1_B(γ) e^{i⟨T, φ⟩}]`**
(cylinder sets times measurable sets form a generating π-system; on each cylinder the law is
identified by its characteristic function on `EuclideanSpace ℝ s`, using the linearity of `T`). -/
theorem measure_eq_of_setIntegral_exp {Γ : Type*} [MeasurableSpace Γ]
    {ν₁ ν₂ : Measure (DistOn U × Γ)} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ∀ (φ : TestOn U) (B : Set Γ), MeasurableSet B →
      ∫ p in univ ×ˢ B, Complex.exp (↑(p.1 φ) * Complex.I) ∂ν₁ =
        ∫ p in univ ×ˢ B, Complex.exp (↑(p.1 φ) * Complex.I) ∂ν₂) : ν₁ = ν₂ := by
  set C₁ := Set.preimage (evalMap (U := U)) '' measurableCylinders (fun _ : TestOn U => ℝ)
  set C := Set.image2 (fun x1 x2 => x1 ×ˢ x2) C₁ {B : Set Γ | MeasurableSet B}
  have hC₁ : IsPiSystem C₁ := by
    have := isPiSystem_measurableCylinders (α := fun _ : TestOn U => ℝ)
    have h2 := this.comap (evalMap (U := U))
    convert h2 using 1
    ext s; simp [C₁, eq_comm]
  have hcylU : (univ : Set (DistOn U)) ∈ C₁ := by
    refine ⟨univ, ?_, by simp⟩
    rw [mem_measurableCylinders]
    exact ⟨∅, univ, MeasurableSet.univ, by simp [cylinder]⟩
  have hspan₁ : IsCountablySpanning C₁ := ⟨fun _ => univ, fun _ => hcylU, iUnion_const univ⟩
  have e1 : (inferInstance : MeasurableSpace (DistOn U)) = MeasurableSpace.generateFrom C₁ :=
    distOn_measurableSpace_eq
  have e2 : (inferInstance : MeasurableSpace Γ) =
      MeasurableSpace.generateFrom {B : Set Γ | MeasurableSet B} :=
    MeasurableSpace.generateFrom_measurableSet.symm
  have hgen : (inferInstance : MeasurableSpace (DistOn U × Γ)) = MeasurableSpace.generateFrom C := by
    calc (inferInstance : MeasurableSpace (DistOn U × Γ))
        = @Prod.instMeasurableSpace _ _ (MeasurableSpace.generateFrom C₁)
            (MeasurableSpace.generateFrom {B : Set Γ | MeasurableSet B}) := by
          rw [← e1, ← e2]
      _ = MeasurableSpace.generateFrom C := generateFrom_prod_eq hspan₁ isCountablySpanning_measurableSet
  have hrect : ∀ s ∈ C, ν₁ s = ν₂ s := by
    rintro _ ⟨E, ⟨t, ht, rfl⟩, B, hB, rfl⟩
    rw [mem_measurableCylinders] at ht
    obtain ⟨S', Sx, hSx, rfl⟩ := ht
    set pr : DistOn U → EuclideanSpace ℝ S' := fun T => WithLp.toLp 2 (fun j : S' => T j)
    have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => measurable_distOn_apply (j : TestOn U))
    have hpr1 : Measurable (fun p : DistOn U × Γ => pr p.1) := hpr.comp measurable_fst
    have hUB : MeasurableSet (univ ×ˢ B : Set (DistOn U × Γ)) := MeasurableSet.univ.prod hB
    have key : ∀ (T : DistOn U) (t : EuclideanSpace ℝ S'),
        inner ℝ (pr T) t = T (∑ j : S', (t.ofLp j) • (j : TestOn U)) := by
      intro T t
      rw [PiLp.inner_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, WithLp.ofLp_toLp, real_inner_eq_re_inner]
      simp
    have hchar : charFun ((ν₁.restrict (univ ×ˢ B)).map (fun p => pr p.1)) =
        charFun ((ν₂.restrict (univ ×ˢ B)).map (fun p => pr p.1)) := by
      funext t
      rw [charFun_apply, charFun_apply,
        integral_map hpr1.aemeasurable (by fun_prop), integral_map hpr1.aemeasurable (by fun_prop)]
      simp_rw [key]
      exact h _ B hB
    have heq := Measure.ext_of_charFun hchar
    have hset : (evalMap ⁻¹' cylinder S' Sx) ×ˢ B =
        (fun p : DistOn U × Γ => pr p.1) ⁻¹' {y | y.ofLp ∈ Sx} ∩ (univ ×ˢ B) := by
      ext p
      simp [pr, cylinder, and_comm]
      exact fun _ => Iff.rfl
    have hmS : MeasurableSet {y : EuclideanSpace ℝ S' | y.ofLp ∈ Sx} :=
      (WithLp.measurable_ofLp 2 _) hSx
    have hval : ∀ ν : Measure (DistOn U × Γ),
        ν ((evalMap ⁻¹' cylinder S' Sx) ×ˢ B) =
          ((ν.restrict (univ ×ˢ B)).map (fun p => pr p.1)) {y | y.ofLp ∈ Sx} := by
      intro ν
      rw [Measure.map_apply hpr1 hmS, Measure.restrict_apply (hpr1 hmS), hset]
    rw [hval, hval, heq]
  refine ext_of_generate_finite C hgen (hC₁.prod MeasurableSpace.isPiSystem_measurableSet) hrect ?_
  have := hrect (univ ×ˢ univ) ⟨univ, hcylU, univ, MeasurableSet.univ, rfl⟩
  rwa [univ_prod_univ] at this
end Law

/-! ### Aux. lemma 13 -/

section Aux13

variable {U : Opens ℂ}

theorem integrable_exp_mul_I {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun o => Complex.exp (↑(f o) * Complex.I)) P :=
  (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hf).mul_const _)).aestronglyMeasurable
    (Eventually.of_forall fun o => by rw [Complex.norm_exp_ofReal_mul_I])

/-- **Step 3 of Aux. lemma 13**: under a Gaussian conditional law given `𝒥` whose mean is
`n(X)` and whose variance is `Cov(X)`, the set integrals of `e^{i⟨h, φ⟩}` over `{X ∈ B}` are
functions of the curve law. -/
theorem setIntegral_exp_eq_of_condGauss {Ω Γ : Type*} {mΓ : MeasurableSpace Γ}
    {J mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn U}
    {X : Ω → Γ} (hh : Measurable h) (hX : Measurable X) (hXJ : MeasurableSpace.comap X mΓ ≤ J)
    (hJ : J ≤ mΩ) {Cov : Γ → TestOn U → ℝ} (hCov : ∀ φ, Measurable fun γ => Cov γ φ)
    {n : Γ → DistOn U} (hn : Measurable n) (φ : TestOn U)
    (hgauss : P[fun o => Complex.exp (↑(h o φ) * Complex.I) | J] =ᵐ[P]
      fun o => Complex.exp (↑(P[fun o => h o φ | J] o) * Complex.I - ↑(Cov (X o) φ / 2)))
    (hc : P[fun o => h o φ | J] =ᵐ[P] fun o => n (X o) φ) {B : Set Γ} (hB : MeasurableSet B) :
    ∫ p in univ ×ˢ B, Complex.exp (↑(p.1 φ) * Complex.I) ∂(P.map fun o => (h o, X o)) =
      ∫ γ in B, Complex.exp (↑(n γ φ) * Complex.I - ↑(Cov γ φ / 2)) ∂(P.map X) := by
  have hUB : MeasurableSet (univ ×ˢ B : Set (DistOn U × Γ)) := MeasurableSet.univ.prod hB
  have hm1 : Measurable fun p : DistOn U × Γ => Complex.exp (↑(p.1 φ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((measurable_distOn_apply φ).comp measurable_fst)).mul_const _)
  have hm2 : Measurable fun γ : Γ => Complex.exp (↑(n γ φ) * Complex.I - ↑(Cov γ φ / 2)) :=
    Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp
      ((measurable_distOn_apply φ).comp hn)).mul_const _).sub
        (Complex.measurable_ofReal.comp ((hCov φ).div_const 2)))
  rw [setIntegral_map hUB hm1.aestronglyMeasurable (hh.prodMk hX).aemeasurable,
    setIntegral_map hB hm2.aestronglyMeasurable hX.aemeasurable]
  have hpre : (fun o => (h o, X o)) ⁻¹' (univ ×ˢ B) = X ⁻¹' B := by ext; simp
  rw [hpre]
  have hs : MeasurableSet[J] (X ⁻¹' B) := hXJ _ ⟨B, hB, rfl⟩
  have hint : Integrable (fun o => Complex.exp (↑(h o φ) * Complex.I)) P :=
    integrable_exp_mul_I ((measurable_distOn_apply φ).comp hh)
  have hce := setIntegral_condExp hJ hint hs
  simp only at hce ⊢
  rw [← hce]
  refine setIntegral_congr_ae (hJ _ hs) ?_
  filter_upwards [hgauss, hc] with o e1 e2 _
  rw [e1, e2]

/-- **Aux. lemma 13** (identifying the field on a thin stopped range). Two couplings of a field
`hᵢ` on `U` and a recorded curve `Xᵢ` (values in a measurable space `Γ`) with equal curve laws;
`A(γ)` is the (relatively closed) range of the curve `γ`, with measurable avoidance events. In both
couplings the field is locally square-integrable with values in `H^{-ε}` ((SR1) and integrable
pairings), and a finer retained history `𝒥ᵢ ⊇ σ(Xᵢ)` gives a Gaussian conditional law whose variance
is the same measurable function `Cov` of the curve, and whose conditional mean off `A` is the same
measurable function `m` of the curve. If (SR3) holds almost surely, the joint laws of the field on
`U` and the recorded curve agree. (Extra retained information in `𝒥ᵢ`, such as field germs on
`A`, is allowed.) -/
theorem aux13_joint_law_eq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {Γ : Type*} {mΓ : MeasurableSpace Γ} {A : Γ → Set ℂ}
    (hAcl : ∀ γ, closure (A γ) ∩ U ⊆ A γ)
    (hAm : ∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)})
    {Cov : Γ → TestOn U → ℝ} (hCov : ∀ φ, Measurable fun γ => Cov γ φ)
    {m : Γ → TestOn U → ℝ} (hm : ∀ φ, Measurable fun γ => m γ φ)
    {Ω₁ : Type*} {J₁ m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {h₁ : Ω₁ → DistOn U} {X₁ : Ω₁ → Γ} (hh₁ : Measurable h₁) (hX₁ : Measurable X₁)
    (hXJ₁ : MeasurableSpace.comap X₁ mΓ ≤ J₁) (hJ₁ : J₁ ≤ m₁)
    (hint₁ : ∀ φ : TestOn U, Integrable (fun o => h₁ o φ) P₁)
    (hSR1₁ : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h₁ o) ζ ∂P₁ < ⊤)
    (hgauss₁ : ∀ φ : TestOn U, P₁[fun o => Complex.exp (↑(h₁ o φ) * Complex.I) | J₁] =ᵐ[P₁]
      fun o => Complex.exp (↑(P₁[fun o => h₁ o φ | J₁] o) * Complex.I - ↑(Cov (X₁ o) φ / 2)))
    (hmean₁ : ∀ φ : TestOn U, ∀ᵐ o ∂P₁, Disjoint (tsupport φ) (A (X₁ o)) →
      P₁[fun o => h₁ o φ | J₁] o = m (X₁ o) φ)
    {Ω₂ : Type*} {J₂ m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn U} {X₂ : Ω₂ → Γ} (hh₂ : Measurable h₂) (hX₂ : Measurable X₂)
    (hXJ₂ : MeasurableSpace.comap X₂ mΓ ≤ J₂) (hJ₂ : J₂ ≤ m₂)
    (hint₂ : ∀ φ : TestOn U, Integrable (fun o => h₂ o φ) P₂)
    (hSR1₂ : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h₂ o) ζ ∂P₂ < ⊤)
    (hgauss₂ : ∀ φ : TestOn U, P₂[fun o => Complex.exp (↑(h₂ o φ) * Complex.I) | J₂] =ᵐ[P₂]
      fun o => Complex.exp (↑(P₂[fun o => h₂ o φ | J₂] o) * Complex.I - ↑(Cov (X₂ o) φ / 2)))
    (hmean₂ : ∀ φ : TestOn U, ∀ᵐ o ∂P₂, Disjoint (tsupport φ) (A (X₂ o)) →
      P₂[fun o => h₂ o φ | J₂] o = m (X₂ o) φ)
    (hlaw : P₁.map X₁ = P₂.map X₂)
    (hSR3 : ∀ᵐ γ ∂(P₁.map X₁), ∀ K, IsCompact K → K ⊆ U →
      dimH (A γ ∩ K) < ENNReal.ofReal (2 - 2 * ε)) :
    P₁.map (fun o => (h₁ o, X₁ o)) = P₂.map (fun o => (h₂ o, X₂ o)) := by
  classical
  have hcut : ∀ k, ∃ ζ : TestOn U, EqOn ζ 1 (exhaustK U k) := fun k => by
    obtain ⟨ζ, -, h1⟩ := exists_cutoff_testOn (exhaustK U k).isCompact (exhaustK_subset U k)
    exact ⟨ζ, h1⟩
  choose ζ hζ using hcut
  have hSR3₁ := ae_of_ae_map hX₁.aemeasurable hSR3
  have hSR3₂ := ae_of_ae_map hX₂.aemeasurable (hlaw ▸ hSR3)
  obtain ⟨N₁, hN₁m, hN₁v, hN₁r, hN₁off⟩ := exists_curve_condMean hX₁ hXJ₁ hJ₁ hh₁ hint₁ hε0 hε1
    hSR1₁ hAcl hAm hSR3₁ hm hmean₁ hζ
  obtain ⟨N₂, -, hN₂v, hN₂r, hN₂off⟩ := exists_curve_condMean hX₂ hXJ₂ hJ₂ hh₂ hint₂ hε0 hε1
    hSR1₂ hAcl hAm hSR3₂ hm hmean₂ hζ
  -- Doob–Dynkin: the curve-measurable version is a measurable function of the curve
  obtain ⟨n, hnm, hn⟩ := hN₁m.exists_eq_measurable_comp
  -- the properties of `n` hold for almost every curve
  have hnr : ∀ᵐ γ ∂(P₁.map X₁), ∀ k, negSobolevSq ε (n γ) (ζ k) < ⊤ := by
    have hms : MeasurableSet {γ | ∀ k, negSobolevSq ε (n γ) (ζ k) < ⊤} := by
      have : {γ | ∀ k, negSobolevSq ε (n γ) (ζ k) < ⊤} =
          ⋂ k, {γ | negSobolevSq ε (n γ) (ζ k) < ⊤} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun k =>
        measurableSet_lt ((measurable_negSobolevSq ε (ζ k)).comp hnm) measurable_const
    rw [ae_map_iff hX₁.aemeasurable hms]
    filter_upwards [hN₁r] with o ho
    rw [hn] at ho
    exact ho
  have hnoff : ∀ φ : TestOn U, ∀ᵐ γ ∂(P₁.map X₁), Disjoint (tsupport φ) (A γ) → n γ φ = m γ φ := by
    intro φ
    have hms : MeasurableSet {γ | Disjoint (tsupport φ) (A γ) → n γ φ = m γ φ} := by
      have : {γ | Disjoint (tsupport φ) (A γ) → n γ φ = m γ φ} =
          {γ | Disjoint (tsupport φ) (A γ)}ᶜ ∪ {γ | n γ φ = m γ φ} := by
        ext γ; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
      rw [this]
      exact (hAm _ φ.hasCompactSupport).compl.union
        (measurableSet_eq_fun ((measurable_distOn_apply φ).comp hnm) (hm φ))
    rw [ae_map_iff hX₁.aemeasurable hms]
    filter_upwards [hN₁off φ] with o ho hd
    rw [← ho hd, hn]
    rfl
  -- in the second coupling the curve-measurable version is `n ∘ X₂`
  have hnr₂ : ∀ᵐ o ∂P₂, ∀ k, negSobolevSq ε (n (X₂ o)) (ζ k) < ⊤ :=
    ae_of_ae_map hX₂.aemeasurable (hlaw ▸ hnr)
  have hnoff₂ : ∀ φ : TestOn U, ∀ᵐ o ∂P₂, Disjoint (tsupport φ) (A (X₂ o)) →
      n (X₂ o) φ = m (X₂ o) φ := fun φ => ae_of_ae_map hX₂.aemeasurable (hlaw ▸ hnoff φ)
  have hN₂n : ∀ᵐ o ∂P₂, N₂ o = n (X₂ o) :=
    ae_eq_of_ae_eq_off hε0 hε1 hζ hN₂r hnr₂ (ae_of_all _ fun o => hAcl (X₂ o)) hSR3₂ fun φ => by
      filter_upwards [hN₂off φ, hnoff₂ φ] with o e1 e2 hd
      rw [e1 hd, e2 hd]
  have hc₁ : ∀ φ : TestOn U, P₁[fun o => h₁ o φ | J₁] =ᵐ[P₁] fun o => n (X₁ o) φ := fun φ => by
    filter_upwards [hN₁v φ] with o e
    rw [e, hn]
    rfl
  have hc₂ : ∀ φ : TestOn U, P₂[fun o => h₂ o φ | J₂] =ᵐ[P₂] fun o => n (X₂ o) φ := fun φ => by
    filter_upwards [hN₂v φ, hN₂n] with o e1 e2
    rw [e1, e2]
  -- the joint laws
  refine measure_eq_of_setIntegral_exp fun φ B hB => ?_
  rw [setIntegral_exp_eq_of_condGauss hh₁ hX₁ hXJ₁ hJ₁ hCov hnm φ (hgauss₁ φ) (hc₁ φ) hB,
    setIntegral_exp_eq_of_condGauss hh₂ hX₂ hXJ₂ hJ₂ hCov hnm φ (hgauss₂ φ) (hc₂ φ) hB, hlaw]

end Aux13

end InteractingSLE.Sobolev
