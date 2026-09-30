import QuantumZipper.Proofs.Complex.KernelChordR1

/-!
# KT2 input R: Schwarz reflection of the left-normalized uniformizer

`leftReflection : LeftReflection`. For a simple chord `η` and a left-normalized uniformizer
`φ : D₁ → ℍ`, the map `Φ = schwarzReflect (extendFrom D₁ φ)` — `φ` on `D₁`, its real boundary
values `b` on `(−∞,0)`, and `conj ∘ φ ∘ conj` on `conj D₁` — is holomorphic and bijective from
`leftDoubled η` onto `ℂ \ [0,∞)`, with `Φ(−1) = −1` and `Φ'(−1) > 0`.

Sources and route:
* boundary values on `(−∞,0)`: Carathéodory boundary correspondence (Pommerenke, *Boundary
  Behaviour of Conformal Maps* (1992), Thm 2.6), `exists_boundary_values_leftUniformizer`;
  continuity of the extension up to `(−∞,0) ∪ {0}` is `continuousOn_extendFrom`;
* holomorphy across `(−∞,0)`: Schwarz reflection principle (Ahlfors, *Complex Analysis*,
  3rd ed., Ch. 4, §6.5, Thm 24), `CA.exists_reflection_extension`;
* `b` maps `(−∞,0)` onto `(−∞,0)`: own elementary argument (intermediate value theorem, using
  `b(−1) = −1`, `b ≠ 0`, `b(x) → 0` as `x → 0⁻` from `φ(0) = 0`, and `|b(x)|` unbounded from
  `φ(∞) = ∞`);
* `Φ'(−1) > 0`: own elementary argument (difference quotients along `ℝ` are real, those along
  `i ℝ₊` have positive imaginary part since `Φ(ℍ ∩ D₁) ⊆ ℍ`; `Φ' ≠ 0` by injectivity).
-/

noncomputable section

open Set Metric Filter Topology Complex Function Bornology
open QuantumZipper.CA.Uniformizer
open scoped ComplexConjugate ComplexOrder

namespace QuantumZipper.CA.Kernel

/-- Growth of an extension: if `‖f‖ → ∞` at `∞` within `A` and `f` has limits at the points of
`T ⊆ closure A`, then `‖extendFrom A f‖ ≥ M` on `T` far out. -/
theorem exists_norm_ge_of_extendFrom {f : ℂ → ℂ} {A T : Set ℂ} (hT : T ⊆ closure A)
    (hlim : ∀ z ∈ T, ∃ y, Tendsto f (𝓝[A] z) (𝓝 y))
    (hf : Tendsto (fun z => ‖f z‖) (cobounded ℂ ⊓ 𝓟 A) atTop) (M : ℝ) :
    ∃ r : ℝ, ∀ z ∈ T, r < ‖z‖ → M ≤ ‖extendFrom A f z‖ := by
  have h1 := tendsto_atTop.1 hf M
  rw [eventually_inf_principal] at h1
  obtain ⟨r, -, hr⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 h1
  refine ⟨r, fun z hzT hzr => ?_⟩
  have hU : (closedBall (0 : ℂ) r)ᶜ ∈ 𝓝 z :=
    isClosed_closedBall.isOpen_compl.mem_nhds (by simp [not_le, hzr])
  have : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hT hzT)
  have ht := tendsto_extendFrom (hlim z hzT)
  have hev : ∀ᶠ w in 𝓝[A] z, f w ∈ {v : ℂ | M ≤ ‖v‖} := by
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with w hw hwA
    exact hr hw hwA
  exact (isClosed_le continuous_const continuous_norm).mem_of_tendsto ht hev

/-- A continuous nonvanishing real function on `(−∞,0)` with `b(−1) = −1`, small values near
`0⁻` and unbounded values is negative and maps `(−∞,0)` onto `(−∞,0)` (intermediate value
theorem). -/
theorem neg_and_surj_of_ivt {b : ℝ → ℝ} (hc : ContinuousOn b (Iio 0))
    (h0 : ∀ x : ℝ, x < 0 → b x ≠ 0) (h1 : b (-1) = -1)
    (hsmall : ∀ ε > 0, ∃ a < 0, |b a| < ε) (hlarge : ∀ M : ℝ, ∃ x < 0, M ≤ |b x|) :
    (∀ x : ℝ, x < 0 → b x < 0) ∧ ∀ y : ℝ, y < 0 → ∃ x < 0, b x = y := by
  have hsub : ∀ {x x' : ℝ}, x < 0 → x' < 0 → uIcc x x' ⊆ Iio 0 := fun hx hx' c hc' => by
    rcases Set.mem_uIcc.1 hc' with ⟨-, h⟩ | ⟨-, h⟩
    · exact lt_of_le_of_lt h hx'
    · exact lt_of_le_of_lt h hx
  have hneg : ∀ x : ℝ, x < 0 → b x < 0 := by
    intro x hx
    by_contra hpos
    have hpos : 0 < b x := lt_of_le_of_ne (not_lt.1 hpos) (h0 x hx).symm
    obtain ⟨c, hc', hbc⟩ := intermediate_value_uIcc (hc.mono (hsub hx (by norm_num : (-1 : ℝ) < 0)))
      (show (0 : ℝ) ∈ uIcc (b x) (b (-1)) by
        rw [h1]; exact Set.mem_uIcc.2 (Or.inr ⟨by norm_num, hpos.le⟩))
    exact h0 c (hsub hx (by norm_num) hc') hbc
  refine ⟨hneg, fun y hy => ?_⟩
  obtain ⟨a, ha, hba⟩ := hsmall (-y) (by linarith)
  obtain ⟨x₀, hx₀, hbx⟩ := hlarge (-y + 1)
  have h1' := hneg a ha
  have h2' := hneg x₀ hx₀
  rw [abs_of_neg h1'] at hba
  rw [abs_of_neg h2'] at hbx
  obtain ⟨c, hc', hbc⟩ := intermediate_value_uIcc (hc.mono (hsub hx₀ ha))
    (show y ∈ uIcc (b x₀) (b a) from Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
  exact ⟨c, hsub hx₀ ha hc', hbc⟩

/-- **KT2 input R (Schwarz reflection of the left-normalized uniformizer).** -/
theorem leftReflection : LeftReflection := by
  intro η φ hη hφ
  obtain ⟨b, hb, hbinj, hb0⟩ := exists_boundary_values_leftUniformizer hη hφ
  obtain ⟨⟨hbij, hd, h0, hinf⟩, hm1⟩ := hφ
  set D := leftComponent η with hDdef
  have hDo : IsOpen D := isOpen_leftComponent hη
  have hDH : D ⊆ H := leftComponent_subset_H η
  set N : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re < 0} with hNdef
  set B : Set ℂ := D ∪ N ∪ {0} with hBdef
  have hre : ∀ z : ℂ, z.im = 0 → z = (z.re : ℂ) := fun z h => Complex.ext (by simp) (by simp [h])
  have hBcl : B ⊆ closure D := by
    rintro z ((hz | ⟨h0z, hneg⟩) | hz)
    · exact subset_closure hz
    · rw [hre z h0z]; exact ofReal_mem_closure_leftComponent hη hneg
    · rw [mem_singleton_iff.1 hz]; exact zero_mem_closure_leftComponent hη
  have hlim : ∀ z ∈ B, ∃ y, Tendsto φ (𝓝[D] z) (𝓝 y) := by
    rintro z ((hz | ⟨h0z, hneg⟩) | hz)
    · exact ⟨φ z, (hd.continuousOn.continuousAt (hDo.mem_nhds hz)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · rw [hre z h0z]; exact ⟨_, hb z.re hneg⟩
    · rw [mem_singleton_iff.1 hz]; exact ⟨0, h0⟩
  set φt := extendFrom D φ with hφtdef
  have hcont : ContinuousOn φt B := continuousOn_extendFrom hBcl hlim
  have hφtD : ∀ z ∈ D, φt z = φ z := extendFrom_extends hd.continuousOn
  have hφtN : ∀ x : ℝ, x < 0 → φt x = (b x : ℂ) := fun x hx =>
    extendFrom_eq (ofReal_mem_closure_leftComponent hη hx) (hb x hx)
  have hφt0 : φt 0 = 0 := extendFrom_eq (zero_mem_closure_leftComponent hη) h0
  have hb1 : b (-1) = -1 := by
    have : (𝓝[D] ((-1 : ℝ) : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (ofReal_mem_closure_leftComponent hη (by norm_num))
    have h1 := tendsto_nhds_unique (hb (-1) (by norm_num))
      (by push_cast; exact hm1 : Tendsto φ (𝓝[D] ((-1 : ℝ) : ℂ)) (𝓝 (-1)))
    exact_mod_cast h1
  -- the real boundary function
  have hbc : ContinuousOn b (Iio 0) := by
    have h1 : ContinuousOn (fun x : ℝ => (φt (x : ℂ)).re) (Iio 0) :=
      continuous_re.comp_continuousOn (hcont.comp continuous_ofReal.continuousOn
        fun x (hx : x < 0) => Or.inl (Or.inr ⟨by simp, by simpa using hx⟩))
    refine h1.congr fun x (hx : x < 0) => ?_
    simp [hφtN x hx]
  have hsmall : ∀ ε > 0, ∃ a < 0, |b a| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hH⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 (Or.inr rfl)) ε hε
    refine ⟨-(δ / 2), by linarith, ?_⟩
    have hmem : ((-(δ / 2) : ℝ) : ℂ) ∈ B := Or.inl (Or.inr ⟨by simp, by simp; linarith⟩)
    have hdist : dist ((-(δ / 2) : ℝ) : ℂ) 0 < δ := by
      rw [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
    have := hH hmem hdist
    rwa [hφt0, dist_zero_right, hφtN _ (by linarith), norm_real, Real.norm_eq_abs] at this
  have hlarge : ∀ M : ℝ, ∃ x < 0, M ≤ |b x| := by
    intro M
    obtain ⟨r, hr⟩ := exists_norm_ge_of_extendFrom (T := N)
      (fun z hz => hBcl (Or.inl (Or.inr hz))) (fun z hz => hlim z (Or.inl (Or.inr hz))) hinf M
    set x : ℝ := -(|r| + 1)
    have hx : x < 0 := by have := abs_nonneg r; simp only [x]; linarith
    have h1 := hr (x : ℂ) ⟨by simp, by simpa using hx⟩ (by
      rw [norm_real, Real.norm_eq_abs, abs_of_neg hx]
      simp only [x]; linarith [le_abs_self r])
    rw [show extendFrom D φ (x : ℂ) = (b x : ℂ) from hφtN x hx, norm_real, Real.norm_eq_abs] at h1
    exact ⟨x, hx, h1⟩
  obtain ⟨hbneg, hbsurj⟩ := neg_and_surj_of_ivt hbc hb0 hb1 hsmall hlarge
  -- the reflected map
  set Φ := CA.schwarzReflect φt with hΦdef
  have hΦ : ∀ w, Φ w = if 0 ≤ w.im then φt w else conj (φt (conj w)) := fun w => rfl
  have hΦD : ∀ z ∈ D, Φ z = φ z := fun z hz => by
    rw [hΦ, if_pos (hDH hz).le, hφtD z hz]
  have hΦC : ∀ z, conj z ∈ D → Φ z = conj (φ (conj z)) := fun z hz => by
    have h1 : 0 < (conj z).im := hDH hz
    rw [conj_im] at h1
    rw [hΦ, if_neg (by linarith), hφtD _ hz]
  have hΦN : ∀ x : ℝ, x < 0 → Φ x = (b x : ℂ) := fun x hx => by
    rw [hΦ, if_pos (by simp), hφtN x hx]
  -- the three pieces of the doubled domain
  have hpos : ∀ z ∈ leftDoubled η, 0 < z.im → z ∈ D := fun z hz h =>
    mem_leftComponent_of_mem_leftDoubled hz h
  have hnegp : ∀ z ∈ leftDoubled η, z.im < 0 → conj z ∈ D := by
    rintro z ((hz | ⟨v, hv, rfl⟩) | ⟨h0z, -⟩) h
    · have : 0 < z.im := hDH hz
      linarith
    · rwa [conj_conj]
    · linarith
  have hzero : ∀ z ∈ leftDoubled η, z.im = 0 → z.re < 0 := by
    rintro z ((hz | ⟨v, hv, rfl⟩) | ⟨-, hneg⟩) h
    · have : 0 < z.im := hDH hz
      linarith
    · have : 0 < v.im := hDH hv
      rw [conj_im] at h
      linarith
    · exact hneg
  -- holomorphy
  have hΦd : DifferentiableOn ℂ Φ (leftDoubled η) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases lt_trichotomy z.im 0 with h | h | h
    · have hcz := hnegp z hz h
      have h1 : DifferentiableAt ℂ φ (conj z) := hd.differentiableAt (hDo.mem_nhds hcz)
      have h2 := h1.conj_conj
      rw [conj_conj] at h2
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [(hDo.preimage continuous_conj).mem_nhds hcz] with w hw
      exact hΦC w hw
    · have hneg := hzero z hz h
      rw [hre z h]
      set x := z.re
      obtain ⟨δ, hδ, hnear⟩ := mem_leftComponent_of_near_neg hη hneg
      set r := min δ (-x)
      have hr : 0 < r := lt_min hδ (by linarith)
      have hsub : H ∩ ball (x : ℂ) r ⊆ D := fun w hw =>
        hnear w hw.1 (lt_of_lt_of_le hw.2 (min_le_left _ _))
      have hHb : Hbar ∩ ball (x : ℂ) r ⊆ B := by
        rintro w ⟨hw0, hw⟩
        rcases (show (0 : ℝ) ≤ w.im from hw0).eq_or_lt with h0w | h0w
        · refine Or.inl (Or.inr ⟨h0w.symm, ?_⟩)
          have h1 := abs_re_le_norm (w - x)
          rw [mem_ball, dist_eq_norm] at hw
          simp only [sub_re, ofReal_re] at h1
          have := (abs_lt.1 (lt_of_le_of_lt h1 (lt_of_lt_of_le hw (min_le_right _ _)))).2
          linarith
        · exact Or.inl (Or.inl (hsub ⟨h0w, hw⟩))
      have hdiff : DifferentiableOn ℂ φt (H ∩ ball (x : ℂ) r) :=
        (hd.mono hsub).congr fun w hw => hφtD w (hsub hw)
      have hreal : ∀ w ∈ ball (x : ℂ) r, w.im = 0 → (φt w).im = 0 := fun w hw h0w => by
        have hwB := hHb ⟨show (0 : ℝ) ≤ w.im by rw [h0w], hw⟩
        rcases hwB with (hwD | ⟨-, hwneg⟩) | hw0
        · have : 0 < w.im := hDH hwD
          linarith
        · rw [hre w h0w, hφtN _ hwneg]; simp
        · rw [mem_singleton_iff.1 hw0, hφt0]; simp
      obtain ⟨G, hGd, hGeq, hGsym⟩ :=
        CA.exists_reflection_extension hdiff (hcont.mono hHb) hreal
      refine (hGd.differentiableAt (ball_mem_nhds _ hr)).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds (x : ℂ) hr] with w hw
      by_cases hw0 : 0 ≤ w.im
      · rw [hΦ, if_pos hw0]; exact (hGeq ⟨hw0, hw⟩).symm
      · rw [hΦ, if_neg hw0]
        have hcw : conj w ∈ Hbar ∩ ball (x : ℂ) r :=
          ⟨show 0 ≤ (conj w).im by rw [conj_im]; linarith, conj_mem_ball_ofReal hw⟩
        rw [← hGeq hcw, hGsym w hw, conj_conj]
    · have hzD := hpos z hz h
      refine (hd.differentiableAt (hDo.mem_nhds hzD)).congr_of_eventuallyEq ?_
      filter_upwards [hDo.mem_nhds hzD] with w hw
      exact hΦD w hw
  -- values and signs
  have hkey : ∀ z ∈ leftDoubled η,
      (0 < z.im → 0 < (Φ z).im) ∧ (z.im < 0 → (Φ z).im < 0) ∧ (z.im = 0 → (Φ z).im = 0) := by
    intro z hz
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [hΦD z (hpos z hz h)]; exact hbij.mapsTo (hpos z hz h)
    · rw [hΦC z (hnegp z hz h), conj_im]
      have : 0 < (φ (conj z)).im := hbij.mapsTo (hnegp z hz h)
      linarith
    · rw [hre z h, hΦN _ (hzero z hz h)]; simp
  have hinj : InjOn Φ (leftDoubled η) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have him : (Φ z₁).im = (Φ z₂).im := by rw [heq]
    obtain ⟨a1, a2, a3⟩ := hkey z₁ hz₁
    obtain ⟨b1, b2, b3⟩ := hkey z₂ hz₂
    rcases lt_trichotomy z₁.im 0 with h1 | h1 | h1 <;>
      rcases lt_trichotomy z₂.im 0 with h2 | h2 | h2
    · have e := heq
      rw [hΦC z₁ (hnegp z₁ hz₁ h1), hΦC z₂ (hnegp z₂ hz₂ h2)] at e
      have e2 := hbij.injOn (hnegp z₁ hz₁ h1) (hnegp z₂ hz₂ h2) ((starRingEnd ℂ).injective e)
      simpa using congrArg conj e2
    · linarith [a2 h1, b3 h2]
    · linarith [a2 h1, b1 h2]
    · linarith [a3 h1, b2 h2]
    · have e := heq
      rw [hre z₁ h1, hre z₂ h2, hΦN _ (hzero z₁ hz₁ h1), hΦN _ (hzero z₂ hz₂ h2)] at e
      have e2 := hbinj (hzero z₁ hz₁ h1) (hzero z₂ hz₂ h2) (by exact_mod_cast e)
      rw [hre z₁ h1, hre z₂ h2, e2]
    · linarith [a3 h1, b1 h2]
    · linarith [a1 h1, b2 h2]
    · linarith [a1 h1, b3 h2]
    · rw [hΦD z₁ (hpos z₁ hz₁ h1), hΦD z₂ (hpos z₂ hz₂ h2)] at heq
      exact hbij.injOn (hpos z₁ hz₁ h1) (hpos z₂ hz₂ h2) heq
  have hmaps : MapsTo Φ (leftDoubled η) slitNeg := by
    intro z hz
    show -Φ z ∈ slitPlane
    rw [mem_slitPlane_iff]
    obtain ⟨a1, a2, a3⟩ := hkey z hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · right; rw [neg_im]; linarith [a2 h]
    · left
      rw [hre z h, hΦN _ (hzero z hz h), neg_re, ofReal_re]
      linarith [hbneg _ (hzero z hz h)]
    · right; rw [neg_im]; linarith [a1 h]
  have hsurj : SurjOn Φ (leftDoubled η) slitNeg := by
    intro w hw
    have hw' : -w ∈ slitPlane := hw
    rw [mem_slitPlane_iff, neg_re, neg_im] at hw'
    rcases lt_trichotomy w.im 0 with h | h | h
    · have hcw : conj w ∈ H := show 0 < (conj w).im by rw [conj_im]; linarith
      obtain ⟨z, hz, hzw⟩ := hbij.surjOn hcw
      refine ⟨conj z, Or.inl (Or.inr ⟨z, hz, rfl⟩), ?_⟩
      rw [hΦC _ (by rwa [conj_conj]), conj_conj, hzw, conj_conj]
    · have hwr : w.re < 0 := by
        rcases hw' with h' | h'
        · linarith
        · exact absurd (by rw [h]; simp) h'
      obtain ⟨c, hc, hbc⟩ := hbsurj w.re hwr
      refine ⟨c, Or.inr ⟨by simp, by simpa using hc⟩, ?_⟩
      rw [hΦN c hc, hbc, ← hre w h]
    · obtain ⟨z, hz, hzw⟩ := hbij.surjOn (show w ∈ H from h)
      exact ⟨z, Or.inl (Or.inl hz), by rw [hΦD z hz, hzw]⟩
  have hbijΦ : BijOn Φ (leftDoubled η) slitNeg := ⟨hmaps, hinj, hsurj⟩
  have hΦm1 : Φ (-1) = -1 := by
    have := hΦN (-1) (by norm_num)
    push_cast at this
    rw [this, hb1]; simp
  -- the derivative at `-1`
  have hm1D := neg_one_mem_leftDoubled η
  have hdc : HasDerivAt Φ (deriv Φ (-1)) (-1) :=
    (hΦd.differentiableAt ((isOpen_leftDoubled hη).mem_nhds hm1D)).hasDerivAt
  set c := deriv Φ (-1) with hcdef
  have hc0 : c ≠ 0 := Koebe.deriv_ne_zero_of_injOn (isOpen_leftDoubled hη) hΦd hinj hm1D
  -- real direction: `c` is real
  have hcim : c.im = 0 := by
    have hl : HasDerivAt (fun s : ℝ => -1 + (s : ℂ)) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add (-1)
    have hc' : HasDerivAt Φ c ((fun s : ℝ => -1 + (s : ℂ)) 0) := by simpa using hdc
    have h := hasDerivAt_iff_tendsto_slope.1 (hc'.comp (0 : ℝ) hl)
    rw [mul_one] at h
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope (Φ ∘ fun s : ℝ => -1 + (s : ℂ)) 0 t ∈
        {w : ℂ | w.im = 0} := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℝ) one_pos)] with t ht
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      have ht1 : -1 + t < 0 := by linarith [(abs_lt.1 ht).2]
      have e1 : Φ (-1 + (t : ℂ)) = (b (-1 + t) : ℂ) := by
        rw [← hΦN _ ht1]; push_cast; rfl
      simp only [slope_def_module, Function.comp_apply, e1, ofReal_zero,
        add_zero, hΦm1, smul_im, sub_im, ofReal_im, neg_im, one_im]
      simp
    exact (isClosed_eq continuous_im continuous_const).mem_of_tendsto h hev
  -- imaginary direction: `c.re ≥ 0`
  have hcre : 0 ≤ c.re := by
    obtain ⟨δ, hδ, hnear⟩ := mem_leftComponent_of_near_neg hη (x := -1) (by norm_num)
    have hl : HasDerivAt (fun s : ℝ => -1 + (s : ℂ) * I) I 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add (-1)
    have hc' : HasDerivAt Φ c ((fun s : ℝ => -1 + (s : ℂ) * I) 0) := by simpa using hdc
    have h := hasDerivAt_iff_tendsto_slope.1 (hc'.comp (0 : ℝ) hl)
    have h' := h.mono_left (nhdsWithin_mono _ fun t (ht : t ∈ Ioi (0 : ℝ)) => ne_of_gt ht)
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope (Φ ∘ fun s : ℝ => -1 + (s : ℂ) * I) 0 t ∈
        {w : ℂ | 0 ≤ w.im} := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      have hmem : -1 + (t : ℂ) * I ∈ D := by
        refine hnear _ (show 0 < (-1 + (t : ℂ) * I).im by simpa using ht.1) ?_
        rw [dist_eq_norm]; push_cast
        rw [show -1 + (t : ℂ) * I - -1 = (t : ℂ) * I by ring, norm_mul, norm_I, mul_one,
          norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        exact ht.2
      have hpos' : 0 < (Φ (-1 + (t : ℂ) * I)).im := by
        rw [hΦD _ hmem]; exact hbij.mapsTo hmem
      simp only [slope_def_module, Function.comp_apply, ofReal_zero, zero_mul,
        add_zero, hΦm1, smul_im, sub_im, neg_im, one_im, sub_zero, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 ht.1.le) (by linarith)
    have := (isClosed_le continuous_const continuous_im).mem_of_tendsto h' hev
    simpa using this
  have hcpos : 0 < c := by
    rw [Complex.lt_def]
    refine ⟨lt_of_le_of_ne (by simpa using hcre) fun h => hc0 ?_, by simp [hcim]⟩
    exact Complex.ext (by simpa using h.symm) (by simpa using hcim)
  exact ⟨Φ, isOpen_leftDoubled hη, hΦd, hbijΦ, hΦm1, hcpos, hΦD⟩

end QuantumZipper.CA.Kernel
