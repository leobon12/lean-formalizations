import SupercriticalLQGUniqueness.B2.PfeLocal.L6Err
import SupercriticalLQGUniqueness.B2.PfeAxioms.FiniteConstantScale
import SupercriticalLQGUniqueness.B2.Median.Scale
import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPLength

 




















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.DFGPS.L217 LQGMetric.LFPP Uniqueness.Toolkit.CompactPathInfimum
open PfeWeyl

 
theorem l6_ofReal_exp_mul (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp y) = ENNReal.ofReal (Real.exp (x + y)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos x).le, ← Real.exp_add]

theorem l6_ofReal_exp_ne_zero (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos x)).ne'

theorem l6_mul_le_mul_left {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c := by gcongr

theorem l6_mul_le_mul_right {a b c : ℝ≥0∞} (h : a ≤ b) : a * c ≤ b * c := by gcongr

theorem l6_ofReal_exp_le {x y : ℝ} (h : x ≤ y) :
    ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp y) :=
  ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h)

 
theorem l6_limsup_le_of_cmp {a x : ℕ → ℝ≥0∞} {β : ℕ → ℝ} {b : ℝ}
    (hβ : Tendsto β atTop (𝓝 b)) (h : ∀ᶠ n in atTop, a n ≤ ENNReal.ofReal (Real.exp (β n)) * x n) :
    limsup a atTop ≤ ENNReal.ofReal (Real.exp b) * limsup x atTop := by
  have hκ : Tendsto (fun n => ENNReal.ofReal (Real.exp (β n))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp b))) :=
    (ENNReal.continuous_ofReal.comp Real.continuous_exp).continuousAt.tendsto.comp hβ
  calc limsup a atTop ≤ limsup (fun n => ENNReal.ofReal (Real.exp (β n)) * x n) atTop :=
        limsup_le_limsup h
    _ ≤ limsup (fun n => ENNReal.ofReal (Real.exp (β n))) atTop * limsup x atTop :=
        ENNReal.limsup_mul_le' (by rw [hκ.limsup_eq]; exact Or.inl (l6_ofReal_exp_ne_zero b))
          (by rw [hκ.limsup_eq]; exact Or.inl ENNReal.ofReal_ne_top)
    _ = _ := by rw [hκ.limsup_eq]

 
theorem l6_le_liminf_of_cmp {a x : ℕ → ℝ≥0∞} {β : ℕ → ℝ} {b : ℝ}
    (hβ : Tendsto β atTop (𝓝 b)) (h : ∀ᶠ n in atTop, x n ≤ ENNReal.ofReal (Real.exp (β n)) * a n) :
    ENNReal.ofReal (Real.exp (-b)) * liminf x atTop ≤ liminf a atTop := by
  have hβ' : Tendsto (fun n => -β n) atTop (𝓝 (-b)) := hβ.neg
  have hκ : Tendsto (fun n => ENNReal.ofReal (Real.exp (-β n))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-b)))) :=
    (ENNReal.continuous_ofReal.comp Real.continuous_exp).continuousAt.tendsto.comp hβ'
  have h' : ∀ᶠ n in atTop, ENNReal.ofReal (Real.exp (-β n)) * x n ≤ a n := by
    filter_upwards [h] with n hn
    calc ENNReal.ofReal (Real.exp (-β n)) * x n
        ≤ ENNReal.ofReal (Real.exp (-β n)) * (ENNReal.ofReal (Real.exp (β n)) * a n) := by gcongr
      _ = a n := by
        rw [← mul_assoc, l6_ofReal_exp_mul, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one,
          one_mul]
  calc ENNReal.ofReal (Real.exp (-b)) * liminf x atTop
      = liminf (fun n => ENNReal.ofReal (Real.exp (-β n))) atTop * liminf x atTop := by
        rw [hκ.liminf_eq]
    _ ≤ liminf (fun n => ENNReal.ofReal (Real.exp (-β n)) * x n) atTop := ENNReal.le_liminf_mul
    _ ≤ liminf a atTop := liminf_le_liminf h'

 
theorem l6_obs_cmp {ξ : ℝ} (hξ : 0 ≤ ξ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {O : Set ℂ}
    (hO : IsOpen O) {δ : ℝ} (hδ : ∀ x ∈ O, |φ' x - φ x| ≤ δ) {d : L5Code}
    (hd : l5Rect d.1 ⊆ O) :
    l5Obs (normalizedLFPPMetric ξ a φ') d ≤
      ENNReal.ofReal (Real.exp (ξ * δ)) * l5Obs (normalizedLFPPMetric ξ a φ) d := by
  have h := l6_compactPathInf_lfpp_le ξ a hO hδ hd (E := l5Ball d.2.1) (F := l5Ball d.2.2)
  rwa [abs_of_nonneg hξ] at h

 
theorem l6_obs_add_const (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (c : ℝ) (d : L5Code) :
    l5Obs (normalizedLFPPMetric ξ a (φ + ContinuousMap.const ℂ c)) d =
      ENNReal.ofReal (Real.exp (ξ * c)) * l5Obs (normalizedLFPPMetric ξ a φ) d := by
  unfold l5Obs
  refine Median.compactPathInf_eq_mul_of_dist_scale _ _ _ (l6_ofReal_exp_ne_zero _)
    ENNReal.ofReal_ne_top (fun x y => ?_) _ _ _
  exact PfeAxioms.normalizedLFPPMetric_add_const ξ a φ _ c (fun w => by simp) (x, y)

section Sample

variable {ξ : ℝ} (hξ : 0 ≤ ξ) {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
  (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)) (S : L6Geo)
  {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)} {f : ℕ → DistC} {L : LSCMetric}
  (hconv : Tendsto (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) atTop (𝓝 L))
  (hsmall : ∀ k : ℕ, SmallAnnulusCosts (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n)))
    L (closedBall 0 k) (ball 0 ((k : ℝ) + 1)))

include hsmall hconv in
 
theorem l6_sample_sandwich (c : L5Code) {m₁ m₂ : ℕ} (h : m₁ < m₂) :
    limsup (fun n => l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) (l6Enlarge c m₁))
        atTop ≤ l5Obs L (l6Enlarge c m₂) ∧
      l5Obs L (l6Enlarge c m₂) ≤
        liminf (fun n => l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n)))
          (l6Enlarge c m₂)) atTop :=
  l6_sandwich hconv (fun _ => isLengthSpace_normalizedLFPPMetric _ _ _)
    (fun _ => PfeAxioms.finitePathsEuclideanContinuous_normalizedLFPPMetric _ _ _)
    (fun _ => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric _ _ _) hsmall c h

include hconv in
theorem l6_sample_liminf (d : L5Code) :
    l5Obs L d ≤
      liminf (fun n => l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) d) atTop :=
  compactPathInf_seq_liminf hconv (l5Rect_isCompact _) (l5Ball_isCompact _) (l5Ball_isCompact _)

include hξ in
 
theorem l6_cmpA {n : ℕ} {d : L5Code} (hact : l6Act S.V₁ (e n) d) (g : DistC) :
    l6An ξ m e S n g d ≤ ENNReal.ofReal (Real.exp (ξ * l6ErrA S V (e n) g - ξ * S.cA g)) *
        l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) g)) d ∧
      l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) g)) d ≤
        ENNReal.ofReal (Real.exp (ξ * l6ErrA S V (e n) g + ξ * S.cA g)) *
          l6An ξ m e S n g d := by
  have hd : l5Rect d.1 ⊆ (S.V₁ : Set ℂ) :=
    (self_subset_cthickening _).trans hact
  set φ : C(ℂ, ℝ) := V (e n) g + ContinuousMap.const ℂ (-S.cA g) with hφ
  have hb : ∀ x ∈ (S.V₁ : Set ℂ), |(locMollifyC (e n) (e n).2 (S.ren g) + 0) x - φ x| ≤
      l6ErrA S V (e n) g := by
    intro x hx
    have := l6_abs_le_norm_res (R := S.R)
      (locMollifyC (e n) (e n).2 (S.ren g) - (V (e n) g - ContinuousMap.const ℂ (S.cA g)))
      (S.hV₁R hx)
    simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      add_zero, hφ] at this ⊢
    unfold l6ErrA
    convert this using 2; ring
  have hb' : ∀ x ∈ (S.V₁ : Set ℂ), |φ x - (locMollifyC (e n) (e n).2 (S.ren g) + 0) x| ≤
      l6ErrA S V (e n) g := fun x hx => by rw [abs_sub_comm]; exact hb x hx
  have hsh := l6_obs_add_const ξ (m (e n)) (V (e n) g) (-S.cA g) d
  rw [← hφ] at hsh
  rw [l6An_apply hact]
  constructor
  · calc l5Obs (normalizedLFPPMetric ξ (m (e n)) (locMollifyC (e n) (e n).2 (S.ren g) + 0)) d
        ≤ ENNReal.ofReal (Real.exp (ξ * l6ErrA S V (e n) g)) *
            l5Obs (normalizedLFPPMetric ξ (m (e n)) φ) d :=
          l6_obs_cmp hξ _ S.V₁.isOpen hb hd
      _ = _ := by
        rw [hsh, ← mul_assoc, l6_ofReal_exp_mul]
        congr 3; ring
  · have h2 := l6_obs_cmp hξ (m (e n)) S.V₁.isOpen hb' hd
    rw [hsh] at h2
    calc l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) g)) d
        = ENNReal.ofReal (Real.exp (ξ * S.cA g)) * (ENNReal.ofReal (Real.exp (ξ * -S.cA g)) *
            l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) g)) d) := by
          rw [← mul_assoc, l6_ofReal_exp_mul, show ξ * S.cA g + ξ * -S.cA g = 0 by ring,
            Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (ξ * S.cA g)) *
            (ENNReal.ofReal (Real.exp (ξ * l6ErrA S V (e n) g)) *
              l5Obs (normalizedLFPPMetric ξ (m (e n))
                (locMollifyC (e n) (e n).2 (S.ren g) + 0)) d) := by gcongr
      _ = _ := by
        rw [← mul_assoc, l6_ofReal_exp_mul]
        congr 3; ring

include hξ in
 
theorem l6_cmpB {g₀ : L6S → DistC} {n : ℕ} {d : L5Code} (hact : l6Act S.U₁ (e n) d) (j : ℕ)
    (g : DistC) :
    l6Bn ξ m e S g₀ n g (d, j) ≤ ENNReal.ofReal (Real.exp (ξ * (l6ErrB S V (e n) g₀ g +
        ‖l6Res S.R (l6W S.R j) - S.u g₀ g‖))) *
        l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) g)) d ∧
      l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) g)) d ≤
        ENNReal.ofReal (Real.exp (ξ * (l6ErrB S V (e n) g₀ g +
          ‖l6Res S.R (l6W S.R j) - S.u g₀ g‖))) * l6Bn ξ m e S g₀ n g (d, j) := by
  have hd : l5Rect d.1 ⊆ (S.U₁ : Set ℂ) := (self_subset_cthickening _).trans hact
  set δ := l6ErrB S V (e n) g₀ g + ‖l6Res S.R (l6W S.R j) - S.u g₀ g‖ with hδ
  have hb : ∀ x ∈ (S.U₁ : Set ℂ),
      |(locMollifyC (e n) (e n).2 (S.N2 g₀ g) + l6W S.R j) x - V (e n) g x| ≤ δ := by
    intro x hx
    have hxR := S.hU₁R hx
    have h1 := l6_abs_le_norm_res (R := S.R) (locMollifyC (e n) (e n).2 (S.N2 g₀ g) -
      (V (e n) g - ContinuousMap.const ℂ (S.cA g) - S.Fb g₀ g)) hxR
    have h2 := ContinuousMap.norm_coe_le_norm (l6Res S.R (l6W S.R j) - S.u g₀ g) ⟨x, hxR⟩
    simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      Real.norm_eq_abs, l6Res_apply, L6Geo.u] at h1 h2 ⊢
    have e1 : locMollifyC (e n) (e n).2 (S.N2 g₀ g) x + l6W S.R j x - V (e n) g x =
        (locMollifyC (e n) (e n).2 (S.N2 g₀ g) x - (V (e n) g x - S.cA g - S.Fb g₀ g x)) +
          (l6W S.R j x - (S.Fb g₀ g x + S.cA g)) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    show _ ≤ l6ErrB S V (e n) g₀ g + _
    exact add_le_add h1 h2
  have hb' : ∀ x ∈ (S.U₁ : Set ℂ),
      |V (e n) g x - (locMollifyC (e n) (e n).2 (S.N2 g₀ g) + l6W S.R j) x| ≤ δ :=
    fun x hx => by rw [abs_sub_comm]; exact hb x hx
  rw [l6Bn_apply hact]
  exact ⟨l6_obs_cmp hξ _ S.U₁.isOpen hb hd, l6_obs_cmp hξ _ S.U₁.isOpen hb' hd⟩

include hξ he hconv in
 
theorem l6_pathA_lower (herr : Tendsto (fun n => l6ErrA S V (e n) (f n)) atTop (𝓝 0)) {c : ℝ}
    (hc : Tendsto (fun n => S.cA (f n)) atTop (𝓝 c)) {d : L5Code}
    (hd : l5Rect d.1 ⊆ (S.V₁ : Set ℂ)) :
    ENNReal.ofReal (Real.exp (-(ξ * c))) * l5Obs L d ≤
      liminf (fun n => l6An ξ m e S n (f n) d) atTop := by
  have hβ : Tendsto (fun n => ξ * l6ErrA S V (e n) (f n) + ξ * S.cA (f n)) atTop
      (𝓝 (ξ * c)) := by
    simpa using (herr.const_mul ξ).add (hc.const_mul ξ)
  have hcmp : ∀ᶠ n in atTop, l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) d ≤
      ENNReal.ofReal (Real.exp (ξ * l6ErrA S V (e n) (f n) + ξ * S.cA (f n))) *
        l6An ξ m e S n (f n) d := by
    filter_upwards [l6_eventually_act S.V₁.isOpen hd he] with n hn
    exact (l6_cmpA hξ S hn (f n)).2
  exact (l6_mul_le_mul_left (l6_sample_liminf hconv d)).trans (l6_le_liminf_of_cmp hβ hcmp)

include hξ he hconv hsmall in
 
theorem l6_pathA_upper (herr : Tendsto (fun n => l6ErrA S V (e n) (f n)) atTop (𝓝 0)) {c : ℝ}
    (hc : Tendsto (fun n => S.cA (f n)) atTop (𝓝 c)) (c₀ : L5Code) {m₀ : ℕ}
    (hd : l5Rect (l6Enlarge c₀ m₀).1 ⊆ (S.V₁ : Set ℂ)) :
    limsup (fun n => l6An ξ m e S n (f n) (l6Enlarge c₀ m₀)) atTop ≤
      ENNReal.ofReal (Real.exp (-(ξ * c))) * l5Obs L (l6Enlarge c₀ (m₀ + 1)) := by
  have hβ : Tendsto (fun n => ξ * l6ErrA S V (e n) (f n) - ξ * S.cA (f n)) atTop
      (𝓝 (-(ξ * c))) := by
    simpa using (herr.const_mul ξ).sub (hc.const_mul ξ)
  have hcmp : ∀ᶠ n in atTop, l6An ξ m e S n (f n) (l6Enlarge c₀ m₀) ≤
      ENNReal.ofReal (Real.exp (ξ * l6ErrA S V (e n) (f n) - ξ * S.cA (f n))) *
        l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) (l6Enlarge c₀ m₀) := by
    filter_upwards [l6_eventually_act S.V₁.isOpen hd he] with n hn
    exact (l6_cmpA hξ S hn (f n)).1
  exact (l6_limsup_le_of_cmp hβ hcmp).trans
    (l6_mul_le_mul_left (l6_sample_sandwich hconv hsmall c₀ (Nat.lt_succ_self m₀)).1)

include hξ he hconv in
 
theorem l6_pathB_lower {g₀ : L6S → DistC}
    (herr : Tendsto (fun n => l6ErrB S V (e n) g₀ (f n)) atTop (𝓝 0)) {u : C(L6K S.R, ℝ)}
    (hu : Tendsto (fun n => S.u g₀ (f n)) atTop (𝓝 u)) {d : L5Code}
    (hd : l5Rect d.1 ⊆ (S.U₁ : Set ℂ)) (j : ℕ) {η : ℝ}
    (hη : ‖l6Res S.R (l6W S.R j) - u‖ < η) :
    ENNReal.ofReal (Real.exp (-(ξ * η))) * l5Obs L d ≤
      liminf (fun n => l6Bn ξ m e S g₀ n (f n) (d, j)) atTop := by
  set η₀ := ‖l6Res S.R (l6W S.R j) - u‖
  have hβ : Tendsto (fun n => ξ * (l6ErrB S V (e n) g₀ (f n) +
      ‖l6Res S.R (l6W S.R j) - S.u g₀ (f n)‖)) atTop (𝓝 (ξ * η₀)) := by
    have : Tendsto (fun n => ‖l6Res S.R (l6W S.R j) - S.u g₀ (f n)‖) atTop (𝓝 η₀) :=
      (tendsto_const_nhds.sub hu).norm
    simpa using (herr.add this).const_mul ξ
  have hcmp : ∀ᶠ n in atTop, l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) d ≤
      ENNReal.ofReal (Real.exp (ξ * (l6ErrB S V (e n) g₀ (f n) +
        ‖l6Res S.R (l6W S.R j) - S.u g₀ (f n)‖))) * l6Bn ξ m e S g₀ n (f n) (d, j) := by
    filter_upwards [l6_eventually_act S.U₁.isOpen hd he] with n hn
    exact (l6_cmpB hξ S hn j (f n)).2
  refine le_trans ?_ ((l6_mul_le_mul_left (l6_sample_liminf hconv d)).trans
    (l6_le_liminf_of_cmp hβ hcmp))
  exact l6_mul_le_mul_right (l6_ofReal_exp_le
    (neg_le_neg (mul_le_mul_of_nonneg_left hη.le hξ)))

include hξ he hconv hsmall in
 
theorem l6_pathB_upper {g₀ : L6S → DistC}
    (herr : Tendsto (fun n => l6ErrB S V (e n) g₀ (f n)) atTop (𝓝 0)) {u : C(L6K S.R, ℝ)}
    (hu : Tendsto (fun n => S.u g₀ (f n)) atTop (𝓝 u)) (c₀ : L5Code) {m₀ : ℕ}
    (hd : l5Rect (l6Enlarge c₀ m₀).1 ⊆ (S.U₁ : Set ℂ)) (j : ℕ) {η : ℝ}
    (hη : ‖l6Res S.R (l6W S.R j) - u‖ < η) :
    limsup (fun n => l6Bn ξ m e S g₀ n (f n) (l6Enlarge c₀ m₀, j)) atTop ≤
      ENNReal.ofReal (Real.exp (ξ * η)) * l5Obs L (l6Enlarge c₀ (m₀ + 1)) := by
  set η₀ := ‖l6Res S.R (l6W S.R j) - u‖
  have hβ : Tendsto (fun n => ξ * (l6ErrB S V (e n) g₀ (f n) +
      ‖l6Res S.R (l6W S.R j) - S.u g₀ (f n)‖)) atTop (𝓝 (ξ * η₀)) := by
    have : Tendsto (fun n => ‖l6Res S.R (l6W S.R j) - S.u g₀ (f n)‖) atTop (𝓝 η₀) :=
      (tendsto_const_nhds.sub hu).norm
    simpa using (herr.add this).const_mul ξ
  have hcmp : ∀ᶠ n in atTop, l6Bn ξ m e S g₀ n (f n) (l6Enlarge c₀ m₀, j) ≤
      ENNReal.ofReal (Real.exp (ξ * (l6ErrB S V (e n) g₀ (f n) +
        ‖l6Res S.R (l6W S.R j) - S.u g₀ (f n)‖))) *
        l5Obs (normalizedLFPPMetric ξ (m (e n)) (V (e n) (f n))) (l6Enlarge c₀ m₀) := by
    filter_upwards [l6_eventually_act S.U₁.isOpen hd he] with n hn
    exact (l6_cmpB hξ S hn j (f n)).1
  refine (l6_limsup_le_of_cmp hβ hcmp).trans ?_
  refine (l6_mul_le_mul_left (l6_sample_sandwich hconv hsmall c₀ (Nat.lt_succ_self m₀)).1).trans ?_
  exact l6_mul_le_mul_right (l6_ofReal_exp_le (mul_le_mul_of_nonneg_left hη.le hξ))

end Sample

end SupercriticalLQGUniqueness.B2.PfeLocal
