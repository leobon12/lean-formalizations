import QuantumZipper.Proofs.Zipper.SWCoreB5Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B5 (5): the window sandwich for one map of the class, with map-independent errors

Task SWC-B5 (`handoff/SW-CORE.md`). For one map `ψ` of the class and one scale `k`, with a fixed
(map-independent) fine partition `(φ_n)` of the target interval, fixed window lattice and window
errors `ε₁`, the comparison integral `cmpInt` is squeezed between `c'_N⁻¹ Y_l` and `c_N⁻¹ Y_u`,
where `Y_u, Y_l` are within `2ων(K') + ε₁ |T| (‖f‖+ω)` of the target `∫ f ∘ Φ⁻¹ dν`. All error
terms depend only on the class data, `f` and the partition — this is what makes the transport
uniform over the class. The per-piece weights `F_n = f(t_n) ± ω` and window indices are chosen
from one point `t_n` of each piece (SW proof of Thm 4.2, p. 19; the partition of
`F1.tendsto_lintegral_bdryVarScale`, made map-independent). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

theorem abs_ofReal_sub_norm (s t : ℝ) : ‖(s : ℂ) - (t : ℂ)‖ = |s - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Per-map window sandwich.** -/
theorem perMap_sandwich {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) (hm : 0 < m)
    {a' b' a'' b'' : ℝ} (ha : a < a') (hb : b' < b) (ha'' : a' ≤ a'') (hb'' : b'' ≤ b')
    {δD CD : ℝ} (hD : CoordChange.Data ψ a' b' δD m CD) (hCD : 0 ≤ CD)
    (Φ : ℝ ≃o ℝ) (hΦ : ∀ t ∈ Icc a b, Φ t = (ψ t).re)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf0 : ∀ t, 0 ≤ f t)
    (hfs : ∀ t, f t ≠ 0 → t ∈ Icc a'' b'') {Fm : ℝ} (hFm : ∀ t, f t ≤ Fm)
    {d0 : ℝ} (hd0a : d0 ≤ a'' - a') (hd0b : d0 ≤ b' - b'')
    {ω δf : ℝ} (hω : 0 < ω) (hunif : ∀ s t : ℝ, |s - t| < δf → |f s - f t| ≤ ω)
    {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hhd : 2 * h ≤ m * d0)
    (hhf : 2 * h ≤ m * δf) (hhr : 2 * h ≤ m * CoordChange.Data.r0 δD m CD)
    (hhl : 4 * CD / m * (2 * h / m) ≤ Real.log 2 / (2 * N))
    {T : Finset ℤ} {φ : T → ℝ → ℝ} (hφc : ∀ n, Continuous (φ n))
    (hφs : ∀ n, HasCompactSupport (φ n)) (hφ0 : ∀ n u, 0 ≤ φ n u)
    (hφ1 : ∀ u ∈ Icc (-M) M, ∑ n, φ n u = 1) (hφle : ∀ u, ∑ n, φ n u ≤ 1)
    (hφsupp : ∀ n u, φ n u ≠ 0 → |u - ((n : ℤ) : ℝ) * h| < h)
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] {c c' : ℕ → ℝ} {ε₁ : ℝ} (hε₁ : 0 ≤ ε₁) {k : ℕ}
    (hk : ∀ n : T, ∀ i ∈ Finset.Icc ⌈-Real.log (max (4 * M / ρ) m) / (Real.log 2 / N) + 1 / 2⌉
        ⌈-Real.log m / (Real.log 2 / N) + 1 / 2⌉,
      ((Int.toNat ((k : ℤ) * N + i - 2) : ℕ) : ℤ) = (k : ℤ) * N + i - 2 ∧
      ENNReal.ofReal (c N) * ∫⁻ u, F1.bSupWin γ x N (Int.toNat ((k : ℤ) * N + i - 2)) u *
          ENNReal.ofReal (φ n u) ≤ ENNReal.ofReal ((∫ u, φ n u ∂ν) + ε₁) ∧
      ENNReal.ofReal ((∫ u, φ n u ∂ν) - ε₁) ≤ ENNReal.ofReal (c' N) *
        ∫⁻ u, F1.bInfWin γ x N (Int.toNat ((k : ℤ) * N + i - 2)) u * ENNReal.ofReal (φ n u)) :
    ∃ Yu Yl : ℝ,
      Yu ≤ (∫ u, f (Φ.symm u) ∂ν) + 2 * ω * ν.real (Icc (-M - 1) (M + 1)) +
        ε₁ * (T.card * (Fm + ω)) ∧
      (∫ u, f (Φ.symm u) ∂ν) - 2 * ω * ν.real (Icc (-M - 1) (M + 1)) -
        ε₁ * (T.card * (Fm + ω)) ≤ Yl ∧
      ENNReal.ofReal (c N) * cmpInt γ x ψ f a' b' k ≤ ENNReal.ofReal Yu ∧
      ENNReal.ofReal Yl ≤ ENNReal.ofReal (c' N) * cmpInt γ x ψ f a' b' k := by
  classical
  have hsubI : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha.le hb.le
  have hsub'' : Icc a'' b'' ⊆ Icc a' b' := Icc_subset_Icc ha'' hb''
  set lam := Real.log 2 / N with hlam
  set C1 := max (4 * M / ρ) m with hC1
  set ilo := ⌈-Real.log C1 / lam + 1 / 2⌉ with hilo
  set ihi := ⌈-Real.log m / lam + 1 / 2⌉ with hihi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam0 : 0 < lam := div_pos (Real.log_pos (by norm_num)) hNpos
  have hidx_mono : ∀ s, m ≤ s → s ≤ C1 → ⌈-Real.log s / lam + 1 / 2⌉ ∈ Finset.Icc ilo ihi := by
    intro s hs1 hs2
    have hs0 : 0 < s := hm.trans_le hs1
    rw [Finset.mem_Icc]
    constructor
    · apply Int.ceil_mono
      have := Real.log_le_log hs0 hs2
      have : -Real.log C1 / lam ≤ -Real.log s / lam :=
        div_le_div_of_nonneg_right (by linarith) hlam0.le
      linarith
    · apply Int.ceil_mono
      have := Real.log_le_log hm hs1
      have : -Real.log s / lam ≤ -Real.log m / lam :=
        div_le_div_of_nonneg_right (by linarith) hlam0.le
      linarith
  have hilo_mem : ilo ∈ Finset.Icc ilo ihi := hidx_mono C1 (le_max_right _ _) le_rfl
  have hre_bd : ∀ t ∈ Icc a b, (ψ t).re ∈ Icc (-M) M := by
    intro t ht
    have h1 := hψ.2.1 _ (self_subset_thickening hρ _ (ofReal_mem_segC ht))
    have h2 := Complex.abs_re_le_norm (ψ t)
    exact abs_le.1 (h2.trans h1)
  have hd_bd : ∀ t ∈ Icc a b, m ≤ ‖deriv ψ t‖ ∧ ‖deriv ψ t‖ ≤ C1 := fun t ht =>
    ⟨hψ.2.2.2.2 t ht, (norm_deriv_le_of_class' hψ hρ ht).trans (le_max_left _ _)⟩
  have hlip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, m * |s - t| ≤ |(ψ s).re - (ψ t).re| := by
    intro s hs t ht
    rcases le_total s t with hst | hst
    · have := mul_sub_le_re_sub_of_class hψ hρ hs ht hst
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ t - s), abs_sub_comm]
      exact this.trans (le_abs_self _)
    · have := mul_sub_le_re_sub_of_class hψ hρ ht hs hst
      rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      exact this.trans (le_abs_self _)
  have hpiece : ∀ n u v, φ n u ≠ 0 → φ n v ≠ 0 → |u - v| < 2 * h := by
    intro n u v hu hv
    have e1 := hφsupp n u hu
    have e2 := hφsupp n v hv
    have := abs_sub_le u (((n : ℤ) : ℝ) * h) v
    rw [abs_sub_comm (((n : ℤ) : ℝ) * h) v] at this
    linarith
  -- one point of each piece
  set P : T → Prop := fun n => ∃ t ∈ Icc a' b', φ n (ψ t).re ≠ 0 with hP
  set tn : T → ℝ := fun n => if hn : P n then hn.choose else a' with htn_def
  have htn : ∀ n, P n → tn n ∈ Icc a' b' ∧ φ n (ψ (tn n)).re ≠ 0 := by
    intro n hn
    simp only [htn_def, dif_pos hn]
    exact hn.choose_spec
  have hclose : ∀ n, P n → ∀ t ∈ Icc a' b', φ n (ψ t).re ≠ 0 → m * |t - tn n| < 2 * h := by
    intro n hn t ht h0
    obtain ⟨ht', h0'⟩ := htn n hn
    exact (hlip t (hsubI ht) (tn n) (hsubI ht')).trans_lt (hpiece n _ _ h0 h0')
  have hfclose : ∀ n, P n → ∀ t ∈ Icc a' b', φ n (ψ t).re ≠ 0 → |f t - f (tn n)| ≤ ω := by
    intro n hn t ht h0
    apply hunif
    have := hclose n hn t ht h0
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left hcon hm.le
    linarith
  have hwin : ∀ n, P n → ∀ t ∈ Icc a' b', φ n (ψ t).re ≠ 0 →
      (2 : ℝ) ^ (-((⌈-Real.log ‖deriv ψ (tn n)‖ / lam + 1 / 2⌉ : ℤ) : ℝ) / N) ≤ ‖deriv ψ t‖ ∧
      ‖deriv ψ t‖ ≤
        (2 : ℝ) ^ (-(((⌈-Real.log ‖deriv ψ (tn n)‖ / lam + 1 / 2⌉ : ℤ) : ℝ) - 2) / N) := by
    intro n hn t ht h0
    have hcl := hclose n hn t ht h0
    set R := |t - tn n| with hR
    have hR0 : 0 ≤ R := abs_nonneg _
    have hRr : R ≤ CoordChange.Data.r0 δD m CD := by
      by_contra hcon; push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hm; linarith
    have hRh : R ≤ 2 * h / m := by
      rw [le_div_iff₀ hm]; linarith
    have hlog := hD.abs_log_norm_deriv_sub_le ht hR0 hRr (p := (t : ℂ)) (q := ((tn n : ℝ) : ℂ))
      (mem_closedBall_self hR0)
      (by rw [mem_closedBall, Complex.dist_eq, abs_ofReal_sub_norm, abs_sub_comm])
    rw [abs_ofReal_sub_norm] at hlog
    have hl : |Real.log ‖deriv ψ t‖ - Real.log ‖deriv ψ (tn n)‖| ≤ Real.log 2 / (2 * N) := by
      refine hlog.trans (le_trans ?_ hhl)
      have : 0 ≤ 4 * CD / m := by positivity
      exact mul_le_mul_of_nonneg_left hRh this
    exact mem_win_index hN (hm.trans_le (hd_bd t (hsubI ht)).1) hl
  set idx : T → ℤ := fun n => if P n then ⌈-Real.log ‖deriv ψ (tn n)‖ / lam + 1 / 2⌉ else ilo
    with hidx
  have hidxI : ∀ n, idx n ∈ Finset.Icc ilo ihi := by
    intro n
    by_cases hn : P n
    · simp only [hidx, if_pos hn]
      obtain ⟨ht', -⟩ := htn n hn
      exact hidx_mono _ (hd_bd _ (hsubI ht')).1 (hd_bd _ (hsubI ht')).2
    · simp only [hidx, if_neg hn]; exact hilo_mem
  set J : T → ℕ := fun n => Int.toNat ((k : ℤ) * N + idx n - 2) with hJ
  have hJwin : ∀ n, P n → ∀ t ∈ Icc a' b', φ n (ψ t).re ≠ 0 →
      radius k * ‖deriv ψ t‖ ∈ Icc (winLo N (J n)) (winHi N (J n)) := by
    intro n hn t ht h0
    have hj : ((J n : ℕ) : ℤ) = (k : ℤ) * N + idx n - 2 := (hk n (idx n) (hidxI n)).1
    have hw := hwin n hn t ht h0
    have e : idx n = ⌈-Real.log ‖deriv ψ (tn n)‖ / lam + 1 / 2⌉ := by simp only [hidx, if_pos hn]
    rw [← e] at hw
    exact mem_win_of_scale hN hj hw
  set F : T → ℝ := fun n => if P n then f (tn n) + ω else 0 with hF
  set Fl : T → ℝ := fun n => if P n then max (f (tn n) - ω) 0 else 0 with hFl
  have hFm0 : 0 ≤ Fm := (hf0 0).trans (hFm 0)
  have hF0 : ∀ n, 0 ≤ F n := fun n => by
    simp only [hF]; split_ifs
    · linarith [hf0 (tn n)]
    · exact le_rfl
  have hFl0 : ∀ n, 0 ≤ Fl n := fun n => by
    simp only [hFl]; split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hFle : ∀ n, F n ≤ Fm + ω := fun n => by
    simp only [hF]; split_ifs
    · linarith [hFm (tn n)]
    · linarith
  have hFlle : ∀ n, Fl n ≤ Fm + ω := fun n => by
    simp only [hFl]; split_ifs
    · exact max_le (by linarith [hFm (tn n)]) (by linarith)
    · linarith
  -- the transported test function
  set g : ℝ → ℝ := fun u => f (Φ.symm u) with hg
  have hgc : Continuous g := hf.comp Φ.symm.continuous
  have hgs : HasCompactSupport g := hfc.comp_homeomorph Φ.symm.toHomeomorph
  have hgt : ∀ u, g u ≠ 0 → Φ.symm u ∈ Icc a'' b'' := fun u hu => hfs _ hu
  have hΦsymm : ∀ u, g u ≠ 0 → (ψ (Φ.symm u)).re = u := fun u hu => by
    rw [← hΦ _ (hsubI (hsub'' (hgt u hu)))]; simp
  have hmargin : ∀ n, P n → f (tn n) ≠ 0 → ∀ u, φ n u ≠ 0 →
      (ψ a').re < u ∧ u < (ψ b').re := by
    intro n hn hfn u hu
    obtain ⟨ht', h0'⟩ := htn n hn
    have htn'' := hfs _ hfn
    have hdu := hpiece n _ _ hu h0'
    have hab' : a' ≤ b' := ht'.1.trans ht'.2
    have ha1 := mul_sub_le_re_sub_of_class hψ hρ (hsubI ⟨le_rfl, hab'⟩) (hsubI ht') ht'.1
    have hb1 := mul_sub_le_re_sub_of_class hψ hρ (hsubI ht') (hsubI ⟨hab', le_rfl⟩) ht'.2
    have h3 : m * d0 ≤ m * (tn n - a') :=
      mul_le_mul_of_nonneg_left (by linarith [htn''.1]) hm.le
    have h4 : m * d0 ≤ m * (b' - tn n) :=
      mul_le_mul_of_nonneg_left (by linarith [htn''.2]) hm.le
    constructor <;> linarith [abs_lt.1 hdu]
  -- window bounds
  have hup := cmpInt_le_win (γ := γ) (N := N) (k := k) hx hψ hρ ha hb hf0 hφc hφ0 F J
    (fun t ht => hφ1 _ (hre_bd t (hsubI ht)))
    (fun t ht n h0 => by
      have hn : P n := ⟨t, ht, h0⟩
      refine ⟨?_, hJwin n hn t ht h0⟩
      simp only [hF, if_pos hn]
      have := hfclose n hn t ht h0
      linarith [(abs_le.1 this).2])
  have hlo := win_le_cmpInt (γ := γ) (N := N) (k := k) hx hψ hρ ha hb hf0 hφc hφ0 Fl hFl0 J
    hφle
    (fun n hpos u hu => by
      have hn : P n := by
        by_contra hn; simp only [hFl, if_neg hn] at hpos; exact lt_irrefl _ hpos
      simp only [hFl, if_pos hn] at hpos
      have hfn : f (tn n) ≠ 0 := by
        intro h0; rw [h0, zero_sub, max_eq_right (by linarith)] at hpos
        exact lt_irrefl _ hpos
      obtain ⟨h1, h2⟩ := hmargin n hn hfn u hu
      obtain ⟨ht', -⟩ := htn n hn
      have hab' : a' ≤ b' := ht'.1.trans ht'.2
      have hcont : ContinuousOn (fun t : ℝ => (ψ t).re) (Icc a' b') :=
        Complex.continuous_re.comp_continuousOn (hψ.1.continuousOn.comp
          Complex.continuous_ofReal.continuousOn fun t ht =>
            self_subset_thickening hρ _ (ofReal_mem_segC (hsubI ht)))
      exact intermediate_value_Icc hab' hcont ⟨h1.le, h2.le⟩)
    (fun t ht n h0 => by
      have hn : P n := ⟨t, ht, h0⟩
      refine ⟨?_, hJwin n hn t ht h0⟩
      simp only [hFl, if_pos hn]
      have := hfclose n hn t ht h0
      exact max_le (by linarith [(abs_le.1 this).1]) (hf0 t))
  -- deterministic bounds
  have hK : IsCompact (Icc (-M - 1) (M + 1)) := isCompact_Icc
  have hdu := det_upper (ν := ν) (F := F) (ω := ω) hφc hφs hφ0 hφle hF0 hgc hgs
    (fun u => hf0 _) hω.le hK
    (fun n u hu hpos => by
      have hn : P n := by
        by_contra hn; simp only [hF, if_neg hn] at hpos; exact lt_irrefl _ hpos
      obtain ⟨ht', h0'⟩ := htn n hn
      have hdu := hpiece n _ _ hu h0'
      have hM := hre_bd _ (hsubI ht')
      refine ⟨?_, ⟨by linarith [abs_lt.1 hdu, hM.1], by linarith [abs_lt.1 hdu, hM.2]⟩⟩
      simp only [hF, if_pos hn]
      by_cases hfn : f (tn n) = 0
      · rw [hfn]; linarith [hf0 (Φ.symm u)]
      obtain ⟨h1, h2⟩ := hmargin n hn hfn u hu
      have hab' : a' ≤ b' := ht'.1.trans ht'.2
      rw [← hΦ a' (hsubI ⟨le_rfl, hab'⟩)] at h1
      rw [← hΦ b' (hsubI ⟨hab', le_rfl⟩)] at h2
      have ht : Φ.symm u ∈ Icc a' b' :=
        ⟨(Φ.lt_symm_apply.2 h1).le, (Φ.symm_apply_lt.2 h2).le⟩
      have hre : (ψ (Φ.symm u)).re = u := by rw [← hΦ _ (hsubI ht)]; simp
      have h0 : φ n (ψ (Φ.symm u)).re ≠ 0 := by rw [hre]; exact hu
      have := hfclose n hn _ ht h0
      show f (tn n) + ω ≤ f (Φ.symm u) + 2 * ω
      linarith [(abs_le.1 this).1])
  have hdl := det_lower (ν := ν) (F := Fl) (ω := ω) hφc hφs hφ0 hFl0 hgc hgs hω.le hK
    (fun u hu => by
      have ht := hsub'' (hgt u hu)
      have hre := hΦsymm u hu
      have hM := hre_bd _ (hsubI ht)
      rw [hre] at hM
      refine ⟨hφ1 u hM, ⟨by linarith [hM.1], by linarith [hM.2]⟩, fun n hn0 => ?_⟩
      have h0 : φ n (ψ (Φ.symm u)).re ≠ 0 := by rw [hre]; exact hn0
      have hn : P n := ⟨_, ht, h0⟩
      simp only [hFl, if_pos hn]
      have := hfclose n hn _ ht h0
      show f (Φ.symm u) - 2 * ω ≤ max (f (tn n) - ω) 0
      exact le_max_of_le_left (by linarith [(abs_le.1 this).2]))
  -- assembly
  have hν0 : ∀ n, 0 ≤ ∫ u, φ n u ∂ν := fun n => integral_nonneg (hφ0 n)
  have hsF : ∑ n, F n ≤ T.card * (Fm + ω) := by
    calc ∑ n, F n ≤ ∑ _n : T, (Fm + ω) := Finset.sum_le_sum fun n _ => hFle n
      _ = T.card * (Fm + ω) := by simp; ring
  have hsFl : ∑ n, Fl n ≤ T.card * (Fm + ω) := by
    calc ∑ n, Fl n ≤ ∑ _n : T, (Fm + ω) := Finset.sum_le_sum fun n _ => hFlle n
      _ = T.card * (Fm + ω) := by simp; ring
  refine ⟨∑ n, F n * ((∫ u, φ n u ∂ν) + ε₁), ∑ n, Fl n * max ((∫ u, φ n u ∂ν) - ε₁) 0,
    ?_, ?_, ?_, ?_⟩
  · have e : ∑ n, F n * ((∫ u, φ n u ∂ν) + ε₁) =
        ∑ n, F n * (∫ u, φ n u ∂ν) + ε₁ * ∑ n, F n := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsF hε₁
    linarith
  · have e : ∑ n, Fl n * ((∫ u, φ n u ∂ν) - ε₁) =
        ∑ n, Fl n * (∫ u, φ n u ∂ν) - ε₁ * ∑ n, Fl n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    have h1 : ∑ n, Fl n * ((∫ u, φ n u ∂ν) - ε₁) ≤
        ∑ n, Fl n * max ((∫ u, φ n u ∂ν) - ε₁) 0 :=
      Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hFl0 n)
    rw [e] at h1
    have := mul_le_mul_of_nonneg_left hsFl hε₁
    linarith
  · calc ENNReal.ofReal (c N) * cmpInt γ x ψ f a' b' k ≤ ENNReal.ofReal (c N) *
          ∑ n, ENNReal.ofReal (F n) *
            ∫⁻ u, F1.bSupWin γ x N (J n) u * ENNReal.ofReal (φ n u) := by gcongr
      _ = ∑ n, ENNReal.ofReal (F n) * (ENNReal.ofReal (c N) *
            ∫⁻ u, F1.bSupWin γ x N (J n) u * ENNReal.ofReal (φ n u)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ ∑ n, ENNReal.ofReal (F n) * ENNReal.ofReal ((∫ u, φ n u ∂ν) + ε₁) :=
          Finset.sum_le_sum fun n _ => by gcongr; exact (hk n (idx n) (hidxI n)).2.1
      _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg fun n _ =>
            mul_nonneg (hF0 n) (add_nonneg (hν0 n) hε₁)]
          exact Finset.sum_congr rfl fun n _ => (ENNReal.ofReal_mul (hF0 n)).symm
  · calc ENNReal.ofReal (∑ n, Fl n * max ((∫ u, φ n u ∂ν) - ε₁) 0) =
          ∑ n, ENNReal.ofReal (Fl n) * ENNReal.ofReal ((∫ u, φ n u ∂ν) - ε₁) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun n _ =>
            mul_nonneg (hFl0 n) (le_max_right _ _)]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [ENNReal.ofReal_mul (hFl0 n), F1.ofReal_max_zero]
      _ ≤ ∑ n, ENNReal.ofReal (Fl n) * (ENNReal.ofReal (c' N) *
            ∫⁻ u, F1.bInfWin γ x N (J n) u * ENNReal.ofReal (φ n u)) :=
          Finset.sum_le_sum fun n _ => by gcongr; exact (hk n (idx n) (hidxI n)).2.2
      _ = ENNReal.ofReal (c' N) * ∑ n, ENNReal.ofReal (Fl n) *
            ∫⁻ u, F1.bInfWin γ x N (J n) u * ENNReal.ofReal (φ n u) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ _ := by gcongr

end SWCore
end QuantumZipper
