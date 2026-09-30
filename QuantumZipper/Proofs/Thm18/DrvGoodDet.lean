import QuantumZipper.Proofs.Thm18.DrvGoodDefs
import QuantumZipper.Proofs.RS.TraceHull
import QuantumZipper.Proofs.Thm18.G1PkgTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DRVGOOD: the certificate `Good` gives a good driver (deterministic)

For a continuous driver `W` with `W 0 = 0`, `Good W` implies `RS.RadialGood W`, injectivity of
the trace on `[0,∞)`, `η(t) ∈ ℍ` for `t > 0`, and `K_t = η(0,t]`. The Cauchy bound at rational
data extends to all data by continuity of `f̂_t(iy)` in `t` (`RS.continuousOn_fwdMapInv_mul_I`)
and in `y` (holomorphy, `RS.differentiableOn_fwdMapInv`); the uniform limit is the trace and is
continuous; the hull identity is Rohde–Schramm's deterministic step
(`RS.fwdHull_eq_trace_image_of_good`, Rohde–Schramm, Ann. Math. 161 (2005), Thm 6.1 proof)
with empty hull interiors from `CondV`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace QuantumZipper
namespace DrvGood

/-- A continuous function bounded on the rationals of `(a,b)` is bounded on `[a,b]`. -/
theorem le_of_rat_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (h : ∀ q : ℚ, a < q → (q : ℝ) < b → f q ≤ c) : ∀ t ∈ Icc a b, f t ≤ c := by
  have hcl : IsClosed (Icc a b ∩ f ⁻¹' Iic c) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ioo a b ∩ range ((↑) : ℚ → ℝ) ⊆ Icc a b ∩ f ⁻¹' Iic c := by
    rintro _ ⟨⟨h1, h2⟩, q, rfl⟩
    exact ⟨⟨h1.le, h2.le⟩, h q h1 h2⟩
  have hd : Ioo a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  intro t ht
  have h1 : t ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ht
  have h2 : t ∈ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) := by
    have := closure_mono hd h1
    rwa [closure_closure] at this
  exact (hcl.closure_subset_iff.2 hsub h2).2

variable {W : ℝ → ℝ}

theorem continuousOn_fwdMapInv_y (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    ContinuousOn (fun y : ℝ => fwdMapInv W t ((y : ℂ) * I)) s := by
  refine (RS.differentiableOn_fwdMapInv hW hW0 ht).continuousOn.comp
    (continuous_ofReal.mul continuous_const).continuousOn fun y hy => ?_
  show 0 < ((y : ℂ) * I).im
  rw [im_ofReal_mul_I]; exact hs hy

/-- Extension of a bound in the height variable from rational to real heights. -/
theorem ext_y (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {v : ℂ} {C δ c : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ 1 →
      ‖fwdMapInv W t (((q : ℝ) : ℂ) * I) - v‖ ≤ C * (q : ℝ) ^ δ + c) :
    ∀ y ∈ Ioc (0 : ℝ) 1, ‖fwdMapInv W t ((y : ℂ) * I) - v‖ ≤ C * y ^ δ + c := by
  intro y hy
  have hsub : Icc (y / 2) 1 ⊆ Ioi 0 := fun s hs => by
    simp only [mem_Ioi]; linarith [hs.1, hy.1]
  have hcont : ContinuousOn (fun s : ℝ => ‖fwdMapInv W t ((s : ℂ) * I) - v‖ - C * s ^ δ)
      (Icc (y / 2) 1) :=
    (((continuousOn_fwdMapInv_y hW hW0 ht hsub).sub continuousOn_const).norm).sub
      (continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ => Or.inr hδ))
  have := le_of_rat_Ioo (c := c) (by linarith [hy.2]) hcont
    (fun q h1 h2 => by
      have := h q (by linarith [hy.1]) h2.le
      linarith) y ⟨by linarith [hy.1], hy.2⟩
  linarith

/-- The rational Cauchy bound extends to all times in `[0,M]` and all heights in `(0,1]`. -/
theorem bound_all (hW : Continuous W) (hW0 : W 0 = 0) {δ : ℝ} (hδ : 0 ≤ δ) {C M : ℝ}
    (hM : 0 < M)
    (h : ∀ t y y' : ℚ, 0 ≤ (t : ℝ) → (t : ℝ) ≤ M → 0 < (y : ℝ) → (y : ℝ) ≤ 1 → 0 < (y' : ℝ) →
      (y' : ℝ) ≤ 1 → ‖fwdMapInv W (t : ℝ) (((y : ℝ) : ℂ) * I) -
        fwdMapInv W (t : ℝ) (((y' : ℝ) : ℂ) * I)‖ ≤ C * ((y : ℝ) ^ δ + (y' : ℝ) ^ δ)) :
    ∀ t ∈ Icc (0 : ℝ) M, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ y' ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t ((y : ℂ) * I) - fwdMapInv W t ((y' : ℂ) * I)‖ ≤ C * (y ^ δ + y' ^ δ) := by
  -- step 1: all times, rational heights
  have h1 : ∀ y y' : ℚ, 0 < (y : ℝ) → (y : ℝ) ≤ 1 → 0 < (y' : ℝ) → (y' : ℝ) ≤ 1 →
      ∀ t ∈ Icc (0 : ℝ) M, ‖fwdMapInv W t (((y : ℝ) : ℂ) * I) -
        fwdMapInv W t (((y' : ℝ) : ℂ) * I)‖ ≤ C * ((y : ℝ) ^ δ + (y' : ℝ) ^ δ) := by
    intro y y' hy hy1 hy' hy1'
    refine le_of_rat_Ioo hM
      (((RS.continuousOn_fwdMapInv_mul_I hW hW0 hy hM.le).sub
        (RS.continuousOn_fwdMapInv_mul_I hW hW0 hy' hM.le)).norm) ?_
    intro q hq1 hq2
    exact h q y y' hq1.le hq2.le hy hy1 hy' hy1'
  intro t ht y hy y' hy'
  -- step 2: real first height
  have h2 : ∀ q' : ℚ, 0 < (q' : ℝ) → (q' : ℝ) ≤ 1 → ‖fwdMapInv W t ((y : ℂ) * I) -
      fwdMapInv W t (((q' : ℝ) : ℂ) * I)‖ ≤ C * y ^ δ + C * (q' : ℝ) ^ δ := by
    intro q' hq' hq1'
    have := ext_y hW hW0 ht.1 (v := fwdMapInv W t (((q' : ℝ) : ℂ) * I)) (C := C)
      (c := C * (q' : ℝ) ^ δ) hδ (fun q hq hq1 => by
        have := h1 q q' hq hq1 hq' hq1' t ht
        linarith [mul_add C ((q : ℝ) ^ δ) ((q' : ℝ) ^ δ)]) y hy
    exact this
  -- step 3: real second height
  have := ext_y hW hW0 ht.1 (v := fwdMapInv W t ((y : ℂ) * I)) (C := C) (c := C * y ^ δ) hδ
    (fun q hq hq1 => by rw [norm_sub_rev]; linarith [h2 q hq hq1]) y' hy'
  rw [norm_sub_rev] at this
  linarith [mul_add C (y ^ δ) (y' ^ δ)]

theorem tendsto_rpow_one_div {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ δ) atTop (𝓝 0) := by
  have hc : Tendsto (fun y : ℝ => y ^ δ) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ δ)) :=
    (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto
  rw [Real.zero_rpow hδ.ne'] at hc
  exact hc.comp tendsto_one_div_add_atTop_nhds_zero_nat

/-- From the full Cauchy bound at a time `t ≥ 0`: the sequence and the radial limit converge to
the trace, with the Hölder rate. -/
theorem trace_bound {t : ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C) (h : ∀ y ∈ Ioc (0 : ℝ) 1, ∀ y' ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t ((y : ℂ) * I) - fwdMapInv W t ((y' : ℂ) * I)‖ ≤ C * (y ^ δ + y' ^ δ)) :
    Tendsto (aprx W t) atTop (𝓝 (trace W t)) ∧ trS W t = trace W t ∧
      (∀ y ∈ Ioc (0 : ℝ) 1, ‖fwdMapInv W t ((y : ℂ) * I) - trace W t‖ ≤ C * y ^ δ) ∧
      Tendsto (fun y : ℝ => fwdMapInv W t ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 (trace W t)) := by
  set yn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hyn
  have hyn0 : ∀ n, 0 < yn n := fun n => by simp only [hyn]; positivity
  have hyn1 : ∀ n, yn n ≤ 1 := fun n => by
    simp only [hyn]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmono : ∀ N n, N ≤ n → yn n ≤ yn N := fun N n hNn => by
    simp only [hyn]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hNn 1)
  have hlim0 := tendsto_rpow_one_div hδ
  have hcau : CauchySeq (aprx W t) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => C * (yn N ^ δ + yn N ^ δ)) (fun n m N hn hm => ?_)
      ?_
    · rw [dist_eq_norm]
      refine (h _ ⟨hyn0 n, hyn1 n⟩ _ ⟨hyn0 m, hyn1 m⟩).trans ?_
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC
      · exact Real.rpow_le_rpow (hyn0 n).le (hmono N n hn) hδ.le
      · exact Real.rpow_le_rpow (hyn0 m).le (hmono N m hm) hδ.le
    · have := (hlim0.add hlim0).const_mul C
      rw [add_zero, mul_zero] at this
      exact this
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcau
  have hb : ∀ y ∈ Ioc (0 : ℝ) 1, ‖fwdMapInv W t ((y : ℂ) * I) - p‖ ≤ C * y ^ δ := by
    intro y hy
    have h1 : Tendsto (fun n => ‖fwdMapInv W t ((y : ℂ) * I) - aprx W t n‖) atTop
        (𝓝 ‖fwdMapInv W t ((y : ℂ) * I) - p‖) := (tendsto_const_nhds.sub hp).norm
    have h2 : Tendsto (fun n => C * (y ^ δ + yn n ^ δ)) atTop (𝓝 (C * (y ^ δ + 0))) :=
      (tendsto_const_nhds.add hlim0).const_mul C
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => h y hy _ ⟨hyn0 n, hyn1 n⟩
  have hT := RS.tendsto_fwdMapInv_of_rpow_bound hδ hb
  have htr : trace W t = p := hT.limUnder_eq
  rw [htr]
  exact ⟨hp, hp.limUnder_eq, hb, hT⟩

/-- **The certificate gives a good driver.** -/
theorem good_spec (hW : Continuous W) (hW0 : W 0 = 0) (hG : Good W) :
    RS.RadialGood W ∧ InjOn (trace W) (Ici 0) ∧ (∀ t > (0 : ℝ), trace W t ∈ H) ∧
      ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t := by
  obtain ⟨⟨δq, hδq, hH⟩, hV, hI, hP⟩ := hG
  set δ : ℝ := (δq : ℝ) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact_mod_cast hδq
  -- the full Cauchy bound on `[0, N]`
  have hall : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ∀ y' ∈ Ioc (0 : ℝ) 1, ‖fwdMapInv W t ((y : ℂ) * I) - fwdMapInv W t ((y' : ℂ) * I)‖ ≤
        C * (y ^ δ + y' ^ δ) := by
    intro N
    obtain ⟨C, hC⟩ := hH (N + 1)
    refine ⟨C, Nat.cast_nonneg C, fun t ht y hy y' hy' => ?_⟩
    refine bound_all hW hW0 hδ.le (M := ((N + 1 : ℕ) : ℝ)) (by positivity)
      (fun t y y' ht0 htM hy0 hy1 hy0' hy1' => hC t y y' (by exact_mod_cast ht0)
        (by exact_mod_cast htM) (by exact_mod_cast hy0) (by exact_mod_cast hy1)
        (by exact_mod_cast hy0') (by exact_mod_cast hy1')) t ⟨ht.1, ?_⟩ y hy y' hy'
    have : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact ht.2.trans this
  have htb : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) N,
      Tendsto (aprx W t) atTop (𝓝 (trace W t)) ∧ trS W t = trace W t ∧
      (∀ y ∈ Ioc (0 : ℝ) 1, ‖fwdMapInv W t ((y : ℂ) * I) - trace W t‖ ≤ C * y ^ δ) ∧
      Tendsto (fun y : ℝ => fwdMapInv W t ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 (trace W t)) := by
    intro N
    obtain ⟨C, hC0, hC⟩ := hall N
    exact ⟨C, hC0, fun t ht => trace_bound hδ hC0 (hC t ht)⟩
  have hpt : ∀ t : ℝ, 0 ≤ t → trS W t = trace W t := fun t ht => by
    obtain ⟨C, -, hC⟩ := htb ⌈t⌉₊
    exact (hC t ⟨ht, Nat.le_ceil t⟩).2.1
  -- continuity of the trace
  have hcont : ContinuousOn (trace W) (Ici 0) := by
    refine RS.continuousOn_Ici_of_Icc fun N hN => ?_
    obtain ⟨C, hC0, hC⟩ := htb ⌈N⌉₊
    have hsub : Icc (0 : ℝ) N ⊆ Icc (0 : ℝ) ⌈N⌉₊ := Icc_subset_Icc le_rfl (Nat.le_ceil N)
    have hU : TendstoUniformlyOn (fun n t => aprx W t n) (trace W) atTop (Icc 0 N) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hl := (tendsto_rpow_one_div hδ).const_mul C
      rw [mul_zero] at hl
      filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn t ht
      rw [dist_comm, dist_eq_norm]
      have hy : (1 / ((n : ℝ) + 1)) ∈ Ioc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]⟩
      exact ((hC t (hsub ht)).2.2.1 _ hy).trans_lt hn
    refine hU.continuousOn (Eventually.frequently (Eventually.of_forall fun n => ?_))
    exact RS.continuousOn_fwdMapInv_mul_I hW hW0 (by positivity) hN
  -- the trace starts at `0`
  have h0 : trace W 0 = 0 := by
    obtain ⟨C, -, hC⟩ := htb 0
    have h1 := (hC 0 ⟨le_rfl, by simp⟩).2.2.2
    have h2 : Tendsto (fun y : ℝ => fwdMapInv W 0 ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
      have h3 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
        have h4 : Continuous fun y : ℝ => (y : ℂ) * I := continuous_ofReal.mul continuous_const
        convert (h4.tendsto 0).mono_left nhdsWithin_le_nhds using 2
        simp
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (by rw [im_ofReal_mul_I]; exact hy), hW0,
        ofReal_zero, add_zero]
    exact tendsto_nhds_unique h1 h2
  have hRG : RS.RadialGood W := by
    refine ⟨hW, hW0, h0, hcont, δ, hδ, fun N => ?_⟩
    obtain ⟨C, -, hC⟩ := htb N
    exact ⟨C, fun t ht y hy => (hC t ht).2.2.1 y hy⟩
  -- `ℍ`-valuedness
  have hHv : ∀ t > (0 : ℝ), trace W t ∈ H := by
    intro t ht
    obtain ⟨a, ha0, hat⟩ := exists_rat_btwn ht
    obtain ⟨b, htb', hb⟩ := exists_rat_btwn (lt_add_one t)
    obtain ⟨m, hm⟩ := hP a b (by exact_mod_cast ha0) (by exact_mod_cast hat.trans htb')
    have hab : (a : ℝ) < b := hat.trans htb'
    have hcIcc : ContinuousOn (fun u => -(trace W u).im) (Icc (a : ℝ) b) :=
      (continuous_im.comp_continuousOn (hcont.mono fun u hu => le_trans ha0.le hu.1)).neg
    have := le_of_rat_Ioo (c := -(1 / ((m : ℝ) + 1))) hab hcIcc (fun q hq1 hq2 => by
      have h1 := hm q (by exact_mod_cast hq1.le) (by exact_mod_cast hq2.le)
      rw [hpt q (by linarith)] at h1
      linarith) t ⟨hat.le, htb'.le⟩
    show 0 < (trace W t).im
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  -- injectivity
  have hsep : ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ < s₂ → trace W s₁ ≠ trace W s₂ := by
    intro s₁ s₂ h1 h12
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h12
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hq2
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (lt_add_one s₂)
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt h1 hq1
    obtain ⟨m, hm⟩ := hI 0 q r s le_rfl (by exact_mod_cast hq0) (by exact_mod_cast hr1)
      (by exact_mod_cast hr2.trans hs1)
    have hrs : (r : ℝ) < s := hr2.trans hs1
    have hr0 : (0 : ℝ) ≤ r := by linarith
    -- step over `v`
    have hv : ∀ u : ℚ, 0 < (u : ℝ) → (u : ℝ) < q →
        1 / ((m : ℝ) + 1) ≤ ‖trace W u - trace W s₂‖ := by
      intro u hu1 hu2
      have hc : ContinuousOn (fun v => -‖trace W u - trace W v‖) (Icc (r : ℝ) s) :=
        ((continuousOn_const.sub (hcont.mono fun v hv => le_trans hr0 hv.1)).norm).neg
      have := le_of_rat_Ioo (c := -(1 / ((m : ℝ) + 1))) hrs hc (fun v hv1 hv2 => by
        have h1 := hm u v (by exact_mod_cast hu1.le) (by exact_mod_cast hu2.le)
          (by exact_mod_cast hv1.le) (by exact_mod_cast hv2.le)
        rw [hpt u hu1.le, hpt v (by linarith)] at h1
        linarith) s₂ ⟨hr2.le, hs1.le⟩
      linarith
    have hc : ContinuousOn (fun u => -‖trace W u - trace W s₂‖) (Icc (0 : ℝ) q) :=
      (((hcont.mono fun u hu => hu.1).sub continuousOn_const).norm).neg
    have := le_of_rat_Ioo (c := -(1 / ((m : ℝ) + 1))) hq0 hc (fun u hu1 hu2 => by
      have := hv u hu1 hu2
      linarith) s₁ ⟨h1, hq1.le⟩
    intro he
    rw [he, sub_self, norm_zero] at this
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hinj : InjOn (trace W) (Ici 0) := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hsep a b ha h hab
    · exact hsep b a hb h hab.symm
  -- hulls
  have hhull : ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t := by
    intro t ht
    have hint : interior (fwdHull W t) = ∅ := by
      have hsub : interior (fwdHull W t) ⊆ fwdHull W ⌈t⌉₊ :=
        interior_subset.trans (fwdHull_mono.1 (Nat.le_ceil t))
      exact (isOpen_interior.measure_eq_zero_iff volume).1 (measure_mono_null hsub (hV _))
    refine RS.fwdHull_eq_trace_image_of_good hRG (fun s hs => ?_) ht hint
    rcases RS.trace_mem_fwdHull_or_real hW hW0 hs.le (hRG.tendsto hs.le) with h | h
    · exact h
    · exfalso
      have := hHv s hs
      rw [show trace W s ∈ H ↔ 0 < (trace W s).im from Iff.rfl, h] at this
      exact lt_irrefl _ this
  exact ⟨hRG, hinj, hHv, hhull⟩

end DrvGood
end QuantumZipper
