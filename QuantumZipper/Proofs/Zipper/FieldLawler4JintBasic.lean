import QuantumZipper.Proofs.Zipper.FieldLawler4WdReal
import QuantumZipper.Proofs.Zipper.FieldLawler3TopSep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-JINT (basic): real boundary values of `Z_t⁻¹` and half-discs at `±R`

Task FL4-JINT (Track A round 4). Tools for `FieldLawler4Jint.lean`:

* `fl4j_F_real`: on `ℝ` the boundary extension `F` of `Z_t⁻¹` takes values in `K_t ∪ ℝ`;
* `fl4j_pos_preimage` / `fl4j_neg_preimage`: a real `x` to the right (left) of every real point
  of `K = γ[0, t]` is `F u` for some `u > 0` (`u < 0`): follow `F` along `[0, M]` from
  `F 0 = γ(t) ∈ K` to `F M ≈ M` (bounded distortion), start after the last visit of `K` and use
  the intermediate value theorem;
* `fl4j_halfdisk`: if `±R ∈ closure Wd`, a half-disc of `B(0,R)` at `±R` lies in `Wd`.

Own elementary point-set arguments (Field–Lawler, EJP 20 (2015), p. 9, use the domain `Wd`
without comment).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4j_vert_tendsto (u : ℝ) :
    Tendsto (fun s : ℝ => (u : ℂ) + s * I) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
  have : Tendsto (fun s : ℝ => (u : ℂ) + s * I) (𝓝 0) (𝓝 ((u : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
    (continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

lemma fl4j_vert_mem {u s : ℝ} (hs : 0 < s) : (u : ℂ) + s * I ∈ H := by
  show 0 < ((u : ℂ) + s * I).im
  simpa using hs

lemma fl4j_F_vert (hc : SideCtx W t F) (u : ℝ) :
    Tendsto (fun s : ℝ => F ((u : ℂ) + s * I)) (𝓝[>] 0) (𝓝 (F u)) := by
  refine (hc.Fcont _ (show (0 : ℝ) ≤ (u : ℂ).im by simp)).tendsto.comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨fl4j_vert_tendsto u, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact le_of_lt (show (0 : ℝ) < ((u : ℂ) + s * I).im from fl4j_vert_mem hs)

/-- On `ℝ`, `F` takes values in `K_t ∪ ℝ`. -/
lemma fl4j_F_real (hc : SideCtx W t F) (u : ℝ) : F u ∈ fwdHull W t ∨ (F u).im = 0 := by
  have hT := fl4j_F_vert hc u
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, F ((u : ℂ) + s * I) ∈ H \ fwdHull W t := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact hc.F_mem_dom (fl4j_vert_mem hs)
  have him : 0 ≤ (F u).im := by
    have : Tendsto (fun s : ℝ => (F ((u : ℂ) + s * I)).im) (𝓝[>] 0) (𝓝 (F u).im) :=
      (continuous_im.tendsto _).comp hT
    exact ge_of_tendsto this (hev.mono fun s hs => le_of_lt (show (0 : ℝ) < _ from hs.1))
  by_contra hne
  push Not at hne
  have hD : F u ∈ H \ fwdHull W t := ⟨lt_of_le_of_ne him (Ne.symm hne.2), hne.1⟩
  have hZ : ContinuousAt (fwdMap W t) (F u) :=
    hc.continuousOn_fwdMap.continuousAt (hc.isOpen_dom.mem_nhds hD)
  have h1 : Tendsto (fun s : ℝ => fwdMap W t (F ((u : ℂ) + s * I))) (𝓝[>] 0)
      (𝓝 (fwdMap W t (F u))) := hZ.tendsto.comp hT
  have h2 : Tendsto (fun s : ℝ => fwdMap W t (F ((u : ℂ) + s * I))) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
    refine (fl4j_vert_tendsto u).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact (hc.fwdMap_F (fl4j_vert_mem hs)).symm
  have he := tendsto_nhds_unique h1 h2
  have h3 : (0 : ℝ) < (fwdMap W t (F u)).im := hc.mapsTo hD
  rw [he] at h3
  simp at h3

lemma fl4j_F_bound (hc : SideCtx W t F) {C : ℝ} (hC : ∀ u ∈ H, ‖F u - u‖ ≤ C) (u : ℝ) :
    ‖F u - u‖ ≤ C := by
  have hT : Tendsto (fun s : ℝ => ‖F ((u : ℂ) + s * I) - ((u : ℂ) + s * I)‖) (𝓝[>] 0)
      (𝓝 ‖F u - u‖) :=
    (continuous_norm.tendsto _).comp ((fl4j_F_vert hc u).sub (fl4j_vert_tendsto u))
  refine le_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact hC _ (fl4j_vert_mem hs)

/-- Intermediate value step: after the last visit of the closed set `K`, a path which ends to
the right of `x` and is real off `K` passes through `x`. -/
lemma fl4j_ivt {g : ℝ → ℂ} {M x : ℝ} {K : Set ℂ} (hK : IsClosed K) (hM : 0 ≤ M)
    (hg : ContinuousOn g (Icc 0 M)) (hg0 : g 0 ∈ K)
    (hgK : ∀ u ∈ Icc 0 M, g u ∈ K ∨ (g u).im = 0)
    (hKx : ∀ z ∈ K, z.im = 0 → z.re < x) (hgM : x < (g M).re) (hgMK : g M ∉ K) :
    ∃ u ∈ Ioc 0 M, g u = x := by
  set T := Icc 0 M ∩ g ⁻¹' K
  have hT : IsClosed T := hg.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hTne : T.Nonempty := ⟨0, ⟨le_rfl, hM⟩, hg0⟩
  have hTb : BddAbove T := ⟨M, fun u hu => hu.1.2⟩
  set u₁ := sSup T
  have hu₁ : u₁ ∈ T := hT.csSup_mem hTne hTb
  have hu₁M : u₁ < M := lt_of_le_of_ne hu₁.1.2 fun e => hgMK (e ▸ hu₁.2)
  have hsub : Icc u₁ M ⊆ Icc 0 M := Icc_subset_Icc_left hu₁.1.1
  have hreal : ∀ u ∈ Ioc u₁ M, (g u).im = 0 := fun u hu =>
    (hgK u (hsub (Ioc_subset_Icc_self hu))).resolve_left fun h =>
      absurd (le_csSup hTb ⟨hsub (Ioc_subset_Icc_self hu), h⟩) (not_le.2 hu.1)
  have him₁ : (g u₁).im = 0 := by
    have hcl : IsClosed (Icc u₁ M ∩ (fun u => (g u).im) ⁻¹' {0}) :=
      (continuous_im.comp_continuousOn (hg.mono hsub)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have h1 : Ioc u₁ M ⊆ Icc u₁ M ∩ (fun u => (g u).im) ⁻¹' {0} := fun u hu =>
      ⟨Ioc_subset_Icc_self hu, hreal u hu⟩
    have h2 := closure_minimal h1 hcl
    rw [closure_Ioc hu₁M.ne] at h2
    exact (h2 ⟨le_rfl, hu₁M.le⟩).2
  have hlt : (g u₁).re < x := hKx _ hu₁.2 him₁
  obtain ⟨u, hu, hux⟩ := intermediate_value_Icc hu₁M.le
    (continuous_re.comp_continuousOn (hg.mono hsub)) ⟨hlt.le, hgM.le⟩
  have hux' : (g u).re = x := hux
  have hu' : u ∈ Ioc u₁ M := ⟨lt_of_le_of_ne hu.1 fun e => by
    rw [← e] at hux'; exact hlt.ne hux', hu.2⟩
  refine ⟨u, ⟨lt_of_le_of_lt hu₁.1.1 hu'.1, hu.2⟩, Complex.ext ?_ ?_⟩
  · simpa using hux'
  · simpa using hreal u hu'

lemma fl4j_hull_sub (hc : SideCtx W t F) : fwdHull W t ⊆ trace W '' Icc 0 t := by
  rw [hc.hull]; exact image_mono Ioc_subset_Icc_self

lemma fl4j_K_closed (hc : SideCtx W t F) : IsClosed (trace W '' Icc 0 t) :=
  (isCompact_Icc.image_of_continuousOn hc.trCont).isClosed

lemma fl4j_tip_mem (hc : SideCtx W t F) : trace W t ∈ trace W '' Icc 0 t :=
  ⟨t, ⟨hc.tpos.le, le_rfl⟩, rfl⟩

lemma fl4j_F_cont (hc : SideCtx W t F) (M : ℝ) : ContinuousOn (fun u : ℝ => F u) (Icc 0 M) :=
  hc.Fcont.comp continuous_ofReal.continuousOn fun u _ => show (0 : ℝ) ≤ (u : ℂ).im by simp

/-- A real `x` to the right of all real points of `K` is `F u` for some `u > 0`. -/
lemma fl4j_pos_preimage (hc : SideCtx W t F) {R x : ℝ}
    (hKR : ∀ z ∈ trace W '' Icc 0 t, ‖z‖ ≤ R)
    (hKx : ∀ z ∈ trace W '' Icc 0 t, z.im = 0 → z.re < x) : ∃ u : ℝ, 0 < u ∧ F u = x := by
  obtain ⟨C, hC⟩ := hc.bound
  set M : ℝ := |R| + |C| + |x| + 1
  have hMdef : M = |R| + |C| + |x| + 1 := rfl
  have hM : 0 ≤ M := by positivity
  have hFM := fl4j_F_bound hc hC M
  have h2 : |(F M).re - M| ≤ |C| := by
    have := (abs_re_le_norm (F M - M)).trans (hFM.trans (le_abs_self C))
    simpa using this
  have hre := (abs_le.1 h2).1
  have hRx : R ≤ |R| := le_abs_self R
  have hxx : x ≤ |x| := le_abs_self x
  have hx0 := abs_nonneg x
  have hR0 := abs_nonneg R
  obtain ⟨u, hu, hux⟩ := fl4j_ivt (g := fun u : ℝ => F u) (fl4j_K_closed hc) hM (fl4j_F_cont hc M)
    (by show F ((0 : ℝ) : ℂ) ∈ _; rw [ofReal_zero, hc.F0]; exact fl4j_tip_mem hc)
    (fun u _ => (fl4j_F_real hc u).imp_left fun h => fl4j_hull_sub hc h) hKx
    (by show x < (F M).re; linarith)
    (fun h => by
      have h1 := hKR _ h
      have h3 := (le_abs_self (F M).re).trans (abs_re_le_norm (F M))
      change ‖F M‖ ≤ R at h1
      linarith)
  exact ⟨u, hu.1, hux⟩

/-- A real `x` to the left of all real points of `K` is `F u` for some `u < 0`. -/
lemma fl4j_neg_preimage (hc : SideCtx W t F) {R x : ℝ}
    (hKR : ∀ z ∈ trace W '' Icc 0 t, ‖z‖ ≤ R)
    (hKx : ∀ z ∈ trace W '' Icc 0 t, z.im = 0 → x < z.re) : ∃ u : ℝ, u < 0 ∧ F u = x := by
  obtain ⟨C, hC⟩ := hc.bound
  set M : ℝ := |R| + |C| + |x| + 1
  have hMdef : M = |R| + |C| + |x| + 1 := rfl
  have hM : 0 ≤ M := by positivity
  have hFM := fl4j_F_bound hc hC (-M)
  have h2 : |(F ((-M : ℝ) : ℂ)).re + M| ≤ |C| := by
    have := (abs_re_le_norm (F ((-M : ℝ) : ℂ) - ((-M : ℝ) : ℂ))).trans (hFM.trans (le_abs_self C))
    simpa using this
  have hre := (abs_le.1 h2).2
  have hRx : R ≤ |R| := le_abs_self R
  have hxx : -x ≤ |x| := neg_le_abs x
  have hx0 := abs_nonneg x
  have hR0 := abs_nonneg R
  set K : Set ℂ := (fun z : ℂ => -z) ⁻¹' (trace W '' Icc 0 t)
  have hK : IsClosed K := (fl4j_K_closed hc).preimage continuous_neg
  have hgc : ContinuousOn (fun u : ℝ => -F ((-u : ℝ) : ℂ)) (Icc 0 M) := by
    refine (hc.Fcont.comp (continuous_ofReal.comp continuous_neg).continuousOn
      fun u _ => show (0 : ℝ) ≤ ((-u : ℝ) : ℂ).im by simp).neg
  obtain ⟨u, hu, hux⟩ := fl4j_ivt (g := fun u : ℝ => -F ((-u : ℝ) : ℂ)) (x := -x) hK hM hgc
    (by
      show -(-F ((-(0 : ℝ) : ℝ) : ℂ)) ∈ trace W '' Icc 0 t
      rw [neg_neg, neg_zero, ofReal_zero, hc.F0]; exact fl4j_tip_mem hc)
    (fun u _ => (fl4j_F_real hc (-u)).imp
      (fun h => show -(-F ((-u : ℝ) : ℂ)) ∈ trace W '' Icc 0 t by
        rw [neg_neg]; exact fl4j_hull_sub hc h)
      (fun h => by show (-F ((-u : ℝ) : ℂ)).im = 0; rw [neg_im, h, neg_zero]))
    (fun z hz hzi => by
      have := hKx (-z) hz (by rw [neg_im, hzi, neg_zero])
      rw [neg_re] at this; linarith)
    (by show -x < (-F ((-M : ℝ) : ℂ)).re; rw [neg_re]; linarith)
    (fun h => by
      have h1 := hKR _ h
      change ‖-(-F ((-M : ℝ) : ℂ))‖ ≤ R at h1
      rw [neg_neg] at h1
      have h4 := abs_re_le_norm (F ((-M : ℝ) : ℂ))
      have h5 := neg_le_abs (F ((-M : ℝ) : ℂ)).re
      linarith)
  refine ⟨-u, by linarith [hu.1], ?_⟩
  have := congrArg Neg.neg hux
  simpa using this

/-- **Half-disc at `±R`.** If `c = ±R` is in `closure Wd`, a half-disc of `B(0,R)` at `c` lies in
`Wd`, and `K = γ[0,t]` stays at distance `≥ ρ` from `c`. -/
lemma fl4j_halfdisk (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hH : trace W t ∈ H) {p₀ : ℂ} {c : ℝ}
    (hcR : |c| = R) (hcW : (c : ℂ) ∈ closure (fl4Wd W t R ε α β p₀)) :
    ∃ ρ > 0, (∀ z ∈ ball (c : ℂ) ρ, z ∈ ball (0 : ℂ) R → 0 < z.im →
      z ∈ fl4Wd W t R ε α β p₀) ∧ ∀ z ∈ trace W '' Icc 0 t, ρ ≤ ‖z - c‖ := by
  set Kc : Set ℂ := trace W '' Icc 0 t ∪ closure (flCircArc ε α β)
  have hKc : IsClosed Kc := (fl4j_K_closed hc).union isClosed_closure
  have hcn : ‖(c : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, hcR]
  have hxK : (c : ℂ) ∉ Kc := by
    rintro (⟨s, hs, hsc⟩ | h)
    · rcases hs.2.lt_or_eq with h' | h'
      · have := hlt s ⟨hs.1, h'⟩
        rw [hsc, hcn] at this; exact lt_irrefl _ this
      · have : (0 : ℝ) < (trace W t).im := hH
        rw [← h', hsc] at this; simp at this
    · have := fl4_closure_arc_subset h
      rw [mem_sphere_zero_iff_norm, abs_of_pos hε, hcn] at this
      exact hεR.ne this.symm
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl _ hxK
  refine ⟨ρ, hρ, fun z hz hzR hzi => ?_, fun z hz => ?_⟩
  · set V := ball (c : ℂ) ρ ∩ ball 0 R ∩ {w : ℂ | 0 < w.im}
    have hdom : V ⊆ fl4WdDom W t R ε α β := by
      intro w hw
      have hwK := hρK hw.1.1
      refine ⟨⟨hw.2, hw.1.2⟩, ?_⟩
      rintro (h | h)
      · exact hwK (Or.inl (fl4j_hull_sub hc h))
      · exact hwK (Or.inr h)
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 hcW _ (ball_mem_nhds _ hρ)
    have hVc : IsPreconnected V :=
      (((convex_ball _ ρ).inter (convex_ball 0 R)).inter
        (convex_halfSpace_im_gt (r := 0))).isPreconnected
    have hsub := hVc.subset_connectedComponentIn
      ⟨⟨hw1, fl4wd_subset_ball hw2⟩, (fl4wd_subset_D hw2).1⟩ hdom
    rw [← connectedComponentIn_eq hw2] at hsub
    exact hsub ⟨⟨hz, hzR⟩, hzi⟩
  · by_contra hlt'
    push Not at hlt'
    exact hρK (by rw [mem_ball, dist_eq_norm]; exact hlt') (Or.inl hz)

end FieldLawler
end QuantumZipper
