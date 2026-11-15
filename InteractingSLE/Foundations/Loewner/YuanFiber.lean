import InteractingSLE.Foundations.Topology.PathComplement
import QuantumZipper.Proofs.Complex.BasicsReflection

/-!
# Fibres of boundary extensions of conformal maps (input to [Yua22])

Packet GEO-YUAN of `planning/INFRA-GEO.md` §4. Let `F` be continuous on `ℍ̄`, holomorphic and
injective on `ℍ`, and suppose that `F` maps no real point into `F(ℍ)` (true for the continuous
extension of a conformal map of `ℍ` onto a domain,
`exists_continuousOn_extension_of_path_of_tendsto`).
The fibres of such an `F` are very thin:

* `exists_ne_of_injOn`: `F` is not constant on any nondegenerate real interval (Schwarz reflection
  and the identity theorem). This is the elementary form of the fact used in Y. Yuan,
  *Topological characterisations of Loewner traces*, Indiana Univ. Math. J. 71 (2022),
  arXiv:2003.05535v4 ([Yua22]) §2.1, that the preimage of a boundary point has measure zero
  ([Pom] Theorem 1.7); only "no interval" is ever used.
* `subsingleton_of_isPreconnected_of_forall_eq`: a preconnected subset of `ℍ̄` on which `F` is
  constant has at most one point.
* `exists_tendsto_of_tendsto_comp`: **cluster-set lemma.** If `G : ℍ → ℍ̄` is continuous and
  bounded near `x` and `F ∘ G` has a limit at `x`, then `G` itself has a limit at `x`. This is the
  device by which [Yua22] §2.1 shows that the limit points of `γ_t` at a time form a single point
  or a null subset of `ℝ`; the connectedness of the cluster set is replaced by an
  intermediate-value argument on a vertical line.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar)

namespace InteractingSLE

/-- The real line inside `ℂ`. -/
theorem mem_Hbar_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z ∈ Hbar := by
  show 0 ≤ z.im
  rw [hz]

theorem H_subset_Hbar : H ⊆ Hbar := fun z hz => show 0 ≤ z.im from le_of_lt (show 0 < z.im from hz)

theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

/-- **No interval in a fibre.** A function continuous on `ℍ̄`, holomorphic and injective on `ℍ`, is
not constant on any nondegenerate real interval: by Schwarz reflection `F − c` would extend
holomorphically across the interval with zeros accumulating there, hence vanish near it, against
injectivity. -/
theorem exists_ne_of_injOn {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) (hc : ContinuousOn F Hbar)
    (hinj : InjOn F H) {a b : ℝ} (hab : a < b) (c : ℂ) : ∃ m ∈ Ioo a b, F m ≠ c := by
  by_contra hcon
  push Not at hcon
  set x : ℝ := (a + b) / 2 with hx
  set r : ℝ := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set g : ℂ → ℂ := fun z => F z - c with hg
  have hreal_mem : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → z.re ∈ Ioo a b := by
    intro z hz hzim
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |z.re - x| < r := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    rw [abs_lt] at h1
    constructor <;> linarith
  have hgd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r) :=
    (hd.sub (differentiableOn_const c)).mono inter_subset_left
  have hgc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r) :=
    (hc.sub continuousOn_const).mono inter_subset_left
  have hgreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → g z = 0 := by
    intro z hz hzim
    have hzr := hreal_mem z hz hzim
    have hze := eq_ofReal_re_of_im_eq_zero hzim
    simp only [hg]
    rw [hze, hcon _ hzr, sub_self]
  obtain ⟨G, hGd, hGeq, -⟩ := QuantumZipper.CA.exists_reflection_extension hgd hgc
    (fun z hz hzim => by rw [hgreal z hz hzim, Complex.zero_im])
  have hGa : AnalyticOnNhd ℂ G (ball (x : ℂ) r) := hGd.analyticOnNhd isOpen_ball
  have hx0 : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr0
  -- zeros of `G` accumulate at `x` along the real axis
  have hfreq : ∃ᶠ z in 𝓝[≠] (x : ℂ), G z = 0 := by
    have hT : Tendsto (fun ε : ℝ => ((x + ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => ((x + ε : ℝ) : ℂ)) (𝓝 0) (𝓝 ((x + 0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
        intro h
        have : ε = 0 := by linarith
        exact (ne_of_gt hε) this
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ((x + ε : ℝ) : ℂ) = 0 := by
      have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < r :=
        nhdsWithin_le_nhds (eventually_lt_nhds hr0)
      filter_upwards [hlt, self_mem_nhdsWithin] with ε hεr hε0
      have hmem : ((x + ε : ℝ) : ℂ) ∈ ball (x : ℂ) r := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show x + ε - x = ε by ring, abs_of_pos hε0]
        exact hεr
      have hHb : ((x + ε : ℝ) : ℂ) ∈ Hbar ∩ ball (x : ℂ) r :=
        ⟨mem_Hbar_of_im_eq_zero (Complex.ofReal_im _), hmem⟩
      rw [hGeq hHb]
      exact hgreal _ hmem (Complex.ofReal_im _)
    exact hT.frequently hev.frequently
  have hzero := hGa.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected hx0 hfreq
  -- two distinct points of `ℍ ∩ B(x, r)` where `F = c`
  set p₁ : ℂ := (x : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hp₁
  set p₂ : ℂ := (x : ℂ) + ((r / 4 : ℝ) : ℂ) * I with hp₂
  have hmemH : ∀ s : ℝ, 0 < s → s < r → ((x : ℂ) + (s : ℂ) * I) ∈ H ∩ ball (x : ℂ) r := by
    intro s hs hsr
    refine ⟨?_, ?_⟩
    · show 0 < ((x : ℂ) + (s : ℂ) * I).im
      simpa using hs
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hs]
      exact hsr
  have hFc : ∀ s : ℝ, 0 < s → s < r → F ((x : ℂ) + (s : ℂ) * I) = c := by
    intro s hs hsr
    have hm := hmemH s hs hsr
    have h1 : G ((x : ℂ) + (s : ℂ) * I) = 0 := hzero hm.2
    rw [hGeq ⟨H_subset_Hbar hm.1, hm.2⟩] at h1
    simpa [hg, sub_eq_zero] using h1
  have hq₁ := hmemH (r / 2) (by positivity) (by linarith)
  have hq₂ := hmemH (r / 4) (by positivity) (by linarith)
  have heq : F p₁ = F p₂ := by
    rw [hp₁, hp₂, hFc _ (by positivity) (by linarith), hFc _ (by positivity) (by linarith)]
  have := hinj hq₁.1 hq₂.1 heq
  rw [add_right_inj] at this
  have h2 := congrArg Complex.im this
  simp at h2
  linarith

/-- **Connected subsets of a fibre are points.** Let `F` be continuous on `ℍ̄`, holomorphic and
injective on `ℍ`, mapping no real point into `F(ℍ)`. A preconnected subset of `ℍ̄` on which `F` is
constant has at most one point. -/
theorem subsingleton_of_isPreconnected_of_forall_eq {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H)
    (hc : ContinuousOn F Hbar) (hinj : InjOn F H) (hR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H)
    {C : Set ℂ} (hC : IsPreconnected C) (hCH : C ⊆ Hbar) {c : ℂ} (hFC : ∀ z ∈ C, F z = c) :
    C.Subsingleton := by
  by_cases hcD : c ∈ F '' H
  · have hCH' : C ⊆ H := by
      intro z hz
      by_contra hzH
      have hz0 : z.im = 0 :=
        le_antisymm (not_lt.1 hzH) (show 0 ≤ z.im from hCH hz)
      exact hR z hz0 (hFC z hz ▸ hcD)
    intro z₁ h₁ z₂ h₂
    exact hinj (hCH' h₁) (hCH' h₂) ((hFC z₁ h₁).trans (hFC z₂ h₂).symm)
  · have hC0 : ∀ z ∈ C, z.im = 0 := by
      intro z hz
      by_contra hne
      have hzH : z ∈ H :=
        show 0 < z.im from lt_of_le_of_ne (show 0 ≤ z.im from hCH hz) (Ne.symm hne)
      exact hcD ⟨z, hzH, hFC z hz⟩
    have hre : IsPreconnected (Complex.re '' C) :=
      hC.image _ Complex.continuous_re.continuousOn
    have key : ∀ z₁ ∈ C, ∀ z₂ ∈ C, z₁.re < z₂.re → False := by
      intro z₁ h₁ z₂ h₂ hlt
      obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hd hc hinj hlt c
      obtain ⟨z, hz, hzm⟩ := hre.Icc_subset (mem_image_of_mem _ h₁) (mem_image_of_mem _ h₂)
        (Ioo_subset_Icc_self hm)
      have hzeq : z = (m : ℂ) := by rw [eq_ofReal_re_of_im_eq_zero (hC0 z hz), hzm]
      exact hFm (hzeq ▸ hFC z hz)
    intro z₁ h₁ z₂ h₂
    rcases lt_trichotomy z₁.re z₂.re with h | h | h
    · exact (key z₁ h₁ z₂ h₂ h).elim
    · exact Complex.ext h ((hC0 z₁ h₁).trans (hC0 z₂ h₂).symm)
    · exact (key z₂ h₂ z₁ h₁ h).elim

theorem isClosed_Hbar : IsClosed Hbar :=
  isClosed_le continuous_const Complex.continuous_im

theorem convex_H : Convex ℝ H :=
  convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0

/-- A cluster point of `G` (with values eventually in `ℍ̄`) is mapped by `F` to the limit of
`F ∘ G`. -/
theorem eq_of_mapClusterPt {α : Type*} {F : ℂ → ℂ} {G : α → ℂ} (hc : ContinuousOn F Hbar)
    {l : Filter α}
    (hGl : ∀ᶠ w in l, G w ∈ Hbar) {v : ℂ} (hFG : Tendsto (fun w => F (G w)) l (𝓝 v)) {ξ : ℂ}
    (hξ : ξ ∈ Hbar) (hcl : MapClusterPt ξ l G) : F ξ = v := by
  have h1 : Tendsto F (𝓝 ξ ⊓ map G l) (𝓝 (F ξ)) :=
    (hc ξ hξ).tendsto.mono_left (inf_le_inf_left _ (tendsto_principal.2 hGl))
  have h2 : MapClusterPt (F ξ) l (F ∘ G) := hcl.tendsto_comp' h1
  have h3 : ClusterPt (F ξ) (𝓝 v) := ClusterPt.mono h2 hFG
  by_contra hne
  exact h3.ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))

/-- **Cluster-set lemma.** Let `F` be continuous on `ℍ̄`, holomorphic and injective on `ℍ`,
mapping no real point into `F(ℍ)`, and let `G` be continuous on `ℍ` with values in `ℍ̄`, bounded
near `x ∈ ℍ̄`. If `F ∘ G` has a limit `v` at `x` (within `ℍ`), then so has `G`, and its limit lies
in the fibre of `v`. -/
theorem exists_tendsto_of_tendsto_comp {F G : ℂ → ℂ} (hd : DifferentiableOn ℂ F H)
    (hc : ContinuousOn F Hbar) (hinj : InjOn F H) (hR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H)
    {x : ℂ} (hx : x ∈ Hbar) (hGc : ContinuousOn G H) (hGH : MapsTo G H Hbar) {R : ℝ}
    (hGR : ∀ᶠ w in 𝓝[H] x, ‖G w‖ ≤ R) {v : ℂ}
    (hFG : Tendsto (fun w => F (G w)) (𝓝[H] x) (𝓝 v)) :
    ∃ ξ ∈ Hbar, F ξ = v ∧ Tendsto G (𝓝[H] x) (𝓝 ξ) := by
  set l : Filter ℂ := 𝓝[H] x with hl
  have hxcl : x ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hx
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxcl
  set s : Set ℂ := closedBall 0 R ∩ Hbar with hs
  have hsc : IsCompact s := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hlH : ∀ᶠ w in l, w ∈ H := self_mem_nhdsWithin
  have hmem : ∀ᶠ w in l, G w ∈ s := by
    filter_upwards [hGR, hlH] with w hwR hwH
    exact ⟨mem_closedBall_zero_iff.2 hwR, hGH hwH⟩
  have hmemHbar : ∀ᶠ w in l, G w ∈ Hbar := hmem.mono fun _ h => h.2
  -- every cluster point lies in the fibre of `v`
  have hfib : ∀ ξ ∈ s, MapClusterPt ξ l G → F ξ = v := fun ξ hξ hcl =>
    eq_of_mapClusterPt hc hmemHbar hFG hξ.2 hcl
  obtain ⟨ξ₀, hξ₀s, hξ₀⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 hmem)
  -- the cluster point is unique
  have huniq : ∀ ξ₁ ∈ s, MapClusterPt ξ₁ l G → ∀ ξ₂ ∈ s, MapClusterPt ξ₂ l G →
      ξ₁.re < ξ₂.re → False := by
    intro ξ₁ h₁s h₁ ξ₂ h₂s h₂ hlt
    have hF₁ := hfib ξ₁ h₁s h₁
    have hF₂ := hfib ξ₂ h₂s h₂
    -- `v` is not a value on `ℍ`, so both points are real
    have hvD : v ∉ F '' H := by
      rintro ⟨z, hzH, hzv⟩
      have hreal : ∀ ξ ∈ s, F ξ = v → ξ ∈ H := by
        intro ξ hξ hFξ
        by_contra hξH
        have h0 : ξ.im = 0 := le_antisymm (not_lt.1 hξH) (show 0 ≤ ξ.im from hξ.2)
        exact hR ξ h0 ⟨z, hzH, hzv.trans hFξ.symm⟩
      have := hinj (hreal ξ₁ h₁s hF₁) (hreal ξ₂ h₂s hF₂) (hF₁.trans hF₂.symm)
      rw [this] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hd hc hinj hlt v
    set l' : Filter ℂ := l ⊓ 𝓟 {w | (G w).re = m} with hl'
    have hl'ne : l'.NeBot := by
      rw [hl', inf_principal_neBot_iff]
      intro U hU
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
      set S : Set ℂ := ball x ε ∩ H with hS
      have hSl : S ∈ l := by
        rw [hS, inter_comm]; exact inter_mem_nhdsWithin H (ball_mem_nhds x hε)
      have hSc : IsPreconnected S := ((convex_ball x ε).inter convex_H).isPreconnected
      have hlo : ∃ w₁ ∈ S, (G w₁).re < m := by
        have hfr : ∃ᶠ w in l, G w ∈ ball ξ₁ (m - ξ₁.re) :=
          h₁.frequently (ball_mem_nhds ξ₁ (by linarith [hm.1]))
        obtain ⟨w, hwb, hwS⟩ := (hfr.and_eventually hSl).exists
        refine ⟨w, hwS, ?_⟩
        have := Complex.abs_re_le_norm (G w - ξ₁)
        rw [mem_ball, dist_eq_norm] at hwb
        rw [Complex.sub_re] at this
        linarith [le_abs_self ((G w).re - ξ₁.re)]
      have hhi : ∃ w₂ ∈ S, m < (G w₂).re := by
        have hfr : ∃ᶠ w in l, G w ∈ ball ξ₂ (ξ₂.re - m) :=
          h₂.frequently (ball_mem_nhds ξ₂ (by linarith [hm.2]))
        obtain ⟨w, hwb, hwS⟩ := (hfr.and_eventually hSl).exists
        refine ⟨w, hwS, ?_⟩
        have := Complex.abs_re_le_norm (G w - ξ₂)
        rw [mem_ball, dist_eq_norm] at hwb
        rw [Complex.sub_re] at this
        linarith [neg_abs_le ((G w).re - ξ₂.re)]
      obtain ⟨w₁, hw₁S, hw₁⟩ := hlo
      obtain ⟨w₂, hw₂S, hw₂⟩ := hhi
      have hGS : ContinuousOn (fun w => (G w).re) S :=
        Complex.continuous_re.comp_continuousOn (hGc.mono inter_subset_right)
      obtain ⟨w, hwS, hwm⟩ := hSc.intermediate_value hw₁S hw₂S hGS ⟨hw₁.le, hw₂.le⟩
      exact ⟨w, hεU hwS, hwm⟩
    have hl'le : l' ≤ l := inf_le_left
    obtain ⟨ζ, hζs, hζ⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 (hl'le hmem))
    have hζre : ζ.re = m := by
      by_contra hne
      have hopen : {y : ℂ | y.re ≠ m} ∈ 𝓝 ζ :=
        (isOpen_ne_fun Complex.continuous_re continuous_const).mem_nhds hne
      have hev : ∀ᶠ w in l', (G w).re = m := mem_inf_of_right (mem_principal_self _)
      obtain ⟨w, hw1, hw2⟩ := ((hζ.frequently hopen).and_eventually hev).exists
      exact hw1 hw2
    have hFζ : F ζ = v :=
      eq_of_mapClusterPt hc (hl'le hmemHbar) (hFG.mono_left hl'le) hζs.2 hζ
    by_cases hζH : ζ ∈ H
    · exact hvD ⟨ζ, hζH, hFζ⟩
    · have h0 : ζ.im = 0 := le_antisymm (not_lt.1 hζH) (show 0 ≤ ζ.im from hζs.2)
      have : ζ = (m : ℂ) := by rw [eq_ofReal_re_of_im_eq_zero h0, hζre]
      exact hFm (this ▸ hFζ)
  have hall : ∀ ξ ∈ s, MapClusterPt ξ l G → ξ = ξ₀ := by
    intro ξ hξs hξ
    have hF := hfib ξ hξs hξ
    have hF₀ := hfib ξ₀ hξ₀s hξ₀
    rcases lt_trichotomy ξ.re ξ₀.re with h | h | h
    · exact (huniq ξ hξs hξ ξ₀ hξ₀s hξ₀ h).elim
    · -- equal real parts: both points real, or one of them in `ℍ`
      by_cases hvD : v ∈ F '' H
      · obtain ⟨z, hzH, hzv⟩ := hvD
        have hreal : ∀ η ∈ s, F η = v → η ∈ H := by
          intro η hη hFη
          by_contra hηH
          have h0 : η.im = 0 := le_antisymm (not_lt.1 hηH) (show 0 ≤ η.im from hη.2)
          exact hR η h0 ⟨z, hzH, hzv.trans hFη.symm⟩
        exact hinj (hreal ξ hξs hF) (hreal ξ₀ hξ₀s hF₀) (hF.trans hF₀.symm)
      · have him : ∀ η ∈ s, F η = v → η.im = 0 := by
          intro η hη hFη
          by_contra hne
          exact hvD ⟨η, show 0 < η.im from lt_of_le_of_ne (show 0 ≤ η.im from hη.2)
            (Ne.symm hne), hFη⟩
        exact Complex.ext h ((him ξ hξs hF).trans (him ξ₀ hξ₀s hF₀).symm)
    · exact (huniq ξ₀ hξ₀s hξ₀ ξ hξs hξ h).elim
  exact ⟨ξ₀, hξ₀s.2, hfib ξ₀ hξ₀s hξ₀, hsc.tendsto_nhds_of_unique_mapClusterPt hmem hall⟩

end InteractingSLE
