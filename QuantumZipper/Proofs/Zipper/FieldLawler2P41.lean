import QuantumZipper.Proofs.Zipper.FieldLawler2Wind
import QuantumZipper.Proofs.Zipper.FieldLawler2Max
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL2-P41: Field–Lawler Prop. 4.1 (analytic form)

Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), §4, Prop. 4.1, p. 10:
for a real point `x` of `D` whose real component is `(e', e)`, with `e, e'` in one connected
component of `D^c`, the probability that Brownian motion from `x` reaches another real crosscut
before leaving `D` is at most `1/2`.

Field–Lawler argue with Brownian paths: on `E_x ∩ Ē_x` the path and its reflection lie in `D`
and separate `e` from `e'`, which is impossible (`fl2_symm_path_absurd`); by reflection symmetry
`P(E_x) = P(Ē_x)` and `P(E_x ∪ Ē_x) ≤ 1`. We follow this argument in its Dirichlet form (own
analytic transcription, no Brownian motion): with `ũ = u ∘ conj`, the function `u + ũ - 1` is
harmonic on the component `G` of `x` in `(D ∩ conj D) \ closure A`; the path argument shows that
`closure G` meets `A` at no point off the finitely many endpoints, so `u + ũ - 1 ≤ 0` at every
other frontier point and at `∞`, and Lindelöf's maximum principle
(`fl2_harm_le_zero_off_finite`; Garnett–Marshall, *Harmonic Measure*, Ch. I, Lemma 1.1, p. 2)
gives `u + ũ ≤ 1` on `G`; at the real point `x`, `u x = ũ x`.
-/

noncomputable section

open Set Metric Filter Complex ComplexConjugate
open scoped Topology

namespace QuantumZipper.FieldLawler

open Thm18Asm.LWFar

/-- **Field–Lawler Prop. 4.1** (EJP 20 (2015), §4, p. 10), harmonic-measure form, for a real
boundary set `A` whose closure adds only finitely many points `E`. -/
theorem fl2_prop41_half {D K A : Set ℂ} {u : ℂ → ℝ} {x e e' : ℝ} (E : Finset ℂ)
    (hD : IsOpen D) (hxD : (x : ℂ) ∈ D) (he'x : e' < x) (hxe : x < e)
    (hK : IsConnected K) (hKD : Disjoint K D) (heK : (e : ℂ) ∈ K) (he'K : (e' : ℂ) ∈ K)
    (hAR : ∀ a ∈ A, ∃ t : ℝ, a = t ∧ (t < e' ∨ e < t))
    (hAD : A ⊆ D) (hAb : Bornology.IsBounded A) (hAE : closure A ⊆ A ∪ (E : Set ℂ))
    (hu : IsHarmMeas (D \ A) A u) : u x ≤ 1 / 2 := by
  have hAim : ∀ a ∈ A, a ∈ {w : ℂ | w.im = 0} := fun a ha => by
    obtain ⟨t, rfl, -⟩ := hAR a ha; simp
  have hclA : ∀ z ∈ closure A, z.im = 0 := fun z hz =>
    closure_minimal hAim (isClosed_eq continuous_im continuous_const) hz
  have hclA' : ∀ z ∈ closure A, z.re ≤ e' ∨ e ≤ z.re := fun z hz => by
    have hsub : A ⊆ {w : ℂ | w.re ≤ e' ∨ e ≤ w.re} := fun a ha => by
      obtain ⟨t, rfl, ht | ht⟩ := hAR a ha
      · left; simp only [ofReal_re]; linarith
      · right; simp only [ofReal_re]; linarith
    exact closure_minimal hsub ((isClosed_le continuous_re continuous_const).union
      (isClosed_le continuous_const continuous_re)) hz
  have hconjA : ∀ z, conj z ∈ closure A → z ∈ closure A := fun z hz => by
    have h1 : z.im = 0 := by simpa using hclA _ hz
    rwa [Complex.conj_eq_iff_im.2 h1] at hz
  set V : Set ℂ := {z | z ∈ D ∧ conj z ∈ D} with hV
  have hVo : IsOpen V := hD.inter (hD.preimage Complex.continuous_conj)
  set W : Set ℂ := V \ closure A with hW
  have hWo : IsOpen W := hVo.sdiff isClosed_closure
  have hxW : (x : ℂ) ∈ W := by
    refine ⟨⟨hxD, by simpa using hxD⟩, fun h => ?_⟩
    rcases hclA' _ h with h' | h' <;> simp only [ofReal_re] at h' <;> linarith
  set G := connectedComponentIn W (x : ℂ) with hG
  have hGo : IsOpen G := hWo.connectedComponentIn
  have hGW : G ⊆ W := connectedComponentIn_subset W _
  have hxG : (x : ℂ) ∈ G := mem_connectedComponentIn hxW
  have hGc : IsConnected G := isConnected_connectedComponentIn_iff.2 hxW
  have hGp : IsPathConnected G := hGo.isConnected_iff_isPathConnected.1 hGc
  have hGu : ∀ y ∈ G, y ∈ D \ A := fun y hy =>
    ⟨(hGW hy).1.1, fun h => (hGW hy).2 (subset_closure h)⟩
  have hGu' : ∀ y ∈ G, conj y ∈ D \ A := fun y hy =>
    ⟨(hGW hy).1.2, fun h => (hGW hy).2 (hconjA y (subset_closure h))⟩
  have h01 := hu.mem01
  set f : ℂ → ℝ := fun z => u z + u (conj z) - 1 with hf_def
  have hf : InnerProductSpace.HarmonicOnNhd f G := fun y hy =>
    ((hu.harm y (hGu y hy)).add (fl_harmonicAt_conj (hu.harm _ (hGu' y hy)))).sub
      (InnerProductSpace.harmonicAt_const 1)
  have hbd : BddAbove (f '' G) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := h01 y (hGu y hy)
    have h2 := h01 _ (hGu' y hy)
    simp only [hf_def]; linarith
  -- boundary behaviour of `u` at a frontier point of `D \ A` off `closure A`
  have hbnd : ∀ ε > 0, ∀ z, z ∉ D → z ∈ closure (D \ A) → z ∉ closure A →
      ∃ δ > 0, ∀ w ∈ D \ A, dist w z < δ → u w ≤ ε := by
    intro ε hε z hzD hzc hzA
    have hzfr : z ∈ frontier (D \ A) := ⟨hzc, fun h => hzD (interior_subset h).1⟩
    have hev := (hu.zero z hzfr hzA).eventually (gt_mem_nhds hε)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hδ'⟩ := hev
    exact ⟨δ, hδ, fun w hw hwd => (hδ' hwd hw).le⟩
  have hfr : ∀ x₀ ∈ frontier G, x₀ ∉ E → ∀ ε > 0, ∃ δ > 0, ∀ y ∈ G, dist y x₀ < δ →
      f y ≤ ε := by
    intro x₀ hx₀ hx₀E ε hε
    rw [hGo.frontier_eq] at hx₀
    obtain ⟨hx₀c, hx₀G⟩ := hx₀
    -- the symmetric-path argument: `closure G` meets `A` only at the points of `E`
    have hx₀A : x₀ ∉ closure A := by
      intro hcl
      have hx₀A : x₀ ∈ A := by
        rcases hAE hcl with h | h
        · exact h
        · exact absurd (Finset.mem_coe.1 h) hx₀E
      obtain ⟨a, rfl, ha⟩ := hAR _ hx₀A
      have haV : (a : ℂ) ∈ V := ⟨hAD hx₀A, by simpa using hAD hx₀A⟩
      obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo _ haV
      obtain ⟨y, hyG, hyb⟩ := Metric.mem_closure_iff.1 hx₀c r hr
      have hj1 : JoinedIn V (x : ℂ) y :=
        (hGp.joinedIn _ hxG _ hyG).mono (fun z hz => (hGW hz).1)
      have hj2 : JoinedIn V y (a : ℂ) :=
        (((convex_ball (a : ℂ) r).isPathConnected ⟨_, mem_ball_self hr⟩).joinedIn _
          (by rw [mem_ball, dist_comm]; exact hyb) _ (mem_ball_self hr)).mono hrV
      have hj := hj1.trans hj2
      have hγ : ∀ t, hj.somePath t ∈ V := hj.somePath_mem
      rcases ha with ha | ha
      · exact fl2_symm_path_absurd hj.somePath.symm
          (fun t => by rw [Path.symm_apply]; exact (hγ _).1)
          (fun t => by rw [Path.symm_apply]; exact (hγ _).2)
          hK hKD he'K heK ⟨ha, he'x⟩ (Or.inr hxe)
      · exact fl2_symm_path_absurd hj.somePath (fun t => (hγ t).1) (fun t => (hγ t).2)
          hK hKD heK he'K ⟨hxe, ha⟩ (Or.inl he'x)
    -- a frontier point of `G` off `closure A` leaves `D` or `conj D`
    have hnV : x₀ ∉ D ∨ conj x₀ ∉ D := by
      by_contra hc
      push Not at hc
      have hx₀W : x₀ ∈ W := ⟨hc, hx₀A⟩
      obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo _ hx₀W
      obtain ⟨y, hyG, hyb⟩ := Metric.mem_closure_iff.1 hx₀c r hr
      have hpc : IsPreconnected (ball x₀ r ∪ G) :=
        IsPreconnected.union' ⟨y, by rwa [mem_ball, dist_comm], hyG⟩
          (convex_ball x₀ r).isPreconnected hGc.isPreconnected
      have hsub := hpc.subset_connectedComponentIn (x := (x : ℂ)) (Or.inr hxG)
        (union_subset hrW hGW)
      exact hx₀G (hsub (Or.inl (mem_ball_self hr)))
    rcases hnV with h | h
    · obtain ⟨δ, hδ, hδ'⟩ := hbnd ε hε x₀ h (closure_mono (fun w hw => hGu w hw) hx₀c) hx₀A
      refine ⟨δ, hδ, fun y hy hyd => ?_⟩
      have h1 := hδ' y (hGu y hy) hyd
      have h2 := (h01 _ (hGu' y hy)).2
      simp only [hf_def]; linarith
    · have hcc : conj x₀ ∈ closure (D \ A) :=
        map_mem_closure Complex.continuous_conj hx₀c (fun w hw => hGu' w hw)
      obtain ⟨δ, hδ, hδ'⟩ := hbnd ε hε (conj x₀) h hcc (fun h' => hx₀A (hconjA x₀ h'))
      refine ⟨δ, hδ, fun y hy hyd => ?_⟩
      have h1 := hδ' (conj y) (hGu' y hy) (by rwa [Complex.dist_conj_conj])
      have h2 := (h01 _ (hGu y hy)).2
      simp only [hf_def]; linarith
  have hinf : ∀ ε > 0, ∃ R, ∀ y ∈ G, R ≤ ‖y‖ → f y ≤ ε := by
    intro ε hε
    have hev := (hu.infty hAb).eventually (gt_mem_nhds hε)
    rw [eventually_inf_principal] at hev
    obtain ⟨R, -, hR⟩ :=
      (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 hev
    refine ⟨R + 1, fun y hy hyR => ?_⟩
    have h1 : u y < ε := hR (by
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]; linarith) (hGu y hy)
    have h2 := (h01 _ (hGu' y hy)).2
    simp only [hf_def]; linarith
  have hmax := fl2_harm_le_zero_off_finite E hGo hf hbd hfr hinf (x : ℂ) hxG
  simp only [hf_def, Complex.conj_ofReal] at hmax
  linarith

/-- **Field–Lawler Prop. 4.1** (EJP 20 (2015), §4, p. 10) with `A` a finite union of real open
intervals `(p.1, p.2)`, `p ∈ I`, each contained in `D` and disjoint from `[e', e]`. -/
theorem fl2_prop41_half_intervals {D K : Set ℂ} {u : ℂ → ℝ} {x e e' : ℝ} (I : Finset (ℝ × ℝ))
    (hD : IsOpen D) (hxD : (x : ℂ) ∈ D) (he'x : e' < x) (hxe : x < e)
    (hK : IsConnected K) (hKD : Disjoint K D) (heK : (e : ℂ) ∈ K) (he'K : (e' : ℂ) ∈ K)
    (hID : ∀ p ∈ I, ((↑) : ℝ → ℂ) '' Ioo p.1 p.2 ⊆ D)
    (hIe : ∀ p ∈ I, Disjoint (Ioo p.1 p.2) (Icc e' e))
    (hu : IsHarmMeas (D \ ⋃ p ∈ I, ((↑) : ℝ → ℂ) '' Ioo p.1 p.2)
      (⋃ p ∈ I, ((↑) : ℝ → ℂ) '' Ioo p.1 p.2) u) :
    u x ≤ 1 / 2 := by
  refine fl2_prop41_half (I.image (fun p => (p.1 : ℂ)) ∪ I.image (fun p => (p.2 : ℂ)))
    hD hxD he'x hxe hK hKD heK he'K ?_ (iUnion₂_subset hID) ?_ ?_ hu
  · intro a ha
    simp only [mem_iUnion, mem_image] at ha
    obtain ⟨p, hp, t, ht, rfl⟩ := ha
    have hn : t ∉ Icc e' e := Set.disjoint_left.1 (hIe p hp) ht
    simp only [mem_Icc, not_and_or, not_le] at hn
    exact ⟨t, rfl, hn⟩
  · refine (Bornology.isBounded_biUnion_finset I).2 fun p _ => ?_
    exact (isCompact_Icc.image continuous_ofReal).isBounded.subset
      (image_mono Ioo_subset_Icc_self)
  · rw [Finset.closure_biUnion]
    refine iUnion₂_subset fun p hp => ?_
    have hc : closure (((↑) : ℝ → ℂ) '' Ioo p.1 p.2) ⊆ ((↑) : ℝ → ℂ) '' Icc p.1 p.2 :=
      closure_minimal (image_mono Ioo_subset_Icc_self)
        (isCompact_Icc.image continuous_ofReal).isClosed
    intro z hz
    obtain ⟨t, ⟨h1, h2⟩, rfl⟩ := hc hz
    rcases h1.eq_or_lt with h1 | h1
    · right; subst h1
      simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
      exact Or.inl ⟨p, hp, rfl⟩
    rcases h2.eq_or_lt with h2 | h2
    · right; subst h2
      simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
      exact Or.inr ⟨p, hp, rfl⟩
    · left
      exact mem_biUnion hp ⟨t, ⟨h1, h2⟩, rfl⟩

end QuantumZipper.FieldLawler
