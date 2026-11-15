/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40InfFace

/-!
# Aux. lemmas 40–41 with the junction at the original target

Specification §6.2, **Aux.** lemma 40 (conditions (a), (b) of Proposition 6.12, p. 204) and
**Aux.** lemma 41 (`source/spec/p193-240.md` L213–L265: "the pause-free erased path
`ζ = ψ ∘ γ̂_C` has a continuous Loewner driving function up to its terminal capacity time"; "The
real-circle case with `x₀` the original target … [is] included in that Jordan-face proof"), with
ruling R41's Proposition 1.6, for the pocket of `IsReversePocketInf` (`σ = T(x₀) = ∞`), a Jordan
coordinate `ψ` of `C` at infinity (`IsJordanCoordInf`), and `ζ = ψ ∘ γ̂_C` on `[0, ℓ(∞))`.

The argument is that of `Aux41Full` for the finite junction; the only change is in (RG3)–(RG5):
the central face `F_s` is unbounded, so the conformal map `Φ_s = G_u ∘ ψ ∘ f̄_s` is read on the
bounded Jordan domain `ψ_p(F_s) = innerSide Γ` (`IsReversePocketInf.exists_face`), as
`G_u ∘ ψ ∘ f̄_s ∘ ψ_p⁻¹`, with `p` left of the gates and of the collapsed own future.

## Main results (namespace `IsReversePocketInf`)

* `image_inter_domain`: **(GC2) in the coordinate**, `ψ(C ∩ D_{fR(u)}) = ℍ \ fill(ζ([0, u]))`;
* `drivingCriterionA`, `drivingCriterionB`: **conditions (a), (b)** on every `[0, S]`, `S < ℓ(∞)`;
* `hasContinuousOwnFuture`: **(RG1)–(RG5)**;
* `aux40`, `aux41`, `exists_aux41`: **Aux. lemmas 40–41 at infinity**.

All results assume Aux. lemma 37's conclusion (`AttachmentConstancyInf`), the named input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.YuanCharacterisation (invExt HasContinuousOwnFuture)

namespace InteractingSLE.Sec6

namespace IsReversePocketInf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-! ### The erased path in the Jordan coordinate -/

theorem continuousOn_ζ_Icc (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    ContinuousOn (fun v => ψ (erasedPathInf η C τ v)) (Icc 0 u) :=
  hψ.1.comp (hP.continuousOn_erasedPath_Icc hAC hu) fun _ hv =>
    hP.erasedPath_mem ⟨hv.1, hv.2.trans_lt hu.2⟩

theorem continuousOn_ζ (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) :
    ContinuousOn (fun v => ψ (erasedPathInf η C τ v)) (Ico 0 (clockEnd η C τ)) :=
  hψ.1.comp (hP.continuousOn_erasedPath hAC) fun _ hv => hP.erasedPath_mem hv

theorem mapsTo_ζ (hP : IsReversePocketInf W η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) :
    MapsTo (fun v => ψ (erasedPathInf η C τ v)) (Ico 0 (clockEnd η C τ)) Hbar :=
  fun _ hv => hψ.2.2.1 (hP.erasedPath_mem hv)

theorem ζ_zero (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) : ψ (erasedPathInf η C τ 0) = 0 := by
  rw [hP.erasedPath_zero hAC]; exact hψ.2.2.2.2.2.1

/-- **(GC2) in the Jordan coordinate at infinity** (Specification p. 206: "By (GC2), the physical
target component is `E_s`"): `ψ(C ∩ D_{fR(u)}) = ℍ \ fill(ζ([0, u]))` for `u ∈ [0, ℓ(∞))`. -/
theorem image_inter_domain (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    ψ '' (C ∩ (H \ fwdHull W (pocketFibreInf η C τ u))) =
      H \ fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u) := by
  have hψ' := hψ
  obtain ⟨hψc, hψi, -, hψconf, -, -, hψt⟩ := hψ'
  set s := pocketFibreInf η C τ u with hsdef
  set ζ : ℝ → ℂ := fun v => ψ (erasedPathInf η C τ v) with hζdef
  set D := H \ fwdHull W s with hDdef
  have hτs : τ ≤ s := hP.fibre_mem hu
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  have hsub : ∀ v ∈ Icc 0 u, v ∈ Ico 0 (clockEnd η C τ) := fun v hv =>
    ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hcpt : IsCompact (ζ '' Icc 0 u) :=
    isCompact_Icc.image_of_continuousOn (hP.continuousOn_ζ_Icc hAC hψ hu)
  have hpre := hP.isPreconnected_inter_domain hτs
  have hunb := hP.not_isBounded_inter_domain hs0
  have hGC2 := hP.erasedPath_image_inter hu
  -- (⊆): `ψ(C ∩ D_s)` is preconnected, unbounded and misses `ζ([0, u])`
  have hfwd : ψ '' (C ∩ D) ⊆ H \ fillH (ζ '' Icc 0 u) := by
    refine subset_H_diff_fillH_of_isPreconnected hcpt.isBounded
      (hpre.image _ (hψc.mono fun z hz => subset_closure hz.1)) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hψconf.2.mapsTo hz.1, fun hcl => ?_⟩
      rw [hcpt.isClosed.closure_eq] at hcl
      obtain ⟨v, hv, hvz⟩ := hcl
      have hzv : erasedPathInf η C τ v = z :=
        hψi (hP.erasedPath_mem (hsub v hv)) (subset_closure hz.1) hvz
      have hzR : z ∈ η '' Icc 0 s := by
        have := hGC2 ▸ (show z ∈ erasedPathInf η C τ '' Icc 0 u ∩ C from ⟨⟨v, hv, hzv⟩, hz.1⟩)
        exact this.1
      exact hz.2.2 (mem_fwdHull_of_mem_trace hP.trace hs0 hz.2.1 hzR)
    · intro hb
      have hne : (cobounded ℂ ⊓ 𝓟 (C ∩ D)).NeBot := by
        refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
        by_contra h
        rw [not_nonempty_iff_eq_empty] at h
        have hUb : IsBounded Uᶜ := isBounded_def.2 (by rwa [compl_compl])
        refine hunb (hUb.subset fun z hz hzU => ?_)
        have : z ∈ U ∩ (C ∩ D) := ⟨hzU, hz⟩
        rw [h] at this
        exact this
      have ht' : Tendsto ψ (cobounded ℂ ⊓ 𝓟 (C ∩ D)) (cobounded ℂ) :=
        hψt.mono_left (inf_le_inf_left _ (principal_mono.2 fun z hz => subset_closure hz.1))
      obtain ⟨z, hzb, hz⟩ := ((ht'.eventually (isBounded_def.1 hb)).and
        (eventually_inf_principal.2 (Eventually.of_forall fun z hz => hz))).exists
      exact hzb ⟨z, hz, rfl⟩
  refine Subset.antisymm hfwd ?_
  -- (⊇): pull `ℍ \ fill(ζ([0, u]))` back by the holomorphic inverse of `ψ`
  set e := QuantumZipper.CA.univalentOPH hP.isOpen hψconf.1 hψconf.2.injOn with hedef
  have htarget : e.target = H := by
    rw [hedef, QuantumZipper.CA.univalentOPH_target]; exact hψconf.2.image_eq
  have hsymmC : MapsTo e.symm H C := fun w hw => by
    have := e.map_target (htarget ▸ hw)
    rwa [hedef, QuantumZipper.CA.univalentOPH_source] at this
  have hψe : ∀ w ∈ H, ψ (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hP.isOpen hψconf.1 hψconf.2.injOn
      (by rw [hψconf.2.image_eq]; exact hw)
  have hK : IsHPHull (fillH (ζ '' Icc 0 u)) :=
    YuanCharacterisation.isHPHull_fillH_image (hP.continuousOn_ζ_Icc hAC hψ hu) hu.1
      (hP.ζ_zero hAC hψ)
  set Q := e.symm '' (H \ fillH (ζ '' Icc 0 u)) with hQdef
  have hQpre : IsPreconnected Q :=
    hK.isConnected.isPreconnected.image _ ((htarget ▸ e.continuousOn_symm).mono sdiff_subset)
  have hQC : Q ⊆ C := by rintro _ ⟨w, hw, rfl⟩; exact hsymmC hw.1
  have hQR : Disjoint Q (η '' Icc 0 s) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ hR
    have hmem : e.symm w ∈ η '' Icc 0 s ∩ C := ⟨hR, hsymmC hw.1⟩
    rw [← hGC2] at hmem
    obtain ⟨⟨v, hv, hve⟩, -⟩ := hmem
    have : w ∈ ζ '' Icc 0 u := ⟨v, hv, by simp only [hζdef, hve, hψe w hw.1]⟩
    exact hw.2 ⟨hw.1, Or.inl (subset_closure this)⟩
  obtain ⟨z₀, hz₀⟩ : (C ∩ D).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact hunb (by rw [hne]; exact isBounded_empty)
  have hz₀Q : z₀ ∈ Q := ⟨ψ z₀, hfwd ⟨z₀, hz₀, rfl⟩,
    QuantumZipper.CA.univalentOPH_symm_apply_apply hP.isOpen hψconf.1 hψconf.2.injOn hz₀.1⟩
  have hQD := subset_domain_of_isPreconnected hP.trace hs0 hQpre (hQC.trans hP.subset_H) hQR
    hz₀Q hz₀.2
  intro w hw
  exact ⟨e.symm w, ⟨hsymmC hw.1, hQD ⟨w, hw, rfl⟩⟩, hψe w hw.1⟩

/-- Every retained point after the chart time `s = fR(u)` adheres to `C ∩ D_s`. -/
theorem erasedPath_mem_closure_inter (hP : IsReversePocketInf W η C α₁ α₂ τ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < clockEnd η C τ) :
    erasedPathInf η C τ v ∈ closure (C ∩ (H \ fwdHull W (pocketFibreInf η C τ u))) := by
  have hu' : u ∈ Ico 0 (clockEnd η C τ) := ⟨hu, huv.trans_lt hv⟩
  have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨hu.trans huv, hv⟩
  set s := pocketFibreInf η C τ u with hsdef
  set b := pocketFibreInf η C τ v with hbdef
  have hsb : s ≤ b := hP.monotoneOn_fibre hu' hv' huv
  have hb0 : 0 ≤ b := hP.fibre_nonneg hv'
  have hbcl := hP.fibre_mem_closure hv'
  have hsub : {t | b < t ∧ η t ∈ C} ⊆ Ici 0 := fun t ht => hb0.trans ht.1.le
  have hc : ContinuousWithinAt η {t | b < t ∧ η t ∈ C} b :=
    (hP.trace.2.1 b (mem_Ici.2 hb0)).mono hsub
  refine closure_minimal ?_ isClosed_closure (hc.mem_closure_image hbcl)
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := hb0.trans ht.1.le
  have hcl := trace_mem_closure_domain hP.trace hP.continuous_W hP.W_zero ht0
  have hDD : H \ fwdHull W t ⊆ H \ fwdHull W s := fun z hz =>
    ⟨hz.1, fun h => hz.2 (fwdHull_mono' (hsb.trans ht.1.le) h)⟩
  exact hP.isOpen.inter_closure ⟨ht.2, closure_mono hDD hcl⟩

/-- **Aux. lemma 40, condition (a)** at infinity: the future of `ζ` stays in the closure of the
unbounded component `ℍ \ fill(ζ([0, t]))`. -/
theorem drivingCriterionA (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {S : ℝ}
    (hS : S < clockEnd η C τ) :
    DrivingCriterionA (fun v => ψ (erasedPathInf η C τ v)) S := by
  intro t ht
  rw [← hP.image_inter_domain hAC hψ ⟨ht.1.le, ht.2.trans hS⟩]
  rintro _ ⟨v, hv, rfl⟩
  have hvσ : v < clockEnd η C τ := hv.2.trans_lt hS
  have hmem := hP.erasedPath_mem_closure_inter ht.1.le hv.1.le hvσ
  have hc : ContinuousWithinAt ψ (C ∩ (H \ fwdHull W (pocketFibreInf η C τ t)))
      (erasedPathInf η C τ v) :=
    (hψ.1 _ (hP.erasedPath_mem ⟨ht.1.le.trans hv.1.le, hvσ⟩)).mono fun z hz => subset_closure hz.1
  exact hc.mem_closure_image hmem

/-- **Aux. lemma 40, condition (b)** at infinity: no nontrivial interval of `ζ` lies in its earlier
range together with `ℝ`. -/
theorem drivingCriterionB (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {S : ℝ} (hS : S < clockEnd η C τ) :
    DrivingCriterionB (fun v => ψ (erasedPathInf η C τ v)) S := by
  intro t ht
  set A := {u ∈ Ioo t S | ψ (erasedPathInf η C τ u) ∈ (fun v => ψ (erasedPathInf η C τ v)) ''
    Icc 0 t ∨ (ψ (erasedPathInf η C τ u)).im = 0} with hAdef
  by_contra hne
  obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 isOpen_interior v₀ hv₀
  have hball : ∀ v, |v - v₀| < ε → v ∈ A := fun v hv =>
    interior_subset (hεA (by rw [mem_ball, Real.dist_eq]; exact hv))
  set v₁ := v₀ - ε / 2 with hv₁
  set v₂ := v₀ + ε / 2 with hv₂
  have hA₁ := hball v₁ (by rw [hv₁, abs_of_neg (by linarith)]; linarith)
  have hA₂ := hball v₂ (by rw [hv₂, abs_of_pos (by linarith)]; linarith)
  have hσ₂ : v₂ < clockEnd η C τ := hA₂.1.2.trans hS
  have h0₁ : 0 ≤ v₁ := ht.1.le.trans hA₁.1.1.le
  have hm₁ : v₁ ∈ Ico 0 (clockEnd η C τ) := ⟨h0₁, (show v₁ < v₂ by linarith).trans hσ₂⟩
  have hm₂ : v₂ ∈ Ico 0 (clockEnd η C τ) := ⟨h0₁.trans (by linarith), hσ₂⟩
  set a₁ := pocketFibreInf η C τ v₁ with ha₁
  set a₂ := pocketFibreInf η C τ v₂ with ha₂
  have hℓ₁ := hP.clock_fibre hm₁
  have hℓ₂ := hP.clock_fibre hm₂
  have ha₁₂ : a₁ < a₂ := by
    by_contra h
    push Not at h
    have := hP.monotone_clock h
    rw [hℓ₁, hℓ₂] at this
    linarith
  obtain ⟨t₀, ht₀, ht₀I⟩ := hP.exists_mem_of_clock_lt ha₁₂ (by rw [hℓ₁, hℓ₂]; linarith)
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t₀ ht₀I
  set l := max (t₀ - δ) a₁ with hl
  set r := min (t₀ + δ) a₂ with hr
  have hlt : l < t₀ := max_lt (by linarith) ht₀.1
  have htr : t₀ < r := lt_min (by linarith) ht₀.2
  have hJ : ∀ x, l < x → x < r → x ∈ visitSetInf η C τ := fun x hlx hxr => hδI (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (t₀ - δ) a₁]
    · linarith [min_le_left (t₀ + δ) a₂])
  set c := (l + t₀) / 2 with hc
  set d := (t₀ + r) / 2 with hd
  have hcd : c < d := by rw [hc, hd]; linarith
  have hc0 : 0 ≤ c :=
    hP.nonneg.trans (le_of_lt (hJ c (by rw [hc]; linarith) (by rw [hc]; linarith)).1)
  have hsub : η '' Icc c d ⊆ η '' Icc 0 c := by
    rintro _ ⟨t', ht', rfl⟩
    have ht'I := hJ t' (by rw [hc] at ht'; linarith [ht'.1]) (by rw [hd] at ht'; linarith [ht'.2])
    have hal : a₁ ≤ l := le_max_right _ _
    have hlo : pocketClockInf η C τ a₁ < pocketClockInf η C τ t' := hP.clock_lt_of_mem
      (t := (l + c) / 2) (by rw [hc]; linarith) (by rw [hc] at ht'; linarith [ht'.1])
      (hJ _ (by rw [hc]; linarith) (by rw [hc]; linarith))
    have hhi : pocketClockInf η C τ t' < pocketClockInf η C τ a₂ := hP.clock_lt_of_mem
      (t := (d + r) / 2) (by rw [hd] at ht'; linarith [ht'.2]) (by
        have : r ≤ a₂ := min_le_right _ _
        rw [hd]; linarith) (hJ _ (by rw [hd]; linarith) (by rw [hd]; linarith))
    rw [hℓ₁] at hlo
    rw [hℓ₂] at hhi
    set w := pocketClockInf η C τ t' with hw
    have hwA := hball w (by rw [abs_lt]; constructor <;> linarith)
    have hfw : pocketFibreInf η C τ w = t' := hP.fibre_clock_of_mem ht'I
    have hηC : η t' ∈ C := ht'I.2
    rcases hwA.2 with ⟨w', hw', hψw⟩ | him
    · simp only [erasedPathInf, hfw] at hψw
      have heq : erasedPathInf η C τ w' = η t' := hψ.2.1
        (hP.erasedPath_mem ⟨hw'.1, hw'.2.trans_lt (ht.2.trans hS)⟩) (subset_closure hηC) hψw
      have hmem : η t' ∈ erasedPathInf η C τ '' Icc 0 t ∩ C := ⟨⟨w', hw', heq⟩, hηC⟩
      rw [hP.erasedPath_image_inter ⟨ht.1.le, ht.2.trans hS⟩] at hmem
      obtain ⟨t'', ht'', he⟩ := hmem.1
      have hft : pocketFibreInf η C τ t ≤ a₁ :=
        hP.monotoneOn_fibre ⟨ht.1.le, ht.2.trans hS⟩ hm₁ hA₁.1.1.le
      exact ⟨t'', ⟨ht''.1, ht''.2.trans (hft.trans (hal.trans (by rw [hc]; linarith)))⟩, he⟩
    · simp only [erasedPathInf, hfw] at him
      exact absurd him (ne_of_gt (hψ.2.2.2.1.2.1 hηC))
  exact not_image_subset_of_lt hP.trace hP.continuous_W hP.W_zero hc0 hcd hsub

/-- Strict growth of the relative fillings (Specification p. 206), from conditions (a), (b). -/
theorem strictMonoOn_fillH_ζ (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {S : ℝ}
    (hS : S < clockEnd η C τ) :
    StrictMonoOn (fun t => fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 t)) (Icc 0 S) :=
  strictMonoOn_fillH_of_drivingCriteria ((hP.continuousOn_ζ hAC hψ).mono fun _ hv =>
    ⟨hv.1, hv.2.trans_lt hS⟩) (hP.drivingCriterionA hAC hψ hS) (hP.drivingCriterionB hψ hS)

/-- On `[u, S]` the fibre endpoints of the clock restricted to `[fR(u), fR(S)]` are those in
`[τ, ∞)`. -/
theorem fibreRight_restrict (hP : IsReversePocketInf W η C α₁ α₂ τ) {u S v : ℝ} (hu : 0 ≤ u)
    (hS : S < clockEnd η C τ) (hv : v ∈ Icc u S) :
    fibreRight (pocketClockInf η C τ) (pocketFibreInf η C τ u) (pocketFibreInf η C τ S) v =
      pocketFibreInf η C τ v := by
  have hv0 : 0 ≤ v := hu.trans hv.1
  have hu' : u ∈ Ico 0 (clockEnd η C τ) := ⟨hu, (hv.1.trans hv.2).trans_lt hS⟩
  have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv0, hv.2.trans_lt hS⟩
  have hS' : S ∈ Ico 0 (clockEnd η C τ) := ⟨hv0.trans hv.2, hS⟩
  have hℓs := hP.clock_fibre hu'
  have hvA : pocketFibreInf η C τ v ∈ {t ∈ Icc (pocketFibreInf η C τ u) (pocketFibreInf η C τ S) |
      pocketClockInf η C τ t ≤ max v (pocketClockInf η C τ (pocketFibreInf η C τ u))} :=
    ⟨⟨hP.monotoneOn_fibre hu' hv' hv.1, hP.monotoneOn_fibre hv' hS' hv.2⟩, by
      rw [hP.clock_fibre hv']; exact le_max_left _ _⟩
  refine le_antisymm (csSup_le ⟨_, hvA⟩ fun t ht => ?_) (le_csSup ⟨_, fun t ht => ht.1.2⟩ hvA)
  rw [hℓs, max_eq_left hv.1] at ht
  by_contra h
  push Not at h
  exact absurd ht.2 (not_le.2 (hP.lt_clock_of_fibre_lt hv' h))

/-- **(RG1)–(RG5) at infinity** (Specification pp. 204–206; ruling R41's Proposition 1.6): after
every erased prefix `ζ([0, u])`, `u < S < ℓ(∞)`, the future `ζ|[u, S]` lifts continuously through
the inverse of the relative mapping-out function, `β(v) = Φ̄(ψ_p(Δ_s(v)))`, `s = fR(u)`, with
`Φ = G_u ∘ ψ ∘ f̄_s ∘ ψ_p⁻¹` the conformal map of the bounded face `ψ_p(F_s)` onto `ℍ` and `Δ_s` the
collapsed own-mapped future. This is condition (ii) of [Yua22, Theorem 1.1]. -/
theorem hasContinuousOwnFuture (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {S : ℝ}
    (hS : S < clockEnd η C τ) :
    HasContinuousOwnFuture (fun v => ψ (erasedPathInf η C τ v)) S := by
  intro u hu
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  set ζ : ℝ → ℂ := fun v => ψ (erasedPathInf η C τ v) with hζdef
  set s := pocketFibreInf η C τ u with hsdef
  set S' := pocketFibreInf η C τ S with hS'def
  have hu' : u ∈ Ico 0 (clockEnd η C τ) := ⟨hu.1, hu.2.trans hS⟩
  have hSm : S ∈ Ico 0 (clockEnd η C τ) := ⟨hu.1.trans hu.2.le, hS⟩
  have hτs : τ ≤ s := hP.fibre_mem hu'
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  have hℓs : pocketClockInf η C τ s = u := hP.clock_fibre hu'
  have hℓS' : pocketClockInf η C τ S' = S := hP.clock_fibre hSm
  have hsS' : s ≤ S' := hP.monotoneOn_fibre hu' hSm hu.2.le
  have hvI : ∀ v ∈ Icc u S, v ∈ Ico 0 (clockEnd η C τ) := fun v hv =>
    ⟨hu.1.trans hv.1, hv.2.trans_lt hS⟩
  have hζc : ContinuousOn ζ (Icc 0 u) := hP.continuousOn_ζ_Icc hAC hψ hu'
  have hζH : MapsTo ζ (Icc 0 u) Hbar :=
    (hP.mapsTo_ζ hψ).mono_left fun v hv => ⟨hv.1, hv.2.trans_lt hu'.2⟩
  set K := fillH (ζ '' Icc 0 u) with hKdef
  set G := ConformalImage.mapOut K with hGdef
  have hK : IsHPHull K := YuanCharacterisation.isHPHull_fillH_image hζc hu.1 (hP.ζ_zero hAC hψ)
  have hG : IsMapOut K G := ConformalImage.isMapOut_mapOut hK
  obtain ⟨hinvc, hinvG⟩ := invExt_facts hu.1 hζc hζH (hP.ζ_zero hAC hψ)
  -- the collapsed own-mapped future `Δ_s`
  set Δ : ℝ → ℂ := fun v => trMap W s (pocketFibreInf η C τ v) 0 with hΔdef
  have hΔc : ContinuousOn Δ (Icc u S) := by
    have h := continuousOn_collapsed_ownFuture hη hW hW0 hP.continuous_clock hP.monotone_clock
      hs0 hsS' (S := S') ?_
    · rw [hℓs, hℓS'] at h
      exact h.congr fun v hv => by
        simp only [hΔdef]
        exact congrArg (fun x => trMap W s x 0) (hP.fibreRight_restrict hu.1 hS hv).symm
    intro a ha b hb hab hℓab hmax
    obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre hτs (hP.clock_lt_of_fibre hSm) ha hb hab hℓab
      hmax
    have has : s < a := by
      refine lt_of_le_of_ne ha.1 fun h => ?_
      rw [← h] at hℓab
      exact (hP.clock_lt_of_fibre hu' b (lt_of_le_of_lt (le_of_eq h) hab)).ne hℓab
    exact (hP.gap_eq hAC hs0 has (hτs.trans ha.1) hab hgap
      (Or.inr (hacl.resolve_left has.ne')) hbcl).1
  have hfib_s : ∀ v ∈ Icc u S, s ≤ pocketFibreInf η C τ v := fun v hv =>
    hP.monotoneOn_fibre hu' (hvI v hv) hv.1
  have hfΔ : ∀ v ∈ Icc u S, trMap W 0 s (Δ v) = erasedPathInf η C τ v := fun v hv =>
    traceMapOut_trMap_zero hη hW hW0 hs0 (hfib_s v hv)
  have hΔF₀ : ∀ v ∈ Icc u S, Δ v ∈ closure {w ∈ H | trMap W 0 s w ∈ C} := by
    intro v hv
    refine ownFuture_mem_closure_face (F := {w ∈ H | trMap W 0 s w ∈ C}) hη hW hW0 hP.isOpen hs0
      (fun t hst htC hδH => ⟨hδH, by rw [traceMapOut_trMap_zero hη hW hW0 hs0 hst]; exact htC⟩) ?_
    refine closure_mono (s := {t | pocketFibreInf η C τ v < t ∧ η t ∈ C})
      (t := {t | s < t ∧ η t ∈ C}) (fun t ht => ⟨(hfib_s v hv).trans_lt ht.1, ht.2⟩) ?_
    exact hP.fibre_mem_closure (hvI v hv)
  -- a pole `p` left of the gates and of `Δ_s`, and the bounded face `F = ψ_p(F_s)`
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hΔc).isBounded.exists_norm_le
  obtain ⟨P, hPf⟩ := hP.exists_face hτs
  set p : ℝ := min P (-|B|) - 1 with hpdef
  have hpP : p < P := by have := min_le_left P (-|B|); linarith
  have hΔp : ∀ v ∈ Icc u S, Δ v ≠ p := by
    intro v hv h'
    have h1 : ‖Δ v‖ ≤ B := hB _ ⟨v, hv, rfl⟩
    rw [h', norm_real, Real.norm_eq_abs] at h1
    have h2 : p ≤ -|B| - 1 := by have := min_le_right P (-|B|); linarith
    have h3 : |B| + 1 ≤ |p| := by
      rw [abs_of_neg (show p < 0 by linarith [abs_nonneg B])]; linarith
    linarith [le_abs_self B]
  obtain ⟨Γ, hΓJ, hΓH, hiff⟩ := hPf p hpP
  obtain ⟨⟨x₁, hx₁, hin⟩, hFb, hFfr, -, -, -, -, -, -⟩ := jordan_sides hΓJ hΓH
  set F := innerSide Γ with hFdef
  have hFH : F ⊆ H := innerSide_subset_H hΓJ hΓH
  set χ : ℂ → ℂ := fun ζ' => trMap W 0 s (psiMapInv p ζ') with hχdef
  have hf : IsConformalBijection χ F (C ∩ (H \ fwdHull W s)) :=
    hP.isConformalBijection_face hs0 hΓJ hΓH hiff
  have hψ' : IsConformalBijection ψ (C ∩ (H \ fwdHull W s)) (H \ K) := by
    refine ⟨hψ.2.2.2.1.1.mono inter_subset_left, ?_⟩
    have := (hψ.2.2.2.1.2.injOn.mono inter_subset_left).bijOn_image
      (s := C ∩ (H \ fwdHull W s))
    rwa [hP.image_inter_domain hAC hψ hu'] at this
  have hΦ := isConformalBijection_comp hG.1 (isConformalBijection_comp hψ' hf)
  have hΦ' : IsConformalBijection (G ∘ (ψ ∘ χ)) (connectedComponentIn Γᶜ x₁) H := by
    rw [← hin]; exact hΦ
  obtain ⟨p', hp'Γ, Φ', hΦeq, hΦc, hΦH, hΦt⟩ :=
    exists_bdryExt_of_isConformalBijection hΓJ hx₁ (hin ▸ hFb) hΦ'
  rw [← hin] at hΦeq hΦc hΦH hΦt
  have hp'F : p' ∉ F := fun h => innerSide_subset_compl h hp'Γ
  have hFsub : F ⊆ closure F \ {p'} := fun w hw => ⟨subset_closure hw, fun h => hp'F (h ▸ hw)⟩
  -- `Δ'_s = ψ_p ∘ Δ_s` stays in `F̄`
  set Δ' : ℝ → ℂ := fun v => psiMap p (Δ v) with hΔ'def
  have hΔ'0 : ∀ v ∈ Icc u S, Δ' v ≠ 0 := fun v hv h => hΔp v hv (psiMap_eq_zero_iff.1 h)
  have hΔ'c : ContinuousOn Δ' (Icc u S) := continuousOn_psiMap.comp hΔc fun v hv => hΔp v hv
  have himgF : psiMap p '' {w ∈ H | trMap W 0 s w ∈ C} ⊆ F := by
    rintro _ ⟨w, hw, rfl⟩
    have hwp : w ≠ p := fun h => by rw [h] at hw; exact not_mem_H_ofReal p hw.1
    exact (hiff _ ((psiMap_mem_H_iff hwp).2 hw.1)).1 (by rw [psiMapInv_psiMap]; exact hw.2)
  have hΔF : ∀ v ∈ Icc u S, Δ' v ∈ closure F := by
    intro v hv
    have hc : ContinuousWithinAt (psiMap p) {w ∈ H | trMap W 0 s w ∈ C} (Δ v) :=
      (continuousOn_psiMap.continuousAt
        (isOpen_compl_singleton.mem_nhds (hΔp v hv))).continuousWithinAt
    exact closure_mono himgF (hc.mem_closure_image (hΔF₀ v hv))
  have hχΔ : ∀ v ∈ Icc u S, χ (Δ' v) = erasedPathInf η C τ v := fun v hv => by
    simp only [hχdef, hΔ'def, psiMapInv_psiMap]; exact hfΔ v hv
  have hfc : ContinuousOn (trMap W 0 s) Hbar :=
    YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs0
  have hfC : MapsTo χ F (closure C) := fun w hw => subset_closure (hf.2.mapsTo hw).1
  -- `ψ ∘ χ` is continuous within `F` at every `Δ'_s(v)`
  have hgc : ∀ v ∈ Icc u S, ContinuousWithinAt (fun w => ψ (χ w)) F (Δ' v) := by
    intro v hv
    have hmem : χ (Δ' v) ∈ closure C := by rw [hχΔ v hv]; exact hP.erasedPath_mem (hvI v hv)
    have hpic : ContinuousAt (psiMapInv p) (Δ' v) :=
      continuousOn_psiMapInv.continuousAt (isOpen_compl_singleton.mem_nhds (hΔ'0 v hv))
    have h1 : psiMapInv p (Δ' v) ∈ Hbar := by
      simp only [hΔ'def, psiMapInv_psiMap]
      exact YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hs0 (hfib_s v hv)
    have hχc : ContinuousWithinAt χ F (Δ' v) :=
      (hfc _ h1).comp hpic.continuousWithinAt fun w hw =>
        QuantumZipper.H_subset_Hbar (psiMapInv_mem_H (hFH hw))
    exact (hψ.1 _ hmem).comp hχc hfC
  -- the pole is not reached
  have hΔp' : ∀ v ∈ Icc u S, Δ' v ≠ p' := by
    intro v hv hvp
    have hpcl : p' ∈ closure F := by
      rw [← hFfr] at hp'Γ; exact frontier_subset_closure hp'Γ
    have : (𝓝[F] p').NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
    obtain ⟨M, hM⟩ := hG.exists_norm_le hK
    have hg := hgc v hv
    rw [hvp] at hg
    set c := ψ (χ p') with hcdef
    have h1 : ∀ᶠ w in 𝓝[F] p', ‖ψ (χ w)‖ < ‖c‖ + 1 := by
      filter_upwards [hg.tendsto.eventually (Metric.ball_mem_nhds c one_pos)] with w hw
      have := norm_sub_norm_le (ψ (χ w)) c
      rw [dist_eq_norm] at hw
      linarith
    have h2 : ∀ᶠ w in 𝓝[F] p', ‖c‖ + 1 + M < ‖(G ∘ (ψ ∘ χ)) w‖ :=
      (tendsto_norm_atTop_iff_cobounded.2 hΦt).eventually (eventually_gt_atTop _)
    obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    have hz : ψ (χ w) ∈ H \ K := hψ'.2.mapsTo (hf.2.mapsTo hwF)
    have := hM _ hz
    simp only [Function.comp_apply] at hw2
    linarith
  refine ⟨fun v => Φ' (Δ' v), hΦc.comp hΔ'c fun v hv => ⟨hΔF v hv, hΔp' v hv⟩,
    fun v hv => hΦH ⟨hΔF v hv, hΔp' v hv⟩, fun v hv => ?_⟩
  -- the identity `invExt K (Φ̄(Δ'_s(v))) = ζ(v)`, by uniqueness of limits within `F`
  have : (𝓝[F] (Δ' v)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hΔF v hv)
  have hmemp : Δ' v ∈ closure F \ {p'} := ⟨hΔF v hv, hΔp' v hv⟩
  have hc₁ : ContinuousWithinAt (fun w => invExt K (Φ' w)) F (Δ' v) :=
    ((hinvc _ (hΦH hmemp)).comp (hΦc _ hmemp) hΦH).mono hFsub
  have heq : ∀ w ∈ F, invExt K (Φ' w) = ψ (χ w) := fun w hw => by
    rw [hΦeq hw]
    exact hinvG _ (hψ'.2.mapsTo (hf.2.mapsTo hw))
  have := tendsto_nhds_unique (hc₁.tendsto.congr' (eventually_nhdsWithin_of_forall heq))
    (hgc v hv).tendsto
  rw [this, hχΔ v hv]

/-- **Aux. lemma 40 at infinity** (Specification p. 203, `σ = ∞`), under Aux. lemma 37's
attachment constancy: the terminal clock value `ℓ(∞)` is positive; the erased path `γ̂_C` is
continuous on `[0, ℓ(∞))`, starts at `y₀` and stays in `C̄`; erasure changes no range in `C`
((GC2)); and in every Jordan coordinate `ψ` of `C` at infinity the path `ζ = ψ ∘ γ̂_C` satisfies
conditions (a) and (b) of Proposition 6.12 on every `[0, S]`, `S < ℓ(∞)`. -/
theorem aux40 (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) :
    0 < clockEnd η C τ ∧ ContinuousOn (erasedPathInf η C τ) (Ico 0 (clockEnd η C τ)) ∧
      erasedPathInf η C τ 0 = α₁ 0 ∧
      MapsTo (erasedPathInf η C τ) (Ico 0 (clockEnd η C τ)) (closure C) ∧
      (∀ u ∈ Ico 0 (clockEnd η C τ),
        erasedPathInf η C τ '' Icc 0 u ∩ C = η '' Icc 0 (pocketFibreInf η C τ u) ∩ C) ∧
      ∀ S < clockEnd η C τ, DrivingCriterionA (fun v => ψ (erasedPathInf η C τ v)) S ∧
        DrivingCriterionB (fun v => ψ (erasedPathInf η C τ v)) S :=
  ⟨hP.clockEnd_pos hAC, hP.continuousOn_erasedPath hAC, hP.erasedPath_zero hAC,
    fun _ hv => hP.erasedPath_mem hv, fun _ hu => hP.erasedPath_image_inter hu,
    fun _ hS => ⟨hP.drivingCriterionA hAC hψ hS, hP.drivingCriterionB hψ hS⟩⟩

/-- **Aux. lemma 41 at infinity** (Specification p. 204), under Aux. lemma 37's attachment
constancy, for every Jordan coordinate `ψ` of `C` at infinity: on every `[0, S']`,
`0 < S' < ℓ(∞)`, the fillings of `ζ = ψ ∘ γ̂_C` are the hulls of a continuous driver `W'` after a
continuous strictly increasing capacity change `σ'`, and `ζ` has the uniform simple approximations
on every `[0, S]`, `S < S'`. -/
theorem aux41 (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {S' : ℝ} (hS'0 : 0 < S') (hS' : S' < clockEnd η C τ) :
    (∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧
      StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
      ∀ t ∈ Icc 0 S', fwdHull W' (σ' t) =
        fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 t)) ∧
      ∀ S < S', HasSimpleApproxOn (fun v => ψ (erasedPathInf η C τ v)) S := by
  have hsub : Icc 0 S' ⊆ Ico 0 (clockEnd η C τ) := fun v hv => ⟨hv.1, hv.2.trans_lt hS'⟩
  have key := fun {S : ℝ} (hSS' : S < S') =>
    exists_loewner_and_hasSimpleApproxOn_of_hasContinuousOwnFuture hS'0
      ((hP.continuousOn_ζ hAC hψ).mono hsub) (hP.ζ_zero hAC hψ) ((hP.mapsTo_ζ hψ).mono_left hsub)
      (hP.strictMonoOn_fillH_ζ hAC hψ hS') (hP.hasContinuousOwnFuture hAC hψ hS') hSS'
  exact ⟨(key (S := S' / 2) (by linarith)).1, fun S hS => (key hS).2⟩

/-- **Aux. lemmas 40–41 at infinity, existence form**: the pocket has a Jordan coordinate `ψ` at
infinity (`y₀ ↦ 0`) in which the erased path has a continuous Loewner driver up to its terminal
capacity time and the uniform simple approximations. -/
theorem exists_aux41 (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) :
    0 < clockEnd η C τ ∧ ∃ ψ : ℂ → ℂ, IsJordanCoordInf C (α₁ 0) ψ ∧
      ∀ S' ∈ Ioo 0 (clockEnd η C τ),
        (∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧
          StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
          ∀ t ∈ Icc 0 S', fwdHull W' (σ' t) =
            fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 t)) ∧
          ∀ S < S', HasSimpleApproxOn (fun v => ψ (erasedPathInf η C τ v)) S := by
  obtain ⟨ψ, hψ⟩ := hP.exists_isJordanCoordInf
  exact ⟨hP.clockEnd_pos hAC, ψ, hψ, fun S' hS' => hP.aux41 hAC hψ hS'.1 hS'.2⟩

/-! ### The terminal value -/

/-- **No final gap at infinity** (Specification p. 203: "If `σ = ∞`, reverse containment and
transience imply that every incoming point strictly after `x₀` is first visited at a finite time;
the attachments therefore tend to `x₀`. Constancy on a final infinite interval is again
impossible"): `ℓ(a) < ℓ(∞)` for every `a ≥ τ`. -/
theorem clock_lt_clockEnd (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) {a : ℝ} (ha : τ ≤ a) :
    pocketClockInf η C τ a < clockEnd η C τ := by
  refine lt_of_le_of_ne (hP.clock_le_clockEnd a) fun hℓ => ?_
  have hgap : ∀ t, a ≤ t → η t ∉ C := by
    intro t hat htC
    have htI := hP.mem_visitSet ((hP.nonneg.trans ha).trans hat) htC
    have := (hP.monotone_clock hat).trans_lt ((hP.clock_lt_of_mem_visitSet htI
      (lt_add_one t)).trans_le (hP.clock_le_clockEnd _))
    rw [hℓ] at this
    exact lt_irrefl _ this
  set u := lastVisit (fun t => η '' Icc 0 t) α₁ a with hudef
  have hu0 : 0 ≤ u := (hP.chart ha (Or.inl rfl)).1
  obtain ⟨t, ht⟩ := hP.visited₁ (u + 1) (mem_Ici.2 (by linarith))
  have hat : a ≤ t := by
    by_contra h
    push Not at h
    have := le_lastVisit (R := fun t => η '' Icc 0 t) hP.tendsto₁ (hP.isCompact_range a).isBounded
      (mem_Ici.2 (by linarith)) (monotone_image_Icc h.le ht)
    linarith
  have hc := (hAC a t ha hat fun t' ht' => hgap t' ht'.1).1
  have := le_lastVisit (R := fun t => η '' Icc 0 t) hP.tendsto₁ (hP.isCompact_range t).isBounded
    (mem_Ici.2 (by linarith)) ht
  rw [hc] at this
  linarith

/-- The fibre endpoints tend to `∞` at the terminal clock value. -/
theorem tendsto_fibre (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) :
    Tendsto (pocketFibreInf η C τ) (𝓝[<] (clockEnd η C τ)) atTop := by
  rw [Filter.tendsto_atTop]
  intro T
  have hlt := hP.clock_lt_clockEnd hAC (le_max_right T τ)
  filter_upwards [Ioo_mem_nhdsLT (max_lt hlt (hP.clockEnd_pos hAC))] with v hv
  have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨(le_max_right _ _).trans hv.1.le, hv.2⟩
  by_contra h
  push Not at h
  have := hP.monotone_clock (h.le.trans (le_max_left T τ))
  rw [hP.clock_fibre hv'] at this
  linarith [le_max_left (pocketClockInf η C τ (max T τ)) 0, hv.1]

/-- **The terminal value of the erased path at infinity** (Specification p. 203: "at an infinite
terminal time it follows from its convergence to the original target. In the latter case `x₀` is
that target"): if the counterflow tends to its original target `∞` (the premise of Aux. lemma 40),
then `γ̂_C(v) → ∞` as `v ↑ ℓ(∞)`, and `ζ = ψ ∘ γ̂_C → ∞` in every Jordan coordinate at infinity. -/
theorem tendsto_erasedPath (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun v => ‖erasedPathInf η C τ v‖) (𝓝[<] (clockEnd η C τ)) atTop :=
  htr.comp (hP.tendsto_fibre hAC)

theorem tendsto_ζ (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun v => ψ (erasedPathInf η C τ v)) (𝓝[<] (clockEnd η C τ)) (cobounded ℂ) := by
  refine hψ.2.2.2.2.2.2.comp (tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1
    (hP.tendsto_erasedPath hAC htr), tendsto_principal.2 ?_⟩)
  filter_upwards [Ioo_mem_nhdsLT (hP.clockEnd_pos hAC)] with v hv
  exact hP.erasedPath_mem ⟨hv.1.le, hv.2⟩

end IsReversePocketInf

end InteractingSLE.Sec6
