/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdRefl
import InteractingSLE.Spec.Sec7.WallOrdArcs
import InteractingSLE.Spec.Sec7.R6FcJordanInf
import InteractingSLE.Spec.Sec7.PocketStopMarkedPathInf

/-!
# R.5's outer collars land in the reference hull (`R5Lift.R7OuterReflInf`, pocket opening at the flow seed)

Packet PROVE-WALL-ORDER, target (3), seed-opening shape. The argument of `WallOrdRefl.lean` with the pocket's junction
at `∞` (no terminal corner and no terminal time): walls parametrized from `m(y₀)` towards `∞`, attachments the last
visited parameters (`Sec6.lastVisit`), Aux. 37 in the form `AttachmentConstancyInf`, and the Jordan coordinate at
infinity (`Sec6.IsJordanCoordInf`, continuous on the whole closed pocket).

* **`exists_mem_pocket_before_lastVisit`**, **`mem_closure_pocket_visitsInf`**, `mem_closure_pocket_visits_cfgInfR/L`:
  a newly visited wall point is reached through the pocket;
* **`outerRefl_pathwiseInf`**, **`r7OuterReflInf_of_cfg`**: `R5Lift.R7OuterReflInf` on every seed-opening
  reverse-contained pocket test.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.WallOrd

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

section Generic

variable {η : ℝ → ℂ} {C : Set ℂ} {α : ℝ → ℂ} {τ : ℝ}

/-- **A newly visited point of an arm at infinity is preceded by pocket visits** (Aux. lemma 37 at infinity with the
reverse first-visit order from `α 0`). -/
theorem exists_mem_pocket_before_lastVisit (hη : ContinuousOn η (Ici 0)) (hαc : ContinuousOn α (Ici 0))
    (hαt : Tendsto (fun v => ‖α v‖) atTop atTop)
    (hconst : ∀ a b : ℝ, τ ≤ a → a ≤ b → (∀ t ∈ Icc a b, η t ∉ C) →
      Sec6.lastVisit (fun t => η '' Icc 0 t) α b = Sec6.lastVisit (fun t => η '' Icc 0 t) α a)
    (hrev : Sec6.IsReverseVisitOrderInf α fun t => η '' Icc 0 t) {v t₁ a : ℝ} (hv : 0 ≤ v)
    (ht₁ : η t₁ = α v) (hfresh : α v ∉ η '' Ico 0 t₁) (hτa : τ ≤ a) (ha0 : 0 ≤ a) (ha : a < t₁)
    (h0 : α 0 ∈ η '' Icc 0 a) : ∃ t ∈ Icc a t₁, η t ∈ C := by
  by_contra hno
  push Not at hno
  have hc := hconst a t₁ hτa ha.le fun t ht => hno t ht
  have hK : ∀ t, IsCompact (η '' Icc 0 t) := fun t => isCompact_Icc.image_of_continuousOn (hη.mono fun u hu => hu.1)
  have hmem := Sec6.lastVisit_mem (R := fun t => η '' Icc 0 t) hαc hαt (hK a) ⟨0, mem_Ici.2 le_rfl, h0⟩
  have hle : v ≤ Sec6.lastVisit (fun t => η '' Icc 0 t) α t₁ :=
    Sec6.le_lastVisit (R := fun t => η '' Icc 0 t) hαt (hK t₁).isBounded hv ⟨t₁, ⟨ha0.trans ha.le, le_rfl⟩, ht₁⟩
  rw [hc] at hle
  exact hfresh (image_mono (Icc_subset_Ico_right ha) (hrev a v hv _ hmem.1 hle hmem.2))

/-- **A newly visited point of an arm at infinity is reached from the pocket.** -/
theorem mem_closure_pocket_visitsInf (hη : ContinuousOn η (Ici 0)) (hαc : ContinuousOn α (Ici 0))
    (hαt : Tendsto (fun v => ‖α v‖) atTop atTop)
    (hconst : ∀ a b : ℝ, τ ≤ a → a ≤ b → (∀ t ∈ Icc a b, η t ∉ C) →
      Sec6.lastVisit (fun t => η '' Icc 0 t) α b = Sec6.lastVisit (fun t => η '' Icc 0 t) α a)
    (hrev : Sec6.IsReverseVisitOrderInf α fun t => η '' Icc 0 t) {v t₁ a : ℝ} (hv : 0 ≤ v) (hvC : α v ∉ C)
    (ht₁ : η t₁ = α v) (hfresh : α v ∉ η '' Ico 0 t₁) (hτa : τ ≤ a) (ha0 : 0 ≤ a) (ha : a < t₁)
    (h0 : α 0 ∈ η '' Icc 0 a) : α v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ C}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hct : ContinuousWithinAt η (Ici 0) t₁ := hη t₁ (ha0.trans ha.le)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hct ε hε
  have ha'1 : max a (t₁ - δ / 2) < t₁ := max_lt ha (by linarith)
  have h0' : α 0 ∈ η '' Icc 0 (max a (t₁ - δ / 2)) := by
    obtain ⟨u, hu, hηu⟩ := h0
    exact ⟨u, ⟨hu.1, hu.2.trans (le_max_left _ _)⟩, hηu⟩
  obtain ⟨t, ht, htC⟩ := exists_mem_pocket_before_lastVisit hη hαc hαt hconst hrev hv ht₁ hfresh
    (hτa.trans (le_max_left _ _)) (ha0.trans (le_max_left _ _)) ha'1 h0'
  have htt : t ≠ t₁ := fun he => hvC (ht₁ ▸ he ▸ htC)
  have ht0 : (0 : ℝ) ≤ t := ha0.trans ((le_max_left _ _).trans ht.1)
  refine ⟨η t, ⟨t, ⟨⟨(le_max_left _ _).trans ht.1, lt_of_le_of_ne ht.2 htt⟩, htC⟩, rfl⟩, ?_⟩
  have hd : dist t t₁ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, le_max_right a (t₁ - δ / 2)]
  rw [← ht₁, dist_comm]
  exact hδε ht0 hd

end Generic

/-- The walls of a two-arc pocket at infinity lie in `ℍ` away from `0`. -/
theorem mem_H_of_mem_frontierInf {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} (hC : IsCfPocketInf C α₁ α₂) {z : ℂ}
    (hz : z ∈ frontier C) (hz0 : z ≠ 0) : z ∈ H := by
  rw [hC.frontier_eq] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · rcases (mem_Ici.1 hv).lt_or_eq with hlt | h0
    · exact hC.mem_H₁ v hlt
    · subst h0
      exact hC.mem_y.resolve_right hz0
  · rcases (mem_Ici.1 hv).lt_or_eq with hlt | h0
    · exact hC.mem_H₂ v hlt
    · subst h0
      rw [hC.seed] at hz0 ⊢
      exact hC.mem_y.resolve_right hz0

section Config

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The pocket-side visits of the right wall of a seed-opening reverse-contained pocket. -/
theorem mem_closure_pocket_visits_cfgInfR (hc : IsCfPocketConfigInf R L r W η) {v t₁ a : ℝ} (hv : 0 ≤ v)
    (ht₁ : η t₁ = cfArcRInf R L r v) (hfresh : cfArcRInf R L r v ∉ η '' Ico 0 t₁)
    (hτa : firstHit η (cfArcRInf R L r 0) ≤ a) (ha : a < t₁) :
    cfArcRInf R L r v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ cfPocket R L r}) := by
  have hT := hc.conf.isCfPocketInf hc.seed
  have hP := hc.isReversePocketInf
  have hvC : cfArcRInf R L r v ∉ cfPocket R L r := fun h => by
    have hF : cfArcRInf R L r v ∈ frontier (cfPocket R L r) := by
      rw [hT.frontier_eq]; exact Or.inl ⟨v, hv, rfl⟩
    rw [hT.isOpen.frontier_eq] at hF
    exact hF.2 h
  exact mem_closure_pocket_visitsInf hc.trace.2.1 hT.cont₁ hT.tendsto₁
    (fun a b h1 h2 h3 => (hc.attach a b h1 h2 h3).1) (cfArcRInf_rev hc.conf hc.seed hc.trace.1 hc.revR) hv hvC
    ht₁ hfresh hτa (hP.nonneg.trans hτa) ha ⟨_, ⟨hP.nonneg, hτa⟩, hP.first_y⟩

/-- The pocket-side visits of the left wall of a seed-opening reverse-contained pocket. -/
theorem mem_closure_pocket_visits_cfgInfL (hc : IsCfPocketConfigInf R L r W η) {v t₁ a : ℝ} (hv : 0 ≤ v)
    (ht₁ : η t₁ = cfArcLInf R L r v) (hfresh : cfArcLInf R L r v ∉ η '' Ico 0 t₁)
    (hτa : firstHit η (cfArcRInf R L r 0) ≤ a) (ha : a < t₁) :
    cfArcLInf R L r v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ cfPocket R L r}) := by
  have hT := hc.conf.isCfPocketInf hc.seed
  have hP := hc.isReversePocketInf
  have hvC : cfArcLInf R L r v ∉ cfPocket R L r := fun h => by
    have hF : cfArcLInf R L r v ∈ frontier (cfPocket R L r) := by
      rw [hT.frontier_eq]; exact Or.inr ⟨v, hv, rfl⟩
    rw [hT.isOpen.frontier_eq] at hF
    exact hF.2 h
  refine mem_closure_pocket_visitsInf hc.trace.2.1 hT.cont₂ hT.tendsto₂
    (fun a b h1 h2 h3 => (hc.attach a b h1 h2 h3).2) (cfArcLInf_rev hc.conf hc.seed hc.trace.1 hc.revL) hv hvC
    ht₁ hfresh hτa (hP.nonneg.trans hτa) ha ?_
  rw [hT.seed]
  exact ⟨_, ⟨hP.nonneg, hτa⟩, hP.first_y⟩

end Config

section Random

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
  {c : Ω → Chart} {ω : Ω}

/-- **The contradiction step at infinity** (see `outerRefl_contra`). -/
theorem outerRefl_contraInf {W' : ℝ≥0 → Ω → ℝ}
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q qs : ℝ≥0} {s : ℝ} (hs0 : 0 ≤ s) (hqs_live : (qs : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (holddom : ((relChart c (travAllInf R L r η ψ) qs ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 s)))
    (hcurdom : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 (leftStopInf R L r η ψ q ω)))) {ξ : ℝ} {p : ℂ} {x ε : ℝ}
    (hcol : IsRefCollar (relChart c (travAllInf R L r η ψ) qs ω) (relChart c (travAllInf R L r η ψ) q ω) ξ p x ε)
    {F : ℂ → ℂ} (hlimF : ∀ u : ℝ, Tendsto (relChart c (travAllInf R L r η ψ) qs ω).2.1 (𝓝[H] (u : ℂ)) (𝓝 (F u)))
    (hNe : ∀ u : ℝ, (𝓝[H] (u : ℂ)).NeBot) {u : ℝ} (hzF : F u ∈ frontier (cfPocket (R ω) (L ω) r))
    (hzH : F u ∈ H) (hzK : F u ∉ fillH (η ω '' Icc 0 s))
    (hzT : F u ∈ η ω '' Icc 0 (leftStopInf R L r η ψ q ω)) (hzs : F u ∉ η ω '' Icc 0 s)
    (hsI : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) < s) (hux : (u : ℂ) ∈ ball (x : ℂ) ε) : False := by
  set C := cfPocket (R ω) (L ω) r with hCdef
  set old := relChart c (travAllInf R L r η ψ) qs ω with holddef
  obtain ⟨hP, hJ⟩ := pocket_of_cfgInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hTopo := hcfg.conf.isCfPocketInf hcfg.seed
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hηc : ContinuousOn (η ω) (Ici 0) := hcfg.trace.2.1
  have hCH : C ⊆ H := hTopo.subset_H
  have hold : old.IsConformal := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hqs_live hc
  -- the first visit of the landing, in `(s, T]`
  obtain ⟨htz0, htz, hfresh⟩ := firstHit_spec hηc
    (⟨leftStopInf R L r η ψ q ω, hzT⟩ : ∃ t, F u ∈ η ω '' Icc 0 t)
  have htzT : firstHit (η ω) (F u) ≤ leftStopInf R L r η ψ q ω := by
    obtain ⟨t₀, ht₀, hηt₀⟩ := hzT
    exact (csInf_le (s := {v ∈ Ici (0 : ℝ) | η ω v = F u}) ⟨0, fun _ h => h.1⟩ ⟨ht₀.1, hηt₀⟩).trans ht₀.2
  have hstz : s < firstHit (η ω) (F u) := lt_of_not_ge fun h => hzs ⟨_, ⟨htz0, h⟩, htz⟩
  -- the counterflow reaches it through the pocket (Aux. 37)
  have hvis : F u ∈ closure (η ω '' {t | t ∈ Ico s (firstHit (η ω) (F u)) ∧ η ω t ∈ C}) := by
    have hzF' := hzF
    rw [hTopo.frontier_eq] at hzF'
    rcases hzF' with ⟨v, hv, hve⟩ | ⟨v, hv, hve⟩
    · have := mem_closure_pocket_visits_cfgInfR hcfg hv (htz.trans hve.symm) (by rw [hve]; exact hfresh) hsI.le
        hstz
      rwa [hve] at this
    · have := mem_closure_pocket_visits_cfgInfL hcfg hv (htz.trans hve.symm) (by rw [hve]; exact hfresh) hsI.le
        hstz
      rwa [hve] at this
  -- near the landing the pocket lies in the old domain
  have hKo : IsOpen (H \ fillH (η ω '' Icc 0 s)) := by
    rw [← hcfg.trace.2.2 s hs0]
    exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull hcfg.continuous_W hs0
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hKo (F u) ⟨hzH, hzK⟩
  have hloc : ∀ w ∈ C ∩ ball (F u) δ, w ∈ (old.dom : Set ℂ) := fun w hw => by
    rw [holddom]; exact ⟨hw.1, hδK hw.2⟩
  -- the old chart is continuous at the landing
  obtain ⟨Wc, hWc, hWc0, -, -, -, hrel0⟩ :=
    exists_relChart_eq_loewner (c := c) (γ := travAllInf R L r η ψ) hγ hqs_live
  have hrel : old = (c ω).loewner Wc qs := hrel0
  have hzC : F u ∈ closure C := frontier_subset_closure hzF
  have hψc : Tendsto (ψ ω) (𝓝[C] (F u)) (𝓝 (ψ ω (F u))) := ((hJ.1 _ hzC).mono subset_closure).tendsto
  have hψim : (ψ ω (F u)).im = 0 := hJ.2.2.2.2.1 _ hzF
  have hψX : ψ ω (F u) = ((ψ ω (F u)).re : ℂ) := Complex.ext (by simp) (by simp [hψim])
  have hy₀C : cfArcRInf (R ω) (L ω) r 0 ∈ closure C := by
    refine frontier_subset_closure ?_
    rw [hTopo.frontier_eq]
    exact Or.inl ⟨0, mem_Ici.2 le_rfl, rfl⟩
  have hX0 : (ψ ω (F u)).re ≠ 0 := by
    intro hX
    have h1 : ψ ω (F u) = ψ ω (cfArcRInf (R ω) (L ω) r 0) := by
      rw [hψX, hX, hJ.2.2.2.2.2.1]; simp
    have h2 := hJ.2.1 hzC hy₀C h1
    exact hzs ⟨_, ⟨hP.nonneg, hsI.le⟩, hP.first_y.trans h2.symm⟩
  have hXK : (((ψ ω (F u)).re : ℝ) : ℂ) ∉ closure (fwdHull Wc qs) := by
    rw [← hψX]
    refine R6Fc.notMem_closure_of_ball_subsetInf hJ ((QuantumZipper.fwdHull_mono (W := Wc)).2 _) hzC hδ
      fun w hw => ⟨hw.1, ?_⟩
    have hwd := hloc w hw
    rw [hrel] at hwd
    have := (fwd_mem_compl_of_mem_dom_loewner hc hWc hWc0 qs.coe_nonneg hwd).1
    rwa [heq hw.1] at this
  obtain ⟨y, hy⟩ := tendsto_loewner_fwd_of_alive hc hdom heq hWc hWc0 qs.coe_nonneg
    (by rw [← hψX]; exact hψc) hX0 hXK
  rw [← hrel] at hy
  -- its limit is `u`
  have hinv : Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝[(old.dom : Set ℂ)] (F u)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlimF u, eventually_nhdsWithin_of_forall fun w hw => hold.inv_mem_dom hw⟩
  have hyu : (y : ℂ) = u := by
    have := hNe u
    refine tendsto_nhds_unique (hy.comp hinv) ?_
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    exact (hold.2.2 w hw).symm
  -- a pocket visit near the landing is in the collar image, hence off `K_T`
  set Pv := η ω '' {t | t ∈ Ico s (firstHit (η ω) (F u)) ∧ η ω t ∈ C} with hPv
  have hzPv : F u ∈ closure (Pv ∩ ball (F u) δ) := by
    rw [Metric.mem_closure_iff] at hvis ⊢
    intro e he
    obtain ⟨b, hb, hbd⟩ := hvis (min e δ) (lt_min he hδ)
    exact ⟨b, ⟨hb, by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hbd (min_le_right _ _)⟩,
      lt_of_lt_of_le hbd (min_le_left _ _)⟩
  have : (𝓝[Pv ∩ ball (F u) δ] (F u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzPv
  have hPvC : ∀ w ∈ Pv, w ∈ C := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  have hle : 𝓝[Pv ∩ ball (F u) δ] (F u) ≤ 𝓝[(old.dom : Set ℂ)] (F u) :=
    nhdsWithin_mono _ fun w hw => hloc w ⟨hPvC w hw.1, hw.2⟩
  have hball : ball (x : ℂ) ε ∈ 𝓝 (y : ℂ) := by
    rw [hyu]; exact isOpen_ball.mem_nhds hux
  have h1 : ∀ᶠ w in 𝓝[Pv ∩ ball (F u) δ] (F u), old.1 w ∈ ball (x : ℂ) ε := (hy.mono_left hle) hball
  obtain ⟨w, hw1, hw2⟩ := (h1.and self_mem_nhdsWithin).exists
  obtain ⟨⟨t, ⟨htI, htC⟩, rfl⟩, hwb⟩ := hw2
  have hwd := hloc _ ⟨htC, hwb⟩
  have hcm : old.2.1 (old.1 (η ω t)) ∈ ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) :=
    hcol.2.1 ⟨_, ⟨hold.fwd_mem hwd, hw1⟩, rfl⟩
  rw [hold.inv_fwd hwd, hcurdom] at hcm
  exact hcm.2.2 ⟨hCH htC, Or.inl (subset_closure ⟨t, ⟨hs0.trans htI.1, htI.2.le.trans htzT⟩, rfl⟩)⟩

/-- **The outer collars' old landings lie in the reference hull** (one sample, seed-opening reverse-contained
pocket). -/
theorem outerRefl_pathwiseInf {W' : ℝ≥0 → Ω → ℝ} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {ξ : ℝ}
    (hpX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ R5Wall.outerExcInf R L r η ψ q ω)
    {s : ℝ} (hs0 : 0 ≤ s) (hsC : η ω s ∈ cfPocket (R ω) (L ω) r)
    (hsq : (visitCapInf R L r η ψ ω s).toNNReal ≤ q) {x ε : ℝ}
    (hcol : IsRefCollar (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω)
      (relChart c (travAllInf R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε)
    (hpK : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) s) :
    ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
      extendFrom H (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).2.1 u ∈
        fwdHull (fun t : ℝ => W' t.toNNReal ω) s := by
  set C := cfPocket (R ω) (L ω) r with hCdef
  set qs := (visitCapInf R L r η ψ ω s).toNNReal with hqsdef
  set cur := relChart c (travAllInf R L r η ψ) q ω with hcurdef
  set old := relChart c (travAllInf R L r η ψ) qs ω with holddef
  set p := extendFrom H cur.2.1 ξ with hpdef
  set T := leftStopInf R L r η ψ q ω with hTdef
  obtain ⟨hP, hJ⟩ := pocket_of_cfgInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hAC := hcfg.attach
  have hTopo := hcfg.conf.isCfPocketInf hcfg.seed
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hηc : ContinuousOn (η ω) (Ici 0) := hcfg.trace.2.1
  have hfill : ∀ t : ℝ, 0 ≤ t → fwdHull (fun t : ℝ => W' t.toNNReal ω) t = fillH (η ω '' Icc 0 t) :=
    fun t ht => hcfg.trace.2.2 t ht
  have hCH : C ⊆ H := hTopo.subset_H
  -- the reference time is an interior visit, its capacity is live, and `T⁰(c(s)) = s ≤ T`
  have hsI : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) < s := hP.mem_Ioi_of_mem hs0 hsC
  have hrc0 : 0 ≤ visitCapInf R L r η ψ ω s :=
    (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hJ).capClock_nonneg (relTimeInf_nonneg hP hAC hsI.le)
  have hqs : (qs : ℝ) = visitCapInf R L r η ψ ω s := Real.coe_toNNReal _ hrc0
  have hsq' : visitCapInf R L r η ψ ω s ≤ q := by rw [← hqs]; exact_mod_cast hsq
  have hqs_live : (qs : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := lt_of_le_of_lt (by exact_mod_cast hsq) hq
  have hq' : ENNReal.ofReal (q : ℝ) <
      capLife (travInf (η ω) C (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq
  have hrs' : ENNReal.ofReal (visitCapInf R L r η ψ ω s) <
      capLife (travInf (η ω) C (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [← hqs, ENNReal.ofReal_coe_nnreal]; exact hqs_live
  have hvis_s : ambTime0Inf (η ω) C (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)
      (visitCapInf R L r η ψ ω s) = s := ambTime0Inf_relCapInf_of_visit hP hAC hJ ⟨hsI, hsC⟩
  have hTs : leftStopInf R L r η ψ qs ω = s := by
    show ambTime0Inf _ _ _ _ (qs : ℝ) = s
    rw [hqs]; exact hvis_s
  have hτT : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ T := le_ambTime0Inf hP hAC (ψ ω) q
  have hsT : s ≤ T := by
    have h1 := (ambTime0Inf_le_iff hP hAC hJ q.coe_nonneg hq' hτT).1 le_rfl
    have h2 := (ambTime0Inf_le_iff hP hAC hJ hrc0 hrs' hτT).2 (hsq'.trans h1)
    rwa [hvis_s] at h2
  -- the two domains
  have hcurdom : (cur.dom : Set ℂ) = C ∩ (H \ fillH (η ω '' Icc 0 T)) :=
    current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq
  have holddom : (old.dom : Set ℂ) = C ∩ (H \ fillH (η ω '' Icc 0 s)) := by
    rw [← hTs]; exact current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hqs_live
  have hKsT : fillH (η ω '' Icc 0 s) ⊆ fillH (η ω '' Icc 0 T) := fillH_mono (image_mono (Icc_subset_Icc_right hsT))
  -- the current landing `p` is visited by `s`
  obtain ⟨-, -, hpfr⟩ := current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq ξ
  have hpKs : p ∈ fillH (η ω '' Icc 0 s) := by rw [← hfill s hs0]; exact hpK
  have hpcl : p ∈ closure (H \ fillH (η ω '' Icc 0 s)) :=
    closure_mono (fun z (hz : z ∈ C ∩ (H \ fillH (η ω '' Icc 0 T))) =>
      (⟨hz.2.1, fun h => hz.2.2 (hKsT h)⟩ : z ∈ H \ fillH (η ω '' Icc 0 s))) (frontier_subset_closure hpfr)
  have hcpt : ∀ t, IsClosed (η ω '' Icc 0 t) := fun t =>
    (isCompact_Icc.image_of_continuousOn (hηc.mono fun u hu => hu.1)).isClosed
  have hpS : p ∈ η ω '' Icc 0 s := by
    have := mem_closure_of_mem_fillH_of_mem_closure_compl hpKs hpcl
    rwa [(hcpt s).closure_eq] at this
  have hpT : p ∈ η ω '' Icc 0 T := image_mono (Icc_subset_Icc_right hsT) hpS
  -- `p` is neither a time-`T` attachment nor `0`
  simp only [R5Wall.outerExcInf, mem_insert_iff, mem_singleton_iff, not_or] at hpX
  obtain ⟨hA₁, hA₂, hp0⟩ := hpX
  -- near `p` the walls are visited by `T`
  have hrevR := cfArcRInf_rev hcfg.conf hcfg.seed hcfg.trace.1 hcfg.revR
  have hrevL := cfArcLInf_rev hcfg.conf hcfg.seed hcfg.trace.1 hcfg.revL
  obtain ⟨r₁, hr₁, hball₁⟩ := R5Out.exists_ball_frontier_subset_rangeInf_of_wallOrder hTopo hηc hrevR hrevL
    ⟨_, ⟨hP.nonneg, hτT⟩, hP.first_y⟩ hpT hA₁ hA₂
  -- the old chart and its inverse extension
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_cases (Or.inr hψ) hc hdom heq
  obtain ⟨F, hF, hFc, hFD⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hqs_live hE hEc
  have hold : old.IsConformal := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hqs_live hc
  have hxbar : ∀ u : ℝ, (u : ℂ) ∈ Hbar := fun u => mem_Hbar_of_im_eq_zero (by simp)
  have hlimF : ∀ u : ℝ, Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝 (F u)) := fun u =>
    (((hFc _ (hxbar u)).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hF hw)
  have hcl : ∀ u : ℝ, (u : ℂ) ∈ closure H := fun u => by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hxbar u
  have hNe : ∀ u : ℝ, (𝓝[H] (u : ℂ)).NeBot := fun u => mem_closure_iff_nhdsWithin_neBot.1 (hcl u)
  have hFx : F x = p := by
    have := hNe x
    exact tendsto_nhds_unique (hlimF x) (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1
  have hext : ∀ u : ℝ, extendFrom H old.2.1 u = F u := fun u => extendFrom_eq (hcl u) (hlimF u)
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
  obtain ⟨ρ₀, hρ₀, hρF⟩ := Metric.continuousWithinAt_iff.1 (hFc _ (hxbar x)) (min r₁ ‖p‖) (lt_min hr₁ hpn)
  refine ⟨min ρ₀ ε, lt_min hρ₀ hcol.1, fun u hu => ?_⟩
  rw [hext, hfill s hs0]
  have hux : dist (u : ℂ) x < ρ₀ := lt_of_lt_of_le (mem_ball.1 hu) (min_le_left _ _)
  have hzb : dist (F u) p < min r₁ ‖p‖ := by
    have := hρF (hxbar u) hux
    rwa [hFx] at this
  have hzC : F u ∈ closure C := by
    obtain ⟨y, hy, hFy⟩ := hFD (hxbar u)
    exact hFy ▸ hED hy
  have hzfr : F u ∉ (old.dom : Set ℂ) := by
    have := inverse_real_landing_mem_frontier hold (hlimF u)
    rw [old.dom.isOpen.frontier_eq] at this
    exact this.2
  rw [holddom] at hzfr
  by_cases hzinC : F u ∈ C
  · by_contra hzK
    exact hzfr ⟨hzinC, hCH hzinC, hzK⟩
  -- a wall point near `p`, visited by `T`
  have hzF : F u ∈ frontier C := ⟨hzC, by rwa [hTopo.isOpen.interior_eq]⟩
  have hzT : F u ∈ η ω '' Icc 0 T := hball₁ ⟨hzF, lt_of_lt_of_le hzb (min_le_left _ _)⟩
  have hz0 : F u ≠ 0 := fun h => by
    have := lt_of_lt_of_le hzb (min_le_right _ _)
    rw [h, dist_zero_left] at this
    exact lt_irrefl _ this
  have hzH : F u ∈ H := mem_H_of_mem_frontierInf hTopo hzF hz0
  by_contra hzK
  have hzs : F u ∉ η ω '' Icc 0 s := fun h => hzK ⟨hzH, Or.inl (subset_closure h)⟩
  exact outerRefl_contraInf hcfg hψ hc hdom heq hs0 hqs_live holddom hcurdom hcol hlimF hNe hzF hzH hzK hzT hzs
    hsI (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 hu) (min_le_right _ _)))

/-- **`R5Lift.R7OuterReflInf` holds on every seed-opening reverse-contained pocket test** (target (3), seed-opening
shape). -/
theorem r7OuterReflInf_of_cfg [MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hX : ∀ ω ∈ A, R5Wall.outerExcInf R L r η ψ q ω ⊆ X ω) :
    R5Lift.R7OuterReflInf P A R L r η ψ xL xR c W' ζ' X q := by
  refine Eventually.of_forall fun ω hω hq ξ _ hpX _ i x ε hev hsC hcol hpK => ?_
  have hpK' : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
      fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i) := by
    rw [← hev.2.2.2.2]; exact hpK
  exact outerRefl_pathwiseInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) hq
    (fun h => hpX (hX ω hω h)) (rationalOriginalTime i).coe_nonneg hsC hev.2.2.2.1 hcol hpK'

end Random

end InteractingSLE.Sec7.WallOrd
