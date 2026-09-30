import QuantumZipper.Proofs.Zipper.SWCoreNA2Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2 (base): per-scale variance and modulus bounds for pushed and image circles of a uniform family

Task SWC-NA (`handoff/SW-CORE.md` §5). For a finite-parameter family `(F q, c q, a q)` of maps of
one area class `AreaClass x₁ x₂ y₁ y₂ ρ M m`, centres in the rectangle and radius factors in
`[1,2]`, Lipschitz in `q`, the pushed circles `circM.map (swcPhiPush F c a k q)` and image circles
`circM.map (swcPhiRound F c a k q)` satisfy, for all `k ≥ k₀`, the hypotheses `hvar` and `hmod` of
`swcNA2_distortion_small`.

Proof: `hvar` is the per-map estimate `swcVA_kernelCov2_push_le` (SW arXiv:1605.06171, Lemma 3.4,
(3.20), p. 15–16) after identifying `circM`-pushforwards of circle parametrizations with folded
circles; `hmod` is the generic map-direction energy bound `swcVA_kernelCov2_map_map_le` applied
with `σ = circM` to the two parametrizations (centre, radius and map changing at once), with the
parametrizations `O(‖q − q'‖)`-close by the Lipschitz hypotheses and Cauchy estimates. Own
elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC TwoPoint Thm18Asm.G1RC

section NA2Inst

theorem swcNA2I_frost_mono {ν : Measure ℂ} {α C C' : ℝ} (h : IsFrostman ν α C) (hC : C ≤ C') :
    IsFrostman ν α C' := fun w s hs =>
  (h w s hs).trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hs.le α))

/-- `swcVA_kernelCov2_map_map_le` (SWCoreVAPsi.lean) for a probability measure `σ` on any
measurable space (same proof). -/
theorem swcNA2I_kernelCov2_map_map_le {α : Type*} [MeasurableSpace α] {σ : Measure α} [IsProbabilityMeasure σ]
    {f g : α → ℂ}
    (hf : Measurable f) (hg : Measurable g) {C B ε : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hFf : IsFrostman (σ.map f) 1 C) (hFg : IsFrostman (σ.map g) 1 C)
    (hfB : ∀ᵐ x ∂σ, ‖f x‖ ≤ B) (hgB : ∀ᵐ x ∂σ, ‖g x‖ ≤ B)
    (hfg : ∀ᵐ x ∂σ, ‖f x - g x‖ ≤ ε) :
    |kernelCov2 neumannH (σ.map f, σ.map g) (σ.map f, σ.map g)| ≤
      2 * (swcPotK C B * ε ^ (1 / 2 : ℝ)) := by
  have : IsProbabilityMeasure (σ.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (σ.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hsuppf : ∀ᵐ y ∂σ.map f, ‖y‖ ≤ B :=
    (ae_map_iff hf.aemeasurable (measurableSet_le measurable_norm measurable_const)).2 hfB
  have hsuppg : ∀ᵐ y ∂σ.map g, ‖y‖ ≤ B :=
    (ae_map_iff hg.aemeasurable (measurableSet_le measurable_norm measurable_const)).2 hgB
  -- potentials: bounded and Hölder on `B̄(0,B)`
  have hmass : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], κ.real univ = 1 := fun κ _ => by
    simp
  have hpot : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], IsFrostman κ 1 C →
      (∀ᵐ y ∂κ, ‖y‖ ≤ B) →
      (∀ x : ℂ, ‖x‖ ≤ B → |neuPot κ x| ≤ 2 * (C / 1) + 2 * (Real.log (B + B + 1) * 1)) ∧
      ∀ x x' : ℂ, ‖x‖ ≤ B → ‖x'‖ ≤ B →
        |neuPot κ x - neuPot κ x'| ≤ swcPotK C B * ‖x - x'‖ ^ (1 / 2 : ℝ) := by
    intro κ _ hF hsupp
    refine ⟨fun x hx => ?_, fun x x' hx hx' => ?_⟩
    · have := abs_neuPot_le hF one_pos hC hB hsupp hx
      rwa [hmass κ] at this
    · have := abs_neuPot_sub_le hF one_pos le_rfl hC hB hsupp hx hx'
      rw [hmass κ] at this
      simpa [swcPotK] using this
  -- the kernel as integrals of potentials
  have hkc : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ] (h : α → ℂ), Measurable h →
      kernelCov neumannH (σ.map h) κ = ∫ x, neuPot κ (h x) ∂σ := by
    intro κ _ h hh
    show ∫ y, neuPot κ y ∂σ.map h = _
    rw [integral_map hh.aemeasurable (measurable_neuPot κ).aestronglyMeasurable]
  have hint : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], IsFrostman κ 1 C →
      (∀ᵐ y ∂κ, ‖y‖ ≤ B) → ∀ h : α → ℂ, Measurable h → (∀ᵐ x ∂σ, ‖h x‖ ≤ B) →
      Integrable (fun x => neuPot κ (h x)) σ := by
    intro κ _ hF hsupp h hh hhB
    refine Integrable.of_bound ((measurable_neuPot κ).comp hh).aestronglyMeasurable
      (2 * (C / 1) + 2 * (Real.log (B + B + 1) * 1)) ?_
    filter_upwards [hhB] with x hx
    rw [Real.norm_eq_abs]
    exact (hpot κ hF hsupp).1 _ hx
  have hdiff : ∀ (κ : Measure ℂ) [IsProbabilityMeasure κ], IsFrostman κ 1 C →
      (∀ᵐ y ∂κ, ‖y‖ ≤ B) →
      |∫ x, neuPot κ (f x) ∂σ - ∫ x, neuPot κ (g x) ∂σ| ≤ swcPotK C B * ε ^ (1 / 2 : ℝ) := by
    intro κ _ hF hsupp
    have hK0 : 0 ≤ swcPotK C B := by
      unfold swcPotK
      have : 0 ≤ Real.log (B + B + 1) := Real.log_nonneg (by linarith)
      positivity
    rw [← integral_sub (hint κ hF hsupp f hf hfB) (hint κ hF hsupp g hg hgB),
      ← Real.norm_eq_abs]
    calc ‖∫ x, (neuPot κ (f x) - neuPot κ (g x)) ∂σ‖
        ≤ swcPotK C B * ε ^ (1 / 2 : ℝ) * σ.real univ :=
          norm_integral_le_of_norm_le_const (by
            filter_upwards [hfB, hgB, hfg] with x h1 h2 h3
            rw [Real.norm_eq_abs]
            refine ((hpot κ hF hsupp).2 _ _ h1 h2).trans ?_
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg _) h3 (by norm_num)) hK0)
      _ = swcPotK C B * ε ^ (1 / 2 : ℝ) := by simp
  have e : kernelCov2 neumannH (σ.map f, σ.map g) (σ.map f, σ.map g) =
      (∫ x, neuPot (σ.map f) (f x) ∂σ - ∫ x, neuPot (σ.map f) (g x) ∂σ) -
        (∫ x, neuPot (σ.map g) (f x) ∂σ - ∫ x, neuPot (σ.map g) (g x) ∂σ) := by
    simp only [kernelCov2]
    rw [hkc (σ.map f) f hf, hkc (σ.map g) f hf, hkc (σ.map f) g hg, hkc (σ.map g) g hg]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have h1 := hdiff (σ.map f) hFf hsuppf
  have h2 := hdiff (σ.map g) hFg hsuppg
  linarith

theorem swcNA2I_potK_mono {C C' B B' : ℝ} (hC : C ≤ C') (hB : 0 ≤ B) (hB' : B ≤ B') :
    swcPotK C B ≤ swcPotK C' B' := by
  unfold swcPotK
  have : Real.log (B + B + 1) ≤ Real.log (B' + B' + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 : 4 * C / 1 ≤ 4 * C' / 1 := by linarith
  have h5 : C / 1 ≤ C' / 1 := by linarith
  linarith

theorem swcNA2I_mem_thick {x₁ x₂ y₁ y₂ δ r : ℝ} {z u : ℂ} (hz : z ∈ rectC x₁ x₂ y₁ y₂)
    (hu : ‖u - z‖ ≤ r) (hr : r < δ) : u ∈ thickening δ (rectC x₁ x₂ y₁ y₂) :=
  mem_thickening_iff.2 ⟨z, hz, by rw [dist_eq_norm]; linarith⟩

theorem swcNA2I_circ_norm (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circleMap z r θ - z‖ = r := by
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr]

theorem swcNA2I_circ_sub (z z' : ℂ) (r r' θ : ℝ) :
    ‖circleMap z r θ - circleMap z' r' θ‖ ≤ ‖z - z'‖ + |r - r'| := by
  have e : circleMap z r θ - circleMap z' r' θ = (z - z') + circleMap 0 (r - r') θ := by
    simp only [circleMap]; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_circleMap_zero]

/-- The `circM`-pushforward of a pushed circle parametrization is the pushed folded circle. -/
theorem swcNA2I_map_push {x₁ x₂ y₁ y₂ ρ M m : ℝ} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) {z : ℂ} (hz : z ∈ rectC x₁ x₂ y₁ y₂) {r : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hrz : r ≤ z.im) :
    circM.map (fun θ => ψ (circleMap z r θ)) = (foldedCircle z r).map ψ := by
  classical
  set U := thickening ρ (rectC x₁ x₂ y₁ y₂) with hU
  set ψt := U.piecewise ψ 0 with hψt
  have hψtm : Measurable ψt :=
    hψ.1.continuousOn.measurable_piecewise continuousOn_const isOpen_thickening.measurableSet
  have hmem : ∀ u : ℂ, ‖u - z‖ = r → ψt u = ψ u := fun u hu =>
    piecewise_eq_of_mem _ _ _ (swcNA2I_mem_thick hz hu.le hrρ)
  have e1 : (fun θ => ψ (circleMap z r θ)) = ψt ∘ circleMap z r := by
    funext θ; exact (hmem _ (swcNA2I_circ_norm z hr.le θ)).symm
  rw [e1, ← Measure.map_map hψtm (continuous_circleMap z r).measurable,
    ← Thm18Asm.G1RC.circleUnif_eq_map, ← foldedCircle_eq_circleUnif hr.le hrz]
  refine Measure.map_congr ?_
  rw [foldedCircle_eq_circleUnif hr.le hrz]
  filter_upwards [CircleMV.ae_circleUnif z r] with u hu
  rw [abs_of_pos hr] at hu
  exact hmem u hu

/-- The `circM`-pushforward of a round circle parametrization is the folded circle. -/
theorem swcNA2I_map_round {w : ℂ} {s : ℝ} (hs : 0 ≤ s) (hsw : s ≤ w.im) :
    circM.map (circleMap w s) = foldedCircle w s := by
  rw [foldedCircle_eq_circleUnif hs hsw, Thm18Asm.G1RC.circleUnif_eq_map]

theorem swcNA2I_deriv_le {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) {u : ℂ}
    (hu : u ∈ thickening (ρ / 2) (rectC x₁ x₂ y₁ y₂)) : ‖deriv ψ u‖ ≤ |M| / (ρ / 4) :=
  swcVA_norm_deriv_le hρ hψ.1 (fun z hz => (hψ.2.2.1 z hz).1.trans (le_abs_self M)) hu

/-- **Per-scale variance bound** in the `circM` parametrization. -/
theorem swcNA2I_var {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hy : 0 < y₁) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 < R₀ ∧ ∀ ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m, ∀ z ∈ rectC x₁ x₂ y₁ y₂,
      ∀ r : ℝ, 0 < r → r ≤ R₀ →
        |kernelCov2 neumannH (circM.map (fun θ => ψ (circleMap z r θ)),
            circM.map (circleMap (ψ z) (r * ‖deriv ψ z‖)))
          (circM.map (fun θ => ψ (circleMap z r θ)),
            circM.map (circleMap (ψ z) (r * ‖deriv ψ z‖)))| ≤ C * r := by
  obtain ⟨C, r₀, hC, hr₀, h⟩ :=
    swcVA_kernelCov2_push_le (a := x₁) (b := x₂) (d := y₂) (M := M) hy hρ hm
  set M₁ := |M| / (ρ / 4) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  refine ⟨C, min r₀ (min (ρ / 2) (min y₁ (ρ / (M₁ + 1)))), hC,
    lt_min hr₀ (lt_min (by positivity) (lt_min hy (by positivity))),
    fun ψ hψ z hz r hr hrr => ?_⟩
  have hr0 : r ≤ r₀ := hrr.trans (min_le_left _ _)
  have hr1 : r ≤ ρ / 2 := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r ≤ y₁ :=
    hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr3 : r ≤ ρ / (M₁ + 1) :=
    hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hzU : z ∈ thickening ρ (rectC x₁ x₂ y₁ y₂) := self_subset_thickening hρ _ hz
  have hd : ‖deriv ψ z‖ ≤ M₁ :=
    swcNA2I_deriv_le hρ hψ (self_subset_thickening (by positivity) _ hz)
  have hs : r * ‖deriv ψ z‖ ≤ (ψ z).im := by
    have h1 : r * ‖deriv ψ z‖ ≤ ρ / (M₁ + 1) * (M₁ + 1) :=
      mul_le_mul hr3 (by linarith) (norm_nonneg _) (by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at h1
    linarith [(hψ.2.2.1 z hzU).2]
  rw [swcNA2I_map_push hψ hz hr (by linarith) (hr2.trans hz.2.1),
    swcNA2I_map_round (by positivity) hs]
  exact h ψ hψ z hz r hr hr0

/-- **Per-scale modulus for pushed circles** (map, centre and radius changing at once). -/
theorem swcNA2I_push_mod {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hy : 0 < y₁) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m, ∀ φ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m,
      ∀ z ∈ rectC x₁ x₂ y₁ y₂, ∀ z' ∈ rectC x₁ x₂ y₁ y₂, ∀ r r' t : ℝ, 0 < t → t ≤ r → t ≤ r' →
        r ≤ R₀ → r' ≤ R₀ → ∀ ε : ℝ,
        (∀ θ, ‖ψ (circleMap z r θ) - φ (circleMap z' r' θ)‖ ≤ ε) →
        |kernelCov2 neumannH (circM.map (fun θ => ψ (circleMap z r θ)),
            circM.map (fun θ => φ (circleMap z' r' θ)))
          (circM.map (fun θ => ψ (circleMap z r θ)),
            circM.map (fun θ => φ (circleMap z' r' θ)))| ≤
          2 * (swcPotK (12 / (m / 2 * t)) |M| * ε ^ (1 / 2 : ℝ)) := by
  obtain ⟨R₀, hR₀, h⟩ := swcVA_push_facts (a := x₁) (b := x₂) (d := y₂) (M := M) hy hρ hm
  refine ⟨min R₀ (min (ρ / 2) y₁), lt_min hR₀ (lt_min (by positivity) hy),
    fun ψ hψ φ hφ z hz z' hz' r r' t ht htr htr' hr hr' ε hε => ?_⟩
  have hr0 : 0 < r := ht.trans_le htr
  have hr0' : 0 < r' := ht.trans_le htr'
  have key : ∀ χ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m, ∀ w ∈ rectC x₁ x₂ y₁ y₂, ∀ s : ℝ, 0 < s →
      t ≤ s → s ≤ min R₀ (min (ρ / 2) y₁) →
      Measurable (fun θ => χ (circleMap w s θ)) ∧
      IsFrostman (circM.map (fun θ => χ (circleMap w s θ))) 1 (12 / (m / 2 * t)) ∧
      ∀ θ, ‖χ (circleMap w s θ)‖ ≤ |M| := by
    intro χ hχ w hw s hs hts hsR
    have hs1 : s ≤ R₀ := hsR.trans (min_le_left _ _)
    have hs2 : s ≤ ρ / 2 := hsR.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hs3 : s ≤ y₁ := hsR.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmem : ∀ θ, circleMap w s θ ∈ thickening ρ (rectC x₁ x₂ y₁ y₂) := fun θ =>
      swcNA2I_mem_thick hw (swcNA2I_circ_norm w hs.le θ).le (by linarith)
    obtain ⟨χt, -, hχe, hχF, -⟩ := h χ hχ w hw s hs hs1
    refine ⟨(hχ.1.continuousOn.comp_continuous (continuous_circleMap w s) hmem).measurable, ?_,
      fun θ => (hχ.2.2.1 _ (hmem θ)).1.trans (le_abs_self M)⟩
    rw [swcNA2I_map_push hχ hw hs (by linarith) (hs3.trans hw.2.1), hχe]
    refine swcNA2I_frost_mono hχF ?_
    have hm2 : 0 < m / 2 := by positivity
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hts hm2.le)
  obtain ⟨h1m, h1F, h1B⟩ := key ψ hψ z hz r hr0 htr hr
  obtain ⟨h2m, h2F, h2B⟩ := key φ hφ z' hz' r' hr0' htr' hr'
  exact swcNA2I_kernelCov2_map_map_le h1m h2m (by positivity) (abs_nonneg M) h1F h2F
    (ae_of_all _ h1B) (ae_of_all _ h2B) (ae_of_all _ hε)

/-- **Modulus for round circles.** -/
theorem swcNA2I_round_mod {w w' : ℂ} {s s' t B : ℝ} (ht : 0 < t) (hts : t ≤ s) (hts' : t ≤ s')
    (hsw : s ≤ w.im) (hsw' : s' ≤ w'.im) (hB : ‖w‖ + s ≤ B) (hB' : ‖w'‖ + s' ≤ B) :
    |kernelCov2 neumannH (circM.map (circleMap w s), circM.map (circleMap w' s'))
        (circM.map (circleMap w s), circM.map (circleMap w' s'))| ≤
      2 * (swcPotK (12 / t) B * (‖w - w'‖ + |s - s'|) ^ (1 / 2 : ℝ)) := by
  have hs : 0 < s := ht.trans_le hts
  have hs' : 0 < s' := ht.trans_le hts'
  have hF : ∀ (v : ℂ) (u : ℝ), 0 < u → t ≤ u → u ≤ v.im →
      IsFrostman (circM.map (circleMap v u)) 1 (12 / t) := by
    intro v u hu htu huv
    rw [swcNA2I_map_round hu.le huv]
    have := swcVA_isFrostman_push (ψ := id) measurable_id hu one_pos (K := closedBall v u)
      (fun x _ y _ => by simp) huv subset_rfl
    rw [Measure.map_id] at this
    refine swcNA2I_frost_mono this ?_
    rw [one_mul]
    exact div_le_div_of_nonneg_left (by norm_num) ht htu
  have hN : ∀ (v : ℂ) (u : ℝ), 0 ≤ u → ∀ θ, ‖circleMap v u θ‖ ≤ ‖v‖ + u := fun v u hu θ => by
    have := swcNA2I_circ_norm v hu θ
    calc ‖circleMap v u θ‖ = ‖(circleMap v u θ - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖circleMap v u θ - v‖ + ‖v‖ := norm_add_le _ _
      _ = ‖v‖ + u := by rw [this]; ring
  have hB0 : 0 ≤ B := by linarith [norm_nonneg w]
  exact swcNA2I_kernelCov2_map_map_le (continuous_circleMap w s).measurable
    (continuous_circleMap w' s').measurable (by positivity) hB0 (hF w s hs hts hsw)
    (hF w' s' hs' hts' hsw') (ae_of_all _ fun θ => (hN w s hs.le θ).trans hB)
    (ae_of_all _ fun θ => (hN w' s' hs'.le θ).trans hB')
    (ae_of_all _ fun θ => swcNA2I_circ_sub w w' s s' θ)

/-! ## Lipschitz estimates on the class -/

theorem swcNA2I_lip_gen {g : ℂ → ℂ} {V : Set ℂ} {δ B D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    (hg : ∀ u ∈ V, ∀ v ∈ ball u δ, DifferentiableAt ℂ g v ∧ ‖deriv g v‖ ≤ D)
    (hB : ∀ u ∈ V, ‖g u‖ ≤ B) {u u' : ℂ} (hu : u ∈ V) (hu' : u' ∈ V) :
    ‖g u - g u'‖ ≤ (D + 2 * B / δ) * ‖u - u'‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB u hu)
  have hsplit := add_mul D (2 * B / δ) ‖u - u'‖
  by_cases h : ‖u - u'‖ < δ
  · have hu'b : u' ∈ ball u δ := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact h
    have h1 := (convex_ball u δ).norm_image_sub_le_of_norm_deriv_le
      (fun v hv => (hg u hu v hv).1) (fun v hv => (hg u hu v hv).2) hu'b (mem_ball_self hδ)
    have h2 : 0 ≤ 2 * B / δ * ‖u - u'‖ := by positivity
    linarith
  · replace h := not_lt.1 h
    have h1 : ‖g u - g u'‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith [hB u hu, hB u' hu'])
    have h2 : 2 * B ≤ 2 * B / δ * ‖u - u'‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : 0 ≤ D * ‖u - u'‖ := by positivity
    linarith

theorem swcNA2I_lip {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) {u u' : ℂ}
    (hu : u ∈ thickening (ρ / 4) (rectC x₁ x₂ y₁ y₂))
    (hu' : u' ∈ thickening (ρ / 4) (rectC x₁ x₂ y₁ y₂)) :
    ‖ψ u - ψ u'‖ ≤ (|M| / (ρ / 4) + 2 * |M| / (ρ / 4)) * ‖u - u'‖ := by
  refine swcNA2I_lip_gen (by positivity) (by positivity) (fun v hv w hw => ?_)
    (fun v hv => ?_) hu hu'
  · have hw2 : w ∈ thickening (ρ / 2) (rectC x₁ x₂ y₁ y₂) :=
      swcVA_mem_thickening hv le_rfl (by linarith [mem_ball.1 hw])
    exact ⟨hψ.1.differentiableAt
      (isOpen_thickening.mem_nhds (thickening_mono (by linarith) _ hw2)),
      swcNA2I_deriv_le hρ hψ hw2⟩
  · exact (hψ.2.2.1 v (thickening_mono (by linarith) _ hv)).1.trans (le_abs_self M)

theorem swcNA2I_lip_deriv {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) {u u' : ℂ}
    (hu : u ∈ thickening (ρ / 16) (rectC x₁ x₂ y₁ y₂))
    (hu' : u' ∈ thickening (ρ / 16) (rectC x₁ x₂ y₁ y₂)) :
    ‖deriv ψ u - deriv ψ u'‖ ≤
      (|M| / (ρ / 4) / (ρ / 4) + 2 * (|M| / (ρ / 4)) / (ρ / 16)) * ‖u - u'‖ := by
  have hA : AnalyticOnNhd ℂ ψ (thickening ρ (rectC x₁ x₂ y₁ y₂)) :=
    hψ.1.analyticOnNhd isOpen_thickening
  have hMb : ∀ z ∈ thickening ρ (rectC x₁ x₂ y₁ y₂), ‖ψ z‖ ≤ |M| := fun z hz =>
    (hψ.2.2.1 z hz).1.trans (le_abs_self M)
  refine swcNA2I_lip_gen (by positivity) (by positivity) (fun v hv w hw => ?_)
    (fun v hv => ?_) hu hu'
  · have hw8 : w ∈ thickening (ρ / 8) (rectC x₁ x₂ y₁ y₂) :=
      swcVA_mem_thickening hv le_rfl (by linarith [mem_ball.1 hw])
    exact ⟨hA.deriv.differentiableOn.differentiableAt
      (isOpen_thickening.mem_nhds (thickening_mono (by linarith) _ hw8)),
      swcVA_norm_deriv2_le hρ hψ.1 hMb hw8⟩
  · exact swcNA2I_deriv_le hρ hψ (thickening_mono (by linarith) _ hv)

theorem swcNA2I_deriv_sub {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hρ : 0 < ρ) {ψ φ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) (hφ : φ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) {e : ℝ}
    (he : ∀ w ∈ thickening ρ (rectC x₁ x₂ y₁ y₂), ‖ψ w - φ w‖ ≤ e) {u : ℂ}
    (hu : u ∈ thickening (ρ / 2) (rectC x₁ x₂ y₁ y₂)) :
    ‖deriv ψ u - deriv φ u‖ ≤ e / (ρ / 4) := by
  have hd : DifferentiableOn ℂ (fun w => ψ w - φ w) (thickening ρ (rectC x₁ x₂ y₁ y₂)) :=
    hψ.1.sub hφ.1
  have huU : u ∈ thickening ρ (rectC x₁ x₂ y₁ y₂) := thickening_mono (by linarith) _ hu
  have := swcVA_norm_deriv_le hρ hd he hu
  have e2 : deriv (fun w => ψ w - φ w) u = deriv ψ u - deriv φ u :=
    ((hψ.1.differentiableAt (isOpen_thickening.mem_nhds huU)).hasDerivAt.sub
      (hφ.1.differentiableAt (isOpen_thickening.mem_nhds huU)).hasDerivAt).deriv
  rwa [e2] at this

theorem swcNA2I_potK_le {m t B : ℝ} (hm : 0 < m) (ht : 0 < t) (ht1 : t ≤ 1) (hB : 0 ≤ B) :
    swcPotK (24 / (m * t)) B ≤ (2 + 288 / m + 4 * Real.log (B + B + 1)) / t := by
  have hL : 0 ≤ Real.log (B + B + 1) := Real.log_nonneg (by linarith)
  have e : swcPotK (24 / (m * t)) B = (2 + 4 * Real.log (B + B + 1)) + 288 / m / t := by
    unfold swcPotK; field_simp; ring
  have e2 : (2 + 288 / m + 4 * Real.log (B + B + 1)) / t =
      (2 + 4 * Real.log (B + B + 1)) / t + 288 / m / t := by ring
  rw [e, e2]
  have := le_div_self (by positivity : (0 : ℝ) ≤ 2 + 4 * Real.log (B + B + 1)) ht ht1
  linarith

theorem swcNA2I_k0 {R : ℝ} (hR : 0 < R) : ∃ k₀ : ℕ, ∀ k ≥ k₀, 2 * radius k ≤ R := by
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (half_pos hR) (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨k₀, fun k hk => ?_⟩
  have : (2⁻¹ : ℝ) ^ k ≤ (2⁻¹ : ℝ) ^ k₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  unfold radius
  linarith

/-! ## The uniform family -/

/-- Hypotheses on a uniform family `(F q, c q, a q)` of class maps, centres and radius factors. -/
structure SwcNA2Unif {n : ℕ} (F : (Fin n → ℝ) → ℂ → ℂ) (c : (Fin n → ℝ) → ℂ)
    (a : (Fin n → ℝ) → ℝ) (x₁ x₂ y₁ y₂ ρ M m H : ℝ) : Prop where
  y_pos : 0 < y₁
  rho_pos : 0 < ρ
  m_pos : 0 < m
  H_nonneg : 0 ≤ H
  cls : ∀ q, F q ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m
  cen : ∀ q, c q ∈ rectC x₁ x₂ y₁ y₂
  a_ge : ∀ q, 1 ≤ a q
  a_le : ∀ q, a q ≤ 2
  c_lip : ∀ q q', ‖c q - c q'‖ ≤ H * ‖q - q'‖
  a_lip : ∀ q q', |a q - a q'| ≤ H * ‖q - q'‖
  F_lip : ∀ q q', ∀ w ∈ thickening ρ (rectC x₁ x₂ y₁ y₂), ‖F q w - F q' w‖ ≤ H * ‖q - q'‖

variable {n : ℕ} {F : (Fin n → ℝ) → ℂ → ℂ} {c : (Fin n → ℝ) → ℂ} {a : (Fin n → ℝ) → ℝ}
  {x₁ x₂ y₁ y₂ ρ M m H : ℝ}

theorem swcNA2I_push_eq (F : (Fin n → ℝ) → ℂ → ℂ) (c : (Fin n → ℝ) → ℂ) (a : (Fin n → ℝ) → ℝ)
    (k : ℕ) (q : Fin n → ℝ) :
    swcPhiPush F c a k q = fun θ => F q (circleMap (c q) (a q * radius k) θ) := rfl

theorem swcNA2I_round_eq (F : (Fin n → ℝ) → ℂ → ℂ) (c : (Fin n → ℝ) → ℂ) (a : (Fin n → ℝ) → ℝ)
    (k : ℕ) (q : Fin n → ℝ) :
    swcPhiRound F c a k q = circleMap (F q (c q)) (a q * radius k * ‖deriv (F q) (c q)‖) := rfl

theorem swcNA2I_radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity

theorem swcNA2I_radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **`hvar` for the uniform family**, for `k ≥ k₀`. -/
theorem swcNA2I_hvar (h : SwcNA2Unif F c a x₁ x₂ y₁ y₂ ρ M m H) :
    ∃ k₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≥ k₀, ∀ q,
      |kernelCov2 neumannH (circM.map (swcPhiPush F c a k q), circM.map (swcPhiRound F c a k q))
        (circM.map (swcPhiPush F c a k q), circM.map (swcPhiRound F c a k q))| ≤
        C * (1 / 2) ^ k := by
  obtain ⟨C, R₀, hC, hR₀, hv⟩ := swcNA2I_var (x₁ := x₁) (x₂ := x₂) (y₂ := y₂) (M := M)
    h.y_pos h.rho_pos h.m_pos
  obtain ⟨k₀, hk₀⟩ := swcNA2I_k0 hR₀
  refine ⟨k₀, 2 * C, by positivity, fun k hk q => ?_⟩
  have ht := swcNA2I_radius_pos k
  have hr : 0 < a q * radius k := mul_pos (by linarith [h.a_ge q]) ht
  have hr2 : a q * radius k ≤ 2 * radius k := mul_le_mul_of_nonneg_right (h.a_le q) ht.le
  rw [swcNA2I_push_eq, swcNA2I_round_eq]
  refine (hv (F q) (h.cls q) (c q) (h.cen q) _ hr (hr2.trans (hk₀ k hk))).trans ?_
  have e : (1 / 2 : ℝ) ^ k = radius k := by unfold radius; rw [one_div]
  rw [e]
  nlinarith

end NA2Inst

end SWCore
end QuantumZipper
