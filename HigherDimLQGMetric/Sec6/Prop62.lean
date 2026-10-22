import HigherDimLQGMetric.Sec6.Prop62Finite
import HigherDimLQGMetric.Sharp.W3Tail

/-!
# [S] Proposition 6.2 and the §6 package

Packet S6b. Source: MA3 Details (a) **D-6.2**, **D-6.3**, D-LOC; blueprint Part A §6 (`prop:62`,
`cor:63`); source l. 996–1129.

* `trapFamily_of_sharp`: **[S] Proposition 6.2** in MA3's corrected deterministic form `TrapFamily`
  (E10, E11) for two sharp weak assignments with the a.s. comparison `c_* D ≤ D̃ ≤ C_* D`, from
  [S] Lemma 6.1 (`FineFieldAmplification`, taken as a hypothesis, packet S5b) with `c₂ < C_*`.
* `sec6Package`: `TrapFamily`, `ConfigLocal` and `Cor63 … m` for every `m`, with the parameter
  constraints explicit (the form consumed by S7a and S8).

Construction (D-6.2, in this order): `η = (1 - p)/2`; the bound datum `β` of D-SF5 with failure
probability `η` (M2b, with W3's (E5)); the index `m₀` of the compact exhaustion containing `Ā_{1,3}`;
the collar `a = lower_{m₀}(3/4)/4`, `g = a`, `b = a/8`, `ε₀ = min(e^{-ξ} b/400, a/24)`; the P2
threshold `aP` on the core; the modulus scale `η_u` with `ω_{m₀}(η_u) < min(b/8, ε₀, aP)`; the mesh
size `δ = min(1/(12√d), η_u/(4√d))`; a spanning tree of the mesh; Lemma 6.1 on the central boxes with
success probability `1 - η` (this fixes `m`, `a₁`, `A₁`); the compact set `𝒢 ⊆ C(β)` of
configurations with witness paths in all boxes; `c₃ = (c₂ + C_*)/2`, `c' = (c₃ + C_*)/2`; the trap
at every `κ ∈ 𝒢` (Lemmas 4.1′, 4.2′); the finite subcover.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Metric
open _root_.Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- **[S] Proposition 6.2** (MA3 D-6.2, corrected deterministic form `TrapFamily`). -/
theorem trapFamily_of_sharp (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {cs Cs c1 c2 aL A₀L ℓL β₀L pstar : ℝ} (hcs : 0 < cs) (hc2 : 0 ≤ c2) (hc2Cs : c2 < Cs)
    (hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
          (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (hFFA : FineFieldAmplification d ξ Q D Dt cs c1 c2 aL A₀L ℓL β₀L pstar) :
    TrapFamily d ξ Q D Dt cs Cs c1 aL A₀L ℓL β₀L pstar := by
  classical
  intro p hp0 hp1
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hCs : 0 < Cs := lt_of_le_of_lt hc2 hc2Cs
  set η : ℝ := (1 - p) / 2 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  have hη1 : η ≤ 1 := by rw [hη_def]; linarith
  have hpη : 1 - 2 * η = p := by rw [hη_def]; ring
  -- Step 1: the compact family `C(β)` (D-SF5)
  obtain ⟨β, Hβ⟩ := config_DSF5_compactFamily hd2 ξ Q hξ hQ D Dt hD hDt
    (e5_sharp_moment hd hξ hQ hD) (e5_sharp_moment hd hξ hQ hDt) cs Cs
    (ε := ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  -- Step 2: the collar constant and the small constants
  obtain ⟨m₀, hm₀⟩ := s6b_exists_core_index (d := d)
  have hlow := β.outer.lower_pos m₀ (3 / 4) (by norm_num)
  set a : ℝ := β.outer.lower m₀ (3 / 4) / 4 with ha_def
  have ha : 0 < a := by positivity
  set b : ℝ := a / 8 with hb_def
  have hb : 0 < b := by positivity
  set ε₀ : ℝ := min (Real.exp (-ξ) * b / 400) (a / 24) with hε₀_def
  have hexp := Real.exp_pos (-ξ)
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀b : ε₀ < Real.exp (-ξ) * b / 200 :=
    (min_le_left _ _).trans_lt (by nlinarith)
  have hε₀a : ε₀ < a / 12 := (min_le_right _ _).trans_lt (by linarith)
  have h3ε₀ : 3 * ε₀ ≤ a := by linarith [min_le_right (Real.exp (-ξ) * b / 400) (a / 24)]
  obtain ⟨aP, haP, HP2⟩ := s6b_core_realization hd2 cs Cs β
  obtain ⟨ηu, hηu, hηu'⟩ := β.outer.modulus_small m₀ (min (b / 8) (min ε₀ aP)) (by positivity)
  -- Step 3: the mesh
  set sd : ℝ := Real.sqrt d with hsd
  have hsd1 : 1 ≤ sd := Real.one_le_sqrt.2 (by exact_mod_cast hd1)
  have hsd0 : 0 < sd := by linarith
  set δ : ℝ := min (1 / (12 * sd)) (ηu / (4 * sd)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / (12 * sd) := min_le_left _ _
  have hδ2 : δ ≤ ηu / (4 * sd) := min_le_right _ _
  have hsmall : δ ≤ 1 / (4 * Real.sqrt d) := by
    refine hδ1.trans ?_
    rw [← hsd]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h3 : 3 * Real.sqrt d * δ ≤ 1 / 4 := by
    rw [← hsd]
    have := mul_le_mul_of_nonneg_left hδ1 (by positivity : (0 : ℝ) ≤ 3 * sd)
    calc 3 * sd * δ ≤ 3 * sd * (1 / (12 * sd)) := this
      _ = 1 / 4 := by field_simp; ring
  have h4 : 4 * Real.sqrt d * δ ≤ ηu := by
    rw [← hsd]
    have := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0 : ℝ) ≤ 4 * sd)
    calc 4 * sd * δ ≤ 4 * sd * (ηu / (4 * sd)) := this
      _ = ηu := by field_simp
  have h17 : 17 * δ / 8 ≤ ηu := by
    have : δ ≤ ηu / 4 := hδ2.trans (div_le_div_of_nonneg_left hηu.le (by norm_num)
      (by linarith))
    linarith
  obtain ⟨T, hT, hTtree⟩ := exists_routingTree hd2 hδ
  have hTconn : T.Connected := hTtree.1
  have hfin : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  -- Step 4: Lemma 6.1 on the central boxes
  set M : ℕ := Fintype.card T.edgeSet with hM
  set eqv : T.edgeSet ≃ Fin M := Fintype.equivFin T.edgeSet with heqv
  set Ob : Fin M → Set (Rd d) := fun i => s6bBoxNbhd (eqv.symm i) with hOb
  set Kb : Fin M → Set (Rd d) := fun i => s6bBox (eqv.symm i) with hKb
  have hdisj : Pairwise (fun i j => Disjoint (Ob i) (Ob j)) := by
    intro i j hij
    exact s6b_boxNbhd_disjoint hδ hT (fun h => hij (eqv.symm.injective h))
  obtain ⟨m, a₁, A₁, ha₁, ha₁A₁, HFFA⟩ := hFFA M Ob Kb (fun i => isOpen_ball)
    (fun i => s6b_box_isCompact hδ _) (fun i => s6b_box_subset_nbhd hδ _)
    (fun i => s6b_box_interior hd1 hδ _) (fun i => s6b_boxNbhd_subset hd1 hδ hsmall hT _) hdisj
    (1 - η) (by linarith)
  have hA₁ : 0 ≤ A₁ := (ha₁.trans ha₁A₁).le
  -- Step 5: the compact set `𝒢`
  set 𝒢 : Set (ConfigC d) := {q | q ∈ configCompactFamily hd2 cs Cs β ∧
    ∀ e : T.edgeSet, s6bWitness q (s6bBox e) (c2 * A₁) a₁ c2} with h𝒢_def
  have h𝒢eq : 𝒢 = configCompactFamily hd2 cs Cs β ∩ ⋂ e : T.edgeSet,
      {q | q ∈ configCompactFamily hd2 cs Cs β ∧ s6bWitness q (s6bBox e) (c2 * A₁) a₁ c2} := by
    ext q
    simp only [h𝒢_def, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun h => ⟨h.1, fun e => ⟨h.1, h.2 e⟩⟩, fun h => ⟨h.1, fun e => (h.2 e).2⟩⟩
  have h𝒢closed : IsClosed 𝒢 := by
    rw [h𝒢eq]
    exact (configCompactFamily_isCompact hd2 cs Cs β).isClosed.inter
      (isClosed_iInter fun e => s6b_isClosed_witness hd2 cs Cs β (s6b_box_isCompact hδ e)
        (s6b_box_subset_outer hd1 hδ hsmall hT e) _ _ _)
  have h𝒢 : IsCompact 𝒢 :=
    (configCompactFamily_isCompact hd2 cs Cs β).of_isClosed_subset h𝒢closed fun q hq => hq.1
  -- Step 6: the ratio constants
  set c₃ : ℝ := (c2 + Cs) / 2 with hc₃_def
  set c' : ℝ := (c₃ + Cs) / 2 with hc'_def
  have hc₂₃ : c2 < c₃ := by rw [hc₃_def]; linarith
  have hc₃c' : c₃ < c' := by rw [hc'_def]; linarith
  have hc'Cs : c' < Cs := by rw [hc'_def, hc₃_def]; linarith
  -- Step 7: the trap at every configuration of `𝒢`
  have hstab : ∀ κ ∈ 𝒢, ∃ f : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      HasCompactSupport f ∧ tsupport f ⊆ ann (0 : Rd d) 1 3 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, 0 < f x ↔ x ∈ meshCollector d δ) ∧
      ∃ cκ ε : ℝ, 0 < cκ ∧ 0 < ε ∧ ∀ q ∈ configCompactFamily hd2 cs Cs β, S6bClose q κ ε →
        S6bStable ξ (meshCollector d δ) f ε₀ b cκ c' a q.1 q.2.1 := by
    intro κ hκ
    have hκC : κ ∈ configCompactFamily hd2 cs Cs β := hκ.1
    have hκB : κ ∈ configBoundSet β := configCompactFamily_subset_bound hd2 cs Cs β hκC
    refine s6b_trap_at hd hξ hcs hCs hκC hδ hsmall hT hTconn ha₁ hc2 hc₂₃ hc₃c' hκ.2 ?_ hb hε₀
      hε₀b hε₀a ?_ ?_
    · intro x y hx hy
      have h := s6b_collar hκB hm₀ (s6b_closure_collector_subset hδ h3 hx) hy
      rw [ha_def]
      linarith
    · intro v x y hx hy
      have hxc : x ∈ s6bCore d := s6b_collector_core hδ hsmall
        (subset_closure (meshStar_subset_meshCollector hd1 hδ v.2 hx))
      have hyc : y ∈ s6bCore d := s6b_collector_core hδ hsmall
        (subset_closure (meshStar_subset_meshCollector hd1 hδ v.2 hy))
      have hxy : dist x y ≤ ηu := by
        rw [Subtype.dist_eq]
        exact (dist_lt_of_mem_meshStar hδ hx hy).le.trans h17
      exact (s6b_upper_small hd2 hκC hm₀ hxc hyc hxy).trans_lt
        (hηu'.trans_le (min_le_left _ _))
    · exact s6b_access hd2 hκC hm₀ HP2 (hηu'.trans_le (min_le_right _ _)) hδ hsmall h4
  -- Step 8: the finite subcover
  obtain ⟨J, f, N, c, Mf, hf, hc, hN, hcover, hTP⟩ := s6b_finite_trap_data hd2 h𝒢
    (fun q hq => hq.1) hξ.le (isOpen_meshCollector d δ)
    (closure_meshCollector_subset_ann_one_three hδ hsmall) ha (by linarith) h3ε₀ hstab
  refine ⟨m, meshCollector d δ, J, f, N, a, b, c, a, a * Real.exp (ξ * Mf), Mf, c',
    isOpen_meshCollector d δ, closure_meshCollector_subset_ann_one_three hδ hsmall,
    sphere_subset_meshCollector hd1 hδ, hf, ha, hb, hc, rfl, rfl, hc'Cs, by linarith, hN, ?_, ?_⟩
  · -- (P)
    refine s6b_prob hd2 hD hDt (U := cs⁻¹) (a := aL) (A₀ := A₀L) (ℓ := ℓL) (β₀ := β₀L)
      (t := c1⁻¹) (ρ := (64 : ℝ)⁻¹ ^ m) (by positivity) ?_
    intro Ω _ P _ h hh r hr hW
    obtain ⟨Ξ, hΞm, hΞae, hΞmass⟩ := Hβ P h hh r hr 0 (hcomp P h hh)
    have hF := HFFA P h hh r hr hW
    have hres := s6b_prob_center hd2 (ξ := ξ) (Q := Q) (D := D) (Dt := Dt) hη.le hη1 (Kb := Kb)
      (fun i => s6b_box_subset_outer hd1 hδ hsmall hT _) hc2 hA₁ (J := J) (N := N)
      (fun D₀ Dt₀ hl hlt s r hs hr hC hwit => hcover D₀ Dt₀ hl hlt hs hr 0
        ⟨hC, fun e => by simpa only [hKb, Equiv.symm_apply_apply] using hwit (eqv e)⟩)
      P h hr Ξ hΞm hΞae hΞmass hF
    rwa [hpη] at hres
  · -- (T)
    intro D₀ Dt₀ hl hlt _ s r z j hs hr hj hNj
    exact hTP D₀ Dt₀ hl hlt s r z j hs hr hj hNj

/-- **The §6 package** (packets S6a + S6b): [S] Proposition 6.2 (`TrapFamily`), the locality of
configuration events (`ConfigLocal`) and [S] Corollary 6.3 (`Cor63 … m` for every shift `m`), for two
sharp weak assignments `D, D̃` (`d ≥ 3`, `ξ > 0`, `√(2d) < Q`) with `c_* D ≤ D̃ ≤ C_* D` a.s. for every
LGF, the §5 constants `aL, A₀L, ℓL, β₀L, pstar` of the lower pair `(D̃, D)` (Proposition 5.4 with
upper constant `c_*⁻¹`), condition (10), the order `c_* < c₁ < c₂ < C_*`, and [S] Lemma 6.1 for the
lower pair (`FineFieldAmplification`, packet S5b). -/
theorem sec6Package (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {cs Cs c0 c1 c2 aL A₀L ℓL β₀L pstar : ℝ}
    (hcs : 0 < cs) (hcs1 : cs < c1) (hc12 : c1 < c2) (hc2Cs : c2 < Cs)
    (hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
          (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (hℓL : 0 < ℓL) (hβ₀L : 0 < β₀L) (hpstar : 0 < pstar)
    (hfreq : FrequencyLemma d ξ Q Dt D cs⁻¹ aL A₀L ℓL β₀L pstar)
    (h10 : cs⁻¹ - aL / A₀L * (cs⁻¹ - c1⁻¹) < c0⁻¹)
    (hFFA : FineFieldAmplification d ξ Q D Dt cs c1 c2 aL A₀L ℓL β₀L pstar) :
    TrapFamily d ξ Q D Dt cs Cs c1 aL A₀L ℓL β₀L pstar ∧ ConfigLocal d ξ Q D Dt ∧
      ∀ m : ℕ, Cor63 d ξ Q D Dt cs c0 c1 aL A₀L ℓL β₀L pstar m := by
  have hc2 : 0 ≤ c2 := (hcs.trans (hcs1.trans hc12)).le
  refine ⟨trapFamily_of_sharp hd hξ hQ hD hDt hcs hc2 hc2Cs hcomp hFFA,
    configLocal_of_sharp (by omega) hD hDt, fun m => ?_⟩
  refine cor63_of_frequency hD hDt hcs hcs1 hℓL hβ₀L hpstar h10 hfreq ?_ m
  intro Ω _ P _ h hh
  exact (hcomp P h hh).mono fun ω hω u v => (hω u v).1

end HigherDimLQGMetric
