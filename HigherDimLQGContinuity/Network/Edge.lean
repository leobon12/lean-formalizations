import HigherDimLQGContinuity.Network.Chain

/-! # Seven open pieces of one labelled edge -/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

def edgeChamberOpen {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (ω : ℝ) :
    Set (Rd d) :=
  ballUnionOpen μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.chamber) ω

def edgeGateOpen {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2)
    (g : ℝ) : Set (Rd d) :=
  ballUnionOpen μ (S.edgeCenter e)
    (labelCellIndices (if i = 0 then (ℓ e).1.gate0 else (ℓ e).1.gate1)) g

def edgeRetainedOpen {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2)
    (ω : ℝ) : Set (Rd d) :=
  ⋃ x ∈ edgeRetainedSamples ℓ e i ω, ball x ω

def edgeLeadOpen {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2)
    (ω : ℝ) : Set (Rd d) :=
  ⋃ x ∈ edgeLeadSamples ℓ e i ω, ball x ω

def edgeRetainedClosed {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2)
    (ω : ℝ) : Set (Rd d) :=
  ⋃ x ∈ edgeRetainedSamples ℓ e i ω, closedBall x ω

def edgeLeadClosed {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2)
    (ω : ℝ) : Set (Rd d) :=
  ⋃ x ∈ edgeLeadSamples ℓ e i ω, closedBall x ω

theorem edgeBallSpecs_open_eq {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (g ω : ℝ) :
    openBallSpecs (edgeBallSpecs ℓ e g ω) =
      edgeRetainedOpen ℓ e 0 ω ∪ edgeLeadOpen ℓ e 0 ω ∪
      edgeGateOpen ℓ e 0 g ∪ edgeChamberOpen ℓ e ω ∪
      edgeGateOpen ℓ e 1 g ∪ edgeLeadOpen ℓ e 1 ω ∪
      edgeRetainedOpen ℓ e 1 ω := by
  classical
  simp only [edgeBallSpecs, openBallSpecs_union, openBallSpecs_image,
    edgeChamberSites, edgeGateSites, Finset.image_image, Function.comp_def,
    edgeRetainedOpen, edgeLeadOpen, edgeChamberOpen, edgeGateOpen]
  ext x
  simp only [mem_union]
  tauto

theorem edgeBallSpecs_closed_eq {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (g ω : ℝ) :
    closedBallSpecs (edgeBallSpecs ℓ e g ω) =
      edgeRetainedClosed ℓ e 0 ω ∪ edgeLeadClosed ℓ e 0 ω ∪
      edgeGateClosed ℓ e 0 g ∪ edgeChamberClosed ℓ ω e ∪
      edgeGateClosed ℓ e 1 g ∪ edgeLeadClosed ℓ e 1 ω ∪
      edgeRetainedClosed ℓ e 1 ω := by
  classical
  simp only [edgeBallSpecs, closedBallSpecs_union, closedBallSpecs_image,
    edgeChamberSites, edgeGateSites, Finset.image_image, Function.comp_def,
    edgeRetainedClosed, edgeLeadClosed, edgeChamberClosed, edgeGateClosed,
    ballUnion]
  ext x
  simp only [mem_union]
  tauto

/-- Connectivity of all seven ball families around one realizable edge.
Only scalar inequalities from the site-constant order are needed. -/
theorem edgeBallSpecs_connected {d Kc Kl N : ℕ} (S : SiteData d)
    {μ ν r c₁ g ω t₀ : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (hreal : (ℓ e).IsRealizable S e S.seed.A S.seed.α S.seed.β t₀)
    (hμ : 0 ≤ μ) (hω : 0 < ω)
    (hμω : Real.sqrt d / 2 * μ < ω)
    (hμg : Real.sqrt d / 2 * μ < g)
    (ht₀ : 0 < t₀) (ht₀six : t₀ ≤ 1 / 6)
    (htipwidth : (d : ℝ) * ν + Real.sqrt d / 2 * μ < g) :
    IsConnected (openBallSpecs (edgeBallSpecs ℓ e g ω)) := by
  rcases hreal with ⟨γ, hmod, _, hstar, hgate0, hgate1, _, _, htip0, htip1⟩
  rcases (ℓ e).2 with ⟨_, _, _, hlead0, hlead1, _⟩
  have hlast0 : 0 < (ℓ e).1.lead0.last.val := by have := hlead0.1; omega
  have hlast1 : 0 < (ℓ e).1.lead1.last.val := by have := hlead1.1; omega
  have hport0 : (ℓ e).1.lead0.point ν 0 = S.port e 0 := hlead0.2.1
  have hport1 : (ℓ e).1.lead1.point ν 0 = S.port e 1 := hlead1.2.1
  let R₀ := edgeRetainedOpen ℓ e 0 ω
  let L₀ := edgeLeadOpen ℓ e 0 ω
  let G₀ := edgeGateOpen ℓ e 0 g
  let Ch := edgeChamberOpen ℓ e ω
  let G₁ := edgeGateOpen ℓ e 1 g
  let L₁ := edgeLeadOpen ℓ e 1 ω
  let R₁ := edgeRetainedOpen ℓ e 1 ω
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 1) :=
    hmod.continuousOn S.seed.α_pos
  have hsub0 : Icc (0 : ℝ) (2 * t₀) ⊆ Icc 0 1 :=
    Icc_subset_Icc le_rfl (by linarith)
  have hsub1 : Icc (1 - 2 * t₀) 1 ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (by linarith) le_rfl
  have hR₀ : IsConnected R₀ := by
    simpa only [R₀, edgeRetainedOpen, edgeRetainedSamples] using
      (connected_segmentSampleBalls
        (S.vertexPoint (S.retainedVertex e 0)) (S.port e 0) hω)
  have hR₁ : IsConnected R₁ := by
    simpa only [R₁, edgeRetainedOpen, edgeRetainedSamples] using
      (connected_segmentSampleBalls
        (S.vertexPoint (S.retainedVertex e 1)) (S.port e 1) hω)
  have hL₀ : IsConnected L₀ := by
    simpa [L₀, edgeLeadOpen, edgeLeadSamples] using
      (connected_leadSampleBalls (ℓ e).1.lead0 ν hω hlast0)
  have hL₁ : IsConnected L₁ := by
    simpa [L₁, edgeLeadOpen, edgeLeadSamples] using
      (connected_leadSampleBalls (ℓ e).1.lead1 ν hω hlast1)
  have hG₀ : IsConnected G₀ := by
    simpa [G₀, edgeGateOpen] using
      (connected_ballUnionOpen_of_coveredHit hμ hμg (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate0) γ (by linarith : (0 : ℝ) ≤ 2 * t₀)
        (hcont.mono hsub0) hgate0)
  have hG₁ : IsConnected G₁ := by
    simpa [G₁, edgeGateOpen] using
      (connected_ballUnionOpen_of_coveredHit hμ hμg (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate1) γ (by linarith : 1 - 2 * t₀ ≤ (1 : ℝ))
        (hcont.mono hsub1) hgate1)
  have hCh : IsConnected Ch := by
    simpa only [Ch, edgeChamberOpen] using
      (connected_ballUnionOpen_of_coveredHit hμ hμω (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.chamber) γ (by norm_num : (0 : ℝ) ≤ 1)
        hcont hstar)
  have hzero : (0 : ℝ) ∈ Icc 0 (2 * t₀) := by constructor <;> linarith
  have hone : (1 : ℝ) ∈ Icc (1 - 2 * t₀) 1 := by constructor <;> linarith
  have hzeroC : γ 0 ∈ Ch := by
    exact coveredHit_image_mem_open hμ hμω (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) γ hstar (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have honeC : γ 1 ∈ Ch := by
    exact coveredHit_image_mem_open hμ hμω (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) γ hstar (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hzeroG : γ 0 ∈ G₀ := by
    simpa [G₀, edgeGateOpen] using
      coveredHit_image_mem_open hμ hμg (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate0) γ hgate0 hzero
  have honeG : γ 1 ∈ G₁ := by
    simpa [G₁, edgeGateOpen] using
      coveredHit_image_mem_open hμ hμg (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate1) γ hgate1 hone
  have htip0G : (ℓ e).1.lead0.point ν (ℓ e).1.lead0.last ∈ G₀ := by
    simpa [G₀, edgeGateOpen] using
      coveredHit_tip_mem_open hμ htipwidth (S.edgeCenter e)
        ((ℓ e).1.lead0.point ν (ℓ e).1.lead0.last)
        (labelCellIndices (ℓ e).1.gate0) γ hgate0 hzero htip0
  have htip1G : (ℓ e).1.lead1.point ν (ℓ e).1.lead1.last ∈ G₁ := by
    simpa [G₁, edgeGateOpen] using
      coveredHit_tip_mem_open hμ htipwidth (S.edgeCenter e)
        ((ℓ e).1.lead1.point ν (ℓ e).1.lead1.last)
        (labelCellIndices (ℓ e).1.gate1) γ hgate1 hone htip1
  have hRL₀ : (R₀ ∩ L₀).Nonempty := by
    refine ⟨S.port e 0, ?_, ?_⟩
    · exact mem_iUnion₂.mpr ⟨_, segmentSamples_end _ _ ω, mem_ball_self hω⟩
    · rw [← hport0]
      exact mem_iUnion₂.mpr ⟨_, leadSamples_start _ ν ω hlast0, mem_ball_self hω⟩
  have hLG₀ : (L₀ ∩ G₀).Nonempty := by
    refine ⟨(ℓ e).1.lead0.point ν (ℓ e).1.lead0.last, ?_, htip0G⟩
    exact mem_iUnion₂.mpr ⟨_, leadSamples_end _ ν ω hlast0, mem_ball_self hω⟩
  have hGC₀ : (G₀ ∩ Ch).Nonempty := ⟨γ 0, hzeroG, hzeroC⟩
  have hCG₁ : (Ch ∩ G₁).Nonempty := ⟨γ 1, honeC, honeG⟩
  have hGL₁ : (G₁ ∩ L₁).Nonempty := by
    refine ⟨(ℓ e).1.lead1.point ν (ℓ e).1.lead1.last, htip1G, ?_⟩
    exact mem_iUnion₂.mpr ⟨_, leadSamples_end _ ν ω hlast1, mem_ball_self hω⟩
  have hLR₁ : (L₁ ∩ R₁).Nonempty := by
    refine ⟨S.port e 1, ?_, ?_⟩
    · rw [← hport1]
      exact mem_iUnion₂.mpr ⟨_, leadSamples_start _ ν ω hlast1, mem_ball_self hω⟩
    · exact mem_iUnion₂.mpr ⟨_, segmentSamples_end _ _ ω, mem_ball_self hω⟩
  rw [edgeBallSpecs_open_eq]
  exact connected_seven_chain R₀ L₀ G₀ Ch G₁ L₁ R₁
    hR₀ hL₀ hG₀ hCh hG₁ hL₁ hR₁
    hRL₀ hLG₀ hGC₀ hCG₁ hGL₁ hLR₁

theorem edgeBallSpecs_mem_left {d Kc Kl N : ℕ} {S : SiteData d}
    {μ ν r c₁ g ω : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (hω : 0 < ω) :
    S.vertexPoint (S.edgeLeft e) ∈ openBallSpecs (edgeBallSpecs ℓ e g ω) := by
  have hR : S.vertexPoint (S.edgeLeft e) ∈ edgeRetainedOpen ℓ e 0 ω := by
    apply mem_iUnion₂.mpr
    refine ⟨S.vertexPoint (S.edgeLeft e), ?_, mem_ball_self hω⟩
    simpa [edgeRetainedSamples, SiteData.retainedVertex] using
      (segmentSamples_start (S.vertexPoint (S.edgeLeft e)) (S.port e 0) ω)
  rw [edgeBallSpecs_open_eq]
  simp only [mem_union]
  tauto

theorem edgeBallSpecs_mem_right {d Kc Kl N : ℕ} {S : SiteData d}
    {μ ν r c₁ g ω : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (hω : 0 < ω) :
    S.vertexPoint (S.edgeRight e) ∈ openBallSpecs (edgeBallSpecs ℓ e g ω) := by
  have hR : S.vertexPoint (S.edgeRight e) ∈ edgeRetainedOpen ℓ e 1 ω := by
    apply mem_iUnion₂.mpr
    refine ⟨S.vertexPoint (S.edgeRight e), ?_, mem_ball_self hω⟩
    simpa [edgeRetainedSamples, SiteData.retainedVertex] using
      (segmentSamples_start (S.vertexPoint (S.edgeRight e)) (S.port e 1) ω)
  rw [edgeBallSpecs_open_eq]
  simp only [mem_union]
  tauto

end HigherDimLQGContinuity
