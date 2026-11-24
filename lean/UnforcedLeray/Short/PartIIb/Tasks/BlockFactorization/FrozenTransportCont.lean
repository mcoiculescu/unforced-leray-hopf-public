import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont.Smooth

/-!
# `PartII-b:F2/4/4`: joint strong continuity of the frozen radial transport

Density of smooth compactly supported data in `X_m`, continuity of `(σ, τ) ↦ T_pl σ τ g` on such
data by dominated convergence (flow field, nonsingularity of the flow), and the isometry field.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ContDiff

open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.FrozenTransportContHelp in
theorem frozenTransportJointCont_proof : UnforcedLeray.Short.IIb.FrozenTransportJointCont := by
  intro m _hm Sig _hSig T hT q0 hq0
  have hd : Dense {f : Xm m | ∃ g : UnforcedLeray.B0579.Plane → ℝ, f =ᵐ[planeMeasure m] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := planeMeasure m) (F := ℝ)
      (by simp)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨h, ⟨g, hhg, hgc, hgd⟩, hdist⟩ := hd.exists_dist_lt q0.2.2 hε4
  have hc := smooth_contOn m Sig T hT g (hgd.continuous) hgc h hhg
  have hq0' : (q0.1, q0.2.1) ∈ Icc 0 Sig ×ˢ (univ : Set ℝ) := ⟨hq0.1, trivial⟩
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousWithinAt_iff.1 (hc _ hq0') (ε / 4) hε4
  refine ⟨min δ1 (ε / 4), lt_min hδ1 hε4, ?_⟩
  rintro ⟨σ, τ, f⟩ hq hqd
  have hqd' : dist (σ, τ, f) q0 < min δ1 (ε / 4) := hqd
  have hlt1 : dist (σ, τ) (q0.1, q0.2.1) < δ1 := by
    have h1 : dist σ q0.1 < δ1 := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hqd' (min_le_left _ _))
    have h2 : dist τ q0.2.1 < δ1 := by
      have : dist (τ, f) q0.2 < min δ1 (ε / 4) :=
        lt_of_le_of_lt (le_max_right _ _) hqd'
      exact lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le this (min_le_left _ _))
    exact max_lt h1 h2
  have hlt2 : dist f q0.2.2 < ε / 4 := by
    have : dist (τ, f) q0.2 < min δ1 (ε / 4) := lt_of_le_of_lt (le_max_right _ _) hqd'
    exact lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le this (min_le_right _ _))
  have hmid := hδ1' (x := (σ, τ)) ⟨hq.1, trivial⟩ hlt1
  simp only at hmid ⊢
  have hσ : σ ∈ Icc 0 Sig := hq.1
  have hσ0 : q0.1 ∈ Icc 0 Sig := hq0.1
  have e1 : dist (T σ τ f) (T σ τ h) = dist f h := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hT.isometry σ hσ]
  have e2 : dist (T q0.1 q0.2.1 h) (T q0.1 q0.2.1 q0.2.2) = dist h q0.2.2 := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hT.isometry _ hσ0]
  calc dist (T σ τ f) (T q0.1 q0.2.1 q0.2.2)
      ≤ dist (T σ τ f) (T σ τ h) + dist (T σ τ h) (T q0.1 q0.2.1 h)
        + dist (T q0.1 q0.2.1 h) (T q0.1 q0.2.1 q0.2.2) := dist_triangle4 _ _ _ _
    _ = dist f h + dist (T σ τ h) (T q0.1 q0.2.1 h) + dist h q0.2.2 := by rw [e1, e2]
    _ ≤ (dist f q0.2.2 + dist q0.2.2 h) + dist (T σ τ h) (T q0.1 q0.2.1 h) + dist h q0.2.2 := by
        gcongr; exact dist_triangle _ _ _
    _ < ε := by
        rw [dist_comm q0.2.2 h] at *
        linarith
