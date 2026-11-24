import UnforcedLeray.Short.PartIIb.Sub.R1
import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Short.PartIIa.ComposeRing
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Lib.AxisymmetricB.Bridge
import UnforcedLeray.Lib.Axisymmetric.Measure

/-!
# Part II-b, task `PartII-b:R1/6`: smooth extension of the similarity lift

Source of record: `the November 2 reference manuscript`, lines 1214, 1243-1246,
1305-1322 (Proposition `sct:lift`: `RingAxisSmooth`, `RingSolenoidal`, `RingDSS`).

Proves `ringLiftSmoothExt_of (h : UnforcedLeray.Short.PartIIa.RingAxisSmooth) :
UnforcedLeray.Short.IIb.RingLiftSmoothExt` in namespace `UnforcedLeray.Short.IIb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa

/-- Along a line `s ↦ p + s • w`, a function differentiable at `p` has derivative `fderiv G p w`
at `s = 0`. -/
private theorem rlse_line {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : X → E) (p w : X) (hG : DifferentiableAt ℝ G p) :
    HasDerivAt (fun s : ℝ => G (p + s • w)) (fderiv ℝ G p w) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s • w) w 0 := by
    have h := (hasDerivAt_id' (0 : ℝ)).smul_const w
    rw [one_smul] at h
    exact h
  have h2 : HasDerivAt (fun s : ℝ => p + s • w) w 0 := h1.const_add p
  have hy : p = (fun s : ℝ => p + s • w) 0 := by simp
  exact hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 hy

/-- The realification `realC` is the continuous linear complexification `Axi.cplxV`. -/
private theorem rlse_realC_eq (x : Space) :
    UnforcedLeray.B0412.realC x = UnforcedLeray.Axi.cplxV x := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply, UnforcedLeray.Axi.cplxV_apply]

/-- The similarity coordinate map `Φ(τ, y) = (e^τ, e^{τ/2} • y)`. -/
private def rlse_Phi (q : ℝ × Space) : ℝ × Space :=
  (Real.exp q.1, Real.exp (q.1 / 2) • q.2)

private theorem rlse_Phi_contDiff : ContDiff ℝ ∞ rlse_Phi := by
  unfold rlse_Phi
  fun_prop

private theorem rlse_Phi_mapsTo :
    MapsTo rlse_Phi univ {z : ℝ × Space | 0 < z.1} :=
  fun q _ => Real.exp_pos q.1

/-- Spatial derivative `dy j` of the similarity profile `q ↦ realC (e^{q.1/2} • u (Φ q))`. -/
private theorem rlse_dy_sim (u : ℝ × Space → Space) (τ : ℝ) (y : Space)
    (hdiff : DifferentiableAt ℝ u (Real.exp τ, Real.exp (τ / 2) • y)) (j : Fin 3) :
    dy j (fun q : ℝ × Space =>
        realC (simProfile 1 (fun t w => u (t, w)) q.1 q.2)) (τ, y) =
      UnforcedLeray.Axi.cplxV (Real.exp (τ / 2) ^ 2 •
        fderiv ℝ (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y) (coordinateVector j)) := by
  set W : ℝ × Space → CVec3 := fun q =>
    UnforcedLeray.Axi.cplxV (Real.exp (q.1 / 2) • u (Real.exp q.1, Real.exp (q.1 / 2) • q.2))
    with hWdef
  have hWfun : (fun q : ℝ × Space =>
      realC (simProfile 1 (fun t w => u (t, w)) q.1 q.2)) = W := by
    funext q
    simp [W, simProfile, pow_one, rlse_realC_eq]
  rw [hWfun]
  have hPhi : DifferentiableAt ℝ rlse_Phi (τ, y) :=
    rlse_Phi_contDiff.differentiable (by simp) (τ, y)
  have hFP : DifferentiableAt ℝ (u ∘ rlse_Phi) (τ, y) :=
    hdiff.comp (τ, y) hPhi
  have hc : DifferentiableAt ℝ (fun q : ℝ × Space => Real.exp (q.1 / 2)) (τ, y) := by
    fun_prop
  have hS : DifferentiableAt ℝ
      (fun q : ℝ × Space => Real.exp (q.1 / 2) • u (Real.exp q.1, Real.exp (q.1 / 2) • q.2))
      (τ, y) := hc.smul hFP
  have hW : DifferentiableAt ℝ W (τ, y) :=
    UnforcedLeray.Axi.cplxV.differentiableAt.comp (τ, y) hS
  have hu : DifferentiableAt ℝ (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y) :=
    hdiff.comp (Real.exp (τ / 2) • y)
      ((differentiableAt_const (Real.exp τ)).prodMk differentiableAt_id)
  have hpt : ∀ s : ℝ, ((τ, y) + s • ((0 : ℝ), coordinateVector j) : ℝ × Space)
      = (τ, y + s • coordinateVector j) := by
    intro s
    ext <;> simp
  have hsplit : ∀ s : ℝ, Real.exp (τ / 2) • (y + s • coordinateVector j)
      = Real.exp (τ / 2) • y + s • (Real.exp (τ / 2) • coordinateVector j) := by
    intro s
    rw [smul_add, smul_comm (Real.exp (τ / 2)) s (coordinateVector j)]
  have hfun : (fun s : ℝ => W ((τ, y) + s • ((0 : ℝ), coordinateVector j)))
      = fun s : ℝ => UnforcedLeray.Axi.cplxV (Real.exp (τ / 2) •
          u (Real.exp τ,
            Real.exp (τ / 2) • y + s • (Real.exp (τ / 2) • coordinateVector j))) := by
    funext s
    rw [hpt s]
    dsimp only [W]
    rw [hsplit s]
  have hline : HasDerivAt (fun s : ℝ => W ((τ, y) + s • ((0 : ℝ), coordinateVector j)))
      (fderiv ℝ W (τ, y) ((0 : ℝ), coordinateVector j)) 0 :=
    rlse_line W (τ, y) ((0 : ℝ), coordinateVector j) hW
  have hline' : HasDerivAt (fun s : ℝ => UnforcedLeray.Axi.cplxV (Real.exp (τ / 2) •
          u (Real.exp τ,
            Real.exp (τ / 2) • y + s • (Real.exp (τ / 2) • coordinateVector j))))
      (fderiv ℝ W (τ, y) ((0 : ℝ), coordinateVector j)) 0 := by
    rw [← hfun]
    exact hline
  have hu_line : HasDerivAt
      (fun s : ℝ => u (Real.exp τ,
        Real.exp (τ / 2) • y + s • (Real.exp (τ / 2) • coordinateVector j)))
      (fderiv ℝ (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y)
        (Real.exp (τ / 2) • coordinateVector j)) 0 :=
    rlse_line (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y)
      (Real.exp (τ / 2) • coordinateVector j) hu
  have hline2 : HasDerivAt (fun s : ℝ => UnforcedLeray.Axi.cplxV (Real.exp (τ / 2) •
          u (Real.exp τ,
            Real.exp (τ / 2) • y + s • (Real.exp (τ / 2) • coordinateVector j))))
      (UnforcedLeray.Axi.cplxV (Real.exp (τ / 2) •
        fderiv ℝ (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y)
          (Real.exp (τ / 2) • coordinateVector j))) 0 :=
    UnforcedLeray.Axi.cplxV.hasFDerivAt.comp_hasDerivAt 0
      (hu_line.const_smul (Real.exp (τ / 2)))
  have hd := hline'.unique hline2
  have hlin : fderiv ℝ (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y)
        (Real.exp (τ / 2) • coordinateVector j)
      = Real.exp (τ / 2) • fderiv ℝ (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y)
        (coordinateVector j) :=
    map_smul _ _ _
  show fderiv ℝ W (τ, y) ((0 : ℝ), coordinateVector j) = _
  rw [hd, hlin, smul_smul, ← pow_two]

/-- The complexified spatial divergence of the similarity profile is `(e^{τ/2})²` times the
physical spatial divergence at `(e^τ, e^{τ/2} • y)`. -/
private theorem rlse_div_sim (u : ℝ × Space → Space) (τ : ℝ) (y : Space)
    (hdiff : DifferentiableAt ℝ u (Real.exp τ, Real.exp (τ / 2) • y)) :
    (∑ j : Fin 3, dy j (fun q : ℝ × Space =>
        realC (simProfile 1 (fun t w => u (t, w)) q.1 q.2)) (τ, y) j) =
      ((Real.exp (τ / 2) ^ 2 *
        Axi.divergence (fun w => u (Real.exp τ, w)) (Real.exp (τ / 2) • y) : ℝ) : ℂ) := by
  simp only [rlse_dy_sim u τ y hdiff, Axi.cplxV_apply, PiLp.smul_apply, smul_eq_mul,
    Axi.divergence]
  push_cast
  rw [Finset.mul_sum]

/-- **`PartII-b:R1/6`.** Smooth extension of the similarity lift across the axis, periodicity in
`τ` with period `2ν⁻²/R`, and vanishing Cartesian divergence (SP 1214, 1243-1246, 1305-1322). -/
theorem ringLiftSmoothExt_of (h : UnforcedLeray.Short.PartIIa.RingAxisSmooth) :
    UnforcedLeray.Short.IIb.RingLiftSmoothExt := by
  obtain ⟨ν₀, hν₀, H⟩ := h 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν hν ψ pr hTr R hR => ?_⟩
  obtain ⟨u, π, hu, hπ, hoff⟩ := H ν hν ψ pr hTr R hR
  obtain ⟨T, hBUC, rfl, rfl⟩ := hTr
  set U : ℝ × Space → CVec3 := fun x =>
    realC (simProfile 1 (fun t y => u (t, y)) x.1 x.2) with hU_def
  set Pw : ℝ × Space → ℂ := fun x =>
    ((simProfile 2 (fun t y => π (t, y)) x.1 x.2 : ℝ) : ℂ) with hPw_def
  -- 1. Smoothness of U and Pw on all of ℝ × ℝ³
  have huPhi : ContDiff ℝ ∞ (fun q : ℝ × Space => u (rlse_Phi q)) :=
    contDiffOn_univ.mp (hu.comp rlse_Phi_contDiff.contDiffOn rlse_Phi_mapsTo)
  have hπPhi : ContDiff ℝ ∞ (fun q : ℝ × Space => π (rlse_Phi q)) :=
    contDiffOn_univ.mp (hπ.comp rlse_Phi_contDiff.contDiffOn rlse_Phi_mapsTo)
  have hU_smooth : ContDiff ℝ ∞ U := by
    have hc1 : ContDiff ℝ ∞ (fun q : ℝ × Space => Real.exp (q.1 / 2) ^ 1) := by fun_prop
    have hreal : ContDiff ℝ ∞ (fun q : ℝ × Space =>
        Real.exp (q.1 / 2) ^ 1 • u (rlse_Phi q)) := hc1.smul huPhi
    have eqU : U = fun q : ℝ × Space =>
        UnforcedLeray.Axi.cplxV (Real.exp (q.1 / 2) ^ 1 • u (rlse_Phi q)) := by
      funext q
      simp [U, simProfile, rlse_Phi, rlse_realC_eq]
    rw [eqU]
    exact UnforcedLeray.Axi.cplxV.contDiff.comp hreal
  have hPw_smooth : ContDiff ℝ ∞ Pw := by
    have hc2 : ContDiff ℝ ∞ (fun q : ℝ × Space => Real.exp (q.1 / 2) ^ 2) := by fun_prop
    have hreal : ContDiff ℝ ∞ (fun q : ℝ × Space =>
        Real.exp (q.1 / 2) ^ 2 • π (rlse_Phi q)) := hc2.smul hπPhi
    have eqPw : Pw = fun q : ℝ × Space =>
        Complex.ofRealCLM (Real.exp (q.1 / 2) ^ 2 • π (rlse_Phi q)) := by
      funext q
      simp [Pw, simProfile, rlse_Phi]
    rw [eqPw]
    exact Complex.ofRealCLM.contDiff.comp hreal
  -- 2. Off-axis agreement with simProfile of liftVelocity and liftPressure
  have h_agree : ∀ x : ℝ × Space, Axi.ϱ x.2 ≠ 0 →
      U x = realC (simProfile 1 (liftVelocity R (trainProfile T.ψ)) x.1 x.2) ∧
      Pw x = ((simProfile 2 (liftPressure R (trainProfile T.p)) x.1 x.2 : ℝ) : ℂ) := by
    intro x hx
    have hx_axis : Real.exp (x.1 / 2) • x.2 ∉ Axi.axis := by
      rw [Axi.mem_axis_iff, Axi.ϱ_smul, abs_of_pos (Real.exp_pos _)]
      exact mul_ne_zero (Real.exp_pos _).ne' hx
    obtain ⟨hu_eq, hπ_eq⟩ := hoff (Real.exp x.1) (Real.exp_pos x.1)
      (Real.exp (x.1 / 2) • x.2) hx_axis
    exact ⟨by simp [U, simProfile, hu_eq], by simp [Pw, simProfile, hπ_eq]⟩
  -- 3. Dense off-axis set
  have h_dense : Dense {y : Space | y ∉ Axi.axis} :=
    Measure.dense_of_ae Axi.ae_not_mem_axis
  -- 4. Periodicity of U in τ with period 2 * ν^(-2) / R
  have h_per : ∀ x : ℝ × Space, U (x.1 + 2 * ν ^ (-(2 : ℝ)) / R, x.2) = U x := by
    intro x
    set P : ℝ := 2 * ν ^ (-(2 : ℝ)) / R
    have hcont1 : Continuous (fun y : Space => U (x.1 + P, y)) :=
      hU_smooth.continuous.comp (continuous_const.prodMk continuous_id)
    have hcont2 : Continuous (fun y : Space => U (x.1, y)) :=
      hU_smooth.continuous.comp (continuous_const.prodMk continuous_id)
    have hfun : (fun y : Space => U (x.1 + P, y)) = (fun y : Space => U (x.1, y)) := by
      refine Continuous.ext_on h_dense hcont1 hcont2 fun y hy => ?_
      have hρ : Axi.ϱ y ≠ 0 := Axi.ϱ_ne_zero hy
      rw [(h_agree (x.1 + P, y) hρ).1, (h_agree (x.1, y) hρ).1]
      dsimp only
      have hR0 : R ≠ 0 := by linarith
      have hper_ψ := qPeriodicOn_trainStream T
      rw [simProfile_liftVelocity_periodic hR0 hper_ψ x.1]
    exact congr_fun hfun x.2
  -- 5. Divergence-free property of U
  have h_div_cont : Continuous (fun x : ℝ × Space => ∑ j : Fin 3, dy j U x j) := by
    refine continuous_finsetSum _ fun j _ => ?_
    have hfd : Continuous (fderiv ℝ U) :=
      (hU_smooth.fderiv_right (m := ∞) (by simp)).continuous
    have hdy_j : Continuous (dy j U) := hfd.clm_apply continuous_const
    exact (PiLp.continuous_apply 2 _ j).comp hdy_j
  have hψ2 : ContDiffOn ℝ 2 (trainProfile T.ψ) ageDomain := by
    have hν_pos : 0 < ν := hν.1
    have hc_pos : 0 < ν ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hν_pos _
    exact (trainStreamSmoothBUC_of UnforcedLeray.Short.PartI.trainStreamSmooth
      ν (ν ^ (-(2 : ℝ))) hν_pos hc_pos T hBUC).of_le (by simp)
  have h_div : ∀ x : ℝ × Space, ∑ j : Fin 3, dy j U x j = 0 := by
    intro x
    have hcont1 : Continuous (fun y : Space => ∑ j : Fin 3, dy j U (x.1, y) j) :=
      h_div_cont.comp (continuous_const.prodMk continuous_id)
    have hfun : (fun y : Space => ∑ j : Fin 3, dy j U (x.1, y) j) = fun _ => 0 := by
      refine Continuous.ext_on h_dense hcont1 continuous_const fun y hy => ?_
      set t : ℝ := Real.exp x.1
      set z : Space := Real.exp (x.1 / 2) • y
      have ht : 0 < t := Real.exp_pos x.1
      have hz : z ∉ Axi.axis := by
        rw [Axi.mem_axis_iff, Axi.ϱ_smul, abs_of_pos (Real.exp_pos _)]
        exact mul_ne_zero (Real.exp_pos _).ne' (Axi.ϱ_ne_zero hy)
      have hopen_t : IsOpen {q : ℝ × Space | 0 < q.1} :=
        isOpen_lt continuous_const continuous_fst
      have hdiff_u : DifferentiableAt ℝ u (t, z) :=
        (hu.contDiffAt (hopen_t.mem_nhds ht)).differentiableAt (by simp)
      rw [rlse_div_sim u x.1 y hdiff_u]
      have hev : (fun w : Space => u (t, w)) =ᶠ[𝓝 z] liftVelocity R (trainProfile T.ψ) t := by
        filter_upwards [Axi.isOpen_compl_axis.mem_nhds hz] with w hw
        exact (hoff t ht w hw).1
      have hdiv_eq : Axi.divergence (fun w : Space => u (t, w)) z =
          Axi.divergence (liftVelocity R (trainProfile T.ψ) t) z := by
        unfold Axi.divergence
        rw [hev.fderiv_eq]
      have hR0 : R ≠ 0 := by linarith
      rw [hdiv_eq, divergence_liftVelocity_eq_zero R t hR0 ht hψ2 hz, mul_zero, Complex.ofReal_zero]
    exact congr_fun hfun x.2
  exact ⟨U, Pw, hU_smooth, hPw_smooth, h_per, h_div, h_agree⟩

end UnforcedLeray.Short.IIb

end
