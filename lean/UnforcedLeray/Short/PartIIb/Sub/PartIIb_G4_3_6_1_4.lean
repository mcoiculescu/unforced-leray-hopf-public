import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# Part II-b, task `PartII-b:G4/3/6/1/4` (`VcSmooth`): decomposition

Source of record: `the November 2 reference manuscript` (SP) line 2205
(`V_c(q,η,s) = ∑ₙ V(q - nc, η, s)`, `V = a⁻² e^{-|x|²/(4a)}(-η, q)`, `a = 1 + νs`).

Components of `Vc ν c s (q,η)` for `s > 0` are `-a⁻² η e^{-η²/(4a)} Θ₀(s,q)` and
`a⁻² e^{-η²/(4a)} Θ₁(s,q)`, with the one-dimensional lattice sums
`Θ₀(s,q) = ∑ₙ e^{-(q-nc)²/(4a)}`, `Θ₁(s,q) = ∑ₙ (q-nc) e^{-(q-nc)²/(4a)}`.  So `VcSmooth` reduces
to the joint smoothness of `Θ₀, Θ₁` on `s > 0` (`ThetaSmooth0`, `ThetaSmooth1`).
Proved here: `vcSmooth_of_theta`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- `Θ₀(s,q) = ∑ₙ e^{-(q-nc)²/(4(1+νs))}`, with `x = (s,q)`. -/
def thetaSum0 (ν c : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-(x.2 - n * c) ^ 2 / (4 * (1 + ν * x.1)))

/-- `Θ₁(s,q) = ∑ₙ (q-nc) e^{-(q-nc)²/(4(1+νs))}`, with `x = (s,q)`. -/
def thetaSum1 (ν c : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n : ℤ, (x.2 - n * c) * Real.exp (-(x.2 - n * c) ^ 2 / (4 * (1 + ν * x.1)))

/-- The lattice Gaussian sum is jointly `C^∞` in `(s,q)` for `s > 0` (SP 2205).  Route: with
`a = 1+νs`, `Θ₀ = e^{-q²/(4a)} · jacobiTheta₂ z τ`, `z = -i q c/(4π a)`, `τ = i c²/(4π a)`, and
`jacobiTheta₂` is jointly complex differentiable on `0 < im τ` (`hasFDerivAt_jacobiTheta₂`), hence
analytic. -/
def ThetaSmooth0 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ContDiffOn ℝ ∞ (thetaSum0 ν c) (Ioi 0 ×ˢ univ)

/-- Same for the first-moment sum `Θ₁` (`Θ₁ = q Θ₀ - c ∑ₙ n e^{…}` and `∑ₙ n e^{…}` is the `z`-derivative
`jacobiTheta₂'`, jointly analytic as a `fderiv` of an analytic function). -/
def ThetaSmooth1 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ContDiffOn ℝ ∞ (thetaSum1 ν c) (Ioi 0 ×ˢ univ)

private theorem exp_split (a X Y : ℝ) (ha : a ≠ 0) :
    Real.exp (-(a⁻¹ * (X + Y) / 4)) =
      Real.exp (-Y / (4 * a)) * Real.exp (-X / (4 * a)) := by
  rw [← Real.exp_add]; congr 1; field_simp; ring

/-- Component formulas for `Vc` on `s > 0`. -/
theorem vc_component_zero {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 < s) (z : ℝ × ℝ) :
    UnforcedLeray.Train.Vc ν c s z 0 =
      -((1 + ν * s)⁻¹ ^ 2) * z.2 * Real.exp (-z.2 ^ 2 / (4 * (1 + ν * s))) *
        thetaSum0 ν c (s, z.1) := by
  have ha : 0 < B0113.heatWidth ν s := by unfold B0113.heatWidth; nlinarith
  have ha' : (1 + ν * s) ≠ 0 := by unfold B0113.heatWidth at ha; exact ha.ne'
  rw [UnforcedLeray.Train.Vc_eq, B0146.periodicVelocity_eq hc.ne' ha]
  show B0146.latticeSum c (B0146.u1 (B0113.heatWidth ν s)) z = _
  unfold B0146.latticeSum thetaSum0
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [B0146.u1, B0113.gw, GaussianVortex.radiusSq, B0113.heatWidth, B0146.shift]
  rw [exp_split _ _ _ ha']
  ring

theorem vc_component_one {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 < s) (z : ℝ × ℝ) :
    UnforcedLeray.Train.Vc ν c s z 1 =
      (1 + ν * s)⁻¹ ^ 2 * Real.exp (-z.2 ^ 2 / (4 * (1 + ν * s))) *
        thetaSum1 ν c (s, z.1) := by
  have ha : 0 < B0113.heatWidth ν s := by unfold B0113.heatWidth; nlinarith
  have ha' : (1 + ν * s) ≠ 0 := by unfold B0113.heatWidth at ha; exact ha.ne'
  rw [UnforcedLeray.Train.Vc_eq, B0146.periodicVelocity_eq hc.ne' ha]
  show B0146.latticeSum c (B0146.u2 (B0113.heatWidth ν s)) z = _
  unfold B0146.latticeSum thetaSum1
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [B0146.u2, B0113.gw, GaussianVortex.radiusSq, B0113.heatWidth, B0146.shift]
  rw [exp_split _ _ _ ha']
  ring

/-- `VcSmooth` from the two lattice-sum smoothness statements. -/
theorem vcSmooth_of_theta (h0 : ThetaSmooth0) (h1 : ThetaSmooth1) : VcSmooth := by
  intro ν c hν hc
  have hU : ∀ x : ℝ × UnforcedLeray.Cyl.Plane, x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set _) → 0 < x.1 :=
    fun x hx => hx.1
  have hw : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => (1 + ν * x.1)⁻¹)
      (Ioi (0 : ℝ) ×ˢ (univ : Set _)) := by
    refine ContDiffOn.inv (by fun_prop) fun x hx => ?_
    have := hU x hx; nlinarith
  have hE : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
      Real.exp (-x.2.2 ^ 2 / (4 * (1 + ν * x.1)))) (Ioi (0 : ℝ) ×ˢ (univ : Set _)) := by
    refine (Real.contDiff_exp.comp_contDiffOn ?_)
    refine ContDiffOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    have := hU x hx; nlinarith
  have hT0 : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => thetaSum0 ν c (x.1, x.2.1))
      (Ioi (0 : ℝ) ×ˢ (univ : Set _)) :=
    (h0 ν c hν hc).comp (by fun_prop) fun x hx => ⟨hx.1, mem_univ _⟩
  have hT1 : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => thetaSum1 ν c (x.1, x.2.1))
      (Ioi (0 : ℝ) ×ˢ (univ : Set _)) :=
    (h1 ν c hν hc).comp (by fun_prop) fun x hx => ⟨hx.1, mem_univ _⟩
  have hA : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
      (-((1 + ν * x.1)⁻¹ ^ 2) * x.2.2 * Real.exp (-x.2.2 ^ 2 / (4 * (1 + ν * x.1))) *
        thetaSum0 ν c (x.1, x.2.1), (1 + ν * x.1)⁻¹ ^ 2 *
          Real.exp (-x.2.2 ^ 2 / (4 * (1 + ν * x.1))) * thetaSum1 ν c (x.1, x.2.1)))
      (Ioi (0 : ℝ) ×ˢ (univ : Set _)) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact ((((hw.pow 2).neg.mul (by fun_prop)).mul hE).mul hT0)
    · exact (((hw.pow 2).mul hE).mul hT1)
  have hB := (UnforcedLeray.Train.toVecL.contDiff (n := ∞)).comp_contDiffOn hA
  refine hB.congr fun x hx => ?_
  have hs : 0 < x.1 := hU x hx
  show _ = UnforcedLeray.Train.toVecL _
  rw [UnforcedLeray.Train.toVecL_apply]
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, UnforcedLeray.Train.toVec_zero]
    exact vc_component_zero hν hc hs x.2
  · simp only [Fin.mk_one, UnforcedLeray.Train.toVec_one]
    exact vc_component_one hν hc hs x.2

end UnforcedLeray.Short.IIb
