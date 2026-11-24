import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs
import UnforcedLeray.Units.B0296.Kernel
import UnforcedLeray.Lib.HeatCylinder.PeriodicLift

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8`: the concrete free part on `X_{-m,c}` (objects)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836:
on the cylinder `C_c = (ℝ/cℤ) × ℝ` the full moving evolution is built at fixed `ν > 0`, `c > 0`
by a Volterra iteration whose free part is the periodic heat semigroup of diffusivity `ν` and
its heat-divergence response.  For the reverse-time adjoint (SP 3060) the state space is
`X_{-m,c} = L²(C_c, ⟨x⟩^{-2m} dx)` (complex, `AdjX`), and the free part is (`AdjHeatSupplier`)
* `S₀(τ) f = e^{ντΔ} f`, the Gaussian convolution of the `c`-periodic lift of `f`
  (`adjS0Fun`), and
* `S(τ)(F, h) = e^{ντΔ}(-∇·F + h)` (`adjSFun`), with the divergence put on the kernel
  (`adjDivFun`), so no derivative of the flux `F` is needed.

This file defines the concrete objects and proves the elementary facts: the explicit Gaussian
formula (`adjHeatKer_eq`), the coordinate derivatives of the kernel, the periodic lift
(`perRep`) and its a.e. invariance, and that the generic kernel operator `adjKerOp` (of which
`adjS0Fun`, `adjDivFun`, `adjSFun` are instances) is `c`-periodic, only depends on the a.e. class
of its argument, is homogeneous, additive where the integrals converge, and strongly measurable.
That the operators map `X_{-m,c}` boundedly into itself is the leaf `KerYoung`
(`HeatExists/CLM.lean`, which builds the continuous linear maps); the leaves are stated in
`HeatExists/Leaves.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The heat kernel of diffusivity `ν` and its gradient -/

/-- **The heat kernel of diffusivity `ν` at age `τ`** (SP 2819-2836: the free part of the
Volterra iteration is the periodic heat semigroup `e^{ντΔ}` of diffusivity `ν`):
`G_{ντ}(x) = (4πντ)^{-1} exp(-|x|²/(4ντ))` (`adjHeatKer_eq`), i.e. B0284's planar Gaussian
`heatKernel2` (the kernel of `e^{θΔ}`) at time `θ = ντ`. -/
def adjHeatKer (ν τ : ℝ) (x : ℝ × ℝ) : ℝ := UnforcedLeray.B0284.heatKernel2 (ν * τ) x

/-- The explicit Gaussian: `G_{ντ}(x) = (4πντ)^{-1} exp(-|x|²/(4ντ))` (`ντ ≥ 0`). -/
theorem adjHeatKer_eq {ν τ : ℝ} (h : 0 ≤ ν * τ) (x : ℝ × ℝ) :
    adjHeatKer ν τ x =
      (4 * Real.pi * (ν * τ))⁻¹ * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * (ν * τ))) := by
  have ha : 0 ≤ 4 * Real.pi * 1 * (ν * τ) := mul_nonneg (by positivity) h
  have hs : (Real.sqrt (4 * Real.pi * 1 * (ν * τ)))⁻¹ * (Real.sqrt (4 * Real.pi * 1 * (ν * τ)))⁻¹
      = (4 * Real.pi * (ν * τ))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt ha, mul_one]
  simp only [adjHeatKer, UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0191.heatKernel]
  calc (Real.sqrt (4 * Real.pi * 1 * (ν * τ)))⁻¹ * Real.exp (-x.1 ^ 2 / (4 * 1 * (ν * τ))) *
        ((Real.sqrt (4 * Real.pi * 1 * (ν * τ)))⁻¹ * Real.exp (-x.2 ^ 2 / (4 * 1 * (ν * τ))))
      = ((Real.sqrt (4 * Real.pi * 1 * (ν * τ)))⁻¹ *
          (Real.sqrt (4 * Real.pi * 1 * (ν * τ)))⁻¹) *
          (Real.exp (-x.1 ^ 2 / (4 * 1 * (ν * τ))) *
            Real.exp (-x.2 ^ 2 / (4 * 1 * (ν * τ)))) := by ring
    _ = (4 * Real.pi * (ν * τ))⁻¹ * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * (ν * τ))) := by
      rw [hs, ← Real.exp_add]
      congr 2
      ring

theorem continuous_adjHeatKer (ν τ : ℝ) : Continuous (adjHeatKer ν τ) := by
  unfold adjHeatKer UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  fun_prop

theorem adjHeatKer_nonneg {ν τ : ℝ} (h : 0 < ν * τ) (x : ℝ × ℝ) : 0 ≤ adjHeatKer ν τ x :=
  UnforcedLeray.B0284.heatKernel2_nonneg h x

/-- **The kernel gradient** `∂_j G_{ντ}` (`j = 0`: `∂_q`, `j = 1`: `∂_η`; SP 2819-2836, the
divergence response `e^{ντΔ}(-∇·F)` is the convolution of `F` with `-∇G_{ντ}`): B0296's
`gradHeatKernel2` at time `ντ`, `∂_j G_θ(x) = -(x_j/(2θ)) G_θ(x)`
(`hasDerivAt_adjHeatKer_fst`, `hasDerivAt_adjHeatKer_snd`). -/
def adjHeatGradKer (ν τ : ℝ) (j : Fin 2) (x : ℝ × ℝ) : ℝ :=
  if j = 0 then (UnforcedLeray.B0296.gradHeatKernel2 (ν * τ) x).1
  else (UnforcedLeray.B0296.gradHeatKernel2 (ν * τ) x).2

theorem continuous_adjHeatGradKer (ν τ : ℝ) (j : Fin 2) : Continuous (adjHeatGradKer ν τ j) := by
  unfold adjHeatGradKer UnforcedLeray.B0296.gradHeatKernel2
  split_ifs
  · exact ((UnforcedLeray.B0296.continuous_dHeatKernel _).comp continuous_fst).mul
      ((UnforcedLeray.B0296.continuous_heatKernel1 _).comp continuous_snd)
  · exact ((UnforcedLeray.B0296.continuous_heatKernel1 _).comp continuous_fst).mul
      ((UnforcedLeray.B0296.continuous_dHeatKernel _).comp continuous_snd)

/-- `adjHeatGradKer ν τ 0` is the `q`-derivative of the kernel (`ντ ≠ 0`). -/
theorem hasDerivAt_adjHeatKer_fst {ν τ : ℝ} (h : ν * τ ≠ 0) (w : ℝ × ℝ) :
    HasDerivAt (fun q => adjHeatKer ν τ (q, w.2)) (adjHeatGradKer ν τ 0 w) w.1 := by
  simpa [adjHeatKer, adjHeatGradKer] using UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst h w

/-- `adjHeatGradKer ν τ 1` is the `η`-derivative of the kernel (`ντ ≠ 0`). -/
theorem hasDerivAt_adjHeatKer_snd {ν τ : ℝ} (h : ν * τ ≠ 0) (w : ℝ × ℝ) :
    HasDerivAt (fun η => adjHeatKer ν τ (w.1, η)) (adjHeatGradKer ν τ 1 w) w.2 := by
  simpa [adjHeatKer, adjHeatGradKer] using UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd h w

/-! ## The periodic lift -/

theorem perRep_eq_centeredPerLift {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) :
    perRep c f = UnforcedLeray.HeatCylinder.centeredPerLift hc f := by
  funext x
  simp [perRep, hc, UnforcedLeray.HeatCylinder.centeredPerLift, UnforcedLeray.Sob.perExt]

theorem stronglyMeasurable_perRep {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hf : StronglyMeasurable f) : StronglyMeasurable (perRep c f) := by
  rw [perRep_eq_centeredPerLift hc]
  exact (UnforcedLeray.HeatCylinder.measurable_centeredPerLift hc hf.measurable).stronglyMeasurable

/-- Cell-a.e. equal data have periodic lifts that agree a.e. on the whole plane (the centered
cell is a fundamental domain, `HeatCylinder.centeredPerLift_congr_ae`). -/
theorem perRep_congr_ae {c m : ℝ} (hc : 0 < c) {f g : ℝ × ℝ → ℂ}
    (hfg : f =ᵐ[B0579.cellMeasure c m] g) : perRep c f =ᵐ[volume] perRep c g := by
  rw [perRep_eq_centeredPerLift hc, perRep_eq_centeredPerLift hc]
  apply UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc
  have h := (B0579.ac_cellMeasure c m).ae_le hfg
  have hcell : UnforcedLeray.Cyl.cell c = B0579.cell c := by
    simp [UnforcedLeray.Cyl.cell, B0579.cell, neg_div]
  rw [UnforcedLeray.Cyl.cellμ, hcell]
  exact h

theorem perRep_add (c : ℝ) (f g : ℝ × ℝ → ℂ) : perRep c (f + g) = perRep c f + perRep c g := by
  funext x
  unfold perRep
  split_ifs <;> rfl

theorem perRep_smul (c : ℝ) (a : ℂ) (f : ℝ × ℝ → ℂ) : perRep c (a • f) = a • perRep c f := by
  funext x
  unfold perRep
  split_ifs <;> rfl

/-- A `c`-periodic function is its own periodic lift. -/
theorem perRep_eq_self_of_periodic {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) : perRep c g = g := by
  funext x
  simp only [perRep, hc, ↓reduceDIte]
  rw [← self_sub_toIcoDiv_zsmul]
  have h := UnforcedLeray.B0289.IsQPeriodic.add_int_mul (c := c) (f := g) hg
    (-(toIcoDiv hc (-(c / 2)) x.1)) x
  convert h using 3
  simp [zsmul_eq_mul, sub_eq_add_neg]

/-! ## The kernel operators -/

/-- **The kernel operator on cell functions**: `f ↦ (x ↦ ∫_{ℝ²} k(x - y) f̃(y) dy)`, with
`f̃ = perRep c f` the `c`-periodic lift (SP 2819-2836: the free part acts on the periodic lift,
restricted to the cell).  `adjS0Fun`, `adjDivFun`, `adjSFun` are its instances. -/
def adjKerOp (c : ℝ) (k : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∫ y, (k (x - y) : ℂ) * perRep c f y

/-- The kernel operator only depends on the cell-a.e. class of its argument. -/
theorem adjKerOp_congr_ae {c m : ℝ} (hc : 0 < c) (k : ℝ × ℝ → ℝ) {f g : ℝ × ℝ → ℂ}
    (hfg : f =ᵐ[B0579.cellMeasure c m] g) : adjKerOp c k f = adjKerOp c k g := by
  funext x
  unfold adjKerOp
  refine integral_congr_ae ?_
  filter_upwards [perRep_congr_ae hc hfg] with y hy
  rw [hy]

/-- The kernel operator is `c`-periodic in `q`. -/
theorem adjKerOp_periodic {c : ℝ} (hc : 0 < c) (k : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ)
    (x : ℝ × ℝ) : adjKerOp c k f (x.1 + c, x.2) = adjKerOp c k f x := by
  unfold adjKerOp
  have hx : ((x.1 + c, x.2) : ℝ × ℝ) = x + (c, 0) := by ext <;> simp
  have hper : ∀ y : ℝ × ℝ, perRep c f (y + (c, 0)) = perRep c f y := fun y => by
    have h := perRep_periodic hc f y
    rwa [show ((y.1 + c, y.2) : ℝ × ℝ) = y + (c, 0) by ext <;> simp] at h
  rw [hx]
  calc ∫ y, (k (x + (c, 0) - y) : ℂ) * perRep c f y
      = ∫ y, (k (x + (c, 0) - (y + (c, 0))) : ℂ) * perRep c f (y + (c, 0)) :=
        (integral_add_right_eq_self
          (fun y => (k (x + (c, 0) - y) : ℂ) * perRep c f y) ((c, 0) : ℝ × ℝ)).symm
    _ = ∫ y, (k (x - y) : ℂ) * perRep c f y := by
        congr 1
        funext y
        rw [hper y, show x + ((c, 0) : ℝ × ℝ) - (y + (c, 0)) = x - y by abel]

/-- The kernel operator produces a `c`-periodic function, its own lift. -/
theorem perRep_adjKerOp {c : ℝ} (hc : 0 < c) (k : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℂ) :
    perRep c (adjKerOp c k f) = adjKerOp c k f :=
  perRep_eq_self_of_periodic hc (adjKerOp_periodic hc k f)

theorem adjKerOp_smul (c : ℝ) (k : ℝ × ℝ → ℝ) (a : ℂ) (f : ℝ × ℝ → ℂ) :
    adjKerOp c k (a • f) = a • adjKerOp c k f := by
  funext x
  simp only [adjKerOp, perRep_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- Additivity at a point where both integrals converge. -/
theorem adjKerOp_add_apply {c : ℝ} {k : ℝ × ℝ → ℝ} {f g : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    (hf : Integrable (fun y => (k (x - y) : ℂ) * perRep c f y))
    (hg : Integrable (fun y => (k (x - y) : ℂ) * perRep c g y)) :
    adjKerOp c k (f + g) x = adjKerOp c k f x + adjKerOp c k g x := by
  simp only [adjKerOp, perRep_add, Pi.add_apply, mul_add]
  exact integral_add hf hg

theorem stronglyMeasurable_adjKerOp {c : ℝ} (hc : 0 < c) {k : ℝ × ℝ → ℝ} (hk : Continuous k)
    {f : ℝ × ℝ → ℂ} (hf : StronglyMeasurable f) : StronglyMeasurable (adjKerOp c k f) := by
  have hF : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k (p.1 - p.2) : ℂ) * perRep c f p.2) :=
    ((Complex.continuous_ofReal.comp
      (hk.comp (continuous_fst.sub continuous_snd))).stronglyMeasurable).mul
      ((stronglyMeasurable_perRep hc hf).comp_measurable measurable_snd)
  exact hF.integral_prod_right'

/-! ## The free part -/

/-- **The free heat flow of a cell function** (SP 2819-2836): `e^{ντΔ} f (x) =
∫_{ℝ²} G_{ντ}(x - y) f̃(y) dy`, the Gaussian convolution of the `c`-periodic lift
`f̃ = perRep c f` (`f` a representative of an element of `X_{-m,c}`). -/
def adjS0Fun (ν c τ : ℝ) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∫ y, (adjHeatKer ν τ (x - y) : ℂ) * perRep c f y

theorem adjS0Fun_eq_adjKerOp (ν c τ : ℝ) : adjS0Fun ν c τ = adjKerOp c (adjHeatKer ν τ) := rfl

/-- **The heat-divergence response of a flux** (SP 2819-2836):
`e^{ντΔ}(-∇·F)(x) = -∑_j ∫_{ℝ²} ∂_j G_{ντ}(x - y) F̃_j(y) dy` (the divergence moved onto the
kernel; `F̃_j = perRep c (F j)`). -/
def adjDivFun (ν c τ : ℝ) (F : Fin 2 → ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  -∑ j : Fin 2, ∫ y, (adjHeatGradKer ν τ j (x - y) : ℂ) * perRep c (F j) y

theorem adjDivFun_eq (ν c τ : ℝ) (F : Fin 2 → ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    adjDivFun ν c τ F x = -∑ j : Fin 2, adjKerOp c (adjHeatGradKer ν τ j) (F j) x := rfl

/-- **The source response** (SP 2819-2836): `S(τ)(F, h) = e^{ντΔ}(-∇·F + h)`, i.e.
`∫ (-∇G_{ντ}(x - y))·F̃(y) dy + ∫ G_{ντ}(x - y) h̃(y) dy`. -/
def adjSFun (ν c τ : ℝ) (F : Fin 2 → ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  adjDivFun ν c τ F x + adjS0Fun ν c τ h x

theorem adjS0Fun_periodic {ν c τ : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    adjS0Fun ν c τ f (x.1 + c, x.2) = adjS0Fun ν c τ f x :=
  adjKerOp_periodic hc _ f x

theorem adjDivFun_periodic {ν c τ : ℝ} (hc : 0 < c) (F : Fin 2 → ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    adjDivFun ν c τ F (x.1 + c, x.2) = adjDivFun ν c τ F x := by
  simp only [adjDivFun_eq, adjKerOp_periodic hc]

theorem adjSFun_periodic {ν c τ : ℝ} (hc : 0 < c) (F : Fin 2 → ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (x : ℝ × ℝ) : adjSFun ν c τ F h (x.1 + c, x.2) = adjSFun ν c τ F h x := by
  simp only [adjSFun, adjDivFun_periodic hc, adjS0Fun_periodic hc]

end UnforcedLeray.Short.IIIa
