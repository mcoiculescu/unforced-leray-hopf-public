import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2_2

/-!
# Helper for `PartII-b:T08/1/2/2/1`: componentwise form of the ring lift

`N_v b (τ,y) = √s (b₀(c) e_r(y) + b₁(c) e_z)` with `c = chart(τ,y)`, `s = age`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.DriftOff

open UnforcedLeray.PhaseSpace (CVec3)

/-- Real vectors of `ℝ³` seen in `ℂ³`, as a real-linear map. -/
def realCL : UnforcedLeray.Space →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => UnforcedLeray.B0412.realC x
      map_add' := fun x y => by ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by ext i; simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul] }

theorem realCL_apply (x : UnforcedLeray.Space) : realCL x = UnforcedLeray.B0412.realC x := rfl

/-- The complex-linear map `v ↦ v₀ • X + v₁ • E` on meridional complex vectors. -/
def pairL (X E : CVec3) : UnforcedLeray.Short.IIb.CMerid →L[ℂ] CVec3 :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight X + (EuclideanSpace.proj (1 : Fin 2)).smulRight E

theorem pairL_apply (X E : CVec3) (v : UnforcedLeray.Short.IIb.CMerid) :
    pairL X E v = v 0 • X + v 1 • E := by
  simp [pairL]

/-- Componentwise form of the ring lift: `N_v b = √s (b₀ e_r + b₁ e_z)` at `(τ,y)`. -/
theorem nvC_rep (R : ℝ) (F : UnforcedLeray.Short.IIb.CProf) (q : ℝ × UnforcedLeray.Space) :
    UnforcedLeray.Short.IIb.NvC R F q =
      √(UnforcedLeray.Axi.age R q.2) •
        (F (UnforcedLeray.Axi.chart R q.1 q.2) 0 • realCL (UnforcedLeray.Axi.eR q.2) +
          F (UnforcedLeray.Axi.chart R q.1 q.2) 1 • realCL UnforcedLeray.Axi.e3) := by
  ext j
  have e0 := (Complex.re_add_im (F (UnforcedLeray.Axi.chart R q.1 q.2) 0)).symm
  have e1 := (Complex.re_add_im (F (UnforcedLeray.Axi.chart R q.1 q.2) 1)).symm
  simp only [UnforcedLeray.Short.IIb.NvC, UnforcedLeray.Axi.Nv, UnforcedLeray.Axi.frameL_apply,
    realCL_apply, UnforcedLeray.Short.IIb.reM, UnforcedLeray.Short.IIb.imM]
  fin_cases j <;> simp [UnforcedLeray.B0412.realC_apply, UnforcedLeray.Axi.eR, UnforcedLeray.Axi.e3]
    <;> (try conv_rhs => rw [e0]) <;> (try conv_rhs => rw [e1]) <;> ring

/-- Joint differentiability of the chart `(τ,y) ↦ chart R τ y` off the axis. -/
theorem chart_diffAt {R : ℝ} (hR : R ≠ 0) {q : ℝ × UnforcedLeray.Space}
    (hq : q.2 ∉ UnforcedLeray.Axi.axis) :
    DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.chart R x.1 x.2) q := by
  have hage : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.age R x.2) q :=
    ((UnforcedLeray.Axi.hasFDerivAt_age R hq).differentiableAt).comp q differentiableAt_snd
  have hpos : UnforcedLeray.Axi.age R q.2 ≠ 0 := (UnforcedLeray.Axi.age_pos hR hq).ne'
  have hphase : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.phase R x.1 x.2) q := by
    unfold UnforcedLeray.Axi.phase
    have h2 : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => R * x.1 / 2) q := by
      fun_prop
    exact h2.sub
      ((differentiableAt_const (R / 2)).mul (hage.log hpos))
  have htrans : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.trans R x.2) q :=
    ((UnforcedLeray.Axi.hasFDerivAt_trans R hq).differentiableAt).comp q differentiableAt_snd
  unfold UnforcedLeray.Axi.chart
  exact hage.prodMk (hphase.prodMk htrans)

/-- Differentiability of the ring lift off the axis, for a differentiable profile. -/
theorem nvC_diffAt {R : ℝ} (hR : R ≠ 0) {F : UnforcedLeray.Short.IIb.CProf}
    (hF : Differentiable ℝ F) {q : ℝ × UnforcedLeray.Space}
    (hq : q.2 ∉ UnforcedLeray.Axi.axis) :
    DifferentiableAt ℝ (UnforcedLeray.Short.IIb.NvC R F) q := by
  have hfun : UnforcedLeray.Short.IIb.NvC R F = fun x : ℝ × UnforcedLeray.Space =>
      √(UnforcedLeray.Axi.age R x.2) •
        (F (UnforcedLeray.Axi.chart R x.1 x.2) 0 • realCL (UnforcedLeray.Axi.eR x.2) +
          F (UnforcedLeray.Axi.chart R x.1 x.2) 1 • realCL UnforcedLeray.Axi.e3) :=
    funext fun x => nvC_rep R F x
  rw [hfun]
  have hage : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.age R x.2) q :=
    ((UnforcedLeray.Axi.hasFDerivAt_age R hq).differentiableAt).comp q differentiableAt_snd
  have hsq : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => √(UnforcedLeray.Axi.age R x.2)) q :=
    hage.sqrt (UnforcedLeray.Axi.age_pos hR hq).ne'
  have hc := chart_diffAt hR hq
  have hFc : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => F (UnforcedLeray.Axi.chart R x.1 x.2)) q :=
    (hF _).comp q hc
  have hp0 : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => F (UnforcedLeray.Axi.chart R x.1 x.2) 0) q :=
    ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Short.IIb.CMerid →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt.comp q hFc
  have hp1 : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => F (UnforcedLeray.Axi.chart R x.1 x.2) 1) q :=
    ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Short.IIb.CMerid →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt.comp q hFc
  have hE : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.eR x.2) q :=
    ((UnforcedLeray.Axi.hasFDerivAt_eR hq).differentiableAt).comp q differentiableAt_snd
  have hR0 : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => realCL (UnforcedLeray.Axi.eR x.2)) q :=
    realCL.differentiableAt.comp q hE
  exact hsq.smul ((hp0.smul hR0).add (hp1.smul (differentiableAt_const _)))

end UnforcedLeray.Short.IIb.DriftOff
