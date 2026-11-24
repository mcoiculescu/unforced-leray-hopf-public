import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_2

/-!
# `gradLiftPointwise` (task `PartIII-b:C/near/pins/3/3/2/3`)

Source `the November 2 reference manuscript` 1666, 1675-1677, 2666-2668, 2683.

Off the axis, `ψ = Ψ ∘ Gpt` with `Gpt` the unreduced chart point (`R = ε⁻¹`).  The chain rule gives
`∂_ϱ ψ = √s (D_εΨ)` and `∂_z ψ = √s ∂_ηΨ`, with `√s = R/ϱ`, which is the Cartesian velocity
`𝒩_v f = √s (f_r e_r + f_z e_z)` at the chart point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The unreduced chart point of a similarity point with `R = ε⁻¹` (source 2666-2668). -/
private def Gpt (ε : ℝ) (x : ℝ × Space) : Chart :=
  (ε⁻¹ ^ 2 / hRad x.2 ^ 2,
    (ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2, ε⁻¹ * x.2 2 / hRad x.2))

/-- The lift equals `Ψ` of the unreduced chart point (periodicity in `q`). -/
private theorem liftScalar_eq {c ε : ℝ} (Ψ : UnforcedLeray.B0226.ProfileTest c)
    (x : ℝ × Space) : liftScalar c ε Ψ x = Ψ.1 (Gpt ε x) := by
  unfold liftScalar chartOf Gpt
  have hper : Function.Periodic
      (fun q : ℝ => Ψ.1 (ε⁻¹ ^ 2 / hRad x.2 ^ 2, q, ε⁻¹ * x.2 2 / hRad x.2)) c :=
    fun q => Ψ.2.periodic (ε⁻¹ ^ 2 / hRad x.2 ^ 2, q, ε⁻¹ * x.2 2 / hRad x.2)
  have h : Ψ.1 (ε⁻¹ ^ 2 / hRad x.2 ^ 2,
      (ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2 -
        ↑(⌊(ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2) / c + 1 / 2⌋ : ℤ) * c,
        ε⁻¹ * x.2 2 / hRad x.2)) =
      Ψ.1 (ε⁻¹ ^ 2 / hRad x.2 ^ 2, (ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2,
        ε⁻¹ * x.2 2 / hRad x.2)) :=
    hper.sub_int_mul_eq _
  have h2 : ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2 -
      c * ↑⌊(ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2) / c + 1 / 2⌋ =
      ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2 -
      ↑⌊(ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2) / c + 1 / 2⌋ * c := by
    ring
  rw [h2, h]

/-- Smoothness of the unreduced chart point off the axis. -/
private theorem contDiffAt_Gpt {ε : ℝ} (hε : 0 < ε) (x : ℝ × Space) (hx : 0 < hRad x.2) :
    ContDiffAt ℝ ∞ (Gpt ε) x := by
  have hz : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : Space => z i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  have hsq : ContDiffAt ℝ ∞ (fun y : ℝ × Space => y.2 0 ^ 2 + y.2 1 ^ 2) x :=
    ((((hz 0).comp contDiff_snd).pow 2).add (((hz 1).comp contDiff_snd).pow 2)).contDiffAt
  have hpos : (fun y : ℝ × Space => y.2 0 ^ 2 + y.2 1 ^ 2) x ≠ 0 := by
    have h := hx
    unfold hRad at h
    exact (Real.sqrt_pos.1 h).ne'
  have hR : ContDiffAt ℝ ∞ (fun y : ℝ × Space => hRad y.2) x := by
    unfold hRad
    exact hsq.sqrt hpos
  have hR0 : hRad x.2 ≠ 0 := hx.ne'
  have hz2 : ContDiffAt ℝ ∞ (fun y : ℝ × Space => y.2 2) x :=
    ((hz 2).comp contDiff_snd).contDiffAt
  have hlog : hRad x.2 / ε⁻¹ ≠ 0 := div_ne_zero hR0 (inv_ne_zero hε.ne')
  unfold Gpt
  refine ContDiffAt.prodMk ?_ (ContDiffAt.prodMk ?_ ?_)
  · exact contDiffAt_const.div (hR.pow 2) (pow_ne_zero 2 hR0)
  · refine ContDiffAt.add ?_ ?_
    · exact contDiffAt_const.mul ((hR.div_const _).log hlog)
    · exact (contDiffAt_const.mul contDiffAt_fst).div_const 2
  · exact (contDiffAt_const.mul hz2).div hR hR0

/-- The unreduced chart point is the Axi chart point. -/
private theorem chart_eq_Gpt {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (y : Space) (hy : 0 < hRad y) :
    UnforcedLeray.Axi.chart ε⁻¹ τ y = Gpt ε (τ, y) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hϱ : UnforcedLeray.Axi.ϱ y = hRad y := rfl
  unfold UnforcedLeray.Axi.chart UnforcedLeray.Axi.age UnforcedLeray.Axi.phase
    UnforcedLeray.Axi.trans Gpt
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  show ε⁻¹ * τ / 2 - ε⁻¹ / 2 * Real.log (ε⁻¹ ^ 2 / UnforcedLeray.Axi.ϱ y ^ 2) =
    ε⁻¹ * Real.log (hRad y / ε⁻¹) + ε⁻¹ * τ / 2
  rw [hϱ, Real.log_div (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 hy.ne'), Real.log_pow,
    Real.log_pow, Real.log_div hy.ne' hR.ne']
  push_cast
  ring

/-- The `q`-shift of a profile point. -/
private def qShift (c : ℝ) : Profile := (0, (c, 0))

private theorem fderiv_qShift {c : ℝ} {Φ : Profile → ℝ} (hΦ : UnforcedLeray.B0220.QPeriodic c Φ)
    (p : Profile) : fderiv ℝ Φ (p + qShift c) = fderiv ℝ Φ p := by
  have hf : (fun x : Profile => Φ (x + qShift c)) = Φ := by
    funext x
    have hq' : x + qShift c = (x.1, x.2.1 + c, x.2.2) := by simp [qShift, Prod.ext_iff]
    rw [hq']
    exact hΦ x
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ) (qShift c) (x := p)
  rw [hf] at h
  exact h.symm

private theorem Deps_qPer {c ε : ℝ} {Φ : Profile → ℝ} (hΦ : UnforcedLeray.B0220.QPeriodic c Φ)
    (p : Profile) : UnforcedLeray.B0226.Deps ε Φ (p.1, p.2.1 + c, p.2.2) =
      UnforcedLeray.B0226.Deps ε Φ p := by
  have hp := fderiv_qShift hΦ p
  have hq : (p.1, p.2.1 + c, p.2.2) = p + qShift c := by simp [qShift, Prod.ext_iff]
  rw [hq]
  unfold UnforcedLeray.B0226.Deps UnforcedLeray.B0226.Kop Axi.dQ Axi.dS Axi.dEta
  simp only [hp]
  simp [qShift]

private theorem dEta_qPer {c : ℝ} {Φ : Profile → ℝ} (hΦ : UnforcedLeray.B0220.QPeriodic c Φ)
    (p : Profile) : Axi.dEta Φ (p.1, p.2.1 + c, p.2.2) = Axi.dEta Φ p := by
  have hp := fderiv_qShift hΦ p
  have hq : (p.1, p.2.1 + c, p.2.2) = p + qShift c := by simp [qShift, Prod.ext_iff]
  rw [hq]
  unfold Axi.dEta
  rw [hp]

/-- A `q`-periodic function is constant on the recentred cell. -/
private theorem cellRep_per (c : ℝ) (g : Profile → ℝ)
    (hg : ∀ p : Profile, g (p.1, p.2.1 + c, p.2.2) = g p) (p : Profile) :
    g (p.1, cellRep c p.2.1, p.2.2) = g p := by
  have hper : Function.Periodic (fun q : ℝ => g (p.1, q, p.2.2)) c :=
    fun q => hg (p.1, q, p.2.2)
  have h := hper.sub_int_mul_eq (x := p.2.1) (⌊(p.2.1 + c / 2) / c⌋)
  unfold cellRep
  have e : p.2.1 - c * ↑⌊(p.2.1 + c / 2) / c⌋ = p.2.1 - ↑⌊(p.2.1 + c / 2) / c⌋ * c := by
    ring
  rw [e]
  exact h

/-- Chain-rule coefficients along the line `t ↦ y + t v`. -/
private def dSv (ε : ℝ) (y v : Space) : ℝ :=
  -(2 * ε⁻¹ ^ 2 * ((y 0 * v 0 + y 1 * v 1) / hRad y)) / hRad y ^ 3

private def dQv (ε : ℝ) (y v : Space) : ℝ :=
  ε⁻¹ * ((y 0 * v 0 + y 1 * v 1) / hRad y) / hRad y

private def dEv (ε : ℝ) (y v : Space) : ℝ :=
  ε⁻¹ * v 2 / hRad y - ε⁻¹ * y 2 * ((y 0 * v 0 + y 1 * v 1) / hRad y) / hRad y ^ 2

private theorem line_hasDerivAt {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (y v : Space) (hy : 0 < hRad y) :
    HasDerivAt (fun t : ℝ => Gpt ε (τ, y + t • v)) (dSv ε y v, dQv ε y v, dEv ε y v) 0 := by
  have hϱne : hRad y ≠ 0 := hy.ne'
  have hyy : y 0 * y 0 + y 1 * y 1 = hRad y ^ 2 := by
    unfold hRad
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    ring
  have h0 : HasDerivAt (fun t : ℝ => y 0 + t * v 0) (v 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 0)).const_add (y 0)
  have h1 : HasDerivAt (fun t : ℝ => y 1 + t * v 1) (v 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 1)).const_add (y 1)
  have h2' : HasDerivAt (fun t : ℝ => y 2 + t * v 2) (v 2) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v 2)).const_add (y 2)
  have h2 : HasDerivAt (fun t : ℝ => (y + t • v) 2) (v 2) 0 := by
    simpa using h2'
  have hFt : ∀ t : ℝ, hRad (y + t • v) = Real.sqrt ((y 0 + t * v 0) * (y 0 + t * v 0) +
      (y 1 + t * v 1) * (y 1 + t * v 1)) := by
    intro t
    unfold hRad
    congr 1
    simp [pow_two]
  have hF : HasDerivAt (fun t : ℝ => (y 0 + t * v 0) * (y 0 + t * v 0) +
      (y 1 + t * v 1) * (y 1 + t * v 1)) (v 0 * y 0 + y 0 * v 0 + (v 1 * y 1 + y 1 * v 1)) 0 := by
    have := (h0.mul h0).add (h1.mul h1)
    refine this.congr_deriv ?_
    simp only [zero_mul, add_zero] <;> ring
  have hsqF0 : Real.sqrt (y 0 * y 0 + y 1 * y 1) = hRad y := by
    rw [hyy, Real.sqrt_sq hy.le]
  have hne : (y 0 + 0 * v 0) * (y 0 + 0 * v 0) + (y 1 + 0 * v 1) * (y 1 + 0 * v 1) ≠ 0 := by
    simp only [zero_mul, add_zero]
    rw [hyy]
    exact pow_ne_zero 2 hϱne
  have hρ : HasDerivAt (fun t : ℝ => hRad (y + t • v))
      ((y 0 * v 0 + y 1 * v 1) / hRad y) 0 := by
    have hs := hF.sqrt hne
    have e1 : (fun t : ℝ => hRad (y + t • v)) = fun t : ℝ => Real.sqrt
        ((y 0 + t * v 0) * (y 0 + t * v 0) + (y 1 + t * v 1) * (y 1 + t * v 1)) := funext hFt
    rw [e1]
    convert hs using 1 <;> simp only [zero_mul, add_zero, hsqF0] <;> field_simp <;> ring
  have hρ0' : hRad (y + (0:ℝ) • v) = hRad y := by simp
  have hne2 : hRad (y + (0:ℝ) • v) ^ 2 ≠ 0 := by
    rw [hρ0']
    exact pow_ne_zero 2 hϱne
  have hlog0 : hRad (y + (0:ℝ) • v) / ε⁻¹ ≠ 0 := by
    rw [hρ0']
    exact div_ne_zero hϱne (inv_ne_zero hε.ne')
  have hne1 : hRad (y + (0:ℝ) • v) ≠ 0 := by
    rw [hρ0']
    exact hϱne
  have hS := (hasDerivAt_const (0:ℝ) (ε⁻¹ ^ 2)).div (hρ.pow 2) hne2
  have hQ0 : HasDerivAt (fun _ : ℝ => ε⁻¹ * τ / 2) 0 0 := hasDerivAt_const _ _
  have hQ := (((hρ.div_const ε⁻¹).log hlog0).const_mul ε⁻¹).add hQ0
  have hη := (h2.const_mul ε⁻¹).div hρ hne1
  have key : HasDerivAt (fun t : ℝ => (ε⁻¹ ^ 2 / hRad (y + t • v) ^ 2,
      (ε⁻¹ * Real.log (hRad (y + t • v) / ε⁻¹) + ε⁻¹ * τ / 2,
        ε⁻¹ * (y + t • v) 2 / hRad (y + t • v)))) _ 0 :=
    hS.prodMk (hQ.prodMk hη)
  have hG : (fun t : ℝ => Gpt ε (τ, y + t • v)) = (fun t : ℝ => (ε⁻¹ ^ 2 / hRad (y + t • v) ^ 2,
      (ε⁻¹ * Real.log (hRad (y + t • v) / ε⁻¹) + ε⁻¹ * τ / 2,
        ε⁻¹ * (y + t • v) 2 / hRad (y + t • v)))) := rfl
  rw [hG]
  convert key using 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · unfold dSv
    norm_num <;> field_simp <;> ring
  · unfold dQv
    norm_num <;> field_simp <;> ring
  · unfold dEv
    norm_num <;> field_simp <;> ring

/-- Linear decomposition of a derivative in the chart coordinates. -/
private theorem fderiv_decomp (Φ : ℝ × (ℝ × ℝ) → ℝ) (p : ℝ × (ℝ × ℝ)) (a b d : ℝ) :
    fderiv ℝ Φ p (a, (b, d)) = a * Axi.dS Φ p + b * Axi.dQ Φ p + d * Axi.dEta Φ p := by
  have h : ((a, (b, d)) : ℝ × (ℝ × ℝ)) = a • ((1:ℝ), ((0:ℝ), (0:ℝ))) +
      b • ((0:ℝ), ((1:ℝ), (0:ℝ))) + d • ((0:ℝ), ((0:ℝ), (1:ℝ))) := by
    ext <;> simp
  rw [h, map_add, map_add, map_smul, map_smul, map_smul]
  simp [Axi.dS, Axi.dQ, Axi.dEta, smul_eq_mul]

/-- The directional derivative of the lift along `v`, in the chart coefficients. -/
private theorem dy_chain (c ε : ℝ) (hε : 0 < ε) (Ψ : UnforcedLeray.B0226.ProfileTest c)
    (τ : ℝ) (y v : Space) (hy : 0 < hRad y) :
    fderiv ℝ (fun x : ℝ × Space => ((liftScalar c ε Ψ x : ℝ) : ℂ)) (τ, y) (0, v) =
      ((dSv ε y v * Axi.dS Ψ.1 (Gpt ε (τ, y)) + dQv ε y v * Axi.dQ Ψ.1 (Gpt ε (τ, y)) +
        dEv ε y v * Axi.dEta Ψ.1 (Gpt ε (τ, y)) : ℝ) : ℂ) := by
  have hψ : (fun x : ℝ × Space => ((liftScalar c ε Ψ x : ℝ) : ℂ)) =
      fun x => ((Ψ.1 (Gpt ε x) : ℝ) : ℂ) := funext fun x => by rw [liftScalar_eq]
  rw [hψ]
  have hΨc : ContDiffAt ℝ ∞ Ψ.1 (Gpt ε (τ, y)) := Ψ.2.smooth.contDiffAt
  have hCc : ContDiffAt ℝ ∞ (fun x : ℝ × Space => ((Ψ.1 (Gpt ε x) : ℝ) : ℂ)) (τ, y) :=
    ContDiffAt.comp (τ, y) Complex.ofRealCLM.contDiff.contDiffAt
      (ContDiffAt.comp (τ, y) hΨc (contDiffAt_Gpt hε (τ, y) hy))
  have hCd : DifferentiableAt ℝ (fun x : ℝ × Space => ((Ψ.1 (Gpt ε x) : ℝ) : ℂ)) (τ, y) :=
    hCc.differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ.1 (Gpt ε (τ, y)) :=
    (Ψ.2.smooth.differentiable (by simp)).differentiableAt
  have hpath : HasDerivAt (fun t : ℝ => ((τ, y + t • v) : ℝ × Space)) ((0:ℝ), v) 0 := by
    have hv : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    exact (hasDerivAt_const (0:ℝ) τ).prodMk hv
  have hc2 := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hCd.hasFDerivAt hpath (by simp)
  have hline := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hΨd.hasFDerivAt
    (line_hasDerivAt hε τ y v hy) (by simp)
  rw [fderiv_decomp] at hline
  have hline2 : HasDerivAt ((fun x : ℝ × Space => ((Ψ.1 (Gpt ε x) : ℝ) : ℂ)) ∘
      fun t : ℝ => ((τ, y + t • v) : ℝ × Space))
      ((dSv ε y v * Axi.dS Ψ.1 (Gpt ε (τ, y)) + dQv ε y v * Axi.dQ Ψ.1 (Gpt ε (τ, y)) +
        dEv ε y v * Axi.dEta Ψ.1 (Gpt ε (τ, y)) : ℝ) : ℂ) 0 := by
    have h := hline.ofReal_comp
    exact h
  exact hc2.unique hline2

theorem gradLiftPointwise : GradLiftPointwise := by
  intro c ε hc hε Ψ f hf τ y hy i
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hε0 : ε ≠ 0 := hε.ne'
  have hfw : ∀ x : Chart, f x = !₂[UnforcedLeray.B0226.Deps ε Ψ.1 x, Axi.dEta Ψ.1 x] := by
    intro x
    ext j
    have h := congrArg (fun v : MeridC => (v j).re) (hf x)
    fin_cases j
    · simpa [merC, UnforcedLeray.Short.PartIIa.cgrad] using h
    · simpa [merC, UnforcedLeray.Short.PartIIa.cgrad] using h
  have hw : UnforcedLeray.Axi.perExt c f (UnforcedLeray.Axi.chart ε⁻¹ τ y) =
      !₂[UnforcedLeray.B0226.Deps ε Ψ.1 (Gpt ε (τ, y)), Axi.dEta Ψ.1 (Gpt ε (τ, y))] := by
    rw [chart_eq_Gpt hε τ y hy]
    unfold UnforcedLeray.Axi.perExt
    rw [hfw, cellRep_per c (UnforcedLeray.B0226.Deps ε Ψ.1) (fun p => Deps_qPer Ψ.2.periodic p),
      cellRep_per c (Axi.dEta Ψ.1) (fun p => dEta_qPer Ψ.2.periodic p)]
  have hvel : velPhys ε⁻¹ c f (τ, y) i = ((√(ε⁻¹ ^ 2 / hRad y ^ 2) *
      (UnforcedLeray.B0226.Deps ε Ψ.1 (Gpt ε (τ, y)) * Axi.eR y i +
        Axi.dEta Ψ.1 (Gpt ε (τ, y)) * Axi.e3 i) : ℝ) : ℂ) := by
    show B0412.realC (UnforcedLeray.Axi.Nv ε⁻¹ (UnforcedLeray.Axi.perExt c f) τ y) i = _
    rw [B0412.realC_apply]
    congr 1
    unfold UnforcedLeray.Axi.Nv
    rw [hw]
    simp only [frameL_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    rfl
  have hϱ : UnforcedLeray.Axi.ϱ y = hRad y := rfl
  have hsq : √(ε⁻¹ ^ 2 / hRad y ^ 2) = ε⁻¹ / hRad y := by
    rw [← div_pow]
    exact Real.sqrt_sq (div_nonneg hR.le hy.le)
  have hG1 : (Gpt ε (τ, y)).1 = ε⁻¹ ^ 2 / hRad y ^ 2 := rfl
  have hG2 : (Gpt ε (τ, y)).2.2 = ε⁻¹ * y 2 / hRad y := rfl
  show _ = fderiv ℝ (fun x : ℝ × Space => ((liftScalar c ε Ψ x : ℝ) : ℂ)) (τ, y)
    (0, coordinateVector i)
  rw [dy_chain c ε hε Ψ τ y (coordinateVector i) hy, hvel, hsq]
  congr 1
  unfold UnforcedLeray.B0226.Deps UnforcedLeray.B0226.Kop
  rw [hG1, hG2]
  fin_cases i <;> simp [dSv, dQv, dEv, coordinateVector_apply, Axi.e3, hϱ] <;> field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.NearInst
