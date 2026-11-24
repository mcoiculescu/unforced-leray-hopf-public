import UnforcedLeray.Units.B0226.Chain

/-!
# B0226, part 5: the pointwise identity `div U = (εr²)⁻¹ (D_ε b_r + ∂_η b_z)`

Blueprint unit B0226, `paper/main.tex` lines 3394–3402, proof outline:
`div U = (1/r) ∂_r b_r + ∂_z(b_z/r)` for `U = a(b_r e_r + b_z e_z)`, with
`∂_r = (εr)⁻¹(∂_q − εK)` and `∂_z = (εr)⁻¹ ∂_η` on profiles, so that
`div U = (εr²)⁻¹ (D_ε b_r + ∂_η b_z)`, `r⁻² = s`.

`divergence_fieldU`: for a profile `b` differentiable at `chart(x,τ)` and `x` off the axis,
the Cartesian divergence (`Axi.divergence`, the convention of `Statement.spatialDivergence`) of
`x ↦ U(x,τ)` is `ε⁻¹ s (D_ε b_r + ∂_η b_z)` at `(s,q,η) = chart(x,τ)`. Hence a classical lift is
divergence free off the axis exactly where `D_ε b_r + ∂_η b_z = 0` (`divergence_fieldU_eq_zero_iff`).
The proof writes `U(·,τ)` as the meridional lift `Axi.liftMer` of
`B(ρ,z) = ρ⁻¹ b(ρ⁻², ε⁻¹ log ρ + τ/(2ε), z/(ερ))` and uses `Axi.divergence_liftMer`

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-- The chart as a function of the meridional coordinates `(ρ, z)` at phase time `τ`. -/
def chartMer (ε τ : ℝ) (m : ℝ × ℝ) : Profile :=
  ((m.1 ^ 2)⁻¹, ε⁻¹ * Real.log m.1 + τ * (2 * ε)⁻¹, m.2 * (ε * m.1)⁻¹)

/-- The meridional profile `B(ρ,z) = ρ⁻¹ b(chart)` of the lift at phase time `τ`. -/
def merProfile (ε τ : ℝ) (b : Profile → Merid) (m : ℝ × ℝ) : Merid :=
  m.1⁻¹ • b (chartMer ε τ m)

theorem chart_eq_chartMer (ε : ℝ) (x : Space) (τ : ℝ) :
    chart ε (x, τ) = chartMer ε τ (Axi.mer x) := by
  rw [chart_eq_chartM]
  rfl

theorem fieldU_eq_liftMer (ε τ : ℝ) (b : Profile → Merid) (x : Space) :
    fieldU ε b (x, τ) = Axi.liftMer (merProfile ε τ b) x := by
  simp only [fieldU, Axi.liftMer, merProfile, ← chart_eq_chartMer]
  ext i
  fin_cases i <;>
    simp [frame_apply, unitR, unitZ, liftA, Axi.mer, radius_eq_ϱ, div_eq_mul_inv] <;> ring

/-- `(Db(p) v)ᵢ = D(bᵢ)(p) v`. -/
theorem fderiv_component {b : Profile → Merid} {p : Profile} (hb : DifferentiableAt ℝ b p)
    (i : Fin 2) (v : Profile) : (fderiv ℝ b p v) i = fderiv ℝ (fun p => b p i) p v := by
  have h : HasFDerivAt (fun p => b p i)
      ((EuclideanSpace.proj i : Merid →L[ℝ] ℝ).comp (fderiv ℝ b p)) p :=
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).hasFDerivAt.comp p hb.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem fderiv_apply_component {b : Profile → Merid} {p : Profile} (hb : DifferentiableAt ℝ b p)
    (i : Fin 2) (a b' c' : ℝ) :
    (fderiv ℝ b p (a, b', c')) i = a * Axi.dS (fun p => b p i) p +
      b' * Axi.dQ (fun p => b p i) p + c' * Axi.dEta (fun p => b p i) p := by
  rw [fderiv_component hb, Axi.clm_triple]
  simp only [Axi.dS, Axi.dQ, Axi.dEta, smul_eq_mul]

/-- **`div U = (εr²)⁻¹ (D_ε b_r + ∂_η b_z)`** (proof outline of B0226, tex lines 3394–3402):
off the axis, for a profile `b` differentiable at `chart(x,τ)`. Here `ε⁻¹ s = (εr²)⁻¹`. -/
theorem divergence_fieldU {ε : ℝ} (hε : ε ≠ 0) {b : Profile → Merid} {x : Space} (τ : ℝ)
    (hr : radius x ≠ 0) (hb : DifferentiableAt ℝ b (chart ε (x, τ))) :
    Axi.divergence (fun x' => fieldU ε b (x', τ)) x =
      ε⁻¹ * ageS x * (Deps ε (fun p => b p 0) (chart ε (x, τ)) +
        Axi.dEta (fun p => b p 1) (chart ε (x, τ))) := by
  have hx : x ∉ Axi.axis := notMem_axis hr
  set m : ℝ × ℝ := Axi.mer x with hm
  have hm1 : m.1 = radius x := rfl
  have hρ : m.1 ≠ 0 := hr
  have hc : chart ε (x, τ) = chartMer ε τ m := chart_eq_chartMer ε x τ
  rw [hc] at hb ⊢
  -- derivative of the meridional chart
  have hs : HasFDerivAt (fun m : ℝ × ℝ => (m.1 ^ 2)⁻¹)
      ((-((m.1 ^ 2) ^ 2)⁻¹) • ((2 • m.1 ^ (2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ)) m :=
    (hasDerivAt_inv (pow_ne_zero 2 hρ)).comp_hasFDerivAt m (hasFDerivAt_fst.pow 2)
  have hq : HasFDerivAt (fun m : ℝ × ℝ => ε⁻¹ * Real.log m.1 + τ * (2 * ε)⁻¹)
      (ε⁻¹ • (m.1⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ)) m :=
    ((hasFDerivAt_fst.log hρ).const_mul ε⁻¹).add_const _
  have hinv : HasFDerivAt (fun m : ℝ × ℝ => (ε * m.1)⁻¹)
      ((-((ε * m.1) ^ 2)⁻¹) • (ε • ContinuousLinearMap.fst ℝ ℝ ℝ)) m :=
    (hasDerivAt_inv (mul_ne_zero hε hρ)).comp_hasFDerivAt m (hasFDerivAt_fst.const_mul ε)
  have hη := hasFDerivAt_snd.mul hinv
  have hg : HasFDerivAt (chartMer ε τ) _ m := hs.prodMk (hq.prodMk hη)
  have hbg := hb.hasFDerivAt.comp m hg
  have hinvρ : HasFDerivAt (fun m : ℝ × ℝ => m.1⁻¹)
      ((-(m.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ) m :=
    (hasDerivAt_inv hρ).comp_hasFDerivAt m hasFDerivAt_fst
  have hB : HasFDerivAt (merProfile ε τ b) _ m := hinvρ.smul hbg
  have hfun : (fun x' => fieldU ε b (x', τ)) = Axi.liftMer (merProfile ε τ b) :=
    funext fun x' => fieldU_eq_liftMer ε τ b x'
  rw [hfun, Axi.divergence_liftMer hx hB.differentiableAt]
  rw [← hm]
  simp only [Axi.dρ, Axi.dz, hB.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, nsmul_eq_mul,
    merProfile, fderiv_apply_component hb]
  simp only [Deps, Kop, chartMer, ageS, ← hm1, Nat.cast_ofNat, mul_zero, mul_one,
    zero_mul, add_zero, zero_add]
  rw [← radius_eq_ϱ, ← hm1]
  field_simp
  ring

/-- A classical lift is divergence free at an off-axis point iff `D_ε b_r + ∂_η b_z = 0` at its
chart point. -/
theorem divergence_fieldU_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) {b : Profile → Merid} {x : Space}
    (τ : ℝ) (hr : radius x ≠ 0) (hb : DifferentiableAt ℝ b (chart ε (x, τ))) :
    Axi.divergence (fun x' => fieldU ε b (x', τ)) x = 0 ↔
      Deps ε (fun p => b p 0) (chart ε (x, τ)) + Axi.dEta (fun p => b p 1) (chart ε (x, τ)) = 0 := by
  rw [divergence_fieldU hε τ hr hb]
  have hs : ageS x ≠ 0 := inv_ne_zero (pow_ne_zero 2 hr)
  constructor
  · intro h
    exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero (inv_ne_zero hε) hs)
  · intro h
    rw [h, mul_zero]

end UnforcedLeray.B0226
