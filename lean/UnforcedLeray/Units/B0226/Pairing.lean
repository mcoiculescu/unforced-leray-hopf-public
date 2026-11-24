import UnforcedLeray.Units.B0226.Chain

/-!
# B0226, part 3: the pairing identity `⟪J_ε b, ∇ₓ(Φ ∘ chart)⟫ = (ε c_J)⁻¹ ⟪b, (D_εΦ, ∂_ηΦ)⟫_H`

Blueprint unit B0226, `paper/main.tex` lines 3394–3402, proof outline ("for the distributional
version, pair with axisymmetric test functions and change variables").

* `physTestOfProfile`: a profile test `Φ` gives the physical test `Φ ∘ chart` of `ℝ³ × period`.
* `physGrad_physTestOfProfile`: `∇ₓ(Φ ∘ chart) = (ε c_J)⁻¹ J_ε (D_εΦ, ∂_ηΦ)` in `L²(dx dτ)`,
  with `c_J = jConst ε = (√(2π) ε)⁻¹` the constant of `J_ε` (B0220).
* `inner_J_physGrad`: since `J_ε` is an isometry, the physical divergence pairing of the lift
  `J_ε b` against `Φ ∘ chart` is `(ε c_J)⁻¹` times the `H`-pairing of `b` with
  `(D_εΦ, ∂_ηΦ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

theorem isPhysTest_comp_chart {ε c : ℝ} (hε : ε ≠ 0) {Φ : Profile → ℝ}
    (hΦ : IsProfileTest c Φ) : IsPhysTest (2 * ε * c) (fun y => Φ (chart ε y)) where
  smooth := contDiff_comp_chart hε hΦ
  periodic x τ := by
    rw [chart_add_period hε c x τ]
    exact hΦ.periodic _
  bounded := bounded_comp_chart hε hΦ

/-- The physical test `Φ ∘ chart` of a profile test `Φ`. -/
def physTestOfProfile {ε c : ℝ} (hε : ε ≠ 0) (Φ : ProfileTest c) : PhysTest ε c :=
  ⟨fun y => Φ.1 (chart ε y), isPhysTest_comp_chart hε Φ.2⟩

theorem fderiv_qPeriodic {c : ℝ} {Φ : Profile → ℝ} (h : QPeriodic c Φ) (p : Profile) :
    fderiv ℝ Φ (p.1, p.2.1 + c, p.2.2) = fderiv ℝ Φ p := by
  have ha : ((p.1, p.2.1 + c, p.2.2) : Profile) = p + ((0 : ℝ), c, (0 : ℝ)) := by
    obtain ⟨s, q, η⟩ := p
    simp [add_comm]
  have hf : (fun x : Profile => Φ (x + ((0 : ℝ), c, (0 : ℝ)))) = Φ := by
    funext x
    obtain ⟨s, q, η⟩ := x
    have := h (s, q, η)
    simpa using this
  rw [ha, ← fderiv_comp_add_right, hf]

theorem qPeriodic_profileGrad {c : ℝ} (ε : ℝ) {Φ : Profile → ℝ} (h : QPeriodic c Φ) :
    QPeriodic c (profileGrad ε Φ) := by
  intro p
  simp only [profileGrad, Deps, Kop, Axi.dS, Axi.dQ, Axi.dEta, fderiv_qPeriodic h p]

/-- `∇ₓ(Φ ∘ chart) = (ε c_J)⁻¹ J_ε (D_εΦ, ∂_ηΦ)` in `L²(dx dτ)` over one period. -/
theorem physGrad_physTestOfProfile {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (Φ : ProfileTest c) :
    physGrad ε c (physTestOfProfile hε.ne' Φ) =
      (ε * jConst ε)⁻¹ • J hε hc (profileGradH ε c Φ) := by
  apply Lp.ext
  have h1 := coeFn_physGrad ε c (physTestOfProfile hε.ne' Φ)
  have h2 := Lp.coeFn_smul ((ε * jConst ε)⁻¹) (J hε hc (profileGradH ε c Φ))
  have h3 := coeFn_J hε hc (profileGradH ε c Φ)
  have h4 := ae_transfer hε hc (coeFn_profileGradH ε c Φ)
  filter_upwards [h1, h2, h3, h4, ae_physMeasure ε c] with y e1 e2 e3 e4 hy
  have hr : radius y.1 ≠ 0 := hy.1
  have hl : liftA y.1 ≠ 0 := inv_ne_zero hr
  rw [e1, e2, Pi.smul_apply, e3]
  have hper : periodize c (⇑(profileGradH ε c Φ)) (chart ε y) =
      profileGrad ε Φ.1 (chart ε y) := by
    change (profileGradH ε c Φ : Profile → Merid) (cellChart ε c y) = _
    rw [e4 hl]
    exact periodic_reduceIoc_eq _ (qPeriodic_profileGrad ε Φ.2.periodic) _ _ _
  have hd : DifferentiableAt ℝ Φ.1 (chart ε y) :=
    (Φ.2.smooth.differentiable (by simp)).differentiableAt
  simp only [fieldU, hper]
  rw [show (physTestOfProfile hε.ne' Φ).1 = fun y => Φ.1 (chart ε y) from rfl,
    gradX_comp_chart hε.ne' hr hd, smul_smul, smul_smul]
  congr 1
  have h2π : √(2 * π) ≠ 0 := by positivity
  unfold jConst
  field_simp

/-- **Change of variables of the divergence pairing**: for `b ∈ H` and a profile test `Φ`,
`⟪J_ε b, ∇ₓ(Φ ∘ chart)⟫_{L²(dx dτ)} = (ε c_J)⁻¹ ⟪b, (D_εΦ, ∂_ηΦ)⟫_H`. -/
theorem inner_J_physGrad {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid)
    (Φ : ProfileTest c) :
    ⟪J hε hc b, physGrad ε c (physTestOfProfile hε.ne' Φ)⟫_ℝ =
      (ε * jConst ε)⁻¹ * ⟪b, profileGradH ε c Φ⟫_ℝ := by
  rw [physGrad_physTestOfProfile hε hc, real_inner_smul_right, LinearIsometry.inner_map_map]

theorem jConst_pos {ε : ℝ} (hε : 0 < ε) : 0 < jConst ε := by
  unfold jConst
  positivity

theorem jFactor_ne_zero {ε : ℝ} (hε : 0 < ε) : (ε * jConst ε)⁻¹ ≠ 0 :=
  inv_ne_zero (mul_pos hε (jConst_pos hε)).ne'

/-- The lift of a profile gradient is a physical gradient: it lies in the orthogonal complement
of the divergence-free fields. -/
theorem J_profileGradH_mem_orthogonal {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (Φ : ProfileTest c) :
    J hε hc (profileGradH ε c Φ) ∈ (physSolenoidal ε c)ᗮ := by
  have h := physGrad_mem_orthogonal (physTestOfProfile hε.ne' Φ)
  rw [physGrad_physTestOfProfile hε hc] at h
  have h' := Submodule.smul_mem _ (ε * jConst ε) h
  rwa [smul_smul, mul_inv_cancel₀ (mul_pos hε (jConst_pos hε)).ne', one_smul] at h'

end UnforcedLeray.B0226
