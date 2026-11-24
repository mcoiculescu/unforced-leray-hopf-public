import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.ZeroSharp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.AMuNorm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1.A0Uniform
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Compose

/-!
# Pointwise facts at one `(n, z)` for clauses 3-4 of `FlatLimit` (source 4709-4730, 4812-4815)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `B_{μ,ν}[a_μ] = B_μ` on `s > 0` (source 4697-4701, 4757-4758). -/
theorem bmat_aMuFun {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) (ν μ : ℝ) (hμ : 0 < μ) {t : ℝ}
    (ht : 0 < t) :
    Bmat ν μ χ (aMuFun μ) t = Bmu χ (deriv χ) ν μ t := by
  have hμ2 : μ + 5 / 2 ≠ 0 := by linarith
  have hd : ∀ x, HasDerivAt χ (deriv χ x) x := fun x =>
    ((hχ.smooth.differentiable (by simp)) x).hasDerivAt
  have hev : Ay ν χ (aMuFun μ) =ᶠ[𝓝 t]
      fun s => (χ (ν * s) * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2))) • (fun i j => Dzero i j) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs : 0 < s := hs
    simp only [Ay]
    rw [aMuFun_pos_eq μ s hs, smul_smul]
  have h1 : HasDerivAt (fun s : ℝ => s ^ (5 / 2 : ℝ)) ((5 / 2 : ℝ) * t ^ ((5 / 2 : ℝ) - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt (fun s : ℝ => χ (ν * s)) (deriv χ (ν * t) * ν) t := by
    have := (hd (ν * t)).comp t ((hasDerivAt_id t).const_mul ν)
    exact this.congr_deriv (by simp)
  have h3 : HasDerivAt (fun s : ℝ => χ (ν * s) * (s ^ (5 / 2 : ℝ) / (μ + 5 / 2)))
      (deriv χ (ν * t) * ν * (t ^ (5 / 2 : ℝ) / (μ + 5 / 2)) +
        χ (ν * t) * ((5 / 2 : ℝ) * t ^ ((5 / 2 : ℝ) - 1) / (μ + 5 / 2))) t :=
    h2.mul (h1.div_const _)
  have h4 := h3.smul_const (fun i j => Dzero i j)
  have hder : deriv (Ay ν χ (aMuFun μ)) t =
      (deriv χ (ν * t) * ν * (t ^ (5 / 2 : ℝ) / (μ + 5 / 2)) +
        χ (ν * t) * ((5 / 2 : ℝ) * t ^ ((5 / 2 : ℝ) - 1) / (μ + 5 / 2))) • (fun i j => Dzero i j) := by
    rw [hev.deriv_eq]; exact h4.deriv
  have hp : t * t ^ ((5 / 2 : ℝ) - 1) = t ^ (5 / 2 : ℝ) := by
    conv_rhs => rw [show (5 / 2 : ℝ) = 1 + ((5 / 2 : ℝ) - 1) by norm_num, Real.rpow_add ht,
      Real.rpow_one]
  have hq : t ^ (5 / 2 : ℝ) = t ^ (3 / 2 : ℝ) * t := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add ht, Real.rpow_one]
  have hq2 : t ^ ((5 / 2 : ℝ) - 1) = t ^ (3 / 2 : ℝ) := by norm_num
  have hAy : Ay ν χ (aMuFun μ) t = (χ (ν * t) * (t ^ (5 / 2 : ℝ) / (μ + 5 / 2))) •
      (fun i j => Dzero i j) := hev.eq_of_nhds
  unfold Bmat
  rw [hder, hAy]
  funext i j
  simp only [Bmu, rMu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rw [hq2, hq]
  field_simp
  ring

/-- `Λ(a_μ) - unitResp = -(3π/16) ε³ν^{5+2μ} Re[iN_νJ(μ)(a₀(B_μ) + (21/4)L(μ))]`. -/
theorem lamFun_sub_unitResp (lam κ ell : ℂ) (J : ℂ → ℂ) (ε ν μ : ℝ) (a : ℂ) :
    -(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ) *
        (Complex.I * Nnu lam κ ν * J (μ : ℂ) * a).re -
      unitResp lam κ (mellinC lam ell J) (ε ^ 3) ν μ =
    -(3 * Real.pi / 16) * ε ^ 3 * ν ^ (5 + 2 * μ) *
        (Complex.I * Nnu lam κ ν * J (μ : ℂ) * (a + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ))).re := by
  unfold unitResp mellinC
  have key : ((-(3 * Real.pi / 16) : ℝ) : ℂ) * (Complex.I * Nnu lam κ ν * J (μ : ℂ) * a) -
      2 * (((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell (μ : ℂ) * J (μ : ℂ) *
        Nnu lam κ ν) =
      ((-(3 * Real.pi / 16) : ℝ) : ℂ) *
        (Complex.I * Nnu lam κ ν * J (μ : ℂ) * (a + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ))) := by
    push_cast
    ring
  have hre := congrArg Complex.re key
  rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
  have h2 : (2 * (((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell (μ : ℂ) *
      J (μ : ℂ) * Nnu lam κ ν)).re =
      2 * (((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell (μ : ℂ) *
      J (μ : ℂ) * Nnu lam κ ν).re := by
    have := Complex.re_ofReal_mul 2 (((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I *
      LCoeff lam ell (μ : ℂ) * J (μ : ℂ) * Nnu lam κ ν)
    simpa using this
  rw [h2] at hre
  have e : ε ^ 3 * ν ^ (5 + 2 * μ) * (-(3 * Real.pi / 16) *
      (Complex.I * Nnu lam κ ν * J (μ : ℂ) * a).re -
      2 * (((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell (μ : ℂ) *
      J (μ : ℂ) * Nnu lam κ ν).re) = ε ^ 3 * ν ^ (5 + 2 * μ) * (-(3 * Real.pi / 16) *
        (Complex.I * Nnu lam κ ν * J (μ : ℂ) * (a + (21 / 4 : ℂ) * LCoeff lam ell (μ : ℂ))).re) :=
    by rw [hre]
  have e2 : ((((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell (μ : ℂ) * J (μ : ℂ)) *
      Nnu lam κ ν) = (((63 * Real.pi / 128 : ℝ) : ℂ) * Complex.I * LCoeff lam ell (μ : ℂ) *
      J (μ : ℂ) * Nnu lam κ ν) := rfl
  rw [e2]
  linear_combination e

/-- The pinned `Λ_{μ,ν}` of the return operators is `LamFun` (source 4812-4815). -/
theorem lam_apply_eq {Pl : UnforcedLeray.Blueprint.Planar.PlanarData} {K : ReturnConsts}
    {L : ReturnLevel} {μ : ℝ} (hn : NearAt Pl K L μ) (hp : RegimePins Pl K L μ)
    (A : AffSp K.as) :
    (concreteOps Pl K L μ).Lam A =
      LamFun Pl.eigenvalue Pl.kappa Pl.strainCoupling (planarJ Pl) L.ε L.ν μ K.χf
        (affIota K.as A) := by
  rw [concreteOps_Lam Pl K L μ hn]
  exact Classical.epsilon_spec hp.lam A

/-- The sharp pointwise bound of `Λ` on `𝒜` (source 4863-4864), for `a_s < Re λ`. -/
theorem lam_apply_le {Pl : UnforcedLeray.Blueprint.Planar.PlanarData} {K : ReturnConsts}
    {L : ReturnLevel} {μ : ℝ} (hn : NearAt Pl K L μ) (hp : RegimePins Pl K L μ)
    {C0 : ℝ}
    (hsh : ∀ (as ν μ : ℝ) (lam ell : ℂ) (A : ℝ → Mat3), 0 < ν → 0 ≤ μ →
      IsAffElem as A → as < lam.re →
      ‖aZero lam ell (μ : ℂ) (Bmat ν μ K.χf A)‖ ≤
        ‖ell‖ * ((1 + μ) * C0 * gamFac μ (lam.re - as)) * affNorm as A)
    (hlt : K.as < Pl.eigenvalue.re) (hμ : 0 ≤ μ) (A : AffSp K.as) :
    |(concreteOps Pl K L μ).Lam A| ≤
      (3 * Real.pi / 16) * (L.ε ^ 3 * L.ν ^ (5 + 2 * μ) * ‖Nnu Pl.eigenvalue Pl.kappa L.ν‖) *
        ‖Pl.mellinJ μ‖ *
        (‖Pl.strainCoupling‖ * ((1 + μ) * C0 * gamFac μ (Pl.eigenvalue.re - K.as))) * ‖A‖ := by
  rw [lam_apply_eq hn hp A]
  unfold LamFun
  have hν := L.ν_pos
  have hε := L.ε_pos
  have ha := hsh K.as L.ν μ Pl.eigenvalue Pl.strainCoupling (affIota K.as A) hν hμ
    (affIota_mem K.as A) hlt
  rw [affNorm_affIota] at ha
  have hk : 0 ≤ (3 * Real.pi / 16) * L.ε ^ 3 * L.ν ^ (5 + 2 * μ) := by
    have := Real.rpow_nonneg hν.le (5 + 2 * μ)
    positivity
  rw [abs_mul, show -(3 * Real.pi / 16) * L.ε ^ 3 * L.ν ^ (5 + 2 * μ) =
    -((3 * Real.pi / 16) * L.ε ^ 3 * L.ν ^ (5 + 2 * μ)) by ring, abs_neg, abs_of_nonneg hk]
  have hre := Complex.abs_re_le_norm (Complex.I * Nnu Pl.eigenvalue Pl.kappa L.ν *
    Pl.mellinJ μ * aZero Pl.eigenvalue Pl.strainCoupling (μ : ℂ)
      (Bmat L.ν μ K.χf (affIota K.as A)))
  have hnorm : ‖Complex.I * Nnu Pl.eigenvalue Pl.kappa L.ν * Pl.mellinJ μ *
      aZero Pl.eigenvalue Pl.strainCoupling (μ : ℂ) (Bmat L.ν μ K.χf (affIota K.as A))‖ ≤
      ‖Nnu Pl.eigenvalue Pl.kappa L.ν‖ * ‖Pl.mellinJ μ‖ *
        (‖Pl.strainCoupling‖ * ((1 + μ) * C0 * gamFac μ (Pl.eigenvalue.re - K.as)) * ‖A‖) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left ha (by positivity)
  have hfin := mul_le_mul_of_nonneg_left (hre.trans hnorm) hk
  refine hfin.trans (le_of_eq ?_)
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
