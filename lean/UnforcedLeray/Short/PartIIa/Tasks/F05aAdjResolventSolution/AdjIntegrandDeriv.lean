import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussEquation

/-!
# Part II-a, task `PartII-a:F05/1/10`: the `t`-derivative of the adjoint integrand

Target: `AdjIntegrandDeriv` (`Short/PartII-a/Sub/F05_1.lean`), proved as
`adjIntegrandDeriv_proof`.

Source of record: `the November 2 reference manuscript`, lines 1403-1413.

Proof outline. Write `G = heatGauss Φ₀ w` with `w = adjW ν t`, `A(q) = (q.1 + t, e • q.2)` with
`e = exp(-t/2)`, and `c = exp(-((μ+1) t))`, so `adjIntegrand ν μ Φ₀ t = c • G ∘ A`.

* Spatial operators of `c • G ∘ A`: `∂_τ = c • ∂_τ G`, `radialT = c • radialT G`,
  `Δ = c e² • ΔG` (the affine lemmas `*_aff`, and `*_smul`, `*_F`).
* `J(w, q) = heatGauss Φ₀ w q` is jointly `C^∞`. Its derivative in `w` is `(2w) • lapT G`
  (`heatGaussEquation_proof`), and in `q` it is the derivative of `G`
  (`fderiv_heat_joint`). The chain rule along `s ↦ (adjW ν s, (p.1 + s, e(s) • p.2))` with
  `d/ds adjW ν s = ν e^{-t}/(2w)` gives the claim (`final_vec` closes the algebra).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

namespace AdjIntegrandDerivAux

/-! ### The affine map `x ↦ (x.1 + t, e • x.2)` -/

theorem hasFDerivAt_aff (t e : ℝ) (q : ℝ × Space) :
    HasFDerivAt (fun x : ℝ × Space => (x.1 + t, e • x.2))
      ((ContinuousLinearMap.fst ℝ ℝ Space).prod (e • ContinuousLinearMap.snd ℝ ℝ Space)) q := by
  have h1 : HasFDerivAt (fun x : ℝ × Space => x.1 + t) (ContinuousLinearMap.fst ℝ ℝ Space) q :=
    hasFDerivAt_fst.add_const t
  have h2 : HasFDerivAt (fun x : ℝ × Space => e • x.2)
      (e • ContinuousLinearMap.snd ℝ ℝ Space) q :=
    hasFDerivAt_snd.const_smul e
  exact h1.prodMk h2

theorem diffAt_aff {K : ℝ × Space → CVec3} (hK : Differentiable ℝ K) (t e : ℝ) (q : ℝ × Space) :
    DifferentiableAt ℝ (fun x : ℝ × Space => K (x.1 + t, e • x.2)) q :=
  (hK _).comp q (hasFDerivAt_aff t e q).differentiableAt

theorem diff_aff {K : ℝ × Space → CVec3} (hK : Differentiable ℝ K) (t e : ℝ) :
    Differentiable ℝ (fun x : ℝ × Space => K (x.1 + t, e • x.2)) :=
  fun q => diffAt_aff hK t e q

theorem contDiff_aff {K : ℝ × Space → CVec3} (hK : ContDiff ℝ ∞ K) (t e : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => K (x.1 + t, e • x.2)) :=
  hK.comp ((contDiff_fst.add contDiff_const).prodMk (contDiff_snd.const_smul e))

theorem fderiv_aff {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (t e : ℝ)
    (q v : ℝ × Space) :
    fderiv ℝ (fun x : ℝ × Space => G (x.1 + t, e • x.2)) q v
      = fderiv ℝ G (q.1 + t, e • q.2) (v.1, e • v.2) := by
  have hcomp : HasFDerivAt (fun x : ℝ × Space => G (x.1 + t, e • x.2))
      ((fderiv ℝ G (q.1 + t, e • q.2)).comp
        ((ContinuousLinearMap.fst ℝ ℝ Space).prod (e • ContinuousLinearMap.snd ℝ ℝ Space))) q :=
    (hG (q.1 + t, e • q.2)).hasFDerivAt.comp q (hasFDerivAt_aff t e q)
  rw [hcomp.fderiv]
  rfl

theorem dτ_aff {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (t e : ℝ) (q : ℝ × Space) :
    dτ (fun x : ℝ × Space => G (x.1 + t, e • x.2)) q = dτ G (q.1 + t, e • q.2) := by
  unfold dτ
  rw [fderiv_aff hG t e q (1, 0)]
  simp

theorem dy_aff {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (t e : ℝ) (j : Fin 3)
    (q : ℝ × Space) :
    dy j (fun x : ℝ × Space => G (x.1 + t, e • x.2)) q = e • dy j G (q.1 + t, e • q.2) := by
  have h : ((0 : ℝ), e • coordinateVector j) = e • ((0 : ℝ), coordinateVector j) := by
    simp
  unfold dy
  rw [fderiv_aff hG t e q (0, coordinateVector j)]
  show fderiv ℝ G (q.1 + t, e • q.2) (0, e • coordinateVector j) = _
  rw [h, map_smul]

theorem radialT_aff {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (t e : ℝ)
    (q : ℝ × Space) :
    radialT (fun x : ℝ × Space => G (x.1 + t, e • x.2)) q = radialT G (q.1 + t, e • q.2) := by
  unfold radialT
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_aff hG t e j q]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [smul_smul, mul_comm]

/-! ### Differentiability of the phase-space derivatives of a smooth function -/

theorem dy_differentiable {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) (j : Fin 3) :
    Differentiable ℝ (dy j G) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (m := 1) (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ G) := h1.differentiable (by simp)
  exact h2.clm_apply (differentiable_const _)

/-! ### Scalar multiples (`c • ·` with `c` complex, or a real scalar) -/

theorem dτ_smul {R : Type} [Semiring R] [Module R CVec3] [SMulCommClass ℝ R CVec3]
    [ContinuousConstSMul R CVec3] (r : R) (Φ : ℝ × Space → CVec3) (q : ℝ × Space)
    (hΦ : DifferentiableAt ℝ Φ q) :
    dτ (fun x => r • Φ x) q = r • dτ Φ q := by
  simp only [dτ, fderiv_fun_const_smul hΦ r, ContinuousLinearMap.smul_apply]

theorem dy_smul' {R : Type} [Semiring R] [Module R CVec3] [SMulCommClass ℝ R CVec3]
    [ContinuousConstSMul R CVec3] (j : Fin 3) (r : R) (Φ : ℝ × Space → CVec3) (q : ℝ × Space)
    (hΦ : DifferentiableAt ℝ Φ q) :
    dy j (fun x => r • Φ x) q = r • dy j Φ q := by
  simp only [dy, fderiv_fun_const_smul hΦ r, ContinuousLinearMap.smul_apply]

theorem radialT_smul {R : Type} [Semiring R] [Module R CVec3] [SMulCommClass ℝ R CVec3]
    [ContinuousConstSMul R CVec3] (r : R) (Φ : ℝ × Space → CVec3)
    (hΦ : Differentiable ℝ Φ) (q : ℝ × Space) :
    radialT (fun x => r • Φ x) q = r • radialT Φ q := by
  unfold radialT
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_smul' j r Φ q (hΦ q), smul_comm]

theorem lapT_smul {R : Type} [Semiring R] [Module R CVec3] [SMulCommClass ℝ R CVec3]
    [ContinuousConstSMul R CVec3] (r : R) (Φ : ℝ × Space → CVec3) (hΦ : ContDiff ℝ ∞ Φ)
    (q : ℝ × Space) :
    lapT (fun x => r • Φ x) q = r • lapT Φ q := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hK : ∀ j, Differentiable ℝ (dy j Φ) := fun j => dy_differentiable hΦ j
  have hf : ∀ j, dy j (fun x => r • Φ x) = fun y => r • dy j Φ y :=
    fun j => funext fun y => dy_smul' j r Φ y (hd y)
  unfold lapT
  simp only [hf, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => dy_smul' j r (dy j Φ) q (hK j q)

theorem lapT_aff {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) (t e : ℝ) (q : ℝ × Space) :
    lapT (fun x : ℝ × Space => G (x.1 + t, e • x.2)) q = e • e • lapT G (q.1 + t, e • q.2) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hterm : ∀ j : Fin 3,
      dy j (dy j (fun x : ℝ × Space => G (x.1 + t, e • x.2))) q
        = e • e • dy j (dy j G) (q.1 + t, e • q.2) := by
    intro j
    have hf : dy j (fun x : ℝ × Space => G (x.1 + t, e • x.2))
        = fun y => e • dy j G (y.1 + t, e • y.2) :=
      funext fun y => dy_aff hGd t e j y
    rw [hf, dy_smul' j e _ q (diffAt_aff (dy_differentiable hG j) t e q),
      dy_aff (dy_differentiable hG j) t e j q]
  unfold lapT
  simp only [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => hterm j

/-! ### The integrand `c • G ∘ A` -/

theorem dτ_F {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℂ) (t e : ℝ)
    (q : ℝ × Space) :
    dτ (fun x : ℝ × Space => c • G (x.1 + t, e • x.2)) q = c • dτ G (q.1 + t, e • q.2) := by
  rw [dτ_smul c (fun x : ℝ × Space => G (x.1 + t, e • x.2)) q (diffAt_aff hG t e q),
    dτ_aff hG t e q]

theorem radialT_F {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (c : ℂ) (t e : ℝ)
    (q : ℝ × Space) :
    radialT (fun x : ℝ × Space => c • G (x.1 + t, e • x.2)) q
      = c • radialT G (q.1 + t, e • q.2) := by
  rw [radialT_smul c (fun x : ℝ × Space => G (x.1 + t, e • x.2)) (diff_aff hG t e) q,
    radialT_aff hG t e q]

theorem lapT_F {G : ℝ × Space → CVec3} (hG : ContDiff ℝ ∞ G) (c : ℂ) (t e : ℝ)
    (q : ℝ × Space) :
    lapT (fun x : ℝ × Space => c • G (x.1 + t, e • x.2)) q
      = c • (e • e • lapT G (q.1 + t, e • q.2)) := by
  rw [lapT_smul c (fun x : ℝ × Space => G (x.1 + t, e • x.2)) (contDiff_aff hG t e) q,
    lapT_aff hG t e q]

/-! ### The joint heat flow `J(w, q) = heatGauss Φ₀ w q` -/

theorem fderiv_zero_vec {G : ℝ × Space → CVec3} (x : ℝ × Space) (v : Space) :
    fderiv ℝ G x (0, v) = ∑ j : Fin 3, v j • dy j G x := by
  have hv : v = ∑ j : Fin 3, v j • coordinateVector j := by
    ext k
    simp [coordinateVector, Pi.single_apply, mul_ite]
  have h0 : ((0 : ℝ), v) = ∑ j : Fin 3, v j • ((0 : ℝ), coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      exact hv
  rw [h0, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

theorem fderiv_one_vec {G : ℝ × Space → CVec3} (hG : Differentiable ℝ G) (x : ℝ × Space)
    (u : Space) :
    fderiv ℝ G x (1, u) = dτ G x + ∑ j : Fin 3, u j • dy j G x := by
  have h : ((1 : ℝ), u) = ((1 : ℝ), (0 : Space)) + ((0 : ℝ), u) := by simp
  rw [h, map_add, fderiv_zero_vec]
  rfl

theorem fderiv_heat_joint (Φ₀ : ℝ × Space → CVec3)
    (hJ : Differentiable ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2))
    (hE : ∀ w : ℝ, 0 < w → ∀ q : ℝ × Space,
      HasDerivAt (fun w' => heatGauss Φ₀ w' q) ((2 * w) • lapT (heatGauss Φ₀ w) q) w)
    {w : ℝ} (hw : 0 < w) (x : ℝ × Space) (a : ℝ) (y : ℝ × Space) :
    fderiv ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) (w, x) (a, y)
      = a • ((2 * w) • lapT (heatGauss Φ₀ w) x) + fderiv ℝ (heatGauss Φ₀ w) x y := by
  have hline : HasDerivAt (fun w' : ℝ => ((w', x) : ℝ × (ℝ × Space)))
      ((1 : ℝ), (0 : ℝ × Space)) w :=
    (hasDerivAt_id' w).prodMk (hasDerivAt_const w x)
  have h1 : HasDerivAt ((fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) ∘
      (fun w' : ℝ => ((w', x) : ℝ × (ℝ × Space))))
      (fderiv ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) (w, x) (1, 0)) w :=
    HasFDerivAt.comp_hasDerivAt w (hJ (w, x)).hasFDerivAt hline
  have hD1 : fderiv ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) (w, x) (1, 0)
      = (2 * w) • lapT (heatGauss Φ₀ w) x := h1.unique (hE w hw x)
  have hL : HasFDerivAt (fun y : ℝ × Space => ((w, y) : ℝ × (ℝ × Space)))
      ((0 : (ℝ × Space) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × Space))) x :=
    (hasFDerivAt_const w x).prodMk (hasFDerivAt_id x)
  have hH : HasFDerivAt (heatGauss Φ₀ w)
      ((fderiv ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) (w, x)).comp
        ((0 : (ℝ × Space) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × Space)))) x :=
    (hJ (w, x)).hasFDerivAt.comp x hL
  have hHy : fderiv ℝ (heatGauss Φ₀ w) x y
      = fderiv ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) (w, x) (0, y) := by
    rw [hH.fderiv]
    rfl
  have hsplit : ((a, y) : ℝ × (ℝ × Space)) = a • ((1 : ℝ), (0 : ℝ × Space)) + ((0 : ℝ), y) := by
    simp
  rw [hsplit, map_add, map_smul, hD1, ← hHy]

/-! ### Sums and the final algebra -/

theorem sum_kappa (G : ℝ × Space → CVec3) (e : ℝ) (p2 : Space) (x : ℝ × Space)
    (hx : x.2 = e • p2) :
    ∑ j : Fin 3, ((e * (-1 / 2)) • p2) j • dy j G x = (-(1 / 2 : ℝ)) • radialT G x := by
  unfold radialT
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hx]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [smul_smul]
  congr 1
  ring

theorem final_vec (c μ' : ℂ) (ν a w e : ℝ) (haw : a * (2 * w) = ν * (e * e))
    (gx dx rx lx : CVec3) :
    c • (a • ((2 * w) • lx) + (dx + (-(1 / 2 : ℝ)) • rx)) + (c * -(μ' + 1)) • gx
      = -(μ' + 1) • (c • gx) + c • dx - (1 / 2 : ℝ) • (c • rx) + ν • (c • (e • e • lx)) := by
  have h1 : a • ((2 * w) • lx) = ν • (e • e • lx) := by
    rw [smul_smul, haw]
    simp only [smul_smul]
  rw [smul_add, smul_add, h1, smul_comm c ν, mul_comm c, mul_smul,
    smul_comm c (-(1 / 2 : ℝ)), neg_smul (1 / 2 : ℝ) (c • rx)]
  abel

end AdjIntegrandDerivAux

open AdjIntegrandDerivAux in
theorem adjIntegrandDeriv_proof : UnforcedLeray.Short.PartIIa.AdjIntegrandDeriv := by
  intro P ν hP hν μ Φ₀ hΦ t ht p
  obtain ⟨hJc, hHc, -⟩ := heatGaussSmooth_proof P hP Φ₀ hΦ
  have hE := heatGaussEquation_proof P hP Φ₀ hΦ
  have hJd : Differentiable ℝ (fun q : ℝ × (ℝ × Space) => heatGauss Φ₀ q.1 q.2) :=
    hJc.differentiable (by simp)
  have hGc : ContDiff ℝ ∞ (heatGauss Φ₀ (adjW ν t)) := hHc (adjW ν t)
  have hGd : Differentiable ℝ (heatGauss Φ₀ (adjW ν t)) := hGc.differentiable (by simp)
  have hexp : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < ν * (1 - Real.exp (-t)) := mul_pos hν (by linarith)
  have hwpos : 0 < adjW ν t := Real.sqrt_pos.mpr hpos
  -- the derivative of the heat parameter `w(s) = √(ν(1 - e^{-s}))`
  have hw' : HasDerivAt (fun s : ℝ => adjW ν s) (ν * Real.exp (-t) / (2 * adjW ν t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => ν * (1 - Real.exp (-s))) (ν * Real.exp (-t)) t := by
      have h := (((hasDerivAt_id' t).neg.exp).const_sub 1).const_mul ν
      exact h.congr_deriv (by simp only [Pi.neg_apply]; try ring)
    exact h1.sqrt hpos.ne'
  -- the derivative of the spatial affine map `s ↦ (p.1 + s, e^{-s/2} p.2)`
  have hκ : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (Real.exp (-t / 2) * (-1 / 2)) t :=
    (((hasDerivAt_id' t).neg).div_const 2).exp
  have hq : HasDerivAt (fun s : ℝ => ((p.1 + s, Real.exp (-s / 2) • p.2) : ℝ × Space))
      ((1 : ℝ), (Real.exp (-t / 2) * (-1 / 2)) • p.2) t :=
    ((hasDerivAt_id' t).const_add p.1).prodMk (hκ.smul_const p.2)
  have hΓ : HasDerivAt
      (fun s : ℝ => ((adjW ν s, (p.1 + s, Real.exp (-s / 2) • p.2)) : ℝ × (ℝ × Space)))
      ((ν * Real.exp (-t) / (2 * adjW ν t)), ((1 : ℝ), (Real.exp (-t / 2) * (-1 / 2)) • p.2)) t :=
    hw'.prodMk hq
  have hJΓ := HasFDerivAt.comp_hasDerivAt t (hJd (adjW ν t, (p.1 + t, Real.exp (-t / 2) • p.2))).hasFDerivAt hΓ
  -- the derivative of the phase `c(s) = exp(-(μ+1) s)`
  have hcf : HasDerivAt (fun s : ℝ => Complex.exp (-((μ + 1) * (s : ℂ))))
      (Complex.exp (-((μ + 1) * (t : ℂ))) * (-(μ + 1))) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id' t)
    have h2 := ((h1.const_mul (μ + 1)).neg).cexp
    exact h2.congr_deriv (by simp only [Pi.neg_apply]; try ring)
  have hsm := hcf.smul hJΓ
  refine (hsm : HasDerivAt (fun s : ℝ => adjIntegrand ν μ Φ₀ s p) _ t).congr_deriv ?_
  -- algebraic identities
  have he2 : Real.exp (-t / 2) * Real.exp (-t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hwe : ν * Real.exp (-t) / (2 * adjW ν t) * (2 * adjW ν t)
      = ν * (Real.exp (-t / 2) * Real.exp (-t / 2)) := by
    rw [div_mul_cancel₀ _ (mul_pos two_pos hwpos).ne', he2]
  have hsum := sum_kappa (heatGauss Φ₀ (adjW ν t)) (Real.exp (-t / 2)) p.2
    (p.1 + t, Real.exp (-t / 2) • p.2) rfl
  have hdτ : dτ (adjIntegrand ν μ Φ₀ t) p
      = Complex.exp (-((μ + 1) * (t : ℂ))) • dτ (heatGauss Φ₀ (adjW ν t))
          (p.1 + t, Real.exp (-t / 2) • p.2) :=
    dτ_F hGd _ t _ p
  have hrad : radialT (adjIntegrand ν μ Φ₀ t) p
      = Complex.exp (-((μ + 1) * (t : ℂ))) • radialT (heatGauss Φ₀ (adjW ν t))
          (p.1 + t, Real.exp (-t / 2) • p.2) :=
    radialT_F hGd _ t _ p
  have hlap : lapT (adjIntegrand ν μ Φ₀ t) p
      = Complex.exp (-((μ + 1) * (t : ℂ))) • (Real.exp (-t / 2) • Real.exp (-t / 2) •
          lapT (heatGauss Φ₀ (adjW ν t)) (p.1 + t, Real.exp (-t / 2) • p.2)) :=
    lapT_F hGc _ t _ p
  have hval : adjIntegrand ν μ Φ₀ t p
      = Complex.exp (-((μ + 1) * (t : ℂ))) • heatGauss Φ₀ (adjW ν t)
          (p.1 + t, Real.exp (-t / 2) • p.2) := rfl
  rw [fderiv_heat_joint Φ₀ hJd hE hwpos, fderiv_one_vec hGd, hsum, hdτ, hrad, hlap, hval]
  exact final_vec _ _ _ _ _ _ hwe _ _ _ _

end UnforcedLeray.Short.PartIIa
