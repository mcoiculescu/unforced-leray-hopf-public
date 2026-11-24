import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.PsiRingSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.HpJGradProof

/-!
# `hAcoef` is differentiable on `s > 0` (`PartIII-b:C/asrc/ra/9/2/2/3`, source 4978-4980)

`ψ^p_A` is jointly `C²` on `s > 0` (`psiRingSmooth_proof`).  Partial `x`- and `s`-derivatives of a
jointly `C²` function are jointly differentiable (`diff_slice_x`, `diff_slice_s`).  On `s > 0`,
`h^p_A = J∇ψ^p_A` (`hpIsJGrad_proof`), and the square roots cancel in `s^{-1/2} ĥ_A`, so
`hAcoef` is locally the pair `(-∂_η ψ, ∂_q ψ + ε(ψ - η∂_ηψ - 2s∂_sψ))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Differentiability of the `x`-partial `∂_v` of a jointly `C²` function. -/
theorem diff_slice_x {G : Chart → ℝ} {p0 : Chart} (hG : ContDiffAt ℝ 2 G p0) (v : ℝ × ℝ) :
    DifferentiableAt ℝ (fun p : Chart => fderiv ℝ (fun y => G (p.1, y)) p.2 v) p0 := by
  have hev : ∀ᶠ p in 𝓝 p0, ContDiffAt ℝ 2 G p := hG.eventually (by simp)
  have hfd : ContDiffAt ℝ 1 (fun p => fderiv ℝ G p) p0 := hG.fderiv_right (m := 1) (by norm_num)
  have hH : DifferentiableAt ℝ (fun p : Chart => fderiv ℝ G p (0, v)) p0 :=
    (hfd.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  refine hH.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  have hs : HasFDerivAt (fun y : ℝ × ℝ => (p.1, y)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hG' : HasFDerivAt G (fderiv ℝ G p) p := (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hc := hG'.comp p.2 hs
  have hfx : fderiv ℝ (fun y => G (p.1, y)) p.2 v = fderiv ℝ G p (0, v) := by
    have h2 : fderiv ℝ (fun y => G (p.1, y)) p.2 =
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := hc.fderiv
    rw [h2]
    rfl
  first | exact hfx.symm | exact hfx

/-- Differentiability of the `s`-derivative of a jointly `C²` function. -/
theorem diff_slice_s {G : Chart → ℝ} {p0 : Chart} (hG : ContDiffAt ℝ 2 G p0) :
    DifferentiableAt ℝ (fun p : Chart => deriv (fun t => G (t, p.2)) p.1) p0 := by
  have hev : ∀ᶠ p in 𝓝 p0, ContDiffAt ℝ 2 G p := hG.eventually (by simp)
  have hfd : ContDiffAt ℝ 1 (fun p => fderiv ℝ G p) p0 := hG.fderiv_right (m := 1) (by norm_num)
  have hH : DifferentiableAt ℝ (fun p : Chart => fderiv ℝ G p (1, 0)) p0 :=
    (hfd.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  refine hH.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  have hd1 : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ × ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hG' : HasFDerivAt G (fderiv ℝ G p) p := (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hc := hG'.comp_hasDerivAt p.1 hd1
  have hd : deriv (fun t => G (t, p.2)) p.1 = fderiv ℝ G p ((1 : ℝ), (0 : ℝ × ℝ)) := hc.deriv
  first | exact hd.symm | exact hd

/-- On `s > 0` the coefficient `hAcoef` is the explicit pair of partials of `ψ^p_A`. -/
theorem hAcoef_pair (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (hν : 0 < ν) (p : Chart)
    (hp : 0 < p.1) :
    hAcoef ν ε χf A p =
      (!₂[-(fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1)),
        fderiv ℝ (psipA ν χf A p.1) p.2 (ei 0) + ε * (psipA ν χf A p.1 p.2 -
          (p.2.2 * fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1) +
            2 * p.1 * deriv (fun t => psipA ν χf A t p.2) p.1))] : Merid) := by
  have hJ := (hpIsJGrad_proof ν hν χf A).2 p.1 hp p.2
  have hsq : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  unfold hAcoef hhatA
  rw [hJ]
  unfold Kop mgrad Jrot emb merOf
  rw [smul_smul, inv_mul_cancel₀ hsq, one_smul]
  ext i
  fin_cases i <;> simp [ei]

/-- `hAcoef` is differentiable on `s > 0` (source 4978-4980). -/
theorem convDiffHat (as : ℝ) (χf : ℝ → ℝ) : ConvDiffHat as χf := by
  intro hχ ν ε hν hε A hA s hs x
  have hG : ContDiffAt ℝ 2 (fun p : Chart => psipA ν χf A p.1 p.2) (s, x) :=
    (psiRingSmooth_proof as χf hχ ν hν A hA).contDiffAt
      (IsOpen.mem_nhds (isOpen_Ioi.prod isOpen_univ) ⟨hs, mem_univ _⟩)
  have hX : DifferentiableAt ℝ (fun p : Chart => fderiv ℝ (psipA ν χf A p.1) p.2 (ei 0)) (s, x) :=
    diff_slice_x hG (ei 0)
  have hY : DifferentiableAt ℝ (fun p : Chart => fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1)) (s, x) :=
    diff_slice_x hG (ei 1)
  have hT : DifferentiableAt ℝ (fun p : Chart => deriv (fun t => psipA ν χf A t p.2) p.1) (s, x) :=
    diff_slice_s hG
  have hGd : DifferentiableAt ℝ (fun p : Chart => psipA ν χf A p.1 p.2) (s, x) :=
    hG.differentiableAt (by norm_num)
  have hfin : DifferentiableAt ℝ (fun p : Chart =>
      (!₂[-(fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1)),
        fderiv ℝ (psipA ν χf A p.1) p.2 (ei 0) + ε * (psipA ν χf A p.1 p.2 -
          (p.2.2 * fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1) +
            2 * p.1 * deriv (fun t => psipA ν χf A t p.2) p.1))] : Merid)) (s, x) := by
    rw [differentiableAt_piLp]
    intro i
    have hη : DifferentiableAt ℝ (fun p : Chart => p.2.2) (s, x) := by fun_prop
    have hp1 : DifferentiableAt ℝ (fun p : Chart => p.1) (s, x) := by fun_prop
    fin_cases i
    · exact hY.neg
    · exact hX.add (((hGd.sub ((hη.mul hY).add ((hp1.const_mul 2).mul hT))).const_mul ε))
  refine hfin.congr_of_eventuallyEq ?_
  have hpos : ∀ᶠ p : Chart in 𝓝 (s, x), 0 < p.1 :=
    (continuous_fst.tendsto (s, x)).eventually (lt_mem_nhds hs)
  filter_upwards [hpos] with p hp
  exact hAcoef_pair ν ε χf A hν p hp

end UnforcedLeray.Short.PartIIIb.Concrete
