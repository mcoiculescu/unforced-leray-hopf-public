import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdComm
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdTimeDeriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.LapPMul

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
If `L U = F` on `Ioo s t`, then `∂_t`-derivative of `∂_j U` is `∂_j (A)` where `A` is the
time derivative of `U`, supplied by `pdTimeDeriv`; `pdComm` moves `∂_j` past `∂_k` and the product
rule `lapPMul_pd_mul` / `lapPMul_pd_add` gives the coefficient terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Smoothness of a first partial, with explicit orders. -/
theorem bwdPdD_cd (k : Fin 2) (g : B0579.Plane → ℝ) (n m : WithTop ℕ∞) (h : n + 1 ≤ m)
    (hg : ContDiff ℝ m g) : ContDiff ℝ n (B0579.pd k g) := by
  show ContDiff ℝ n (fun y => fderiv ℝ g y (B0579.dir k))
  exact (hg.fderiv_right (m := n) h).clm_apply contDiff_const

/-- Pointwise linearity of `pd` for a difference. -/
theorem bwdPdD_sub (j : Fin 2) (g h : B0579.Plane → ℝ) (x : B0579.Plane)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    B0579.pd j (fun y => g y - h y) x = B0579.pd j g x - B0579.pd j h x := by
  unfold B0579.pd
  have H : HasFDerivAt (fun y => g y - h y) (fderiv ℝ g x - fderiv ℝ h x) x :=
    hg.hasFDerivAt.sub hh.hasFDerivAt
  rw [H.fderiv, ContinuousLinearMap.sub_apply]

/-- Pointwise linearity of `pd` for a scalar multiple. -/
theorem bwdPdD_const (j : Fin 2) (c : ℝ) (g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hg : DifferentiableAt ℝ g x) :
    B0579.pd j (fun y => c * g y) x = c * B0579.pd j g x := by
  unfold B0579.pd
  have H : HasFDerivAt (fun y => c * g y) (c • fderiv ℝ g x) x :=
    hg.hasFDerivAt.const_mul c
  rw [H.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem bwdOpPd : UnforcedLeray.Short.IIb.BwdOpPd := by
  intro ν s t b0 b1 U F hU hFb hBwd j r hr x
  -- slices of `U` are smooth on the open interval
  have hsl : ∀ r' ∈ Ioo s t, ContDiff ℝ 4 (U r') := by
    intro r' hr'
    refine contDiff_iff_contDiffAt.2 (fun y => ?_)
    have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2)
        (r', y) :=
      hU.contDiffAt (prod_mem_nhds (Icc_mem_nhds hr'.1 hr'.2) univ_mem)
    have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : B0579.Plane => (r', y')) y :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    have hc := hG.comp y hl
    exact hc.of_le (by simp)
  have hu4 : ContDiff ℝ 4 (U r) := hsl r hr
  have hu2 : ContDiff ℝ 2 (U r) := hu4.of_le (by norm_num)
  have hf : Differentiable ℝ (F r) := (hFb r hr).1.differentiable (by norm_num)
  have hp0 : Differentiable ℝ (b0 r) := (hFb r hr).2.1.differentiable (by norm_num)
  have hp1 : Differentiable ℝ (b1 r) := (hFb r hr).2.2.differentiable (by norm_num)
  have hd0 : ContDiff ℝ 2 (B0579.pd 0 (U r)) := bwdPdD_cd 0 (U r) 2 4 (by norm_num) hu4
  have hd1 : ContDiff ℝ 2 (B0579.pd 1 (U r)) := bwdPdD_cd 1 (U r) 2 4 (by norm_num) hu4
  have hd0d : Differentiable ℝ (B0579.pd 0 (U r)) := hd0.differentiable (by norm_num)
  have hd1d : Differentiable ℝ (B0579.pd 1 (U r)) := hd1.differentiable (by norm_num)
  have hdd00 : Differentiable ℝ (B0579.pd 0 (B0579.pd 0 (U r))) :=
    (bwdPdD_cd 0 (B0579.pd 0 (U r)) 1 2 (by norm_num) hd0).differentiable (by norm_num)
  have hdd11 : Differentiable ℝ (B0579.pd 1 (B0579.pd 1 (U r))) :=
    (bwdPdD_cd 1 (B0579.pd 1 (U r)) 1 2 (by norm_num) hd1).differentiable (by norm_num)
  have hlapd : ∀ y, DifferentiableAt ℝ (fun z => lapP (U r) z) y :=
    fun y => (hdd00 y).add (hdd11 y)
  have hνd : ∀ y, DifferentiableAt ℝ (fun z => ν * lapP (U r) z) y :=
    fun y => (hlapd y).const_mul ν
  have hgd : ∀ y, DifferentiableAt ℝ (fun z => F r z - ν * lapP (U r) z) y :=
    fun y => (hf y).sub (hνd y)
  have hhd : ∀ y, DifferentiableAt ℝ
      (fun z => b0 r z * B0579.pd 0 (U r) z + b1 r z * B0579.pd 1 (U r) z) y :=
    fun y => ((hp0 y).mul (hd0d y)).add ((hp1 y).mul (hd1d y))
  -- the time derivative of `U` is `A`
  have hAd : ∀ r' ∈ Ioo s t, ∀ y : B0579.Plane,
      HasDerivAt (fun r'' => U r'' y)
        ((F r' y - ν * lapP (U r') y) -
          (b0 r' y * B0579.pd 0 (U r') y + b1 r' y * B0579.pd 1 (U r') y)) r' := by
    intro r' hr' y
    obtain ⟨D, hD, hE⟩ := hBwd r' hr' y
    exact hD.congr_deriv (by linarith)
  have hT : HasDerivAt (fun r' => B0579.pd j (U r') x)
      (B0579.pd j (fun y => (F r y - ν * lapP (U r) y) -
        (b0 r y * B0579.pd 0 (U r) y + b1 r y * B0579.pd 1 (U r) y)) x) r :=
    pdTimeDeriv s t U
      (fun r' y => (F r' y - ν * lapP (U r') y) -
        (b0 r' y * B0579.pd 0 (U r') y + b1 r' y * B0579.pd 1 (U r') y))
      hU hAd j r hr x
  -- the Laplacian of `∂_j U`, by commuting derivatives
  have hP1 : B0579.pd j (fun y => lapP (U r) y) x =
      B0579.pd 0 (B0579.pd 0 (B0579.pd j (U r))) x +
        B0579.pd 1 (B0579.pd 1 (B0579.pd j (U r))) x := by
    show B0579.pd j (fun y => B0579.pd 0 (B0579.pd 0 (U r)) y +
      B0579.pd 1 (B0579.pd 1 (U r)) y) x = _
    rw [lapPMul_pd_add j (B0579.pd 0 (B0579.pd 0 (U r))) (B0579.pd 1 (B0579.pd 1 (U r))) x
        (hdd00 x) (hdd11 x),
      pdComm (B0579.pd 0 (U r)) j 0 hd0, pdComm (B0579.pd 1 (U r)) j 1 hd1,
      pdComm (U r) j 0 hu2, pdComm (U r) j 1 hu2]
  -- the coefficient identity at the point
  have hV : B0579.pd j (fun y => (F r y - ν * lapP (U r) y) -
        (b0 r y * B0579.pd 0 (U r) y + b1 r y * B0579.pd 1 (U r) y)) x =
      B0579.pd j (F r) x - ν * (B0579.pd 0 (B0579.pd 0 (B0579.pd j (U r))) x +
          B0579.pd 1 (B0579.pd 1 (B0579.pd j (U r))) x) -
        ((b0 r x * B0579.pd 0 (B0579.pd j (U r)) x + B0579.pd 0 (U r) x * B0579.pd j (b0 r) x) +
          (b1 r x * B0579.pd 1 (B0579.pd j (U r)) x + B0579.pd 1 (U r) x * B0579.pd j (b1 r) x)) := by
    rw [bwdPdD_sub j (fun y => F r y - ν * lapP (U r) y)
        (fun y => b0 r y * B0579.pd 0 (U r) y + b1 r y * B0579.pd 1 (U r) y) x (hgd x) (hhd x),
      bwdPdD_sub j (F r) (fun y => ν * lapP (U r) y) x (hf x) (hνd x),
      bwdPdD_const j ν (fun y => lapP (U r) y) x (hlapd x),
      hP1,
      lapPMul_pd_add j (fun y => b0 r y * B0579.pd 0 (U r) y)
        (fun y => b1 r y * B0579.pd 1 (U r) y) x ((hp0 x).mul (hd0d x)) ((hp1 x).mul (hd1d x)),
      lapPMul_pd_mul j (b0 r) (B0579.pd 0 (U r)) x (hp0 x) (hd0d x),
      lapPMul_pd_mul j (b1 r) (B0579.pd 1 (U r)) x (hp1 x) (hd1d x),
      pdComm (U r) j 0 hu2, pdComm (U r) j 1 hu2] <;> ring
  -- assemble the backward-operator equation for `∂_j U`
  have hL : lapP (fun y => B0579.pd j (U r) y) x =
      B0579.pd 0 (B0579.pd 0 (B0579.pd j (U r))) x +
        B0579.pd 1 (B0579.pd 1 (B0579.pd j (U r))) x := rfl
  refine ⟨_, hT, ?_⟩
  linear_combination hV + ν * hL

end UnforcedLeray.Short.IIb
