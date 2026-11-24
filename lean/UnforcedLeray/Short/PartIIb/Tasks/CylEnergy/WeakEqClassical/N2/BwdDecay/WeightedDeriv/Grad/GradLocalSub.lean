import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.LapPMul
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BwdOpLin
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BwdOpMul
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.BwdOpPd
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutPlane
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradAlg

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
The quantity `gradZ lam η0 φ = ζ |∇φ|² + lam φ²` is a subsolution of the backward operator.
The computation composes the operator rules `bwdOpPd`, `bwdOpMul`, `bwdOpLin` and `bwdOpAt_static`,
expands the gradient of sums of squares with `lapPMul_pd_add` and `lapPMul_pd_mul`, and closes
with the pointwise algebra `gradAlg`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Slices of a jointly `C^∞` function on `[s, t] × ℝ²` are `C²`. -/
theorem gls_slice (s t : ℝ) (U : ℝ → B0579.Plane → ℝ)
    (hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => U z.1 z.2)
      (Icc s t ×ˢ univ))
    (r : ℝ) (hr : r ∈ Icc s t) : ContDiff ℝ 2 (U r) := by
  have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => (r, x)) univ :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have h := hU.comp hcomp (fun x _ => ⟨hr, mem_univ _⟩)
  exact (contDiffOn_univ.1 h).of_le (by simp)

/-- A constant function has zero partial derivatives. -/
theorem gls_pd_const (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun _ : B0579.Plane => (0 : ℝ)) x = 0 := by
  unfold B0579.pd
  simp

/-- Partial derivative of a sum of two squares. -/
theorem gls_pd_sumsq (k : Fin 2) (a b : B0579.Plane → ℝ) (x : B0579.Plane)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) :
    B0579.pd k (fun y => a y * a y + b y * b y) x =
      2 * (a x * B0579.pd k a x) + 2 * (b x * B0579.pd k b x) := by
  have hda : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hdb : Differentiable ℝ b := hb.differentiable (by norm_num)
  have e1 := lapPMul_pd_add k (fun y => a y * a y) (fun y => b y * b y) x
    ((hda x).mul (hda x)) ((hdb x).mul (hdb x))
  have e2 := lapPMul_pd_mul k a a x (hda x) (hda x)
  have e3 := lapPMul_pd_mul k b b x (hdb x) (hdb x)
  rw [e1, e2, e3]
  ring

/-- Sums of backward-operator facts. -/
theorem gls_bwdAdd (ν : ℝ) (b0 b1 U W : ℝ → B0579.Plane → ℝ) (r : ℝ) (x : B0579.Plane)
    (FU FW : ℝ) (hU : ContDiff ℝ 2 (U r)) (hW : ContDiff ℝ 2 (W r))
    (hUa : BwdOpAt ν b0 b1 U r x FU) (hWa : BwdOpAt ν b0 b1 W r x FW) :
    BwdOpAt ν b0 b1 (fun r' y => U r' y + W r' y) r x (FU + FW) := by
  have h := bwdOpLin ν b0 b1 U W r x 1 FU FW hU hW hUa hWa
  have e1 : (fun r' y => U r' y + W r' y) = (fun r' y => 1 * U r' y + W r' y) := by
    funext r' y
    ring
  have e2 : FU + FW = 1 * FU + FW := by ring
  rw [e1, e2]
  exact h

/-- The differentiated equation for a spatial partial, with zero forcing. -/
theorem gls_bwdPd (ν s t : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
      (Icc s t ×ˢ univ))
    (hb : ∀ r ∈ Ioo s t, ContDiff ℝ 1 (b0 r) ∧ ContDiff ℝ 1 (b1 r))
    (hpde : ∀ r ∈ Ioo s t, ∀ x : B0579.Plane, BwdOpAt ν b0 b1 φ r x 0)
    (j : Fin 2) (r : ℝ) (hr : r ∈ Ioo s t) (x : B0579.Plane) :
    BwdOpAt ν b0 b1 (fun r' y => B0579.pd j (φ r') y) r x
      (-(B0579.pd j (b0 r) x * B0579.pd 0 (φ r) x + B0579.pd j (b1 r) x * B0579.pd 1 (φ r) x)) := by
  have h := bwdOpPd ν s t b0 b1 φ (fun _ _ => (0 : ℝ)) hsm
    (fun r' hr' => ⟨contDiff_const, (hb r' hr').1, (hb r' hr').2⟩) hpde j r hr x
  have h0 : B0579.pd j (fun _ : B0579.Plane => (0 : ℝ)) x = 0 := gls_pd_const j x
  convert h using 1
  simp only [h0, zero_sub]

theorem gradLocalSub : UnforcedLeray.Short.IIb.GradLocalSub := by
  intro ν c s t V v ψ φ hν hV0 hDS hφ
  obtain ⟨hcs, _, hcr, _, C, hC0, hCd⟩ := cutProps
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ 5 * V + V * C + 3 * ν * C ≤ 2 * ν * lam := by
    refine ⟨(5 * V + V * C + 3 * ν * C) / (2 * ν), ?_, ?_⟩
    · apply div_nonneg
      · nlinarith [mul_nonneg hV0 hC0, mul_nonneg hν.le hC0]
      · linarith
    · have hν0 : ν ≠ 0 := hν.ne'
      exact le_of_eq (by field_simp)
  refine ⟨lam, hlam0, ?_⟩
  intro η0 r hr x
  have hrI : r ∈ Icc s t := Ioo_subset_Icc_self hr
  have hφr : ContDiff ℝ 2 (φ r) := gls_slice s t φ hφ.smooth r hrI
  have hpj : ∀ j : Fin 2, ContDiff ℝ 2 (fun y => B0579.pd j (φ r) y) := fun j =>
    gls_slice s t (fun r' y => B0579.pd j (φ r') y) (pdJointSmooth s t φ j hφ.smooth) r hrI
  have hbAll : ∀ r' ∈ Ioo s t, ContDiff ℝ 1 (fun y => v r' y 0) ∧
      ContDiff ℝ 1 (fun y => v r' y 1) := by
    intro r' hr'
    have h := hDS.1 r' (Ioo_subset_Icc_self hr')
    exact ⟨(h 0).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)),
      (h 1).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))⟩
  have hpdeAll : ∀ r' ∈ Ioo s t, ∀ y : B0579.Plane,
      BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1) φ r' y 0 := by
    intro r' hr' y
    exact ⟨_, hφ.pde r' hr' y, by beta_reduce; ring⟩
  have hPd0 := gls_bwdPd ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth
    hbAll hpdeAll 0 r hr x
  have hPd1 := gls_bwdPd ν s t (fun r x => v r x 0) (fun r x => v r x 1) φ hφ.smooth
    hbAll hpdeAll 1 r hr x
  have hφ0 : BwdOpAt ν (fun r x => v r x 0) (fun r x => v r x 1) φ r x 0 :=
    hpdeAll r hr x
  have hφφ := bwdOpMul ν _ _ φ φ r x 0 0 hφr hφr hφ0 hφ0
  have hc2 : ContDiff ℝ 2 cutθ := hcs.of_le (by simp)
  have hζc : ContDiff ℝ 2 (cutζ η0) := hc2.comp (contDiff_snd.sub contDiff_const)
  have hPc : ContDiff ℝ 2 (fun y => B0579.pd 0 (φ r) y * B0579.pd 0 (φ r) y +
      B0579.pd 1 (φ r) y * B0579.pd 1 (φ r) y) :=
    ((hpj 0).mul (hpj 0)).add ((hpj 1).mul (hpj 1))
  have hQ0 := bwdOpMul ν _ _ (fun r' y => B0579.pd 0 (φ r') y)
    (fun r' y => B0579.pd 0 (φ r') y) r x _ _ (hpj 0) (hpj 0) hPd0 hPd0
  have hQ1 := bwdOpMul ν _ _ (fun r' y => B0579.pd 1 (φ r') y)
    (fun r' y => B0579.pd 1 (φ r') y) r x _ _ (hpj 1) (hpj 1) hPd1 hPd1
  have hP := gls_bwdAdd ν _ _ (fun r' y => B0579.pd 0 (φ r') y * B0579.pd 0 (φ r') y)
    (fun r' y => B0579.pd 1 (φ r') y * B0579.pd 1 (φ r') y) r x _ _
    ((hpj 0).mul (hpj 0)) ((hpj 1).mul (hpj 1)) hQ0 hQ1
  have hζs := bwdOpAt_static ν (fun r x => v r x 0) (fun r x => v r x 1) (cutζ η0) r x
  have hζP := bwdOpMul ν _ _ (fun _ y => cutζ η0 y)
    (fun r' y => B0579.pd 0 (φ r') y * B0579.pd 0 (φ r') y +
      B0579.pd 1 (φ r') y * B0579.pd 1 (φ r') y) r x _ _ hζc hPc hζs hP
  have hG := bwdOpLin ν _ _ (fun r' y => φ r' y * φ r' y)
    (fun r' y => cutζ η0 y * (B0579.pd 0 (φ r') y * B0579.pd 0 (φ r') y +
      B0579.pd 1 (φ r') y * B0579.pd 1 (φ r') y)) r x lam _ _
    (hφr.mul hφr) (hζc.mul hPc) hφφ hζP
  have hfun : gradZ lam η0 φ = (fun r' y => lam * (φ r' y * φ r' y) +
      cutζ η0 y * (B0579.pd 0 (φ r') y * B0579.pd 0 (φ r') y +
        B0579.pd 1 (φ r') y * B0579.pd 1 (φ r') y)) := by
    funext r' y
    simp only [gradZ, gradSq]
    ring
  have hζ0 : 0 ≤ cutζ η0 x := (hcr (x.2 - η0)).1
  have hζ1 : cutζ η0 x ≤ 1 := (hcr (x.2 - η0)).2
  have hcP := cutPlane η0 x
  have hz0 : B0579.pd 0 (cutζ η0) x = 0 := hcP.1
  have hz1 : B0579.pd 1 (cutζ η0) x = deriv cutθ (x.2 - η0) := hcP.2.1
  have hlz' : lapP (cutζ η0) x = deriv (deriv cutθ) (x.2 - η0) := hcP.2.2
  have hd := hCd (x.2 - η0)
  have hζe : cutζ η0 x = cutθ (x.2 - η0) := rfl
  have hzC : B0579.pd 0 (cutζ η0) x ^ 2 + B0579.pd 1 (cutζ η0) x ^ 2 ≤ C * cutζ η0 x := by
    rw [hz0, hz1, hζe]
    nlinarith [hd.1]
  have hlzC : |lapP (cutζ η0) x| ≤ C := by
    rw [hlz']
    exact hd.2
  have hb0 : |v r x 0| ≤ V := (hDS.2 r hrI x 0).1
  have hb1 : |v r x 1| ≤ V := (hDS.2 r hrI x 1).1
  have hd00 : |B0579.pd 0 (fun y => v r y 0) x| ≤ V := (hDS.2 r hrI x 0).2.1 0
  have hd01 : |B0579.pd 0 (fun y => v r y 1) x| ≤ V := (hDS.2 r hrI x 1).2.1 0
  have hd10 : |B0579.pd 1 (fun y => v r y 0) x| ≤ V := (hDS.2 r hrI x 0).2.1 1
  have hd11 : |B0579.pd 1 (fun y => v r y 1) x| ≤ V := (hDS.2 r hrI x 1).2.1 1
  have hGA := gradAlg ν V C lam (cutζ η0 x) (B0579.pd 0 (cutζ η0) x)
    (B0579.pd 1 (cutζ η0) x) (lapP (cutζ η0) x) (v r x 0) (v r x 1)
    (B0579.pd 0 (fun y => v r y 0) x) (B0579.pd 0 (fun y => v r y 1) x)
    (B0579.pd 1 (fun y => v r y 0) x) (B0579.pd 1 (fun y => v r y 1) x)
    (B0579.pd 0 (φ r) x) (B0579.pd 1 (φ r) x)
    (B0579.pd 0 (fun y => B0579.pd 0 (φ r) y) x) (B0579.pd 0 (fun y => B0579.pd 1 (φ r) y) x)
    (B0579.pd 1 (fun y => B0579.pd 0 (φ r) y) x) (B0579.pd 1 (fun y => B0579.pd 1 (φ r) y) x)
    hν hV0 hC0 hζ0 hζ1 hzC hlzC hb0 hb1 hd00 hd01 hd10 hd11 hlam
  have hPk0 : B0579.pd 0 (fun y => B0579.pd 0 (φ r) y * B0579.pd 0 (φ r) y +
      B0579.pd 1 (φ r) y * B0579.pd 1 (φ r) y) x =
      2 * (B0579.pd 0 (φ r) x * B0579.pd 0 (fun y => B0579.pd 0 (φ r) y) x) +
        2 * (B0579.pd 1 (φ r) x * B0579.pd 0 (fun y => B0579.pd 1 (φ r) y) x) :=
    gls_pd_sumsq 0 (fun y => B0579.pd 0 (φ r) y) (fun y => B0579.pd 1 (φ r) y) x
      (hpj 0) (hpj 1)
  have hPk1 : B0579.pd 1 (fun y => B0579.pd 0 (φ r) y * B0579.pd 0 (φ r) y +
      B0579.pd 1 (φ r) y * B0579.pd 1 (φ r) y) x =
      2 * (B0579.pd 0 (φ r) x * B0579.pd 1 (fun y => B0579.pd 0 (φ r) y) x) +
        2 * (B0579.pd 1 (φ r) x * B0579.pd 1 (fun y => B0579.pd 1 (φ r) y) x) :=
    gls_pd_sumsq 1 (fun y => B0579.pd 0 (φ r) y) (fun y => B0579.pd 1 (φ r) y) x
      (hpj 0) (hpj 1)
  refine ⟨_, hGA, ?_⟩
  rw [hfun]
  convert hG using 1
  linear_combination (-(2 * ν * B0579.pd 0 (cutζ η0) x)) * hPk0 +
    (-(2 * ν * B0579.pd 1 (cutζ η0) x)) * hPk1

end UnforcedLeray.Short.IIb
