import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T6
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T7
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T8
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T10
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.PairLinear

/-!
# `PartIII-b:IIIb-D2/3/1`: `WardHSolenoidal`

The design (definitions of the regularity Props `WardXRegular`, `WardX0Smooth`, `WardX0Structure`,
`OutPrimStream`, `WardStreamCutDivFree`, `BracketAxiNoSwirl`, `PhaseSolenoidalOfPointwise`,
`VelPhysCoefOf`, `WardHCoefMeasurable`, and the proved lemma `bracket_div_free`) is in
`PartIIIb-D2_3_1/Defs.lean`; the lemma tasks live in `PartIIIb-D2_3_1/T<k>.lean`.  The final
theorem `wardHSolenoidal_of` is assembled in this file from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The axis is `volume`-null in the spacetime variable. -/
theorem wfs_ae_snd_not_axis :
    ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), x.2 ∉ axis := by
  rw [Measure.volume_eq_prod]
  exact Measure.quasiMeasurePreserving_snd.ae ae_not_mem_axis

/-- The coefficient of an axisymmetric field only sees the field off the axis. -/
theorem wfs_coefOf_congr {R : ℝ} (hR : 0 < R) (G H : ℝ → Space → Space)
    (h : ∀ τ y, y ∉ axis → G τ y = H τ y) : coefOf R G = coefOf R H := by
  funext p
  by_cases hp : 0 < p.1
  · have hy : NearInst.chartY R p ∉ axis := by
      intro h'
      have h'' : NearInst.chartY R p 0 = 0 ∧ NearInst.chartY R p 1 = 0 := h'
      have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by
        simp [NearInst.chartY]
      have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hp).ne'
      exact hne (h1 ▸ h''.1)
    unfold coefOf
    rw [h _ _ hy]
  · have hs : Real.sqrt p.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hp)
    simp [coefOf, hs]

/-- Off the axis, the Ward field `h = [U, X]` is the bracket of `U` and any field `X` agreeing
with `wardX` there. -/
theorem wfs_wardH_eq_bracket {ν μ R c : ℝ} {χy : ℝ → ℝ} {U : ℝ → SpatialField} {g : Chart → Ten3}
    (X : ℝ → Space → Space)
    (hXeq : ∀ τ y, y ∉ axis → X τ y = wardX ν μ R c χy g τ y) (τ : ℝ) (y : Space)
    (hy : y ∉ axis) :
    wardH ν μ R c χy U g τ y = fderiv ℝ (X τ) y (U τ y) - fderiv ℝ (U τ) y (X τ y) := by
  have hev : wardX ν μ R c χy g τ =ᶠ[𝓝 y] X τ := by
    filter_upwards [isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
    exact (hXeq τ z hz).symm
  unfold wardH
  rw [hev.fderiv_eq, (hXeq τ y hy).symm]

/-- The bracket of two fields, as a function of phase and point. -/
def wfsBr (X U : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  fderiv ℝ (X τ) y (U τ y) - fderiv ℝ (U τ) y (X τ y)

theorem wfs_comp_fderiv_space (G : Space → Space) (hG : Differentiable ℝ G) (i : Fin 3)
    (y v : Space) :
    fderiv ℝ G y v i = fderiv ℝ (fun y' => G y' i) y v := by
  have hl : HasFDerivAt (fun y' => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (G y'))
      (((EuclideanSpace.proj i : Space →L[ℝ] ℝ)).comp (fderiv ℝ G y)) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hG y).hasFDerivAt
  have hfun : (fun y' => G y' i) = (fun y' => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (G y')) :=
    rfl
  rw [hfun, hl.fderiv]
  rfl

theorem wfs_ofReal_fderiv (g : Space → ℝ) (hg : Differentiable ℝ g) (y v : Space) :
    fderiv ℝ (fun y' => ((g y' : ℝ) : ℂ)) y v = ((fderiv ℝ g y v : ℝ) : ℂ) := by
  have hl : HasFDerivAt (fun y' => ((g y' : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ g y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (hg y).hasFDerivAt
  rw [hl.fderiv]
  rfl

theorem wfs_realC_contDiff {F : Space → Space} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun y => B0412.realC (F y)) := by
  have hfun : (fun y => B0412.realC (F y)) =
      fun y => ∑ i : Fin 3, ((F y i : ℝ) : ℂ) • (EuclideanSpace.single i (1 : ℂ) : CVec3) := rfl
  rw [hfun]
  refine ContDiff.sum fun i _ => ?_
  have hc : ContDiff ℝ 1 (fun y => ((F y i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hF)
  exact hc.smul contDiff_const

/-- The complexified real field has zero phase-slice divergence when the real field does. -/
theorem wfs_realC_div {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hdiv : ∀ y, ∑ j : Fin 3, fderiv ℝ F y (coordinateVector j) j = 0) (y : Space) :
    ∑ j : Fin 3, fderiv ℝ (fun y' => B0412.realC (F y')) y (coordinateVector j) j = 0 := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hcomp : ∀ j : Fin 3, fderiv ℝ (fun y' => B0412.realC (F y')) y (coordinateVector j) j =
      fderiv ℝ (fun y' => ((F y' j : ℝ) : ℂ)) y (coordinateVector j) := by
    intro j
    have h := pst_comp_fderiv (w := fun x : ℝ × Space => B0412.realC (F x.2)) 0
      (wfs_realC_contDiff hF) j y (coordinateVector j)
    calc fderiv ℝ (fun y' => B0412.realC (F y')) y (coordinateVector j) j
        = fderiv ℝ (fun y' => B0412.realC (F y') j) y (coordinateVector j) := h.symm
      _ = fderiv ℝ (fun y' => ((F y' j : ℝ) : ℂ)) y (coordinateVector j) := by
          have hfun : (fun y' => B0412.realC (F y') j) = fun y' => ((F y' j : ℝ) : ℂ) :=
            funext fun y' => B0412.realC_apply _ _
          rw [hfun]
  have hsum : ∀ j : Fin 3, fderiv ℝ (fun y' => ((F y' j : ℝ) : ℂ)) y (coordinateVector j) =
      ((fderiv ℝ F y (coordinateVector j) j : ℝ) : ℂ) := by
    intro j
    have hdj : Differentiable ℝ (fun y' => F y' j) :=
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).differentiable.comp hd
    rw [wfs_ofReal_fderiv (fun y' => F y' j) hdj y (coordinateVector j),
      ← wfs_comp_fderiv_space F hd j y (coordinateVector j)]
  have hall : ∑ j : Fin 3, fderiv ℝ (fun y' => B0412.realC (F y')) y (coordinateVector j) j =
      ∑ j : Fin 3, ((fderiv ℝ F y (coordinateVector j) j : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun j _ => (hcomp j).trans (hsum j)
  rw [hall, ← Complex.ofReal_sum, hdiv y, Complex.ofReal_zero]

theorem wfsBr_contDiff1 {X U : ℝ → Space → Space} (hXC : ∀ τ, ContDiff ℝ 2 (X τ))
    (hUC : ∀ τ, ContDiff ℝ 2 (U τ)) (τ : ℝ) :
    ContDiff ℝ 1 (wfsBr X U τ) := by
  have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ (X τ) y (U τ y)) :=
    ((hXC τ).fderiv_right (m := 1) (by norm_num)).clm_apply
      ((hUC τ).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  have h2 : ContDiff ℝ 1 (fun y => fderiv ℝ (U τ) y (X τ y)) :=
    ((hUC τ).fderiv_right (m := 1) (by norm_num)).clm_apply
      ((hXC τ).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  exact h1.sub h2

/-- **`WardHSolenoidal` from the core data.** -/
theorem wfs_core {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ} {χo χy : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (hχy : IsYoungCutoff χy) {U : ℝ → SpatialField}
    {p : ℝ → Space → ℝ} (hc : 0 < c) (hρb : 0 < ρb) (hmZ : 0 ≤ mZ) (hν : 0 < ν) (hε : 0 < ε)
    (hμ0 : 0 < μ) (hUp : IsExactProfile ν (2 * ε * c) U p) (hax : ∀ τ, AxiNoSwirlPt (U τ))
    (hW : IsWardPinned B ε μ hχo χy U p) : WardHSolenoidal B ε := by
  intro T
  have hUC : ∀ τ, ContDiff ℝ 2 (U τ) := by
    intro τ
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Space => ((τ, y) : ℝ × Space)) :=
      contDiff_const.prodMk contDiff_id
    have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    exact (hUp.smoothU.comp hcd).of_le hle
  have hUm : Measurable fun q : ℝ × Space => U q.1 q.2 := hUp.smoothU.continuous.measurable
  have hμ : -(1 / 4 : ℝ) < μ := by linarith
  have hreg : WardXRegular c mZ ρb γ ν ε μ hχo χy :=
    wardXRegular_of c mZ ρb γ ν ε μ hχo χy (Final.wardX0Smooth_of c mZ ρb γ ν ε μ hχo)
      (Final.wardX0Structure_of c mZ ρb γ ν ε μ hχo) (outPrimStream_of c mZ ρb γ ν ε μ hχo)
      (wardStreamCutDivFree_of ν ε⁻¹ χy)
  have hmeasC := wardHCoefMeasurable_of c mZ ρb γ ν ε μ hχo χy U hreg hχy hUC hUm hc hρb hmZ hν
    hε hμ T ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3)
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) EventuallyEq.rfl EventuallyEq.rfl
  obtain ⟨-, hhf, -⟩ := hW T ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3)
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) EventuallyEq.rfl EventuallyEq.rfl
  rw [NearInst.ae_bodyMeasure] at hhf
  have hw1 := wda_velPhys_congr hc hε (Lp.stronglyMeasurable (B.hf T)).measurable hmeasC hhf
  obtain ⟨X, hXC, hXeq, hXdiv, hXper, hXax⟩ :=
    hreg hχy hc hρb hmZ hν hε hμ T ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3)
      ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) EventuallyEq.rfl EventuallyEq.rfl
  have hP : 2 * c / ε⁻¹ = 2 * ε * c := by rw [div_inv_eq_mul]; ring
  have hXf : ∀ τ, X (τ + 2 * c / ε⁻¹) = X τ := fun τ => funext (hXper τ)
  have hUf : ∀ τ, U (τ + 2 * c / ε⁻¹) = U τ := fun τ => funext fun y => by
    rw [hP]
    exact hUp.periodicU τ y
  have hFax : AxiNoSwirl (wfsBr X U) :=
    bracketAxiNoSwirl_of U X hUC hXC (axiNoSwirl_of_pt U hax) hXax
  have hFper : ∀ τ y, wfsBr X U (τ + 2 * c / ε⁻¹) y = wfsBr X U τ y := by
    intro τ y
    simp only [wfsBr, hXf, hUf]
  have hcoef : coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U
      ((chiOStr c mZ ρb γ ν hχo T).fst + (chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3)) =
      coefOf ε⁻¹ (wfsBr X U) :=
    wfs_coefOf_congr (inv_pos.2 hε) _ _ (fun τ y hy => wfs_wardH_eq_bracket X hXeq τ y hy)
  have hw2 : velPhys ε⁻¹ c (coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U
      ((chiOStr c mZ ρb γ ν hχo T).fst + (chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3))) =ᵐ[volume]
      fun x : ℝ × Space => B0412.realC (wfsBr X U x.1 x.2) := by
    filter_upwards [wfs_ae_snd_not_axis] with x hx
    rw [hcoef]
    exact velPhysCoefOf_of ε⁻¹ c (inv_pos.2 hε) hc (wfsBr X U) hFax hFper x hx
  have hsol := phaseSolenoidalOfPointwise_of (2 * ε * c)
    (fun x : ℝ × Space => B0412.realC (wfsBr X U x.1 x.2))
    (fun τ => wfs_realC_contDiff (wfsBr_contDiff1 hXC hUC τ))
    (fun τ y => wfs_realC_div (wfsBr_contDiff1 hXC hUC τ)
      (fun y' => bracket_div_free (U τ) (X τ) (hUC τ) (hXC τ) (hUp.div_free τ) (hXdiv τ) y') y)
  intro φ hφ
  rw [NearInst.pl_pairF_congr_ae (PhaseSpace.gradT φ) hw1,
    NearInst.pl_pairF_congr_ae (PhaseSpace.gradT φ) (ae_restrict_of_ae hw2)]
  exact hsol φ hφ

theorem wardHSolenoidal_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ}
    {χo χy : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hχy : IsYoungCutoff χy) {V rb : ℝ → SpatialField}
    {p : ℝ → Space → ℝ} (hc : 0 < c) (hρb : 0 < ρb) (hmZ : 0 ≤ mZ) (hν : 0 < ν) (hε : 0 < ε)
    (hμ0 : 0 < μ) (hUp : IsExactProfile ν (2 * ε * c) (fun τ y => V τ y + rb τ y) p)
    (hax : ∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y))
    (hW : IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p) : WardHSolenoidal B ε :=
  wfs_core B hχo hχy hc hρb hmZ hν hε hμ0 hUp hax hW

end UnforcedLeray.Short.PartIIIb.Concrete
