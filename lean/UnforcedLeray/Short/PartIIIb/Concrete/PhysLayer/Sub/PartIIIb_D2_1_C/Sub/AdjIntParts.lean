import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3.Grad
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_6b
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinR.Integrable
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection

/-!
# `AdjIntParts`: integration by parts for the adjoint graph domain

Source `the November 2 reference manuscript` lines 1351-1362 and 1556-1583.
Proves `adjIntParts : AdjIntParts`. Helpers are local (prefix `aii_`).

The witness is `h = (μ + 1)Φ - a - b - g` with `a = νΔΦ` and `b = T₀Φ` the `Y₂` fields of
`FWUAdjDom`, using `T₀ᵗ = 3/2 - driftT` on phase tests. Weak solenoidality uses
`Δ(∇φ) = ∇Δφ` and `driftT(∇φ) = ∇(φ - T₀φ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.PartIIIb.Concrete.GradAux

theorem aii_int {P : ℝ} (hP : 0 < P) {X u : ℝ × Space → CVec3} (hX : IsPhaseTest P X)
    (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) :
    Integrable (fun x => dotL (X x) (u x))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) :=
  UnforcedLeray.Short.IIb.integrable_dotL_phaseTest_Yr hP one_lt_two hX hu

theorem aii_pairF_add_left {P : ℝ} (hP : 0 < P) {X Z u : ℝ × Space → CVec3}
    (hX : IsPhaseTest P X) (hZ : IsPhaseTest P Z) (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) :
    pairF P (fun x => X x + Z x) u = pairF P X u + pairF P Z u := by
  have : Fact (0 < P) := ⟨hP⟩
  exact UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable (aii_int hP hX hu)
    (aii_int hP hZ hu) (aii_int hP (hX.add hZ) hu)

theorem aii_pairF_add_right {P : ℝ} (hP : 0 < P) {X u v : ℝ × Space → CVec3}
    (hX : IsPhaseTest P X) (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u)
    (hv : UnforcedLeray.Short.IIb.IsInYr P 2 v) :
    pairF P X (fun x => u x + v x) = pairF P X u + pairF P X v := by
  have : Fact (0 < P) := ⟨hP⟩
  refine UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable (aii_int hP hX hu)
    (aii_int hP hX hv) ?_
  exact ((aii_int hP hX hu).add (aii_int hP hX hv)).congr
    (ae_of_all _ fun x => by simp [dotL_apply, mul_add, Finset.sum_add_distrib, PiLp.add_apply])

theorem aii_pairF_smul_left (P c : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P (fun x => c • X x) u = (c : ℂ) * pairF P X u :=
  UnforcedLeray.Short.IIb.pairF_real_smul P c X u

theorem aii_pairF_smul_right (P c : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P X (fun x => c • u x) = (c : ℂ) * pairF P X u := by
  unfold pairF phaseInt
  simp only [UnforcedLeray.Short.IIb.dotL_rsmul_right, integral_const_mul, Complex.real_smul]
  ring

theorem aii_inYr_smul {P : ℝ} (hP : 0 < P) {u : ℝ × Space → CVec3}
    (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) (c : ℝ) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => c • u x) :=
  isInYr_smul_of_bdd hP (a := fun _ => c) aestronglyMeasurable_const (M := |c|)
    (fun _ => le_rfl) (ae_of_all _ fun _ => rfl) hu

theorem aii_inYr_lin {P : ℝ} (hP : 0 < P) {u v : ℝ × Space → CVec3}
    (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) (hv : UnforcedLeray.Short.IIb.IsInYr P 2 v)
    (c d : ℝ) : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => c • u x + d • v x) :=
  isInYr_add2 hP (fun x => rfl) (aii_inYr_smul hP hu c) (aii_inYr_smul hP hv d)

theorem aii_pairF_lin {P : ℝ} (hP : 0 < P) {X u v : ℝ × Space → CVec3}
    (hX : IsPhaseTest P X) (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u)
    (hv : UnforcedLeray.Short.IIb.IsInYr P 2 v) (c d : ℝ) :
    pairF P X (fun x => c • u x + d • v x) = (c : ℂ) * pairF P X u + (d : ℂ) * pairF P X v := by
  rw [aii_pairF_add_right hP hX (aii_inYr_smul hP hu c) (aii_inYr_smul hP hv d),
    aii_pairF_smul_right, aii_pairF_smul_right]

theorem aii_pairF_sum3 {P : ℝ} (hP : 0 < P) {X a b g : ℝ × Space → CVec3}
    (hX : IsPhaseTest P X) (ha : UnforcedLeray.Short.IIb.IsInYr P 2 a)
    (hb : UnforcedLeray.Short.IIb.IsInYr P 2 b) (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) :
    pairF P X (fun x => a x + b x + g x) = pairF P X a + pairF P X b + pairF P X g := by
  rw [aii_pairF_add_right hP hX (isInYr_add2 hP (fun x => rfl) ha hb) hg,
    aii_pairF_add_right hP hX ha hb]

/-- `Δ(∇φ) = ∇(Δφ)` and the drift identity, as used for weak solenoidality. -/
theorem aii_driftT_gradT {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    driftT (gradT φ) = gradT (fun q => ((-1 : ℝ) • dτ φ q + (1 / 2 : ℝ) • radialT φ q) + φ q) := by
  have hs : ContDiff ℝ ∞ φ := hφ.smooth
  have hc : ContDiff ℝ ∞ (fun q => (-1 : ℝ) • dτ φ q + (1 / 2 : ℝ) • radialT φ q) :=
    ((contDiff_const (c := (-1 : ℝ))).smul (cdDτ hs)).add
      ((contDiff_const (c := (1 / 2 : ℝ))).smul (cdRadial hs))
  have hc1 : ContDiff ℝ ∞ (fun q => (-1 : ℝ) • dτ φ q) :=
    (contDiff_const (c := (-1 : ℝ))).smul (cdDτ hs)
  have hc2 : ContDiff ℝ ∞ (fun q => (1 / 2 : ℝ) • radialT φ q) :=
    (contDiff_const (c := (1 / 2 : ℝ))).smul (cdRadial hs)
  rw [gradT_add_fun hc hs, gradT_add_fun hc1 hc2, gradT_smul_fun (cdDτ hs) (-1 : ℝ),
    gradT_smul_fun (cdRadial hs) (1 / 2 : ℝ)]
  funext q
  have hR := congrFun (gr_radial hs) q
  have hD := congrFun (gr_dτ hs) q
  simp only [driftT]
  rw [hD, hR]
  module


theorem aii_grad_a {P ν : ℝ} {Φ a : ℝ × Space → CVec3} {φs : ℝ × Space → ℂ}
    (hφ : IsPhaseTest P φs) (hΦsol : IsWeakSolenoidal P Φ)
    (ha : UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a) :
    pairF P (gradT φs) a = 0 := by
  have hs : ContDiff ℝ ∞ φs := hφ.smooth
  have e := ha (gradT φs) hφ.gradT
  have e2 : nuLapT ν (gradT φs) = gradT (fun q => ν • lapT φs q) := by
    funext q
    calc nuLapT ν (gradT φs) q = ν • lapT (gradT φs) q := rfl
      _ = ν • gradT (lapT φs) q := by rw [gr_lap hs]
      _ = gradT (fun q => ν • lapT φs q) q := by rw [gradT_smul_fun (cdLap hs) ν]
  have hz : pairF P (gradT (fun q => ν • lapT φs q)) Φ = 0 :=
    hΦsol _ (hφ.lapT.const_smul ν)
  rw [e2, hz] at e
  exact e.symm

theorem aii_grad_b {P : ℝ} {φs : ℝ × Space → ℂ} {Φ b : ℝ × Space → CVec3}
    (hφ : IsPhaseTest P φs) (hΦsol : IsWeakSolenoidal P Φ)
    (hb : UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b) :
    pairF P (gradT φs) b = 0 := by
  have e := hb (gradT φs) hφ.gradT
  rw [aii_driftT_gradT hφ] at e
  have hψ : IsPhaseTest P (fun q => ((-1 : ℝ) • dτ φs q + (1 / 2 : ℝ) • radialT φs q) + φs q) :=
    ((hφ.dτ.const_smul (-1 : ℝ)).add (hφ.radialT.const_smul (1 / 2 : ℝ))).add hφ
  have hz := hΦsol _ hψ
  rw [hz] at e
  exact e.symm

theorem aii_wsol {P ν μ : ℝ} {Φ g a b : ℝ × Space → CVec3} (hP : 0 < P)
    (hΦsol : IsWeakSolenoidal P Φ) (hgsol : IsWeakSolenoidal P g)
    (hΦm : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) (ham : UnforcedLeray.Short.IIb.IsInYr P 2 a)
    (hbm : UnforcedLeray.Short.IIb.IsInYr P 2 b) (hgm : UnforcedLeray.Short.IIb.IsInYr P 2 g)
    (ha : UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a)
    (hb : UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b) :
    IsWeakSolenoidal P (fun x => (μ + 1 : ℝ) • Φ x + (-1 : ℝ) • (a x + b x + g x)) := by
  intro φs hφ
  have hk : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => a x + b x + g x) :=
    isInYr_add2 hP (fun x => rfl) (isInYr_add2 hP (fun x => rfl) ham hbm) hgm
  rw [aii_pairF_lin hP hφ.gradT hΦm hk (μ + 1) (-1), aii_pairF_sum3 hP hφ.gradT ham hbm hgm,
    hΦsol φs hφ, aii_grad_a hφ hΦsol ha, aii_grad_b hφ hΦsol hb, hgsol φs hφ]
  simp

theorem adjIntParts : AdjIntParts := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ
  obtain ⟨a, ha_mem, ha⟩ := hΦ.lapl
  obtain ⟨b, hb_mem, hb⟩ := hΦ.drift
  have hk : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => a x + b x + g x) :=
    isInYr_add2 hP (fun x => rfl) (isInYr_add2 hP (fun x => rfl) ha_mem hb_mem) hΦ.mem_g
  refine ⟨fun x => (μ + 1 : ℝ) • Φ x + (-1 : ℝ) • (a x + b x + g x),
    aii_inYr_lin hP hΦ.mem hk (μ + 1) (-1),
    aii_wsol hP hΦ.sol hΦ.sol_g hΦ.mem ha_mem hb_mem hΦ.mem_g ha hb, ?_⟩
  intro Ψ hΨ
  have hpt : (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) =
      fun x => ((-1 : ℝ) • driftT Ψ x + (-1 : ℝ) • nuLapT ν Ψ x) + (μ + 1 : ℝ) • Ψ x := by
    funext x
    ext i
    simp only [L0, T0, driftT, nuLapT, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      PiLp.neg_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  have hD : IsPhaseTest P (fun x => (-1 : ℝ) • driftT Ψ x) := hΨ.driftT.const_smul (-1 : ℝ)
  have hN : IsPhaseTest P (fun x => (-1 : ℝ) • nuLapT ν Ψ x) :=
    (hΨ.lapT.const_smul ν).const_smul (-1 : ℝ)
  have hZ : IsPhaseTest P (fun x => (μ + 1 : ℝ) • Ψ x) := hΨ.const_smul (μ + 1 : ℝ)
  rw [hpt, aii_pairF_add_left (X := fun x => (-1 : ℝ) • driftT Ψ x + (-1 : ℝ) • nuLapT ν Ψ x)
    (Z := fun x => (μ + 1 : ℝ) • Ψ x) hP (hD.add hN) hZ hΦ.mem,
    aii_pairF_add_left (X := fun x => (-1 : ℝ) • driftT Ψ x) (Z := fun x => (-1 : ℝ) • nuLapT ν Ψ x)
      hP hD hN hΦ.mem,
    aii_pairF_smul_left, aii_pairF_smul_left, aii_pairF_smul_left, hb Ψ hΨ, ha Ψ hΨ,
    aii_pairF_lin hP hΨ hΦ.mem hk (μ + 1) (-1), aii_pairF_sum3 hP hΨ ha_mem hb_mem hΦ.mem_g]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
