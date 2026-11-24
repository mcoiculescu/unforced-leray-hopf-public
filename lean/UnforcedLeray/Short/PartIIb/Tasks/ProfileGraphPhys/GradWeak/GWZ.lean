import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Pair
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Pt
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Norm
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Box
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr

/-!
# `PartII-b:T10/7/1/2/3` (`GWZ`): the `z`-derivative weak identity `∂_η b = Eb`

Source of record: `the November 2 reference manuscript` lines 1912-1921.
Test field `Φ = ctLift c ε (3/2) φ • e_i`:
`-∂_z Φ = ctLift 2 (∂_η^T φ) e_i` (`neg_dy2_tstZ`), paired with `N_v b` by `ct_pair` (`a = 2`);
`Φ · g_2` is `Φ · N_v(√s E b)`, paired by `ct_pair` (`a = 3/2`, `√s E b ∈ H_r` by `inHr_sqrtS_z`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.GWQ

namespace UnforcedLeray.Short.IIb.GWZ

theorem inHr_sqrtS_z {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 1 < r)
    {g2 : ℝ × Space → CVec3} (hg2 : IsInYr (2 * ε * c) r g2)
    {Eb : CProf} (hEp : QPeriodic c (sqrtS Eb))
    (hEm : AEStronglyMeasurable (sqrtS Eb) (hMeas c r))
    (hE : NvC ε⁻¹ (sqrtS Eb) =ᵐ[volume] g2) :
    InHr c r (sqrtS Eb) := by
  have hr0 : 0 < r := by linarith
  refine ⟨hEp, hEm, ?_⟩
  have hnorm := phaseLpNorm_NvC hc hr0 hε (sqrtS Eb) hEp hEm
  rw [phaseLpNorm_congr_ae hE] at hnorm
  have hK : ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) ≠ 0 := by
    have : 0 < (Real.pi * (ε⁻¹) ^ 2) ^ (1 / r) := by positivity
    exact (ENNReal.ofReal_pos.2 this).ne'
  by_contra hcon
  have htop : hNorm c r (sqrtS Eb) = ⊤ := not_lt_top_iff.1 hcon
  rw [htop, ENNReal.mul_top hK] at hnorm
  exact absurd (hnorm ▸ hg2.finite) (lt_irrefl _)

/-- The `z`-test `Ψ e_i` (real scalar coefficient). -/
def tstZ (c ε a : ℝ) (φ : Coord → ℝ) (i : Fin 2) : ℝ × Space → CVec3 :=
  fun x => (ctLift c ε a φ x) • realCL (Evec i x.2)

theorem tstZ_eq (c ε a : ℝ) (φ : Coord → ℝ) (i : Fin 2) (x : ℝ × Space) :
    tstZ c ε a φ i x = (((ctLift c ε a φ x : ℝ) : ℂ)) • frameC i x.2 := by
  simp only [tstZ, frameC_eq]
  rw [Complex.coe_smul]

theorem tstZ_contDiff {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) : ContDiff ℝ ∞ (tstZ c ε a φ i) := by
  obtain ⟨δ, hδ, hvan⟩ := ctLift_vanish (c := c) (a := a) hε hφ
  rw [contDiff_iff_contDiffAt]
  rintro ⟨τ, y⟩
  by_cases hy : Axi.ϱ y < δ
  · have hopen : IsOpen {x : ℝ × Space | Axi.ϱ x.2 < δ} :=
      isOpen_lt (Axi.continuous_ϱ.comp continuous_snd) continuous_const
    have hz : tstZ c ε a φ i =ᶠ[𝓝 (τ, y)] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hy] with x hx
      simp [tstZ, hvan x.1 x.2 hx]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · have hax : y ∉ Axi.axis := fun h => hy (by rw [(Axi.mem_axis_iff y).1 h]; exact hδ)
    have hΨ : ContDiffAt ℝ ∞ (ctLift c ε a φ) (τ, y) :=
      (ctLift_contDiff hc hε hφ).contDiffAt
    have hEv : ContDiffAt ℝ ∞ (Evec i) ((τ, y).2) := contDiffAt_Evec i hax
    have hE : ContDiffAt ℝ ∞ (fun x : ℝ × Space => realCL (Evec i x.2)) (τ, y) :=
      (realCL.contDiff.contDiffAt).comp (τ, y) (hEv.comp (τ, y) contDiffAt_snd)
    exact hΨ.smul hE

theorem tstZ_isPhaseTest {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ}
    (hφ : IsCoordTest φ) (i : Fin 2) :
    IsPhaseTest (2 * ε * c) (tstZ c ε a φ i) := by
  refine ⟨tstZ_contDiff hc hε hφ i, fun τ y => ?_, ?_⟩
  · have h := ctLift_periodic c ε a hε φ (τ, y)
    simp only [tstZ]
    rw [h]
  · obtain ⟨Rb, hRb⟩ := ctLift_bounded (c := c) (a := a) hε hφ
    exact ⟨Rb, fun τ y hy => by simp [tstZ, hRb τ y hy]⟩

theorem eRD_e3 (y : Space) : Axi.eRD y (EuclideanSpace.single 2 1) = 0 := by
  ext k
  rw [Axi.eRD_apply_coord, Axi.ϱD_apply]
  fin_cases k <;> simp [Axi.hor]

theorem exists_EvDZ (i : Fin 2) {y : Space} (hy : y ∉ Axi.axis) :
    ∃ D : Space →L[ℝ] Space, HasFDerivAt (Evec i) D y ∧ D (EuclideanSpace.single 2 1) = 0 := by
  fin_cases i
  · refine ⟨Axi.eRD y, ?_, eRD_e3 y⟩
    show HasFDerivAt (Evec 0) _ y
    rw [Evec_zero]
    exact Axi.hasFDerivAt_eR hy
  · refine ⟨0, ?_, by simp⟩
    show HasFDerivAt (Evec 1) _ y
    rw [Evec_one]
    exact hasFDerivAt_const _ _

theorem dy2_tstZ {c ε a : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) {x : ℝ × Space} (hy : x.2 ∉ Axi.axis) :
    dy 2 (tstZ c ε a φ i) x =
      (fderiv ℝ (ctLift c ε a φ) x (0, EuclideanSpace.single 2 1)) • realCL (Evec i x.2) := by
  obtain ⟨D, hD, hD2⟩ := exists_EvDZ i hy
  have hΨ : HasFDerivAt (ctLift c ε a φ) (fderiv ℝ (ctLift c ε a φ) x) x :=
    ((ctLift_contDiff hc hε hφ).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hE0 : HasFDerivAt (fun y : Space => realCL (Evec i y)) (realCL.comp D) x.2 :=
    realCL.hasFDerivAt.comp x.2 hD
  have hE : HasFDerivAt (fun x : ℝ × Space => realCL (Evec i x.2))
      ((realCL.comp D).comp (ContinuousLinearMap.snd ℝ ℝ Space)) x :=
    hE0.comp x hasFDerivAt_snd
  have h2 : HasFDerivAt (tstZ c ε a φ i) _ x := hΨ.smul hE
  unfold dy
  rw [h2.fderiv]
  simp [coordVec_eq, hD2]

theorem coordT_eta_eq (φ : Coord → ℝ) (m : Coord) :
    coordTranspose vEta dZero φ m = -cpd 2 φ m := by
  have e0 : (fun y => vEta y 0 * φ y) = fun _ => 0 := by funext y; simp [vEta]
  have e1 : (fun y => vEta y 1 * φ y) = fun _ => 0 := by funext y; simp [vEta]
  have e2 : (fun y => vEta y 2 * φ y) = φ := by funext y; simp [vEta]
  unfold coordTranspose
  rw [Fin.sum_univ_three, e0, e1, e2]
  simp [cpd, dZero]

theorem coordT_eta_isCoordTest {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (coordTranspose vEta dZero φ) := by
  have hcpd2 : ContDiff ℝ ∞ (cpd 2 φ) := by
    unfold cpd
    exact (hφ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hform : coordTranspose vEta dZero φ = fun m => -cpd 2 φ m :=
    funext (coordT_eta_eq φ)
  have hout : ∀ m, m ∉ tsupport φ → coordTranspose vEta dZero φ m = 0 := by
    intro m hm
    obtain ⟨_, hd⟩ := zero_of_nmem_tsupport hm
    rw [coordT_eta_eq]
    simp [cpd, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hform]
    exact hcpd2.neg
  · exact HasCompactSupport.intro hφ.compact.isCompact (fun m hm => hout m hm)
  · have hsub : tsupport (coordTranspose vEta dZero φ) ⊆ tsupport φ := by
      refine closure_minimal ?_ (isClosed_tsupport φ)
      intro m hm
      by_contra hn
      exact hm (hout m hn)
    exact hsub.trans hφ.supp

theorem neg_dy2_tstZ {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (i : Fin 2) {x : ℝ × Space} (hy : x.2 ∉ Axi.axis) :
    -(dy 2 (tstZ c ε (3 / 2) φ i) x) =
      (ctLift c ε 2 (coordTranspose vEta dZero φ) x) • realCL (Evec i x.2) := by
  rw [dy2_tstZ hc hε hφ i hy]
  have hz := ct_deriv_z (a := 3 / 2) hc hε hφ x.1 x.2 hy
  have h2 : (3 / 2 + 1 / 2 : ℝ) = 2 := by norm_num
  rw [h2] at hz
  simp only [Prod.mk.eta] at hz
  rw [hz]
  have hT : (fun m => -cpd 2 φ m) = coordTranspose vEta dZero φ :=
    (funext (coordT_eta_eq φ)).symm
  rw [← neg_smul, ← ctLift_neg, hT]

end UnforcedLeray.Short.IIb.GWZ

open UnforcedLeray.Short.IIb.GWZ

theorem gwZ : UnforcedLeray.Short.IIb.GWZ := by
  intro c ε r b g Qb Eb hc hε hr1 hr3 hb hgY hgp hEp hEm hE
  have hr0 : 0 < r := by linarith
  have hEHr : InHr c r (sqrtS Eb) := inHr_sqrtS_z hc hε hr1 (hgY 2) hEp hEm hE
  have hbBox := hrBoxIntegrable c r b hc hr1 hb
  have hEBox := hrBoxIntegrable c r (sqrtS Eb) hc hr1 hEHr
  have hax : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), x.2 ∉ Axi.axis := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae Axi.ae_not_mem_axis
  intro i
  have hIntB : ∀ φ, IsCoordTest φ →
      Integrable (fun x : Coord => b x i * (coordTranspose vEta dZero φ x : ℂ)) := by
    intro φ hφ
    have hT := coordT_eta_isCoordTest hφ
    obtain ⟨a0, Q, ha0, hz⟩ := coord_box hT
    exact integrable_box_mul (fun σ H R L hσ => hbBox σ H R L hσ i) ha0
      hT.smooth.continuous.continuousOn hz
  have hIntE : ∀ φ, IsCoordTest φ → Integrable (fun x : Coord => Eb x i * (φ x : ℂ)) := by
    intro φ hφ
    obtain ⟨a0, Q, ha0, hz⟩ := coord_box hφ
    have hψ : ContinuousOn (fun x : Coord => x.1 ^ (-(1 / 2 : ℝ)) * φ x)
        (Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)) := by
      refine ContinuousOn.mul ?_ hφ.smooth.continuous.continuousOn
      exact (continuous_fst.continuousOn).rpow_const
        (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha0 hx.1.1)))
    have h := integrable_box_mul (fun σ H R L hσ => hEBox σ H R L hσ i) ha0 hψ
      (fun x hx => hz x (by intro h; apply hx; simp [h]))
    refine h.congr (Eventually.of_forall fun x => ?_)
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hpos : 0 < x.1 := lt_of_lt_of_le ha0 (hz x hφx).1.1
      have h1 : Real.sqrt x.1 * x.1 ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]; norm_num
      have hc2 : ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
        exact_mod_cast h1
      simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      linear_combination (Eb x i * (φ x : ℂ)) * hc2
  have hMain : ∀ φ, IsCoordTest φ →
      ∫ x : Coord, Eb x i * (φ x : ℂ) =
        ∫ x : Coord, b x i * (coordTranspose vEta dZero φ x : ℂ) := by
    intro φ hφ
    have hT := coordT_eta_isCoordTest hφ
    set T := coordTranspose vEta dZero φ with hTdef
    have hΦ : IsPhaseTest (2 * ε * c) (tstZ c ε (3 / 2) φ i) := tstZ_isPhaseTest hc hε hφ i
    have hgp2 : pairF (2 * ε * c) (-(dy 2 (tstZ c ε (3 / 2) φ i))) (NvC ε⁻¹ b) =
        pairF (2 * ε * c) (tstZ c ε (3 / 2) φ i) (g 2) := hgp 2 _ hΦ
    have hLHS : pairF (2 * ε * c) (-(dy 2 (tstZ c ε (3 / 2) φ i))) (NvC ε⁻¹ b) =
        ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((2 : ℝ) - 2) : ℝ)) : ℂ) * b x i * (T x : ℂ) := by
      have h1 : pairF (2 * ε * c) (-(dy 2 (tstZ c ε (3 / 2) φ i))) (NvC ε⁻¹ b) =
          pairF (2 * ε * c) (fun x => ((ctLift c ε 2 T x : ℝ) : ℂ) • frameC i x.2)
            (NvC ε⁻¹ b) := by
        unfold pairF
        refine phaseInt_congr_ae ?_
        filter_upwards [hax] with x hx
        have e := neg_dy2_tstZ hc hε hφ i hx
        simp only [Pi.neg_apply]
        rw [e, frameC_eq, Complex.coe_smul]
      rw [h1]
      exact ct_pair c ε r 2 T b i hc hε hr1 hr3 hT hb
    have hRHS : pairF (2 * ε * c) (tstZ c ε (3 / 2) φ i) (g 2) =
        ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * sqrtS Eb x i * (φ x : ℂ) := by
      have h2 : pairF (2 * ε * c) (tstZ c ε (3 / 2) φ i) (g 2) =
          pairF (2 * ε * c) (fun x => ((ctLift c ε (3 / 2) φ x : ℝ) : ℂ) • frameC i x.2)
            (NvC ε⁻¹ (sqrtS Eb)) := by
        unfold pairF
        refine phaseInt_congr_ae ?_
        filter_upwards [hE] with x hx
        rw [tstZ_eq, hx]
      rw [h2]
      exact ct_pair c ε r (3 / 2) φ (sqrtS Eb) i hc hε hr1 hr3 hφ hEHr
    have hkey : ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((2 : ℝ) - 2) : ℝ)) : ℂ) * b x i * (T x : ℂ) =
        ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * sqrtS Eb x i * (φ x : ℂ) := by
      rw [← hLHS, ← hRHS, hgp2]
    have hk : ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) ≠ 0 := by
      have : (Real.pi * ε⁻¹ ^ 2 / c : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hkey' := mul_left_cancel₀ hk hkey
    have eL : ∫ x : Coord, Eb x i * (φ x : ℂ) =
        ∫ x : Coord, (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * sqrtS Eb x i * (φ x : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hφx : φ x = 0
      · simp [hφx]
      · obtain ⟨a0, Q, ha0, hz⟩ := coord_box hφ
        have hpos : 0 < x.1 := lt_of_lt_of_le ha0 (hz x hφx).1.1
        have h1 : x.1 ^ ((3 / 2 : ℝ) - 2) * Real.sqrt x.1 = 1 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]; norm_num
        have hc2 : (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = 1 := by
          exact_mod_cast h1
        simp only [sqrtS, PiLp.smul_apply, smul_eq_mul]
        linear_combination (-(Eb x i * (φ x : ℂ))) * hc2
    have eR' : ∫ x : Coord, (((x.1 ^ ((2 : ℝ) - 2) : ℝ)) : ℂ) * b x i * (T x : ℂ) =
        ∫ x : Coord, b x i * (T x : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp
    rw [eL, ← hkey', eR']
  exact ⟨fun φ hφ => ⟨hIntB φ hφ, hIntE φ hφ⟩, fun φ hφ => hMain φ hφ⟩

#print axioms gwZ
