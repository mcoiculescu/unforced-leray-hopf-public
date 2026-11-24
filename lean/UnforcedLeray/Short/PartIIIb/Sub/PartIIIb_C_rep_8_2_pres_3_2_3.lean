import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_3.Resid
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawGood
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth

/-!
# `presForcePhys` (`PartIII-b:C/rep/8/2/pres/3/2/3`)

Source of record: `the November 2 reference manuscript`:
1205-1225 (the raw lift `U_raw`, `F_R`), 4139-4141 (`D₀`), 2031 and 2522-2523 (axisymmetry), 2347
(`V - U_raw = Σ α_i inlet_i`).

Write `S = V - U_raw = Σ α_i inlet_i` (`IsBallSplit`).  The `V`-convection terms of `convChg` and
`entSrc` cancel, so
`presForce = U·∇U - U_raw·∇U_raw + D₀S + F_R`   (`pf3_presForce_eq`).
* measurability: each summand is continuous off the axis (`U`, `S` jointly `C^∞`, `U_raw` jointly
  `C^∞` off the axis, `F_R` by `Merid.lean`);
* periodicity: `IsExactProfile.periodicU`, `RawGood`, periodicity of the inlet lifts,
  `PartIIa.ringResidual_periodic`;
* axisymmetry: every summand is equivariant under the isometries fixing `e₃` off the axis, so
  `|presForce|` is invariant under the rotation moving `merPt y` to `y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- The inlet combination `S(τ) = Σ α_i inlet_i(τ)`. -/
def pf3S (p : Params) (z : p.Z) (τ : ℝ) (y : Space) : Space :=
  ∑ i : Fin 2, p.coord z i • p.inlet i τ y

theorem pf3_S_smooth (p : Params) (z : p.Z)
    (hInl : ∀ i, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => pf3S p z x.1 x.2) := by
  unfold pf3S
  exact ContDiff.sum fun i _ => (hInl i).const_smul (p.coord z i)

theorem pf3_period_eq (p : Params) : p.period = 2 * p.c / p.R := by
  have h := p.ε_pos.ne'
  unfold Params.period Params.R
  field_simp

theorem pf3_inlet_periodic (p : Params) (i : Fin 2)
    (hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) :
    Function.Periodic (p.inlet i) p.period := by
  refine UnforcedLeray.Cons.C03.periodic_of_lift (R := p.R) (c := p.c) (P := p.period)
    (b := p.inletProfile i) (f := p.inlet i) p.R_pos.ne' (pf3_period_eq p) ?_ ?_ ?_
  · exact fun s _ ξ η => p.inletProfile_periodic i s ξ η
  · intro τ y _
    unfold Params.inlet
    rfl
  · intro τ
    have h : Continuous (fun y : Space => p.inlet i τ y) :=
      Continuous.comp (g := fun x : ℝ × Space => p.inlet i x.1 x.2) (f := fun y : Space => (τ, y))
        hInl.continuous (Continuous.prodMk_right (Y := Space) τ)
    exact h

theorem pf3_S_periodic (p : Params) (z : p.Z)
    (hInl : ∀ i, ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) (τ : ℝ) :
    pf3S p z (τ + p.period) = pf3S p z τ := by
  funext y
  unfold pf3S
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pf3_inlet_periodic p i (hInl i) τ]

theorem pf3_S_equiv (p : Params) (z : p.Z) (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (τ : ℝ)
    (y : Space) : pf3S p z τ (g y) = g (pf3S p z τ y) := by
  unfold pf3S
  have : ∀ i : Fin 2, p.inlet i τ (g y) = g (p.inlet i τ y) := by
    intro i
    have h := pf3_axi_Nv p.R (p.inletProfile i) τ g hg (g y)
    rw [g.symm_apply_apply] at h
    exact h.symm
  simp only [this, map_sum, map_smul]

/-- Off the axis the raw lift's derivative term is equivariant. -/
theorem pf3_raw_equiv (p : Params) (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) (τ : ℝ)
    {y : Space} (hy : y ∉ axis) :
    fderiv ℝ (p.raw τ) (g y) (p.raw τ (g y)) = g (fderiv ℝ (p.raw τ) y (p.raw τ y)) := by
  have hgy : g y ∉ axis := by
    intro h
    exact hy ((mem_axis_iff _).2 (by rw [← pf3_varrho_apply g hg y]; exact (mem_axis_iff _).1 h))
  set N : Space → Space := Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ
    with hN
  have hev : ∀ w : Space, w ∉ axis → p.raw τ =ᶠ[𝓝 w] N := fun w hw =>
    Filter.eventuallyEq_of_mem (isOpen_compl_axis.mem_nhds hw) fun z hz =>
      p.raw_eq_off_axis τ z hz
  rw [(hev _ hgy).fderiv_eq, (hev _ hy).fderiv_eq, (hev _ hgy).eq_of_nhds, (hev _ hy).eq_of_nhds]
  exact pf3_selfAdvect_equiv (pf3_axi_Nv _ _ τ) g hg y

section Level

variable (Pl : PlanarData) (L : ReturnLevel)

/-- `presForce = U·∇U - U_raw·∇U_raw + D₀S + F_R` (the `V`-convection terms cancel). -/
theorem pf3_presForce_eq (z : (L.params Pl).Z)
    (hVS : ∀ τ y, L.V τ y = (L.params Pl).raw τ y + pf3S (L.params Pl) z τ y) (τ : ℝ) (y : Space) :
    presForce Pl L τ y = fderiv ℝ (L.U τ) y (L.U τ y) -
      fderiv ℝ ((L.params Pl).raw τ) y ((L.params Pl).raw τ y) +
      physDmu L.ν 0 (pf3S (L.params Pl) z) τ y + rawResidF Pl L τ y := by
  have hfun : (fun t y' => L.V t y' - rawU Pl L t y') = pf3S (L.params Pl) z := by
    funext t y'
    rw [hVS t y']
    show _ = _
    simp only [rawU]
    abel
  unfold presForce convChg entSrc
  rw [hfun]
  show _ = _
  simp only [rawU]
  abel

theorem pf3_presForce_equiv (z : (L.params Pl).Z)
    (hVS : ∀ τ y, L.V τ y = (L.params Pl).raw τ y + pf3S (L.params Pl) z τ y)
    (hUax : ∀ τ, AxiNoSwirlPt (L.U τ))
    (hSs : ContDiff ℝ ∞ (fun x : ℝ × Space => pf3S (L.params Pl) z x.1 x.2))
    (τ : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) {y : Space} (hy : y ∉ axis) :
    presForce Pl L τ (g y) = g (presForce Pl L τ y) := by
  rw [pf3_presForce_eq Pl L z hVS, pf3_presForce_eq Pl L z hVS]
  have tU := pf3_selfAdvect_equiv (hUax τ) g hg y
  have tR := pf3_raw_equiv (L.params Pl) g hg τ hy
  have tS : physDmu L.ν 0 (pf3S (L.params Pl) z) τ (g y) =
      g (physDmu L.ν 0 (pf3S (L.params Pl) z) τ y) :=
    dmu_gEqv fderivEqv_proved lapEqv_proved L.ν 0 (pf3S (L.params Pl) z) hSs g
      (fun t y' => pf3_S_equiv (L.params Pl) z g hg t y') τ y
  have tF := pf3_ringResidual_equiv (L.params Pl).R L.ν
    (UnforcedLeray.Short.IIb.trainStream (L.params Pl))
    (UnforcedLeray.Short.IIb.trainPressure (L.params Pl)) τ g hg y
  have tF' : rawResidF Pl L τ (g y) = g (rawResidF Pl L τ y) := tF
  rw [tU, tR, tS, tF', map_add, map_add, map_sub]

theorem pf3_physDmu_periodic (ν μ P : ℝ) (S : ℝ → Space → Space) (hS : ∀ t, S (t + P) = S t)
    (τ : ℝ) (y : Space) : physDmu ν μ S (τ + P) y = physDmu ν μ S τ y := by
  have h1 : (fun t => S (t + P) y) = fun t => S t y := funext fun t => congrFun (hS t) y
  have h2 : deriv (fun t => S t y) (τ + P) = deriv (fun t => S t y) τ := by
    rw [← deriv_comp_add_const (f := fun t => S t y) (a := P) (x := τ), h1]
  unfold physDmu
  rw [h2, hS τ]

/-- The level statement (source 1205-1225, 2031, 4139-4141). -/
theorem pf3_presForcePhysAt (z : (L.params Pl).Z)
    (hVS : ∀ τ y, L.V τ y = (L.params Pl).raw τ y + pf3S (L.params Pl) z τ y)
    (hInl : ∀ i, ContDiff ℝ ∞ (fun x : ℝ × Space => (L.params Pl).inlet i x.1 x.2))
    (hRaw : UnforcedLeray.Short.IIb.RawGood (L.params Pl))
    (hprof : IsExactProfile L.ν (2 * L.ε * cOf L.ν) L.U L.pres)
    (hUax : ∀ τ, AxiNoSwirlPt (L.U τ)) (hR : 2 ≤ L.ε⁻¹) : PresForcePhysAt Pl L := by
  have hSs := pf3_S_smooth (L.params Pl) z hInl
  refine ⟨?_, ?_, ?_⟩
  · refine pf4_axisZero_measurable (f := fun τ y => ‖presForce Pl L τ y‖) ?_
    have cU : Continuous (fun x : ℝ × Space => fderiv ℝ (L.U x.1) x.2 (L.U x.1 x.2)) := by
      have hUs : ContDiff ℝ ∞ (fun x : ℝ × Space => L.U x.1 x.2) := hprof.smoothU
      have e : ∀ x : ℝ × Space, fderiv ℝ (L.U x.1) x.2 (L.U x.1 x.2) =
          fderiv ℝ (fun x : ℝ × Space => L.U x.1 x.2) x (0, L.U x.1 x.2) := fun x =>
        pf3_partial_eq (F := fun x : ℝ × Space => L.U x.1 x.2)
          (hUs.differentiable (by simp) x) _
      have hc : Continuous (fun x : ℝ × Space =>
          fderiv ℝ (fun x : ℝ × Space => L.U x.1 x.2) x (0, L.U x.1 x.2)) :=
        ((hUs.fderiv_right (m := ∞) (by simp)).clm_apply
          (contDiff_const.prodMk hUs)).continuous
      exact hc.congr fun x => (e x).symm
    have cR : ContinuousOn (fun x : ℝ × Space => fderiv ℝ ((L.params Pl).raw x.1) x.2
        ((L.params Pl).raw x.1 x.2)) offAxisSet := by
      have hRs : ContDiffOn ℝ ∞ (fun x : ℝ × Space => (L.params Pl).raw x.1 x.2) offAxisSet :=
        hRaw.1
      have e : ∀ x ∈ offAxisSet, fderiv ℝ ((L.params Pl).raw x.1) x.2 ((L.params Pl).raw x.1 x.2) =
          fderiv ℝ (fun x : ℝ × Space => (L.params Pl).raw x.1 x.2) x
            (0, (L.params Pl).raw x.1 x.2) := fun x hx =>
        pf3_partial_eq (F := fun x : ℝ × Space => (L.params Pl).raw x.1 x.2)
          ((hRs.contDiffAt (isOpen_offAxisSet.mem_nhds hx)).differentiableAt (by simp)) _
      have hc : ContinuousOn (fun x : ℝ × Space =>
          fderiv ℝ (fun x : ℝ × Space => (L.params Pl).raw x.1 x.2) x
            (0, (L.params Pl).raw x.1 x.2)) offAxisSet :=
        (hRs.continuousOn_fderiv_of_isOpen isOpen_offAxisSet (by simp)).clm_apply
          (continuousOn_const.prodMk hRs.continuousOn)
      exact hc.congr e
    have cS := (pf3_continuous_physDmu L.ν (pf3S (L.params Pl) z) hSs).continuousOn
      (s := offAxisSet)
    have cF := pf3_rawResidF_contOn Pl L hR
    have hsum := ((cU.continuousOn.sub cR).add cS).add cF
    exact hsum.norm.congr fun x _ => by
      show ‖presForce Pl L x.1 x.2‖ = _
      rw [pf3_presForce_eq Pl L z hVS]
      rfl
  · intro τ y
    have hP : (L.params Pl).period = 2 * L.ε * cOf L.ν := rfl
    have hU : L.U (τ + 2 * L.ε * cOf L.ν) = L.U τ := funext (hprof.periodicU τ)
    have hraw : (L.params Pl).raw (τ + 2 * L.ε * cOf L.ν) = (L.params Pl).raw τ := by
      rw [← hP]; exact funext (hRaw.2.1 τ)
    have hS : pf3S (L.params Pl) z (τ + 2 * L.ε * cOf L.ν) = pf3S (L.params Pl) z τ := by
      rw [← hP]; exact pf3_S_periodic (L.params Pl) z hInl τ
    have hD := pf3_physDmu_periodic L.ν 0 (2 * L.ε * cOf L.ν) (pf3S (L.params Pl) z)
      (fun t => by rw [← hP]; exact pf3_S_periodic (L.params Pl) z hInl t) τ y
    have hF := congrFun (pf3_rawResidF_periodic Pl L hR τ) y
    show ‖presForce Pl L (τ + 2 * L.ε * cOf L.ν) y‖ = ‖presForce Pl L τ y‖
    rw [pf3_presForce_eq Pl L z hVS, pf3_presForce_eq Pl L z hVS, hU, hraw, hD, hF]
  · intro τ y
    by_cases hy : y ∈ axis
    · show ‖presForce Pl L τ y‖ = ‖presForce Pl L τ (merPt y)‖
      rw [pf4_merPt_of_mem_axis hy]
    · obtain ⟨θ, hθ⟩ := axiDens_exists_rot y
      have hg := UnforcedLeray.Axi.fixesAxis_rotZ θ
      have hmer : merPt y ∉ axis := pf_merPt_not_mem_axis hy
      have h := pf3_presForce_equiv Pl L z hVS hUax hSs τ (UnforcedLeray.Axi.rotZ θ) hg hmer
      have hy' : (UnforcedLeray.Axi.rotZ θ) (merPt y) = y := hθ
      rw [hy'] at h
      show ‖presForce Pl L τ y‖ = ‖presForce Pl L τ (merPt y)‖
      rw [h, LinearIsometryEquiv.norm_map]

end Level

theorem presForcePhys (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.PresForcePhys := by
  obtain ⟨ν₁, hν₁, hInlet⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue
    D.Pl.mode D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  obtain ⟨ν₂, hν₂, hRawG⟩ := UnforcedLeray.Short.IIb.rawGoodAll D.Sig D.Pl.eigenvalue
    D.Pl.mode D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have h1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₁ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₁)
  have h2 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₂ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₂)
  filter_upwards [hst.actual, pf2b_axiU D hst, h1, h2,
    D.pf2_eventually_regime hst (ν₀ := 1) one_pos] with n hn hU hn1 hn2 hreg
  obtain ⟨z, -, hV, -, -⟩ := hn.ball
  exact pf3_presForcePhysAt D.Pl (D.level n) z (fun τ y => hV τ y)
    (fun i => hInlet ((D.level n).params D.Pl) _ hn.regime hn1.le rfl rfl i)
    (hRawG ((D.level n).params D.Pl) _ hn.regime hn2.le rfl rfl) hn.profile hU hreg.2

end UnforcedLeray.Short.PartIIIb.Concrete
