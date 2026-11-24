import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.RepairSource
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.Props

/-!
# `PartIII-b:C/rep/4/4/1/org/6/2`: `repair:source` for the unlocalised repair stress

Source `the November 2 reference manuscript` 5169-5176 (`F_r ≤ P_νρR|N_ν|G(w)`,
`19/22 = 4/11 + 1/2`, `g ≤ e^{γ/ν}`), 5134-5139.  The proof of `repairSource` (PartIII-b:C/rep/1)
is rerun for `repStressFull` (no cutoff `χ_o`): `(repPart T).snd = T.snd` as chart fields, so the
pointwise bound `|F| ≤ 2|r_b||𝒩_v w|` holds without the factor `cutFun`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

theorem repPart_snd_eq {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    (repPart T).snd = T.snd := by
  simp [repPart]

/-- pointwise bound for the unlocalised repair stress. -/
theorem repPhasePointwiseFull (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hC0 : 0 < K.C0) (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hax : ∀ τ, AxiNoSwirlPt (L.rb τ))
    (hper : ∀ τ y, L.rb (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.rb τ y) (w : LVel Pl L) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))), ∀ᵐ y : Space,
      UnforcedLeray.Short.IIIa.tensorNorm (repStressFull Pl K L w (τ, y)) ≤
        2 * ‖L.rb τ y‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hrhoRep : 0 < rhoRep K L := by
    unfold rhoRep
    exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
  have hρpos : 0 < L.ρb Pl K := by
    rw [rhoB_eq]
    exact mul_pos (mul_pos hC0 (pow_pos (inv_pos.2 hν) _)) hrhoRep
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have hEx2 : ((multOp Pl K L w).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K)
      (gRate Pl) L.ν] repG Pl K L w := (hEx w).2
  have hgood : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((repPart (multOp Pl K L w)).snd : Chart → Ten3) p = repG Pl K L w p := by
    rw [repPart_snd_eq]; exact hEx2
  have hgood' := hgood
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρpos] at hgood'
  have hN0 := ae_iff.mp hgood'
  have hpt := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hN0
  have hcart := cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.rb hR hc hax hper w
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      UnforcedLeray.Short.IIIa.tensorNorm (repStressFull Pl K L w x) ≤
        2 * ‖L.rb x.1 x.2‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) w x‖ := by
    filter_upwards [hpt] with x hx
    have hP : ((repPart (multOp Pl K L w)).snd : Chart → Ten3)
        (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) =
          repG Pl K L w (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) := not_not.mp hx
    have e1 : repStressFull Pl K L w x =
        NearInst.cartLift L.ε⁻¹ (cOf L.ν) ((repPart (multOp Pl K L w)).snd : Chart → Ten3)
          x.1 x.2 := rfl
    have e2 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) ((repPart (multOp Pl K L w)).snd : Chart → Ten3)
          x.1 x.2 =
        NearInst.cartLift L.ε⁻¹ (cOf L.ν) (repG Pl K L w) x.1 x.2 :=
      cartLift_congr_pt _ _ _ _ _ _ hP
    have e4 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) (repG Pl K L w) x.1 x.2 =
        symProd (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2) :=
      hcart x.1 x.2
    have hv : ‖velPhys L.ε⁻¹ (cOf L.ν) w x‖ = ‖Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2‖ :=
      wda_norm_realC _
    rw [e1, e2, e4, hv]
    exact tensorNorm_symProd_le' _ _
  rw [Measure.volume_eq_prod] at hae
  have h2 := Measure.ae_ae_of_ae_prod hae
  exact ae_restrict_of_ae h2

theorem repairProductFullAt_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (S μ : ℝ)
    (hC0 : 0 < K.C0) (hν1 : L.ν ≤ 1) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hsplit : UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hRb : RbFacts) (hmeas : VelSliceMeas) (hH : HolderPhase)
    (C1 : ℝ) (hC1 : 0 ≤ C1)
    (hV : ∀ w : LVel Pl L,
      ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2 ≤
        ENNReal.ofReal ((C1 * L.ε⁻¹ * Real.exp (gRate Pl / L.ν) * ‖w‖) ^ 2)) (w : LVel Pl L) :
    phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (repStressFull Pl K L w) ≤
      ENNReal.ofReal ((2 * K.C0 * C1) * L.ν⁻¹ ^ (K.k0 + ⌈-Pl.kappa.re⌉₊) * rhoRep K L * L.ε⁻¹ *
        gaugeN Pl L * ‖w‖) := by
  obtain ⟨hax, hper, hrbm⟩ := hRb Pl K L S hsplit hP
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hρeq := rhoB_eq Pl K L
  have hrho : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hρb : 0 ≤ L.ρb Pl K := by rw [hρeq]; positivity
  set P := 2 * L.ε * cOf L.ν with hPdef
  set X : ℝ := C1 * L.ε⁻¹ * Real.exp (gRate Pl / L.ν) * ‖w‖ with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hphase : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressFull Pl K L w (τ, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) ≤
        (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ y : Space, ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ ^ 2 := by
    filter_upwards [repPhasePointwiseFull Pl K L μ hC0 hnear hs hax hper w, hmeas Pl L w]
      with τ h1 h2
    refine le_trans (hH (L.rb τ) (fun y => velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)) _ (hrbm τ) h2 h1) ?_
    have he : eLpNorm (L.rb τ) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
        ENNReal.ofReal (L.ρb Pl K) :=
      le_trans le_self_add (hsplit.energy τ)
    rw [mul_assoc, mul_assoc]
    gcongr
  have hint : (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressFull Pl K L w (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ≤
      (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
        ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2 := by
    rw [← lintegral_const_mul']
    · exact lintegral_mono_ae hphase
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfin : ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressFull Pl K L w (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ≤
      ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
    calc _ ≤ ENNReal.ofReal P⁻¹ * ((ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2) := by gcongr
      _ = (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2) := by ring
      _ ≤ (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) * ENNReal.ofReal (X ^ 2) := by
          gcongr; exact hV w
      _ = ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow hρb,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hroot : (ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressFull Pl K L w (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * L.ρb Pl K * X) := by
    calc _ ≤ (ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hfin (by norm_num)
      _ = ENNReal.ofReal (2 * L.ρb Pl K * X) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_sq (by positivity)
  refine le_trans hroot (ENNReal.ofReal_le_ofReal ?_)
  have hg := gamma_le_gauge Pl L hν1
  have hA : 0 ≤ 2 * K.C0 * C1 * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * ‖w‖ := by positivity
  calc 2 * L.ρb Pl K * X
      = (2 * K.C0 * C1 * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * ‖w‖) *
          Real.exp (gRate Pl / L.ν) := by rw [hρeq, hX]; ring
    _ ≤ (2 * K.C0 * C1 * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * ‖w‖) *
          (L.ν⁻¹ ^ (⌈-Pl.kappa.re⌉₊) * gaugeN Pl L) := mul_le_mul_of_nonneg_left hg hA
    _ = _ := by rw [pow_add]; ring

/-- **`repair:source` for the unlocalised repair stress** (source 5169-5176). -/
theorem repairProductAll (dm dp : ℝ) : RepairProductAll dm dp := by
  intro D hst
  obtain ⟨C1, hC1, hV⟩ := velPhysL2
  refine ⟨2 * D.K.C0 * C1, D.K.k0 + ⌈-D.Pl.kappa.re⌉₊, ?_⟩
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iio_mem_nhds one_pos)
  filter_upwards [hν1, periodSmall D hst, hst.actual, hst.pins, hst.near] with n h1 h2 h3 h4 h5 w
  have h4' := h4 0 ⟨by norm_num, by norm_num⟩
  exact repairProductFullAt_level D.Pl D.K (D.level n) (D.Sin n) (D.mu n 0) hst.C0_pos h1.le h2
    h3.split (h5 0 ⟨by norm_num, by norm_num⟩) h4'.split rbFacts velSliceMeas holderPhase C1 hC1
    (fun w => hV D.Pl hst.gamma_pos.le (D.level n) w) w

end UnforcedLeray.Short.PartIIIb.Concrete
