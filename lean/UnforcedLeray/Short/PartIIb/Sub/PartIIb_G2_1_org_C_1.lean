import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_1.WeakRealPer
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_1.NiceKOut
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_1.DivMoll
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopYoungLateBounds.BoundFromChart
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!
# Part II-b, `PartII-b:G2/1/org/C/1`: `PhysKOutCand`

Source of record: `the November 2 reference manuscript` (SP), lines 2007–2012
(`K_ε = s B_ε T_ε`) and 2432–2437 (global late bound from young + late profile bounds and
`bg:profile-graph`).

Given `F, b ∈ H_p` with `b` real (`im = 0`) and `GraphBound p.ν p.c bgp p.ε C_phys F b`, we project
the weak derivatives `Qb₀, Eb₀` onto their real parts `Qb := reProj Qb₀`, `Eb := reProj Eb₀`
(`WeakRealPer.lean`) and form the chart candidate `g₀ := kOutChart p b Qb Eb`.
1. Combining `rawProf_young_chartJet` on `0 < s ≤ 1` with `rawProfileLate` (`S = 1`) on `s > 1`
   gives `lateProfileQuantity p.ε (rawProf p) x ≤ L` globally on `s > 0`, where
   `L = C_L * (p.ν ^ k_L)⁻¹`.
2. Pointwise control `kOutChart_norm_le_lateProfileQuantity` + `eLpNorm_restrict_le_graph` (`S = univ`)
   yields `InHr p.c bgp g₀` and `hNorm p.c bgp g₀ ≤ ENNReal.ofReal (CK * (p.ν ^ k)⁻¹) * hNorm p.c bgp F`.
3. `divApproxW_proof` approximates `(b, Qb, Eb)` in `DivCloseW` by nice triples `(bn n, Qbn n, Ebn n)`,
   for each of which `isKOut_niceProf` (`NiceKOut.lean`) gives
   `IsKOut p (bn n) (kOutChart p (bn n) (Qbn n) (Ebn n))`; passing to the limit on both sides via
   `driftPairCont_proof` (using `isPhaseTest_convT_raw` from `PartIIIb.Concrete.rawJointSmooth`)
   yields `IsKOut p b g₀`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open PhysKOutCandHelp

private theorem hNorm_kOutChart_le_of_late {p : Params} {d dm dp L : ℝ}
    (hreg : BgRegime p d dm dp) (hL0 : 0 ≤ L)
    (hptL : ∀ x : Coord, 0 < x.1 → lateProfileQuantity p.ε (rawProf p) x ≤ L)
    (b Qb Eb : CProf)
    (hb_m : AEStronglyMeasurable b (hMeas p.c bgp))
    (hQb_m : AEStronglyMeasurable (sqrtS Qb) (hMeas p.c bgp))
    (hEb_m : AEStronglyMeasurable (sqrtS Eb) (hMeas p.c bgp)) :
    hNorm p.c bgp (kOutChart p b Qb Eb) ≤
      ENNReal.ofReal L * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) +
        ENNReal.ofReal (2 * L) * hNorm p.c bgp b := by
  have _ := hreg
  have hRes := eLpNorm_restrict_le_graph p.c_pos (kOutChart p b Qb Eb) b Qb Eb
    hb_m hQb_m hEb_m univ MeasurableSet.univ hL0 (by positivity)
    (fun x _ hx0 =>
      PhysKopYLHelp.kOutChart_norm_le_lateProfileQuantity p b Qb Eb hx0 p.ε_pos.le (hptL x hx0))
  simpa [hNorm, Measure.restrict_univ] using hRes

private theorem s_rawProf0_le_of_late {p : Params} {L : ℝ} {x : Coord}
    (hx0 : 0 < x.1) (hptL : lateProfileQuantity p.ε (rawProf p) x ≤ L) :
    |x.1 * rawProf p x 0| ≤ p.ε⁻¹ * L := by
  have hε_pos : 0 < p.ε := p.ε_pos
  have hsu : 0 ≤ Real.sqrt x.1 * ‖rawProf p x‖ := by positivity
  have hgrad : x.1 * (‖Axi.dEta (rawProf p) x‖ + ‖qEps p.ε (rawProf p) x‖ +
      p.ε * |rawProf p x 0|) ≤ L := by
    unfold lateProfileQuantity at hptL
    have heq : gradProfileQuantity p.ε (rawProf p) x =
        x.1 * (‖Axi.dEta (rawProf p) x‖ + ‖qEps p.ε (rawProf p) x‖ +
          p.ε * |rawProf p x 0|) := rfl
    rw [heq] at hptL
    linarith
  have h1 : x.1 * (p.ε * |rawProf p x 0|) ≤ L := by
    have hnn : 0 ≤ ‖Axi.dEta (rawProf p) x‖ + ‖qEps p.ε (rawProf p) x‖ := by positivity
    have hle : p.ε * |rawProf p x 0| ≤
        ‖Axi.dEta (rawProf p) x‖ + ‖qEps p.ε (rawProf p) x‖ + p.ε * |rawProf p x 0| := by linarith
    exact (mul_le_mul_of_nonneg_left hle hx0.le).trans hgrad
  rw [abs_mul, abs_of_pos hx0]
  calc x.1 * |rawProf p x 0|
      = p.ε⁻¹ * (x.1 * (p.ε * |rawProf p x 0|)) := by field_simp
    _ ≤ p.ε⁻¹ * L := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hε_pos.le)

private theorem kOutChart_diff_split (p : Params) (b Qb Eb b' Qb' Eb' G H : CProf)
    (hGH : ∀ x, Qb' x - Qb x = G x + H x) (x : Coord) :
    kOutChart p b' Qb' Eb' x - kOutChart p b Qb Eb x =
      kOutChart p (fun y => b' y - b y) G (fun y => Eb' y - Eb y) x +
        ((x.1 * rawProf p x 0 : ℝ) : ℂ) • H x := by
  have hQ : ∀ i : Fin 2, Qb' x i = Qb x i + G x i + H x i := fun i => by
    have hi := congrArg (fun m : CMerid => m i) (hGH x)
    simp only [PiLp.sub_apply, PiLp.add_apply] at hi
    linear_combination hi
  ext i
  simp only [kOutChart, hQ, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]
  ring

private theorem tendsto_zero_of_le_inv_succ {f : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hle : ∀ n : ℕ, f n ≤ M * ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    Tendsto f atTop (𝓝 0) := by
  have hlim_real : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlim_enn : Tendsto (fun n : ℕ => M * ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim_real
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hM)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_enn
    (fun _ => bot_le) hle

/-- **`PartII-b:G2/1/org/C/1`**: existence and global late bound of the physical interaction
candidate `g₀ = kOutChart p b Qb Eb` (SP 2007–2012, 2432–2437). -/
theorem physKOutCand : PhysKOutCand := by
  intro dm dp hdm _C_late _k_late C_phys _hCl hCp
  obtain ⟨C_y, k_y, ν_y, hC_y, hν_y, hYoung⟩ := PhysKopYLHelp.rawProf_young_chartJet
  obtain ⟨C_rl, k_rl, ν_rl, hC_rl, hν_rl, hLateProf⟩ := rawProfileLate dm dp hdm
  obtain ⟨ν_raw, hν_raw, Hraw⟩ := UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth dm dp hdm
  set C_L : ℝ := max (3 * C_y) (2 * C_rl)
  set k_L : ℕ := max k_y k_rl
  set CK : ℝ := 3 * C_phys * C_L
  set k : ℕ := k_L + 1
  set ν₀ : ℝ := min (min ν_y ν_rl) (min ν_raw 1)
  have hC_L : 0 < C_L := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCK : 0 < CK := by positivity
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_y hν_rl) (lt_min hν_raw one_pos)
  refine ⟨ν₀, CK, k, hν₀, hCK, ?_⟩
  intro p d hreg hν hε1 _hper _hlate F b hF hb hbr hG
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hε_pos : 0 < p.ε := p.ε_pos
  have hν_y' : p.ν ≤ ν_y := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_rl' : p.ν ≤ ν_rl := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_raw' : p.ν ≤ ν_raw := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hraw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) := Hraw p d hreg hν_raw'
  -- 1. Global bound `lateProfileQuantity p.ε (rawProf p) x ≤ L` on `s > 0`
  set L : ℝ := C_L * (p.ν ^ k_L)⁻¹
  have hL_pos : 0 < L := by positivity
  have hptL : ∀ x : Coord, 0 < x.1 → lateProfileQuantity p.ε (rawProf p) x ≤ L := by
    intro x hx0
    by_cases hx1 : x.1 ≤ 1
    · have hJ := hYoung p d dm dp hreg hν_y' x hx0 hx1
      have hpow : (p.ν ^ k_y)⁻¹ ≤ (p.ν ^ k_L)⁻¹ :=
        inv_anti₀ (pow_pos hν_pos k_L) (pow_le_pow_of_le_one hν_pos.le hν1 (le_max_left k_y k_rl))
      have hCle : 3 * C_y ≤ C_L := le_max_left _ _
      calc lateProfileQuantity p.ε (rawProf p) x
          ≤ 3 * chartJet (rawProf p) x * Real.sqrt 1 :=
            PhysKopYLHelp.lateProfileQuantity_le_young (rawProf p) hx0.le hx1 le_rfl hε_pos.le hε1
        _ ≤ 3 * (C_y * (p.ν ^ k_y)⁻¹) * 1 := by rw [Real.sqrt_one]; gcongr
        _ = (3 * C_y) * (p.ν ^ k_y)⁻¹ := by ring
        _ ≤ C_L * (p.ν ^ k_L)⁻¹ := by gcongr
    · have hx1' : x ∈ lateAgeSet 1 := not_le.mp hx1
      have hLP := (hLateProf p d hreg hν_rl' 1 le_rfl x hx1').2
      have hpow : (p.ν ^ k_rl)⁻¹ ≤ (p.ν ^ k_L)⁻¹ :=
        inv_anti₀ (pow_pos hν_pos k_L) (pow_le_pow_of_le_one hν_pos.le hν1 (le_max_right k_y k_rl))
      have hCle : 2 * C_rl ≤ C_L := le_max_right _ _
      calc lateProfileQuantity p.ε (rawProf p) x
          ≤ C_rl * (p.ν ^ k_rl)⁻¹ * ((1 : ℝ) ^ (-(1 / 2 : ℝ)) + p.ε) := hLP
        _ ≤ C_rl * (p.ν ^ k_rl)⁻¹ * (1 + 1) := by rw [Real.one_rpow]; gcongr
        _ = (2 * C_rl) * (p.ν ^ k_rl)⁻¹ := by ring
        _ ≤ C_L * (p.ν ^ k_L)⁻¹ := by gcongr
  -- 2. Real-projected weak derivatives `Qb, Eb` and `DivData`
  obtain ⟨Sb, Qb₀, Eb₀, _hSb, hQb₀, hEb₀, hGnorm⟩ := hG
  set Qb : CProf := reProj Qb₀
  set Eb : CProf := reProj Eb₀
  have hQb : HasWeakVec (vQ p.ε) (dQ p.ε) b Qb := hasWeakVec_reProj hbr hQb₀
  have hEb : HasWeakVec vEta dZero b Eb := hasWeakVec_reProj hbr hEb₀
  have hQb_per : QPeriodic p.c Qb :=
    hasWeakVec_qPeriodic (fun _ => rfl) (fun _ => rfl) hb.periodic hQb
  have hEb_per : QPeriodic p.c Eb :=
    hasWeakVec_qPeriodic (fun _ => rfl) (fun _ => rfl) hb.periodic hEb
  have hsq_cont : Continuous fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)
  have hQb_m : AEStronglyMeasurable Qb (hMeas p.c bgp) :=
    HasWeakVec.aestronglyMeasurable_hMeas hQb
  have hEb_m : AEStronglyMeasurable Eb (hMeas p.c bgp) :=
    HasWeakVec.aestronglyMeasurable_hMeas hEb
  have hsQb_m : AEStronglyMeasurable (sqrtS Qb) (hMeas p.c bgp) :=
    hsq_cont.aestronglyMeasurable.smul hQb_m
  have hsEb_m : AEStronglyMeasurable (sqrtS Eb) (hMeas p.c bgp) :=
    hsq_cont.aestronglyMeasurable.smul hEb_m
  have hGnorm_re : hNorm p.c bgp b + hNorm p.c bgp Sb +
      ENNReal.ofReal (Real.sqrt p.ν) * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) ≤
      ENNReal.ofReal C_phys * hNorm p.c bgp F := by
    have h1 := hNorm_sqrtS_reProj_le (c := p.c) (r := bgp) Qb₀
    have h2 := hNorm_sqrtS_reProj_le (c := p.c) (r := bgp) Eb₀
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add h1 h2) bot_le)).trans hGnorm
  have hFin_RHS : ENNReal.ofReal C_phys * hNorm p.c bgp F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  have hsqrt_pos : 0 < ENNReal.ofReal (Real.sqrt p.ν) :=
    ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hν_pos)
  have hsQ_fin : hNorm p.c bgp (sqrtS Qb) < ⊤ := by
    have hprod : ENNReal.ofReal (Real.sqrt p.ν) * hNorm p.c bgp (sqrtS Qb) < ⊤ :=
      lt_of_le_of_lt ((mul_le_mul_of_nonneg_left le_self_add bot_le).trans
        (le_add_self.trans hGnorm_re)) hFin_RHS
    by_contra htop
    rw [top_le_iff.mp (not_lt.mp htop), ENNReal.mul_top hsqrt_pos.ne'] at hprod
    exact lt_irrefl _ hprod
  have hsE_fin : hNorm p.c bgp (sqrtS Eb) < ⊤ := by
    have hprod : ENNReal.ofReal (Real.sqrt p.ν) * hNorm p.c bgp (sqrtS Eb) < ⊤ :=
      lt_of_le_of_lt ((mul_le_mul_of_nonneg_left le_add_self bot_le).trans
        (le_add_self.trans hGnorm_re)) hFin_RHS
    by_contra htop
    rw [top_le_iff.mp (not_lt.mp htop), ENNReal.mul_top hsqrt_pos.ne'] at hprod
    exact lt_irrefl _ hprod
  have hd : DivData p.c bgp p.ε b Qb Eb :=
    ⟨hb, hQb, hEb,
      ⟨qPeriodic_sqrtS hQb_per, hsQb_m, hsQ_fin⟩,
      ⟨qPeriodic_sqrtS hEb_per, hsEb_m, hsE_fin⟩⟩
  -- 3. Candidate `g₀ := kOutChart p b Qb Eb`: norm bound, `InHr`, and realness
  set g₀ : CProf := kOutChart p b Qb Eb
  have hg₀_per : QPeriodic p.c g₀ := kOutChart_qPeriodic p hb.periodic hQb_per hEb_per
  have hg₀_m : AEStronglyMeasurable g₀ (hMeas p.c bgp) :=
    kOutChart_aestronglyMeasurable hreg hb.meas hQb_m hEb_m
  have hg₀_im : ∀ x i, (g₀ x i).im = 0 :=
    kOutChart_im_zero p hbr (reProj_im_zero Qb₀) (reProj_im_zero Eb₀)
  have hν_le_sqrt : p.ν ≤ Real.sqrt p.ν := by
    calc p.ν = Real.sqrt p.ν * Real.sqrt p.ν := (Real.mul_self_sqrt hν_pos.le).symm
      _ ≤ 1 * Real.sqrt p.ν :=
          mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt hν1) (Real.sqrt_nonneg _)
      _ = Real.sqrt p.ν := one_mul _
  have hν_inv_ge_one : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hν_pos).mpr hν1
  have hb_bound : hNorm p.c bgp b ≤ ENNReal.ofReal (C_phys * p.ν⁻¹) * hNorm p.c bgp F := by
    have h1 : hNorm p.c bgp b ≤ ENNReal.ofReal C_phys * hNorm p.c bgp F :=
      (le_self_add.trans le_self_add).trans hGnorm_re
    refine h1.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
    nlinarith
  have hgrad_bound : hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb) ≤
      ENNReal.ofReal (C_phys * p.ν⁻¹) * hNorm p.c bgp F := by
    have h1 : ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) ≤
        ENNReal.ofReal C_phys * hNorm p.c bgp F := by
      calc ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))
          ≤ ENNReal.ofReal (Real.sqrt p.ν) *
              (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hν_le_sqrt) bot_le
        _ ≤ hNorm p.c bgp b + hNorm p.c bgp Sb +
              ENNReal.ofReal (Real.sqrt p.ν) *
                (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := le_add_self
        _ ≤ ENNReal.ofReal C_phys * hNorm p.c bgp F := hGnorm_re
    have h_inv_mul : ENNReal.ofReal p.ν⁻¹ * ENNReal.ofReal p.ν = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le), inv_mul_cancel₀ hν_pos.ne',
        ENNReal.ofReal_one]
    calc hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)
        = 1 * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) := (one_mul _).symm
      _ = ENNReal.ofReal p.ν⁻¹ *
            (ENNReal.ofReal p.ν * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb))) := by
          rw [← mul_assoc, h_inv_mul]
      _ ≤ ENNReal.ofReal p.ν⁻¹ * (ENNReal.ofReal C_phys * hNorm p.c bgp F) :=
          mul_le_mul_of_nonneg_left h1 bot_le
      _ = ENNReal.ofReal (C_phys * p.ν⁻¹) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hν_pos.le), mul_comm p.ν⁻¹ C_phys]
  have hg₀_bound : hNorm p.c bgp g₀ ≤ ENNReal.ofReal (CK * (p.ν ^ k)⁻¹) * hNorm p.c bgp F := by
    have h1 := hNorm_kOutChart_le_of_late hreg hL_pos.le hptL b Qb Eb hb.meas hsQb_m hsEb_m
    have hCK_eq : ENNReal.ofReal L * ENNReal.ofReal (C_phys * p.ν⁻¹) +
        ENNReal.ofReal (2 * L) * ENNReal.ofReal (C_phys * p.ν⁻¹) =
        ENNReal.ofReal (CK * (p.ν ^ k)⁻¹) := by
      rw [← ENNReal.ofReal_mul hL_pos.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp [L, CK, k]
      rw [pow_add, pow_one, mul_inv]
      ring
    calc hNorm p.c bgp g₀
        ≤ ENNReal.ofReal L * (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) +
            ENNReal.ofReal (2 * L) * hNorm p.c bgp b := h1
      _ ≤ ENNReal.ofReal L * (ENNReal.ofReal (C_phys * p.ν⁻¹) * hNorm p.c bgp F) +
            ENNReal.ofReal (2 * L) * (ENNReal.ofReal (C_phys * p.ν⁻¹) * hNorm p.c bgp F) :=
          add_le_add (mul_le_mul_of_nonneg_left hgrad_bound bot_le)
            (mul_le_mul_of_nonneg_left hb_bound bot_le)
      _ = (ENNReal.ofReal L * ENNReal.ofReal (C_phys * p.ν⁻¹) +
            ENNReal.ofReal (2 * L) * ENNReal.ofReal (C_phys * p.ν⁻¹)) * hNorm p.c bgp F := by
          rw [← mul_assoc, ← mul_assoc, ← add_mul]
      _ = ENNReal.ofReal (CK * (p.ν ^ k)⁻¹) * hNorm p.c bgp F := by rw [hCK_eq]
  have hg₀_in : InHr p.c bgp g₀ :=
    ⟨hg₀_per, hg₀_m,
      lt_of_le_of_lt hg₀_bound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite)⟩
  -- 4. `IsKOut p b g₀` by passing through `divApproxW_bgp`
  have hbgp1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]; norm_num [bgp]
  obtain ⟨bn, Qbn, Ebn, hbn, hclose⟩ :=
    PhysKOutCandMoll.divApproxW_bgp p.c p.ε b Qb Eb hc_pos hε_pos hd
  set gn : ℕ → CProf := fun n => kOutChart p (bn n) (Qbn n) (Ebn n)
  have hgn_in : ∀ n, InHr p.c bgp (gn n) := by
    intro n
    have hdn := (hbn n).2
    have hQbn_per : QPeriodic p.c (Qbn n) :=
      hasWeakVec_qPeriodic (fun _ => rfl) (fun _ => rfl) hdn.inHr.periodic hdn.weakQ
    have hEbn_per : QPeriodic p.c (Ebn n) :=
      hasWeakVec_qPeriodic (fun _ => rfl) (fun _ => rfl) hdn.inHr.periodic hdn.weakE
    have hQbn_m : AEStronglyMeasurable (Qbn n) (hMeas p.c bgp) :=
      HasWeakVec.aestronglyMeasurable_hMeas hdn.weakQ
    have hEbn_m : AEStronglyMeasurable (Ebn n) (hMeas p.c bgp) :=
      HasWeakVec.aestronglyMeasurable_hMeas hdn.weakE
    have hgn_bd := hNorm_kOutChart_le_of_late hreg hL_pos.le hptL (bn n) (Qbn n) (Ebn n)
      hdn.inHr.meas hdn.inQ.meas hdn.inE.meas
    have hgn_fin : hNorm p.c bgp (gn n) < ⊤ :=
      lt_of_le_of_lt hgn_bd (ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.add_lt_top.mpr ⟨hdn.inQ.finite, hdn.inE.finite⟩),
         ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdn.inHr.finite⟩)
    exact ⟨kOutChart_qPeriodic p hdn.inHr.periodic hQbn_per hEbn_per,
      kOutChart_aestronglyMeasurable hreg hdn.inHr.meas hQbn_m hEbn_m, hgn_fin⟩
  have hgn_tendsto : Tendsto (fun n => hNorm p.c bgp (fun x => gn n x - g₀ x)) atTop (𝓝 0) := by
    set M : ℝ≥0∞ := ENNReal.ofReal (4 * L + p.ε⁻¹ * L)
    refine tendsto_zero_of_le_inv_succ (M := M) ENNReal.ofReal_ne_top (fun n => ?_)
    have hdn := (hbn n).2
    obtain ⟨hb_lt, ⟨Gn, Hn, hGn, hHn, hGHn, hGH_lt⟩, hE_lt⟩ := hclose n
    set δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ_pos : 0 < δ := by positivity
    have hQbn_m : AEStronglyMeasurable (Qbn n) (hMeas p.c bgp) :=
      HasWeakVec.aestronglyMeasurable_hMeas hdn.weakQ
    have hGn_m : AEStronglyMeasurable Gn (hMeas p.c bgp) := by
      have heq : Gn = fun x => (Qbn n x - Qb x) - Hn x :=
        funext fun x => eq_sub_of_add_eq (hGHn x).symm
      rw [heq]
      exact (hQbn_m.sub hQb_m).sub hHn.meas
    set term1 : CProf := kOutChart p (fun y => bn n y - b y) Gn (fun y => Ebn n y - Eb y)
    set term2 : CProf := fun x => ((x.1 * rawProf p x 0 : ℝ) : ℂ) • Hn x
    have hterm1_m : AEStronglyMeasurable term1 (hMeas p.c bgp) :=
      kOutChart_aestronglyMeasurable hreg (hdn.inHr.meas.sub hb.meas) hGn_m
        ((HasWeakVec.aestronglyMeasurable_hMeas hdn.weakE).sub hEb_m)
    have hs_raw0_m : AEStronglyMeasurable (fun x : Coord => ((x.1 * rawProf p x 0 : ℝ) : ℂ))
        (hMeas p.c bgp) := by
      have hae : ∀ᵐ x ∂hMeas p.c bgp, x ∈ {x : Coord | 0 < x.1} :=
        (Axi.ae_ageμ_mem hc_pos (bgp / 2 - 5 / 2)).mono fun _ hx => hx.1
      -- obtain continuity on `{s > 0}` via `rawProfDiffAt` (`DifferentiableAt.continuousAt`)
      have hcont : ContinuousOn (fun x : Coord => ((x.1 * rawProf p x 0 : ℝ) : ℂ))
          {x : Coord | 0 < x.1} := by
        have hc0 : ContinuousOn (rawProf p) {x : Coord | 0 < x.1} := fun x hx =>
          (rawProfDiffAt dm dp p d hreg x hx).continuousAt.continuousWithinAt
        have hc1 : ContinuousOn (fun x : Coord => rawProf p x 0) {x : Coord | 0 < x.1} :=
          (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).continuous.comp_continuousOn hc0
        exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_fst.mul hc1)
      rw [← Measure.restrict_eq_self_of_ae_mem hae]
      exact hcont.aestronglyMeasurable (measurableSet_lt measurable_const measurable_fst)
    have hterm2_m : AEStronglyMeasurable term2 (hMeas p.c bgp) := hs_raw0_m.smul hHn.meas
    have hsplit : (fun x => gn n x - g₀ x) = term1 + term2 :=
      funext (kOutChart_diff_split p b Qb Eb (bn n) (Qbn n) (Ebn n) Gn Hn hGHn)
    have htri : hNorm p.c bgp (fun x => gn n x - g₀ x) ≤
        hNorm p.c bgp term1 + hNorm p.c bgp term2 := by
      unfold hNorm; rw [hsplit]; exact eLpNorm_add_le hterm1_m hterm2_m hp1
    have hsE_sub_m : AEStronglyMeasurable (sqrtS fun y => Ebn n y - Eb y) (hMeas p.c bgp) :=
      hsq_cont.aestronglyMeasurable.smul
        ((HasWeakVec.aestronglyMeasurable_hMeas hdn.weakE).sub hEb_m)
    have ht1_le : hNorm p.c bgp term1 ≤ ENNReal.ofReal (4 * L) * ENNReal.ofReal δ := by
      have h1 := hNorm_kOutChart_le_of_late hreg hL_pos.le hptL
        (fun y => bn n y - b y) Gn (fun y => Ebn n y - Eb y)
        (hdn.inHr.meas.sub hb.meas) hGn.meas hsE_sub_m
      have hGn_le : hNorm p.c bgp (sqrtS Gn) ≤ ENNReal.ofReal δ :=
        le_self_add.trans hGH_lt.le
      calc hNorm p.c bgp term1
          ≤ ENNReal.ofReal L * (hNorm p.c bgp (sqrtS Gn) +
              hNorm p.c bgp (sqrtS fun y => Ebn n y - Eb y)) +
              ENNReal.ofReal (2 * L) * hNorm p.c bgp (fun y => bn n y - b y) := h1
        _ ≤ ENNReal.ofReal L * (ENNReal.ofReal δ + ENNReal.ofReal δ) +
              ENNReal.ofReal (2 * L) * ENNReal.ofReal δ :=
            add_le_add (mul_le_mul_of_nonneg_left (add_le_add hGn_le hE_lt.le) bot_le)
              (mul_le_mul_of_nonneg_left hb_lt.le bot_le)
        _ = ENNReal.ofReal (4 * L) * ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_add hδ_pos.le hδ_pos.le,
              ← ENNReal.ofReal_mul hL_pos.le, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    have ht2_le : hNorm p.c bgp term2 ≤ ENNReal.ofReal (p.ε⁻¹ * L) * ENNReal.ofReal δ := by
      set A : ℝ := p.ε⁻¹ * L
      have hA_nn : 0 ≤ A := by positivity
      have hae_pt : ∀ᵐ x ∂(hMeas p.c bgp), ‖term2 x‖ ≤ ‖(A • fun y => ‖Hn y‖) x‖ := by
        filter_upwards [(Axi.ae_ageμ_mem hc_pos (bgp / 2 - 5 / 2)).mono fun _ hx => hx.1]
          with x hx0
        have hnn : 0 ≤ A * ‖Hn x‖ := by positivity
        change ‖((x.1 * rawProf p x 0 : ℝ) : ℂ) • Hn x‖ ≤ ‖A * ‖Hn x‖‖
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg hnn]
        exact mul_le_mul_of_nonneg_right (s_rawProf0_le_of_late hx0 (hptL x hx0)) (norm_nonneg _)
      have hmono : hNorm p.c bgp term2 ≤ ENNReal.ofReal A * hNorm p.c bgp Hn := by
        unfold hNorm
        calc eLpNorm term2 (ENNReal.ofReal bgp) (hMeas p.c bgp)
            ≤ eLpNorm (A • fun y => ‖Hn y‖) (ENNReal.ofReal bgp) (hMeas p.c bgp) :=
              eLpNorm_mono_ae hae_pt
          _ = ENNReal.ofReal A * eLpNorm Hn (ENNReal.ofReal bgp) (hMeas p.c bgp) := by
              rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA_nn]
      have hHn_le : hNorm p.c bgp Hn ≤ ENNReal.ofReal δ := le_add_self.trans hGH_lt.le
      exact hmono.trans (mul_le_mul_of_nonneg_left hHn_le bot_le)
    calc hNorm p.c bgp (fun x => gn n x - g₀ x)
        ≤ ENNReal.ofReal (4 * L) * ENNReal.ofReal δ +
            ENNReal.ofReal (p.ε⁻¹ * L) * ENNReal.ofReal δ :=
          htri.trans (add_le_add ht1_le ht2_le)
      _ = M * ENNReal.ofReal δ := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hb_tendsto : Tendsto (fun n => hNorm p.c bgp (fun x => bn n x - b x)) atTop (𝓝 0) :=
    tendsto_zero_of_le_inv_succ (M := 1) ENNReal.one_ne_top
      (fun n => by simpa using (hclose n).1.le)
  have hKOut : IsKOut p b g₀ := by
    intro Φ hΦ
    have hconv_test : IsPhaseTest p.period (convT p.raw Φ) := isPhaseTest_convT_raw hraw hΦ
    have hL_lim := driftPairCont_proof p.c bgp p.ε (convT p.raw Φ) hc_pos hε_pos hbgp1
      hconv_test b bn hb (fun n => (hbn n).2.inHr) hb_tendsto
    have hR_lim := driftPairCont_proof p.c bgp p.ε Φ hc_pos hε_pos hbgp1
      hΦ g₀ gn hg₀_in hgn_in hgn_tendsto
    have heq_n : ∀ n, pairF p.period (convT p.raw Φ) (NvC p.R (bn n)) =
        pairF p.period Φ (NvC p.R (gn n)) :=
      fun n => isKOut_niceProf hreg hraw (hbn n).1 (hbn n).2.weakQ (hbn n).2.weakE Φ hΦ
    have hL_lim' : Tendsto (fun n => pairF p.period Φ (NvC p.R (gn n))) atTop
        (𝓝 (pairF p.period (convT p.raw Φ) (NvC p.R b))) := by
      simpa only [show 2 * p.ε * p.c = p.period from rfl,
        show p.ε⁻¹ = p.R from rfl, heq_n] using hL_lim
    exact tendsto_nhds_unique hL_lim' hR_lim
  exact ⟨g₀, hg₀_in, hg₀_im, hKOut, hg₀_bound⟩

end UnforcedLeray.Short.IIb
