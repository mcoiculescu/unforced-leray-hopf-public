import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_2_1
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.BroadMult
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearSolver

/-!
# `PartIII-b:C/rep/11/2/2`: the gained split multiplier is `P_ν`-bounded

Source `the November 2 reference manuscript` 2703-2713 (`stress-short:multiplier`:
the thin multiplier norm is at most `2 sup √s W|v|`, the second component at most `2√ρ_b`),
2777-2778 (common positive age weight, in particular the gain), 4029-4040.

The split multiplier `M_U` splits as `fstZ ∘ M_U + sndZ ∘ M_U`.  The thin part is bounded by
`2B` (`B = |C| ν^{-k}` from `SplitMultBound`), the broad part by `2√ρ_b ≤ 2`.  The two component
proofs are those of `NearInst.Delta.thinDiffMult` and `NearInst.Delta.broadMult` with the flat
multiplier `M_0` removed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Short.PartIIIb.NearInst.CoeffMult UnforcedLeray.Short.IIIa
  UnforcedLeray.Blueprint.Planar UnforcedLeray.Cons.C03.Concrete

private theorem fstZ_fst_aux (c mZ ρb : ℝ) (F : Zsp c mZ ρb) :
    (NearInst.Delta.fstZ c mZ ρb F).fst = F.fst := by
  simp [NearInst.Delta.fstZ, zEquiv]

private theorem fstZ_snd_aux (c mZ ρb : ℝ) (F : Zsp c mZ ρb) :
    (NearInst.Delta.fstZ c mZ ρb F).snd = 0 := by
  simp [NearInst.Delta.fstZ, zEquiv]

/-- The thin component of a split multiplier (source 4032-4040 without the flat part). -/
private theorem thin_part (c mZ ρb γ ν R B : ℝ) (hν : 0 < ν) (hc : 0 < c) (hB : 0 ≤ B)
    (V rb : ℝ → UnforcedLeray.SpatialField) (MU : Hsp c →L[ℝ] Zsp c mZ ρb)
    (hMU : NearInst.IsSplitMult MU R V rb)
    (hw : ∀ p : Chart, 0 < p.1 → Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
      ‖UnforcedLeray.Short.IIIa.chartCoeff R V p‖ ≤ B) :
    ‖NearInst.Delta.gainConjM γ hν (NearInst.Delta.fstZ c mZ ρb ∘L MU)‖ ≤ 2 * B := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith : (0 : ℝ) ≤ 2 * B) (fun u => ?_)
  have hY : NearInst.Delta.gainConjM γ hν (NearInst.Delta.fstZ c mZ ρb ∘L MU) u =
      (NearInst.gainEquiv c mZ ρb γ hν).symm
        (NearInst.Delta.fstZ c mZ ρb (MU (NearInst.gainH c γ hν u))) := rfl
  rw [hY, WithLp.prod_norm_eq_of_L1]
  set x : Hsp c := NearInst.gainH c γ hν u with hx
  have hsnd : ((NearInst.gainEquiv c mZ ρb γ hν).symm
      (NearInst.Delta.fstZ c mZ ρb (MU x))).snd = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [NearInst.Delta.gainEquiv_symm_snd c mZ ρb γ hν
        (NearInst.Delta.fstZ c mZ ρb (MU x)),
      Lp.eq_zero_iff_ae_eq_zero.1 (fstZ_snd_aux c mZ ρb (MU x))] with p hp hz0
    rw [hp, hz0]
    simp
  have hG : ((NearInst.Delta.fstZ c mZ ρb (MU x)).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
      fun p => (MU x).fst p := by
    filter_upwards with p
    rw [fstZ_fst_aux]
  have hxae : (x : Chart → Merid) =ᵐ[z1Measure c mZ]
      fun p => NearInst.gainFun γ ν p • (u : Chart → Merid) p :=
    (CoeffMult.z1_ac hc mZ).ae_le (NearInst.Delta.gainLp_ae (μ := ageμ c (-3 / 2)) γ hν u)
  have hfst : ((NearInst.gainEquiv c mZ ρb γ hν).symm
      (NearInst.Delta.fstZ c mZ ρb (MU x))).fst
      =ᵐ[z1Measure c mZ] fun p =>
        ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff R V p) ((u : Chart → Merid) p)) := by
    filter_upwards [NearInst.Delta.gainEquiv_symm_fst c mZ ρb γ hν
        (NearInst.Delta.fstZ c mZ ρb (MU x)),
      hG, (hMU x).1, hxae] with p hYp hGp hMUp hxp
    rw [hYp, hGp, hMUp, hxp]
    exact NearInst.Delta.alg_one _ _ (NearInst.gainInvFun_mul (γ := γ) (ν := ν) p) _ _
  have hb : eLpNorm (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter
      (UnforcedLeray.Short.IIIa.chartCoeff R V p) ((u : Chart → Merid) p)))
      2 (z1Measure c mZ) ≤
      ENNReal.ofReal (Real.sqrt (4 * B ^ 2)) * eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2)) :=
    NearInst.Delta.eLpNorm_le_of_lint' (by positivity)
      (NearInst.Delta.z1_lint' (w := fun p => UnforcedLeray.Short.IIIa.chartCoeff R V p)
        c mZ B hc hB hw)
  rw [hsnd, norm_zero, add_zero, Lp.norm_def, eLpNorm_congr_ae hfst, Lp.norm_def]
  calc _ ≤ (ENNReal.ofReal (Real.sqrt (4 * B ^ 2)) * eLpNorm (u : Chart → Merid) 2
          (ageμ c (-3 / 2))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).2.ne) hb
    _ = 2 * B * (eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
          NearInst.Delta.sqrt_four_mul_sq' hB]

/-- The broad component of a split multiplier (source 2766-2769, 4045-4049 without the flat part). -/
private theorem broad_part (c mZ ρb γ ν R : ℝ) (hν : 0 < ν) (hc : 0 < c) (hρ : 0 < ρb)
    (V rb : ℝ → UnforcedLeray.SpatialField) (MU : Hsp c →L[ℝ] Zsp c mZ ρb)
    (hMU : NearInst.IsSplitMult MU R V rb)
    (hb : ∀ᵐ p ∂(ageμ c (-1 / 2)),
      Real.sqrt p.1 * ‖UnforcedLeray.Short.IIIa.chartCoeff R rb p‖ ≤ ρb) :
    ‖NearInst.Delta.gainConjM γ hν (NearInst.Delta.sndZ c mZ ρb ∘L MU)‖ ≤ 2 * Real.sqrt ρb := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
  have hY : NearInst.Delta.gainConjM γ hν (NearInst.Delta.sndZ c mZ ρb ∘L MU) u =
      (NearInst.gainEquiv c mZ ρb γ hν).symm
        (NearInst.Delta.sndZ c mZ ρb (MU (NearInst.gainH c γ hν u))) := rfl
  rw [hY, WithLp.prod_norm_eq_of_L1]
  set x : Hsp c := NearInst.gainH c γ hν u with hx
  have hfst0 : ((NearInst.gainEquiv c mZ ρb γ hν).symm
      (NearInst.Delta.sndZ c mZ ρb (MU x))).fst = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [NearInst.Delta.gainEquiv_symm_fst c mZ ρb γ hν
        (NearInst.Delta.sndZ c mZ ρb (MU x)),
      Lp.eq_zero_iff_ae_eq_zero.1 (NearInst.Delta.sndZ_fst' c mZ ρb (MU x))] with p hp hz0
    rw [hp, hz0]
    simp
  have hGsnd : (NearInst.Delta.sndZ c mZ ρb (MU x)).snd = (MU x).snd :=
    NearInst.Delta.sndZ_snd' c mZ ρb (MU x)
  have hsnd : ((NearInst.gainEquiv c mZ ρb γ hν).symm
      (NearInst.Delta.sndZ c mZ ρb (MU x))).snd
      =ᵐ[htRhoMeasure c ρb] fun p =>
        ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff R rb p) ((u : Chart → Merid) p)) := by
    have h := NearInst.Delta.gainEquiv_symm_snd c mZ ρb γ hν (NearInst.Delta.sndZ c mZ ρb (MU x))
    rw [hGsnd] at h
    have hxae : (x : Chart → Merid) =ᵐ[htRhoMeasure c ρb]
        fun p => NearInst.gainFun γ ν p • (u : Chart → Merid) p :=
      (CoeffMult.htRho_ac hc ρb).ae_le (NearInst.Delta.gainLp_ae (μ := ageμ c (-3 / 2)) γ hν u)
    filter_upwards [h, (hMU x).2, hxae] with p hYp hMp hxp
    rw [hYp, hMp, hxp]
    exact NearInst.Delta.alg_one _ _ (NearInst.gainInvFun_mul (γ := γ) (ν := ν) p) _ _
  have hbd : eLpNorm (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter
      (UnforcedLeray.Short.IIIa.chartCoeff R rb p) ((u : Chart → Merid) p)))
      2 (htRhoMeasure c ρb) ≤
      ENNReal.ofReal (Real.sqrt (ρb⁻¹ * (4 * ρb ^ 2))) *
        eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2)) :=
    NearInst.Delta.eLpNorm_le_of_lint' (by positivity)
      (NearInst.Delta.ht_lint' (w := fun p => UnforcedLeray.Short.IIIa.chartCoeff R rb p)
        c ρb ρb hc hρ hρ.le hb)
  have hsq : Real.sqrt (ρb⁻¹ * (4 * ρb ^ 2)) = 2 * Real.sqrt ρb := by
    rw [show ρb⁻¹ * (4 * ρb ^ 2) = (2 * Real.sqrt ρb) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hρ.le]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  rw [hfst0, norm_zero, zero_add, Lp.norm_def, eLpNorm_congr_ae hsnd, Lp.norm_def]
  calc _ ≤ (ENNReal.ofReal (Real.sqrt (ρb⁻¹ * (4 * ρb ^ 2))) * eLpNorm (u : Chart → Merid) 2
          (ageμ c (-3 / 2))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).2.ne) hbd
    _ = 2 * Real.sqrt ρb * (eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsq]

/-- Both components together: `‖G⁻¹ M_U g‖ ≤ 2B + 2√ρ_b`. -/
private theorem gainConj_split_bound (c mZ ρb γ ν R B : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (hρ : 0 < ρb) (hB : 0 ≤ B)
    (V rb : ℝ → UnforcedLeray.SpatialField) (MU : Hsp c →L[ℝ] Zsp c mZ ρb)
    (hMU : NearInst.IsSplitMult MU R V rb)
    (hw : ∀ p : Chart, 0 < p.1 → Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p *
      ‖UnforcedLeray.Short.IIIa.chartCoeff R V p‖ ≤ B)
    (hb : ∀ᵐ p ∂(ageμ c (-1 / 2)),
      Real.sqrt p.1 * ‖UnforcedLeray.Short.IIIa.chartCoeff R rb p‖ ≤ ρb) :
    ‖NearInst.Delta.gainConjM γ hν MU‖ ≤ 2 * B + 2 * Real.sqrt ρb := by
  have hM : NearInst.Delta.fstZ c mZ ρb ∘L MU + NearInst.Delta.sndZ c mZ ρb ∘L MU = MU := by
    ext u
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    exact NearInst.Delta.fstZ_add_sndZ c mZ ρb (MU u)
  have hadd : NearInst.Delta.gainConjM γ hν MU =
      NearInst.Delta.gainConjM γ hν (NearInst.Delta.fstZ c mZ ρb ∘L MU) +
        NearInst.Delta.gainConjM γ hν (NearInst.Delta.sndZ c mZ ρb ∘L MU) := by
    conv_lhs => rw [← hM]
    unfold NearInst.Delta.gainConjM
    simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  rw [hadd]
  exact (norm_add_le _ _).trans
    (add_le_add (thin_part c mZ ρb γ ν R B hν hc hB V rb MU hMU hw)
      (broad_part c mZ ρb γ ν R hν hc hρ V rb MU hMU hb))

/-- **`PartIII-b:C/rep/11/2/2`**: the gained split multiplier is bounded by `C ν^{-k}` at the
large levels of `RepairStanding` (source 2703-2713, 2777-2778, 4029-4040). -/
theorem nearMUGainBound_of (hS : NearInst.SplitMultBound) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.NearMUGainBound := by
  obtain ⟨C, k, ν₀, hν₀, h⟩ := hS dm dp hst.dm_pos D.K.m0 D.K.C0 D.K.k0 hst.m0_pos
    hst.m0_lt.le hst.C0_pos D.K.mZ hst.mZ_gt D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos
    hst.planar.eigenpair
  obtain ⟨ν₂, hν₂, hrho⟩ := NearInst.ns_rhoB_le D.K.m0 D.K.C0 dm dp D.K.k0 hst.C0_pos hst.m0_lt
  have hlim := retNu_tendsto D.σ₀ hst.omega_ne
  refine ⟨2 * |C| + 2, k, ?_⟩
  filter_upwards [hst.actual, hlim.eventually (ge_mem_nhds hν₀),
    hlim.eventually (ge_mem_nhds hν₂), hlim.eventually (ge_mem_nhds one_pos),
    SeqData.nearMUExists D hst] with n hn h0 h2 h1 hM
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hρpos : 0 < (D.level n).ρb D.Pl D.K :=
    rhoB_pos (Pl := D.Pl) (K := D.K) (L := D.level n) hst.C0_pos
  have hrhoB : (D.level n).ρb D.Pl D.K ≤ 1 := hrho _ _ hn.regime h2
  obtain ⟨hmeasV, hmeasR, hpt, hae⟩ := h ((D.level n).params D.Pl) _ hn.regime h0 rfl rfl
    (D.Sin n) (D.V n) (D.rb n) hn.split
  have hB : (0 : ℝ) ≤ |C| * ((D.level n).ν⁻¹) ^ k := by positivity
  have hw : ∀ p : Chart, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight D.K.mZ p *
        ‖UnforcedLeray.Short.IIIa.chartCoeff (((D.level n).params D.Pl).R) (D.V n) p‖
        ≤ |C| * ((D.level n).ν⁻¹) ^ k := fun p hp =>
    (hpt p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hae' : ∀ᵐ p ∂(ageμ (cOf (D.level n).ν) (-1 / 2)),
      Real.sqrt p.1 *
        ‖UnforcedLeray.Short.IIIa.chartCoeff (((D.level n).params D.Pl).R) (D.rb n) p‖
        ≤ (D.level n).ρb D.Pl D.K := hae
  have hbound := gainConj_split_bound (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
    (gRate D.Pl) (D.level n).ν (((D.level n).params D.Pl).R) (|C| * ((D.level n).ν⁻¹) ^ k)
    hν hc hρpos hB (D.V n) (D.rb n) (nearMU D.Pl D.K (D.level n))
    (nearMU_spec (Pl := D.Pl) (K := D.K) (L := D.level n) hM) hw hae'
  have hsqrt : Real.sqrt ((D.level n).ρb D.Pl D.K) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hrhoB
  have hk1 : 1 ≤ ((D.level n).ν⁻¹) ^ k := one_le_pow₀ ((one_le_inv₀ hν).2 h1)
  show ‖NearInst.Delta.gainConjM (gRate D.Pl) (D.level n).ν_pos (nearMU D.Pl D.K (D.level n))‖
      ≤ (2 * |C| + 2) * ((D.level n).ν⁻¹) ^ k
  nlinarith [hbound, hk1, hsqrt, le_abs_self C, abs_nonneg C]

end UnforcedLeray.Short.PartIIIb.Concrete

end
