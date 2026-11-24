import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult

/-!
# Proof of `broadMult` (source 2766-2769, 2775-2776, 4045-4049): the broad repair coupling.
Target: `NearInst/Delta/Lemmas.lean`, `BroadMult`.  Helpers are local to this file.
The broad output `sndZ` keeps the second component, which lives on `ρ_b^{-1/2} H_T`; the flat
multiplier has zero second output, so only `M_U`'s broad coefficient `v_b` contributes.  The
`H_T` estimate is a lintegral over `htRhoMeasure = ρ_b⁻¹ ageμ(-1/2)` bounded by the
withDensity inequality, with the pointwise bound `√s|v_b| ≤ ρ_b` used almost everywhere.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar UnforcedLeray.Short.IIIa
  UnforcedLeray.Short.PartIIIb.NearInst.CoeffMult

/-! ## Tensor helpers -/

theorem ten3_symOuter_smul_left (a b : Merid) (r : ℝ) :
    ten3Of (symOuter (r • a) b) = r • ten3Of (symOuter a b) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [ten3Of, symOuter, embedMerid] <;> ring

theorem alg_key (gi g a : ℝ) (hg : gi * g = 1) (t u : Merid) :
    gi • ten3Of (symOuter t ((a * g) • u)) = ten3Of (symOuter (a • t) u) := by
  rw [ten3_symOuter_smul, smul_smul, ten3_symOuter_smul_left,
    show gi * (a * g) = a by linear_combination a * hg]

/-! ## Gain helpers -/

theorem gainLp_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Chart}
    (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (Y : Lp E 2 μ) :
    ((gainLp μ γ hν Y : Lp E 2 μ) : Chart → E) =ᵐ[μ] fun p => gainFun γ ν p • (Y : Chart → E) p :=
  mulBdd_apply_ae _ (gainFun_measurable γ ν) _ (gainFun_le hν) Y

theorem gainLp_inv_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Chart}
    (γ : ℝ) {ν : ℝ} (hν : 0 < ν) {X Y : Lp E 2 μ} (h : gainLp μ γ hν Y = X) :
    (Y : Chart → E) =ᵐ[μ] fun p => gainInvFun γ ν p • (X : Chart → E) p := by
  have h2 := gainLp_ae (μ := μ) γ hν Y
  rw [h] at h2
  filter_upwards [h2] with p hp
  have hp' : (X : Chart → E) p = gainFun γ ν p • (Y : Chart → E) p := hp
  show (Y : Chart → E) p = gainInvFun γ ν p • (X : Chart → E) p
  rw [hp', smul_smul, gainInvFun_mul, one_smul]

theorem gainEquiv_fst' (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (X : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν X).fst = gainLp (z1Measure c mZ) γ hν X.fst := rfl

theorem gainEquiv_snd' (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (X : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν X).snd = gainLp (htRhoMeasure c ρb) γ hν X.snd := rfl

theorem gainEquiv_symm_fst (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (G : Zsp c mZ ρb) :
    ((gainEquiv c mZ ρb γ hν).symm G).fst =ᵐ[z1Measure c mZ]
      fun p => gainInvFun γ ν p • G.fst p := by
  apply gainLp_inv_ae γ hν
  rw [← gainEquiv_fst', ContinuousLinearEquiv.apply_symm_apply]

theorem gainEquiv_symm_snd (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (G : Zsp c mZ ρb) :
    ((gainEquiv c mZ ρb γ hν).symm G).snd =ᵐ[htRhoMeasure c ρb]
      fun p => gainInvFun γ ν p • G.snd p := by
  apply gainLp_inv_ae γ hν
  rw [← gainEquiv_snd', ContinuousLinearEquiv.apply_symm_apply]

/-! ## Norm helpers -/

theorem sqrt_four_mul_sq' {B : ℝ} (hB : 0 ≤ B) : Real.sqrt (4 * B ^ 2) = 2 * B := by
  rw [show (4 : ℝ) * B ^ 2 = (2 * B) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

theorem eLpNorm_le_of_lint' {f : Chart → Ten3} {ν base : Measure Chart} {K : ℝ} (hK : 0 ≤ K)
    {u : Chart → Merid}
    (h : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂ν ≤ ENNReal.ofReal K * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂base) :
    eLpNorm f 2 ν ≤ ENNReal.ofReal (Real.sqrt K) * eLpNorm u 2 base := by
  have h2 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2' : (2 : ENNReal) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm h2 h2', eLpNorm_eq_lintegral_rpow_enorm h2 h2']
  simp only [ENNReal.toReal_ofNat]
  calc _ ≤ (ENNReal.ofReal K * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂base) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt K) * (∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂base) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hK (by norm_num), Real.sqrt_eq_rpow]

/-- The `Z₁` lintegral bound for an arbitrary (not necessarily measurable) coefficient. -/
theorem z1_lint' (c mZ B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) {w u : Chart → Merid}
    (hw : ∀ p : Chart, 0 < p.1 → Real.sqrt p.1 * transWeight mZ p * ‖w p‖ ≤ B) :
    ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂z1Measure c mZ ≤
      ENNReal.ofReal (4 * B ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
  have hd : Measurable fun p : Chart => ENNReal.ofReal (transWeight mZ p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_transWeight' mZ).pow_const 2)
  have hs : Measurable fun p : Chart => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have s1 : ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂z1Measure c mZ ≤
      ∫⁻ p, (ENNReal.ofReal (transWeight mZ p ^ 2) * ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ))
        ∂ageμ c (-1 / 2) :=
    lintegral_withDensity_le_lintegral_mul _ hd _
  have s2 : ∫⁻ p, (ENNReal.ofReal (transWeight mZ p ^ 2) * ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ))
        ∂ageμ c (-1 / 2) ≤
      ∫⁻ p, (ENNReal.ofReal p.1 * (ENNReal.ofReal (transWeight mZ p ^ 2) *
        ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ))) ∂ageμ c (-3 / 2) := by
    rw [ageμ_half hc]
    exact lintegral_withDensity_le_lintegral_mul _ hs _
  calc _ ≤ _ := s1
    _ ≤ _ := s2
    _ ≤ ∫⁻ p, ENNReal.ofReal (4 * B ^ 2) * ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
        lintegral_mono fun p => pt_z1 p mZ B (w p) (u p) (fun hp => hw p hp)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem alg_one (gi g : ℝ) (hg : gi * g = 1) (a u : Merid) :
    gi • ten3Of (symOuter a (g • u)) = ten3Of (symOuter a u) := by
  rw [ten3_symOuter_smul, smul_smul, hg, one_smul]

theorem sndZ_fst' (c mZ ρb : ℝ) (F : Zsp c mZ ρb) : (sndZ c mZ ρb F).fst = 0 := by
  simp [sndZ, zEquiv]

theorem sndZ_snd' (c mZ ρb : ℝ) (F : Zsp c mZ ρb) : (sndZ c mZ ρb F).snd = F.snd := by
  simp [sndZ, zEquiv]

/-- The `H_T` lintegral bound for an almost-everywhere coefficient bound (source 2766-2769). -/
theorem ht_lint' (c ρb B : ℝ) (hc : 0 < c) (hρ : 0 < ρb) (hB0 : 0 ≤ B) {w u : Chart → Merid}
    (hB : ∀ᵐ p ∂(ageμ c (-1 / 2)), Real.sqrt p.1 * ‖w p‖ ≤ B) :
    ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂htRhoMeasure c ρb ≤
      ENNReal.ofReal (ρb⁻¹ * (4 * B ^ 2)) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
  have hsm : Measurable fun p : Chart => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have s1 : ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂ageμ c (-1 / 2) ≤
      ∫⁻ p, (ENNReal.ofReal p.1 * ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ)) ∂ageμ c (-3 / 2) := by
    rw [ageμ_half hc]
    exact lintegral_withDensity_le_lintegral_mul _ hsm _
  have hB' : ∀ᵐ p ∂ageμ c (-3 / 2), ENNReal.ofReal p.1 ≠ 0 → Real.sqrt p.1 * ‖w p‖ ≤ B := by
    rw [ageμ_half hc] at hB
    exact (ae_withDensity_iff hsm).1 hB
  have s2 : ∫⁻ p, (ENNReal.ofReal p.1 * ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ))
      ∂ageμ c (-3 / 2) ≤
      ∫⁻ p, ENNReal.ofReal (4 * B ^ 2) * ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
    lintegral_mono_ae (hB'.mono fun p hp =>
      pt_ht p B (w p) (u p) (fun hs => hp (ENNReal.ofReal_pos.2 hs).ne'))
  have hinv : (0 : ℝ) ≤ ρb⁻¹ := inv_nonneg.2 hρ.le
  calc _ = ENNReal.ofReal ρb⁻¹ * ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ)
          ∂ageμ c (-1 / 2) := by
        unfold htRhoMeasure
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal ρb⁻¹ * (ENNReal.ofReal (4 * B ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ)
          ∂ageμ c (-3 / 2)) := by
        gcongr
        exact s1.trans (s2.trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
    _ = _ := by
        rw [ENNReal.ofReal_mul hinv, mul_assoc]

/-- **The broad repair coupling** (source 2766-2769, 4045-4049). -/
theorem broadMult : BroadMult := by
  intro c mZ ρb γ ν R hν tr V rb M0 MU hc hρ hM0 hMU hB
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
  have hY : gainConjM γ hν (sndZ c mZ ρb ∘L (MU - M0)) u =
      (gainEquiv c mZ ρb γ hν).symm (sndZ c mZ ρb ((MU - M0) (gainH c γ hν u))) := rfl
  rw [hY, WithLp.prod_norm_eq_of_L1]
  set x : Hsp c := gainH c γ hν u with hx
  have hfst0 : ((gainEquiv c mZ ρb γ hν).symm (sndZ c mZ ρb ((MU - M0) x))).fst = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [gainEquiv_symm_fst c mZ ρb γ hν (sndZ c mZ ρb ((MU - M0) x)),
      Lp.eq_zero_iff_ae_eq_zero.1 (sndZ_fst' c mZ ρb ((MU - M0) x))] with p hp hz0
    rw [hp, hz0]
    simp
  have hGsnd : (sndZ c mZ ρb ((MU - M0) x)).snd = (MU x).snd := by
    rw [sndZ_snd']
    show (MU x - M0 x).snd = (MU x).snd
    rw [show (MU x - M0 x).snd = (MU x).snd - (M0 x).snd from rfl, (hM0 x).2, sub_zero]
  have hsnd : ((gainEquiv c mZ ρb γ hν).symm (sndZ c mZ ρb ((MU - M0) x))).snd
      =ᵐ[htRhoMeasure c ρb] fun p => ten3Of (symOuter (chartCoeff R rb p) ((u : Chart → Merid) p)) := by
    have h := gainEquiv_symm_snd c mZ ρb γ hν (sndZ c mZ ρb ((MU - M0) x))
    rw [hGsnd] at h
    have hxae : (x : Chart → Merid) =ᵐ[htRhoMeasure c ρb] fun p => gainFun γ ν p • (u : Chart → Merid) p :=
      (htRho_ac hc ρb).ae_le (gainLp_ae (μ := ageμ c (-3 / 2)) γ hν u)
    filter_upwards [h, (hMU x).2, hxae] with p hYp hMp hxp
    rw [hYp, hMp, hxp]
    exact alg_one _ _ (gainInvFun_mul (γ := γ) (ν := ν) p) _ _
  have hb : eLpNorm (fun p => ten3Of (symOuter (chartCoeff R rb p) ((u : Chart → Merid) p)))
      2 (htRhoMeasure c ρb) ≤
      ENNReal.ofReal (Real.sqrt (ρb⁻¹ * (4 * ρb ^ 2))) * eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2)) :=
    eLpNorm_le_of_lint' (by positivity)
      (ht_lint' (w := fun p => chartCoeff R rb p) c ρb ρb hc hρ hρ.le hB)
  have hsq : Real.sqrt (ρb⁻¹ * (4 * ρb ^ 2)) = 2 * Real.sqrt ρb := by
    rw [show ρb⁻¹ * (4 * ρb ^ 2) = (2 * Real.sqrt ρb) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hρ.le]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  rw [hfst0, norm_zero, zero_add, Lp.norm_def, eLpNorm_congr_ae hsnd, Lp.norm_def]
  calc _ ≤ (ENNReal.ofReal (Real.sqrt (ρb⁻¹ * (4 * ρb ^ 2))) * eLpNorm (u : Chart → Merid) 2
          (ageμ c (-3 / 2))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).2.ne) hb
    _ = 2 * Real.sqrt ρb * (eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsq]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
