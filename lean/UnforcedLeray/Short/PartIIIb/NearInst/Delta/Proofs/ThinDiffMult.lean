import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult

/-!
# Proof of `thinDiffMult` (source 4032-4040, 2758-2775): the thin coefficient difference.
Target: `NearInst/Delta/Lemmas.lean`, `ThinDiffMult`.  Helpers are local to this file (same
statements as in `Proofs/TrainMult.lean`).  The thin output `fstZ` keeps only the first
component; `gainConjM (fstZ ∘ (M_U - M_0))` applied to `u` is `G⁻¹ (fst (M_U - M_0) g u)`, whose
first component is pointwise `ten3Of (symOuter (v - v_flat) u)` after cancelling the gain.
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

private theorem ten3_symOuter_smul_left (a b : Merid) (r : ℝ) :
    ten3Of (symOuter (r • a) b) = r • ten3Of (symOuter a b) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [ten3Of, symOuter, embedMerid] <;> ring

private theorem alg_key (gi g a : ℝ) (hg : gi * g = 1) (t u : Merid) :
    gi • ten3Of (symOuter t ((a * g) • u)) = ten3Of (symOuter (a • t) u) := by
  rw [ten3_symOuter_smul, smul_smul, ten3_symOuter_smul_left,
    show gi * (a * g) = a by linear_combination a * hg]

/-! ## Gain helpers -/

private theorem gainLp_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Chart}
    (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (Y : Lp E 2 μ) :
    ((gainLp μ γ hν Y : Lp E 2 μ) : Chart → E) =ᵐ[μ] fun p => gainFun γ ν p • (Y : Chart → E) p :=
  mulBdd_apply_ae _ (gainFun_measurable γ ν) _ (gainFun_le hν) Y

private theorem gainLp_inv_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Chart}
    (γ : ℝ) {ν : ℝ} (hν : 0 < ν) {X Y : Lp E 2 μ} (h : gainLp μ γ hν Y = X) :
    (Y : Chart → E) =ᵐ[μ] fun p => gainInvFun γ ν p • (X : Chart → E) p := by
  have h2 := gainLp_ae (μ := μ) γ hν Y
  rw [h] at h2
  filter_upwards [h2] with p hp
  have hp' : (X : Chart → E) p = gainFun γ ν p • (Y : Chart → E) p := hp
  show (Y : Chart → E) p = gainInvFun γ ν p • (X : Chart → E) p
  rw [hp', smul_smul, gainInvFun_mul, one_smul]

private theorem gainEquiv_fst' (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (X : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν X).fst = gainLp (z1Measure c mZ) γ hν X.fst := rfl

private theorem gainEquiv_snd' (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (X : Zsp c mZ ρb) :
    (gainEquiv c mZ ρb γ hν X).snd = gainLp (htRhoMeasure c ρb) γ hν X.snd := rfl

private theorem gainEquiv_symm_fst (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (G : Zsp c mZ ρb) :
    ((gainEquiv c mZ ρb γ hν).symm G).fst =ᵐ[z1Measure c mZ]
      fun p => gainInvFun γ ν p • G.fst p := by
  apply gainLp_inv_ae γ hν
  rw [← gainEquiv_fst', ContinuousLinearEquiv.apply_symm_apply]

private theorem gainEquiv_symm_snd (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (G : Zsp c mZ ρb) :
    ((gainEquiv c mZ ρb γ hν).symm G).snd =ᵐ[htRhoMeasure c ρb]
      fun p => gainInvFun γ ν p • G.snd p := by
  apply gainLp_inv_ae γ hν
  rw [← gainEquiv_snd', ContinuousLinearEquiv.apply_symm_apply]

/-! ## Norm helpers -/

private theorem sqrt_four_mul_sq' {B : ℝ} (hB : 0 ≤ B) : Real.sqrt (4 * B ^ 2) = 2 * B := by
  rw [show (4 : ℝ) * B ^ 2 = (2 * B) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

private theorem eLpNorm_le_of_lint' {f : Chart → Ten3} {ν base : Measure Chart} {K : ℝ} (hK : 0 ≤ K)
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
private theorem z1_lint' (c mZ B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) {w u : Chart → Merid}
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

private theorem ten3_symOuter_sub_left (a b d : Merid) :
    ten3Of (symOuter (a - b) d) = ten3Of (symOuter a d) - ten3Of (symOuter b d) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [ten3Of, symOuter, embedMerid] <;> ring

private theorem alg_sub (gi g : ℝ) (hg : gi * g = 1) (a b u : Merid) :
    gi • (ten3Of (symOuter a (g • u)) - ten3Of (symOuter b (g • u))) =
      ten3Of (symOuter (a - b) u) := by
  rw [ten3_symOuter_smul, ten3_symOuter_smul, ← smul_sub, smul_smul, hg, one_smul,
    ten3_symOuter_sub_left]

/-- The thin projection keeps the first component. -/
private theorem fstZ_fst' (c mZ ρb : ℝ) (F : Zsp c mZ ρb) : (fstZ c mZ ρb F).fst = F.fst := by
  simp [fstZ, zEquiv]

private theorem fstZ_snd' (c mZ ρb : ℝ) (F : Zsp c mZ ρb) : (fstZ c mZ ρb F).snd = 0 := by
  simp [fstZ, zEquiv]

/-- **The thin coefficient difference as a multiplier** (source 4032-4040). -/
theorem thinDiffMult : ThinDiffMult := by
  intro c mZ ρb γ ν R hν tr V rb M0 MU B hc hB hM0 hMU hw
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith : (0 : ℝ) ≤ 2 * B) (fun u => ?_)
  have hY : gainConjM γ hν (fstZ c mZ ρb ∘L (MU - M0)) u =
      (gainEquiv c mZ ρb γ hν).symm (fstZ c mZ ρb ((MU - M0) (gainH c γ hν u))) := rfl
  rw [hY, WithLp.prod_norm_eq_of_L1]
  set x : Hsp c := gainH c γ hν u with hx
  have hGfst : (fstZ c mZ ρb ((MU - M0) x)).fst = (MU x).fst - (M0 x).fst := by
    rw [fstZ_fst']
    rfl
  have hsnd : ((gainEquiv c mZ ρb γ hν).symm (fstZ c mZ ρb ((MU - M0) x))).snd = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [gainEquiv_symm_snd c mZ ρb γ hν (fstZ c mZ ρb ((MU - M0) x)),
      Lp.eq_zero_iff_ae_eq_zero.1 (fstZ_snd' c mZ ρb ((MU - M0) x))] with p hp hz0
    rw [hp, hz0]
    simp
  have hxae : (x : Chart → Merid) =ᵐ[z1Measure c mZ] fun p => gainFun γ ν p • (u : Chart → Merid) p :=
    (z1_ac hc mZ).ae_le (gainLp_ae (μ := ageμ c (-3 / 2)) γ hν u)
  have hG : ((fstZ c mZ ρb ((MU - M0) x)).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
      fun p => (MU x).fst p - (M0 x).fst p := by
    rw [hGfst]
    exact Lp.coeFn_sub _ _
  have hfst : ((gainEquiv c mZ ρb γ hν).symm (fstZ c mZ ρb ((MU - M0) x))).fst
      =ᵐ[z1Measure c mZ] fun p =>
        ten3Of (symOuter (chartCoeff R V p - trainMer tr p) ((u : Chart → Merid) p)) := by
    filter_upwards [gainEquiv_symm_fst c mZ ρb γ hν (fstZ c mZ ρb ((MU - M0) x)),
      hG, (hMU x).1, (hM0 x).1, hxae] with p hYp hGp hMUp hM0p hxp
    rw [hYp, hGp, hMUp, hM0p, hxp]
    exact alg_sub _ _ (gainInvFun_mul (γ := γ) (ν := ν) p) _ _ _
  have hb : eLpNorm (fun p => ten3Of (symOuter (chartCoeff R V p - trainMer tr p) ((u : Chart → Merid) p)))
      2 (z1Measure c mZ) ≤
      ENNReal.ofReal (Real.sqrt (4 * B ^ 2)) * eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2)) :=
    eLpNorm_le_of_lint' (by positivity)
      (z1_lint' (w := fun p => chartCoeff R V p - trainMer tr p) c mZ B hc hB hw)
  rw [hsnd, norm_zero, add_zero, Lp.norm_def, eLpNorm_congr_ae hfst, Lp.norm_def]
  calc _ ≤ (ENNReal.ofReal (Real.sqrt (4 * B ^ 2)) * eLpNorm (u : Chart → Merid) 2
          (ageμ c (-3 / 2))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).2.ne) hb
    _ = 2 * B * (eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), sqrt_four_mul_sq' hB]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
