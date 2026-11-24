import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
Proof of `GainInvContract` (source 4092, 4116-4118: for `γ ≥ 0`, `g = e^{γs/(1+νs)} ≥ 1`, so the
inverse gain `g⁻¹` does not increase the norms of `H` and `Z`).
-/

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

theorem gainInvFun_nonneg_le_one {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) :
    0 ≤ gainInvFun γ ν p ∧ gainInvFun γ ν p ≤ 1 :=
  ⟨(inv_pos.2 (gainFun_pos γ ν p)).le, inv_le_one_of_one_le₀ (one_le_gainFun hγ hν p)⟩

theorem gainLp_symm_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Measure Chart) {γ : ℝ} (hγ : 0 ≤ γ) {ν : ℝ} (hν : 0 < ν) (f : Lp E 2 m) :
    ‖(gainLp m γ hν).symm f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_gainLp_symm m γ hν f] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (gainInvFun_nonneg_le_one hγ hν p).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (gainInvFun_nonneg_le_one hγ hν p).2

theorem gainEquiv_symm_fst_snd (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (F : Zsp c mZ ρb) :
    ((gainEquiv c mZ ρb γ hν).symm F).fst = (gainLp (z1Measure c mZ) γ hν).symm F.fst ∧
    ((gainEquiv c mZ ρb γ hν).symm F).snd = (gainLp (htRhoMeasure c ρb) γ hν).symm F.snd := by
  have key : ∀ G : Zsp c mZ ρb, gainEquiv c mZ ρb γ hν G = F →
      G.fst = (gainLp (z1Measure c mZ) γ hν).symm F.fst ∧
        G.snd = (gainLp (htRhoMeasure c ρb) γ hν).symm F.snd := by
    intro G hG
    subst hG
    simp [gainEquiv_fst, gainEquiv_snd]
  exact key _ ((gainEquiv c mZ ρb γ hν).apply_symm_apply F)

theorem gainEquiv_symm_norm_le (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (hγ : 0 ≤ γ)
    (F : Zsp c mZ ρb) : ‖(gainEquiv c mZ ρb γ hν).symm F‖ ≤ ‖F‖ := by
  rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1,
    (gainEquiv_symm_fst_snd c mZ ρb γ hν F).1, (gainEquiv_symm_fst_snd c mZ ρb γ hν F).2]
  exact add_le_add (gainLp_symm_norm_le _ hγ hν F.fst) (gainLp_symm_norm_le _ hγ hν F.snd)

theorem gainInvContract : GainInvContract := by
  intro c mZ ρb γ ν hν hγ
  exact ⟨fun u => gainLp_symm_norm_le (ageμ c (-3 / 2)) hγ hν u,
    fun F => gainEquiv_symm_norm_le c mZ ρb γ hν hγ F⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Body
