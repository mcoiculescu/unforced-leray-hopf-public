import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.MollIntegralSplit

/-!
# `ShiftPairTiling`: unfolding `ℝ × ℝ³` into the translated phase cells

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
The phase cells `cellK P k` (translates of `cellBase P = (0,P] × ℝ³`) tile `ℝ × ℝ³`, so the
integral of an integrable `G` is the sum over `k` of the cell integrals of its translates
(`sp_fold_cell`). For `G w = κ(x - w) e·F(w)` the translate `G(y - kP)` equals
`κ(x - y + kP) e·F(y)` a.e. on the base cell, by the a.e. `P`-periodicity of `F`
(`ae_shift_int`), and the reindexing `k ↦ -k` gives the stated sum.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sp_dot_real (e : CVec3) (r : ℝ) (v : CVec3) : dotL e (r • v) = (r : ℂ) * dotL e v := by
  rw [show r • v = (r : ℂ) • v from (Complex.coe_smul r v).symm, map_smul, smul_eq_mul]

/-- `w ↦ g(w) e·F(w)` is integrable for a locally integrable `F` and a continuous kernel `g` with
compact support. -/
theorem sp_int_kernel {F : ℝ × Space → CVec3} (hF : LocallyIntegrable F volume) (e : CVec3)
    {g : ℝ × Space → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun w => ((g w : ℝ) : ℂ) * dotL e (F w)) volume := by
  have h1 : Integrable (fun w => g w • F w) volume :=
    hF.integrable_smul_left_of_hasCompactSupport hg hgc
  have h2 := (dotL e).integrable_comp h1
  have h3 : (fun w => ((g w : ℝ) : ℂ) * dotL e (F w)) = fun w => dotL e (g w • F w) := by
    funext w
    rw [sp_dot_real]
  rw [h3]
  exact h2

/-- Tiling of `ℝ × ℝ³` by the phase cells: the integral of an integrable `G` is the sum over `k`
of the integrals over the base cell of the translates `G(· + kP)`. -/
theorem sp_fold_cell {P : ℝ} (hP : 0 < P) {G : ℝ × Space → ℂ} (hG : Integrable G volume) :
    ∫ w, G w = ∑' k : ℤ, ∫ y in cellBase P, G (y + ((k : ℝ) * P, (0 : Space))) := by
  have hmeas : ∀ k : ℤ, MeasurableSet (cellK P k) := fun k => measurableSet_cellK P k
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℤ => cellK P k) := by
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro z hzk hzl
    rw [mem_cellK_iff] at hzk hzl
    rcases lt_or_gt_of_ne hkl with h | h
    · have h2 : k + 1 ≤ l := h
      have h' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast h2
      have h3 : ((k : ℝ) + 1) * P ≤ (l : ℝ) * P := mul_le_mul_of_nonneg_right h' hP.le
      linarith [hzk.2, hzl.1]
    · have h2 : l + 1 ≤ k := h
      have h' : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h2
      have h3 : ((l : ℝ) + 1) * P ≤ (k : ℝ) * P := mul_le_mul_of_nonneg_right h' hP.le
      linarith [hzl.2, hzk.1]
  have hcover : (⋃ k : ℤ, cellK P k) = univ := by
    refine Set.eq_univ_of_forall fun z => Set.mem_iUnion.mpr ⟨⌈z.1 / P⌉ - 1, ?_⟩
    rw [mem_cellK_iff]
    have h1 : z.1 / P ≤ (⌈z.1 / P⌉ : ℝ) := Int.le_ceil _
    have h2 : (⌈z.1 / P⌉ : ℝ) < z.1 / P + 1 := Int.ceil_lt_add_one _
    have e : ((⌈z.1 / P⌉ - 1 : ℤ) : ℝ) = (⌈z.1 / P⌉ : ℝ) - 1 := by push_cast; ring
    rw [e]
    constructor
    · have h4 : (⌈z.1 / P⌉ : ℝ) - 1 < z.1 / P := by linarith
      have h5 := (lt_div_iff₀ hP).mp h4
      linarith
    · have h4 := (div_le_iff₀ hP).mp h1
      have e2 : ((⌈z.1 / P⌉ : ℝ) - 1 + 1) * P = (⌈z.1 / P⌉ : ℝ) * P := by ring
      linarith
  have hI : ∫ w, G w = ∑' k : ℤ, ∫ w in cellK P k, G w := by
    have h1 : ∫ w, G w = ∫ w in (⋃ k : ℤ, cellK P k), G w := by
      rw [hcover, setIntegral_univ]
    rw [h1]
    exact integral_iUnion hmeas hdisj hG.integrableOn
  have hshift : ∀ k : ℤ, ∫ w in cellK P k, G w
      = ∫ y in cellBase P, G (y + ((k : ℝ) * P, (0 : Space))) := by
    intro k
    have hT : MeasurePreserving (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space)))
        volume volume := measurePreserving_sub_right volume _
    have hemb : MeasurableEmbedding (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space))) :=
      (Homeomorph.subRight ((k : ℝ) * P, (0 : Space))).measurableEmbedding
    have key := hT.setIntegral_preimage_emb hemb
      (fun y : ℝ × Space => G (y + ((k : ℝ) * P, (0 : Space)))) (cellBase P)
    simp only [sub_add_cancel] at key
    unfold cellK
    exact key
  rw [hI]
  exact tsum_congr hshift

theorem shiftPairTiling : ShiftPairTiling := by
  intro P hP κ hκ hcs F hF x e
  have hloc : LocallyIntegrable F volume := locInt_of_isInYr hP hF
  have hgx : Continuous (fun w : ℝ × Space => κ (x - w)) :=
    hκ.continuous.comp (continuous_const.sub continuous_id)
  have hgxc : HasCompactSupport (fun w : ℝ × Space => κ (x - w)) :=
    hcs.comp_homeomorph (Homeomorph.subLeft x)
  have hG := sp_int_kernel hloc e hgx hgxc
  refine (sp_fold_cell hP hG).trans ?_
  refine ((Equiv.neg ℤ).tsum_eq _).symm.trans ?_
  refine tsum_congr fun k => ?_
  refine setIntegral_congr_ae (measurableSet_cellBase P) ?_
  filter_upwards [ae_shift_int hF.periodic (-k)] with y hy _
  have e1 : y + (((-k : ℤ) : ℝ) * P, (0 : Space)) = (y.1 + ((-k : ℤ) : ℝ) * P, y.2) := by
    ext <;> simp
  have e2 : x - (y + (((-k : ℤ) : ℝ) * P, (0 : Space)))
      = x - y + ((k : ℝ) * P, (0 : Space)) := by
    ext <;> simp <;> ring
  show ((κ (x - (y + (((-k : ℤ) : ℝ) * P, (0 : Space)))) : ℝ) : ℂ)
      * dotL e (F (y + (((-k : ℤ) : ℝ) * P, (0 : Space))))
    = ((κ (x - y + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F y)
  rw [e2, e1, hy]

end UnforcedLeray.Short.PartIIIb.Concrete
