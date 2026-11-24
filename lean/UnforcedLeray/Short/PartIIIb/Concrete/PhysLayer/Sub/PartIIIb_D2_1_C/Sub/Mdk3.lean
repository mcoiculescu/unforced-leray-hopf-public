import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2

/-!
# `FoldCell`: an integrable function integrates as the cell integral of its periodisation

Source: `the November 2 reference manuscript` lines 1351-1362.
The phase cells `cellK P k` tile `ℝ × ℝ³` disjointly; each cell is a translate of `cellBase P`,
and the sum over cells is interchanged with the cell integral by dominated summation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem foldCell : FoldCell := by
  intro P hP G hG
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
  -- integral over ℝ × ℝ³ as the sum over cells
  have hI : ∫ w, G w = ∑' k : ℤ, ∫ w in cellK P k, G w := by
    have h1 : ∫ w, G w = ∫ w in (⋃ k : ℤ, cellK P k), G w := by
      rw [hcover, setIntegral_univ]
    rw [h1]
    exact integral_iUnion hmeas hdisj hG.integrableOn
  -- each cell integral is the base-cell integral of the translate
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
  have shiftR : ∀ k : ℤ, ∫ w in cellK P k, ‖G w‖
      = ∫ y in cellBase P, ‖G (y + ((k : ℝ) * P, (0 : Space)))‖ := by
    intro k
    have hT : MeasurePreserving (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space)))
        volume volume := measurePreserving_sub_right volume _
    have hemb : MeasurableEmbedding (fun z : ℝ × Space => z - ((k : ℝ) * P, (0 : Space))) :=
      (Homeomorph.subRight ((k : ℝ) * P, (0 : Space))).measurableEmbedding
    have key := hT.setIntegral_preimage_emb hemb
      (fun y : ℝ × Space => ‖G (y + ((k : ℝ) * P, (0 : Space)))‖) (cellBase P)
    simp only [sub_add_cancel] at key
    unfold cellK
    exact key
  have hF_int : ∀ k : ℤ, Integrable (fun y : ℝ × Space => G (y + ((k : ℝ) * P, (0 : Space))))
      (volume.restrict (cellBase P)) :=
    fun k => (hG.comp_add_right _).integrableOn
  have hF_sum : Summable (fun k : ℤ =>
      ∫ y : ℝ × Space, ‖G (y + ((k : ℝ) * P, (0 : Space)))‖ ∂(volume.restrict (cellBase P))) := by
    have hs := (hasSum_integral_iUnion (f := fun w => ‖G w‖) hmeas hdisj
      hG.norm.integrableOn).summable
    refine hs.congr fun k => ?_
    exact shiftR k
  rw [hI]
  simp only [hshift]
  exact integral_tsum_of_summable_integral_norm
    (F := fun (k : ℤ) (y : ℝ × Space) => G (y + ((k : ℝ) * P, (0 : Space))))
    hF_int hF_sum
