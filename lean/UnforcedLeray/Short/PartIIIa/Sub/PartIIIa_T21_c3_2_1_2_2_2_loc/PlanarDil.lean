import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1
import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0StrongCont.CcDense
import UnforcedLeray.Short.PartI.Tasks.DilationContinuity.DilX0StrongCont.DilWCc

/-!
# Strong continuity of the planar dilations and the cell lift (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2941-2970 (strong continuity of
the cell rescaling `J_a^{-1}` and of the dilation `S(t,s)` on `L²_m`).  `dilW'` is `Planar.dilW` with
the positivity side condition absorbed (`0` for `a ≤ 0`); it is jointly continuous in the parameter
and the vector.  `liftC` is the zero extension of a real cell field to `L²_m`; it is isometric for
the `X_{m,c}` norm.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.RelB4locAux

/-- `Planar.dilW` with the positivity side condition absorbed. -/
def dilW' {M : ℝ} (hM : 1 < M) (a : ℝ) : Planar.L2w M →L[ℂ] Planar.L2w M :=
  if h : 0 < a then Planar.dilW hM h else 0

theorem dilW'_of_pos {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) :
    dilW' hM a = Planar.dilW hM ha := dif_pos ha

theorem tendsto_dilW'_cc {M : ℝ} (hM : 1 < M) (G : Planar.L2w M) (hG : PartI.IsCcRep G)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    Tendsto (fun a : ℝ => dilW' hM a G) (𝓝 a₀) (𝓝 (dilW' hM a₀ G)) := by
  have h := PartI.dilWCcCont M hM G hG a₀ ha₀
  rw [← map_nhds_subtype_coe_eq_nhds (p := fun a : ℝ => 0 < a) ha₀ (Ioi_mem_nhds ha₀),
    tendsto_map'_iff, dilW'_of_pos hM ha₀]
  refine h.congr (fun a => ?_)
  simp only [Function.comp_apply, dilW'_of_pos hM a.2]

/-- Strong continuity of `a ↦ J_a G` at `a₀ > 0` (ε/3 argument from the compactly supported case). -/
theorem tendsto_dilW' {M : ℝ} (hM : 1 < M) (G : Planar.L2w M) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    Tendsto (fun a : ℝ => dilW' hM a G) (𝓝 a₀) (𝓝 (dilW' hM a₀ G)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := Planar.dilConst M a₀ + 1 with hC
  have hC0 : 0 < C := by
    have := Planar.dilConst_nonneg M a₀
    rw [hC]; linarith
  have hev1 : ∀ᶠ a : ℝ in 𝓝 a₀, Planar.dilConst M a < C ∧ 0 < a := by
    have h1 := (PartI.dilConst_continuousAt M a₀ ha₀).eventually
      (gt_mem_nhds (show Planar.dilConst M a₀ < C by rw [hC]; linarith))
    exact h1.and (Ioi_mem_nhds ha₀)
  have hδ : 0 < ε / (4 * C) := by positivity
  obtain ⟨G', hG', hGG⟩ := PartI.l2wCcDense M hM G (ε / (4 * C)) hδ
  have hev2 := (Metric.tendsto_nhds.1 (tendsto_dilW'_cc hM G' hG' ha₀)) (ε / 2) (by positivity)
  filter_upwards [hev1, hev2] with a ha1 ha2
  rw [dilW'_of_pos hM ha1.2] at ha2 ⊢
  rw [dilW'_of_pos hM ha₀] at ha2 ⊢
  have hJ0 : ‖Planar.dilW hM ha₀‖ ≤ Planar.dilConst M a₀ := Planar.norm_dilW_le hM ha₀
  have hJa : ‖Planar.dilW hM ha1.2‖ ≤ Planar.dilConst M a := Planar.norm_dilW_le hM ha1.2
  have hFG : ‖G - G'‖ < ε / (4 * C) := by rw [norm_sub_rev]; exact hGG
  have hN : 0 ≤ ‖G - G'‖ := norm_nonneg _
  have e1 : ‖Planar.dilW hM ha1.2 (G - G')‖ ≤ C * ‖G - G'‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJa.trans ha1.1.le) hN)
  have e2 : ‖Planar.dilW hM ha₀ (G - G')‖ ≤ C * ‖G - G'‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJ0.trans (by rw [hC]; linarith)) hN)
  have e3 : C * ‖G - G'‖ < ε / 4 := by
    calc C * ‖G - G'‖ < C * (ε / (4 * C)) := mul_lt_mul_of_pos_left hFG hC0
      _ = ε / 4 := by field_simp
  rw [dist_eq_norm] at ha2 ⊢
  have key : Planar.dilW hM ha1.2 G - Planar.dilW hM ha₀ G =
      Planar.dilW hM ha1.2 (G - G') + (Planar.dilW hM ha1.2 G' - Planar.dilW hM ha₀ G')
        - Planar.dilW hM ha₀ (G - G') := by
    simp only [map_sub]; abel
  rw [key]
  calc _ ≤ ‖Planar.dilW hM ha1.2 (G - G') +
        (Planar.dilW hM ha1.2 G' - Planar.dilW hM ha₀ G')‖ +
        ‖Planar.dilW hM ha₀ (G - G')‖ := norm_sub_le _ _
    _ ≤ ‖Planar.dilW hM ha1.2 (G - G')‖ +
        ‖Planar.dilW hM ha1.2 G' - Planar.dilW hM ha₀ G'‖ +
        ‖Planar.dilW hM ha₀ (G - G')‖ := by gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- Joint continuity of `(a, G) ↦ J_a G` at `a₀ > 0`. -/
theorem tendsto_dilW'_joint {M : ℝ} (hM : 1 < M) {ι : Type*} {l : Filter ι} {α : ι → ℝ}
    {G : ι → Planar.L2w M} {a₀ : ℝ} (ha₀ : 0 < a₀) {G₀ : Planar.L2w M}
    (hα : Tendsto α l (𝓝 a₀)) (hG : Tendsto G l (𝓝 G₀)) :
    Tendsto (fun i => dilW' hM (α i) (G i)) l (𝓝 (dilW' hM a₀ G₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C : ℝ := Planar.dilConst M a₀ + 1 with hC
  have hev : ∀ᶠ i in l, Planar.dilConst M (α i) < C ∧ 0 < α i := by
    have h1 := (PartI.dilConst_continuousAt M a₀ ha₀).eventually
      (gt_mem_nhds (show Planar.dilConst M a₀ < C by rw [hC]; linarith))
    exact hα.eventually (h1.and (Ioi_mem_nhds ha₀))
  have h2 : Tendsto (fun i => ‖dilW' hM (α i) G₀ - dilW' hM a₀ G₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_dilW' hM G₀ ha₀).comp hα)
  have h1 : Tendsto (fun i => C * ‖G i - G₀‖) l (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hG).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by simpa using h1.add h2)
  filter_upwards [hev] with i hi
  have hb : ‖dilW' hM (α i)‖ ≤ C := by
    rw [dilW'_of_pos hM hi.2]; exact (Planar.norm_dilW_le hM hi.2).trans hi.1.le
  have key : dilW' hM (α i) (G i) - dilW' hM a₀ G₀ =
      dilW' hM (α i) (G i - G₀) + (dilW' hM (α i) G₀ - dilW' hM a₀ G₀) := by
    simp only [map_sub]; abel
  rw [key]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact ((dilW' hM (α i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-! ## The cell lift -/

/-- Zero extension of a real cell field on `B0579.cell c` to a function on `ℂ`. -/
def liftFun (c : ℝ) (g : ℝ × ℝ → ℝ) (z : ℂ) : ℂ :=
  cellZeroExt c (fun x => ((g x : ℝ) : ℂ)) (cToPlane z)

theorem liftFun_sub (c : ℝ) (g₁ g₂ : ℝ × ℝ → ℝ) :
    liftFun c (g₁ - g₂) = liftFun c g₁ - liftFun c g₂ := by
  funext z
  simp only [liftFun, cellZeroExt, Pi.sub_apply]
  by_cases h : cToPlane z ∈ B0579.cell c
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem eLpNorm_liftFun {c m : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : AEStronglyMeasurable g (B0579.cellMeasure c m)) :
    eLpNorm (liftFun c g) 2 (Planar.wMeasure m) = eLpNorm g 2 (B0579.cellMeasure c m) := by
  have hV : AEStronglyMeasurable (fun x => ((g x : ℝ) : ℂ)) (B0579.cellMeasure c m) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg
  rw [show liftFun c g = fun z : ℂ => cellZeroExt c (fun x => ((g x : ℝ) : ℂ)) (cToPlane z)
    from rfl, BlockPropagatorSub.eLpNorm_cellZeroExt_cToPlane c m hV, xNorm]
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)

theorem memLp_liftFun {c m : ℝ} {g : ℝ × ℝ → ℝ} (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    MemLp (liftFun c g) 2 (Planar.wMeasure m) :=
  BlockPropagatorSub.memLp_cellZeroExt_cToPlane c m hg.ofReal

open Classical in
/-- The lift of a real cell field to `L²_m` (`0` if the field is not in `X_{m,c}`). -/
def liftC (c m : ℝ) (g : ℝ × ℝ → ℝ) : Planar.L2w m :=
  if h : MemLp g 2 (B0579.cellMeasure c m) then (memLp_liftFun h).toLp _ else 0

theorem coeFn_liftC {c m : ℝ} {g : ℝ × ℝ → ℝ} (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    ⇑(liftC c m g) =ᵐ[Planar.wMeasure m] liftFun c g := by
  rw [liftC, dif_pos hg]
  exact (memLp_liftFun hg).coeFn_toLp

theorem norm_liftC_sub {c m : ℝ} {g₁ g₂ : ℝ × ℝ → ℝ}
    (h₁ : MemLp g₁ 2 (B0579.cellMeasure c m)) (h₂ : MemLp g₂ 2 (B0579.cellMeasure c m)) :
    ‖liftC c m g₁ - liftC c m g₂‖ = (eLpNorm (g₁ - g₂) 2 (B0579.cellMeasure c m)).toReal := by
  rw [Lp.norm_def]
  congr 1
  have hae : ⇑(liftC c m g₁ - liftC c m g₂) =ᵐ[Planar.wMeasure m] liftFun c (g₁ - g₂) := by
    filter_upwards [Lp.coeFn_sub (liftC c m g₁) (liftC c m g₂), coeFn_liftC h₁, coeFn_liftC h₂]
      with z hz h1 h2
    rw [hz, liftFun_sub, Pi.sub_apply, Pi.sub_apply, h1, h2]
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_liftFun (h₁.1.sub h₂.1)

/-- `X_{m,c}` convergence of cell fields gives `L²_m` convergence of their lifts. -/
theorem tendsto_liftC {c m : ℝ} {ι : Type*} {l : Filter ι} {g : ι → ℝ × ℝ → ℝ}
    {g₀ : ℝ × ℝ → ℝ} (hg₀ : MemLp g₀ 2 (B0579.cellMeasure c m))
    (hg : ∀ᶠ i in l, MemLp (g i) 2 (B0579.cellMeasure c m))
    (h : Tendsto (fun i => eLpNorm (g i - g₀) 2 (B0579.cellMeasure c m)) l (𝓝 0)) :
    Tendsto (fun i => liftC c m (g i)) l (𝓝 (liftC c m g₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at h'
  refine h'.congr' ?_
  filter_upwards [hg] with i hi
  exact (norm_liftC_sub hi hg₀).symm

end UnforcedLeray.Short.IIIa.RelB4locAux
