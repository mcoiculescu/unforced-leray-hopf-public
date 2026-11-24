import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K3

/-!
# Proof of `SepDomFacts` (`PartIII-b:C/rep/5/2/1/3`, source 2683, 3611-3617)

Measurability of `srcNorm (cartLift ..)` and of `sepDom` (two applications of
`Measurable.lintegral_prod_right'`), `2c/R`-periodicity (the `q`-coordinate shifts by `c` inside
the floor), and axisymmetry (rotation about the axis: `rot_chart`, `rot_cyl`, conjugation
invariance of the Frobenius norm, change of variables `z ↦ Az`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sd_floor_shift (X c : ℝ) (hc : 0 < c) :
    X + c - c * ⌊(X + c) / c + 1 / 2⌋ = X - c * ⌊X / c + 1 / 2⌋ := by
  have hc' : c ≠ 0 := hc.ne'
  rw [show (X + c) / c + 1 / 2 = X / c + 1 / 2 + 1 by field_simp; ring, Int.floor_add_one]
  push_cast
  ring

theorem sd_chartOf_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : Space) (τ : ℝ) :
    NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
  have hR' : R ≠ 0 := hR.ne'
  have hX : R * Real.log (NearInst.hRad z / R) + R * (τ + 2 * c / R) / 2 =
      (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + c := by
    field_simp
    ring
  unfold NearInst.chartOf
  rw [hX, sd_floor_shift _ c hc]

theorem sd_tensorNorm_conj (A M : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * A.transpose = 1) :
    UnforcedLeray.Short.IIIa.tensorNorm (A * M * A.transpose) =
      UnforcedLeray.Short.IIIa.tensorNorm M := by
  have key : ∀ N : Matrix (Fin 3) (Fin 3) ℝ,
      ∑ i, ∑ j, N i j ^ 2 = (N * N.transpose).trace := by
    intro N
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have hA' : A.transpose * A = 1 := mul_eq_one_comm.1 hA
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  congr 1
  rw [key, key]
  have : (A * M * A.transpose) * (A * M * A.transpose).transpose =
      A * (M * M.transpose) * A.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.transpose A, hA', Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA', Matrix.one_mul]


open UnforcedLeray.Short.IIIa in
theorem sd_measurable_srcNorm (R c : ℝ) (f : Chart → Ten3) (hf : Measurable f) :
    Measurable (Function.uncurry (srcNorm (NearInst.cartLift R c f))) := by
  unfold srcNorm tensorNorm Function.uncurry
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  exact (T8_1.measurable_cartLift_entry R c f hf i j).pow_const 2

open UnforcedLeray.Short.IIIa in
theorem sd_measurable_sepKd (j : ℕ) (D : ℝ) : Measurable (sepKd j D) := by
  unfold sepKd
  refine Measurable.ite (measurableSet_le measurable_const measurable_norm) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)

open UnforcedLeray.Short.IIIa in
theorem sd_measurable_sepDom (a : ℝ) (j : ℕ) (D : ℝ) (g : ℝ → Space → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) : Measurable (Function.uncurry (sepDom a j D g)) := by
  unfold sepDom Function.uncurry
  have h1 : Measurable fun p : ((ℝ × Space) × ℝ) × Space =>
      sepKd j D (p.1.1.2 - p.1.2 • p.2) * g (p.1.1.1 + 2 * Real.log p.1.2) p.2 := by
    refine ((sd_measurable_sepKd j D).comp ?_).mul ?_
    · exact (measurable_snd.comp (measurable_fst.comp measurable_fst)).sub
        ((measurable_snd.comp measurable_fst).smul measurable_snd)
    · refine hg.comp (Measurable.prodMk ?_ measurable_snd)
      exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
        (measurable_const.mul (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))
  have h2 := h1.lintegral_prod_right' (ν := (volume : Measure Space))
  have h3 : Measurable fun p : (ℝ × Space) × ℝ =>
      ENNReal.ofReal (p.2 ^ a) * ∫⁻ z : Space, sepKd j D (p.1.2 - p.2 • z) *
        g (p.1.1 + 2 * Real.log p.2) z :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)).mul h2
  exact h3.lintegral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) 1))


open UnforcedLeray.Short.IIIa in
theorem sd_srcNorm_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3) (τ : ℝ)
    (z : Space) :
    srcNorm (NearInst.cartLift R c f) (τ + 2 * c / R) z = srcNorm (NearInst.cartLift R c f) τ z := by
  unfold srcNorm NearInst.cartLift
  rw [sd_chartOf_period R c hR hc z τ]

open UnforcedLeray.Short.IIIa in
theorem sd_sepDom_period (a : ℝ) (j : ℕ) (D R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3)
    (τ : ℝ) (y : Space) :
    sepDom a j D (srcNorm (NearInst.cartLift R c f)) (τ + 2 * c / R) y =
      sepDom a j D (srcNorm (NearInst.cartLift R c f)) τ y := by
  unfold sepDom
  refine lintegral_congr (fun l => ?_)
  congr 1
  refine lintegral_congr (fun z => ?_)
  rw [add_right_comm, sd_srcNorm_period R c hR hc f _ z]

open UnforcedLeray.Short.IIIa in
theorem sd_srcNorm_rot (R c : ℝ) (f : Chart → Ten3) (co si : ℝ) (hco : co ^ 2 + si ^ 2 = 1)
    (τ : ℝ) (z : Space) :
    srcNorm (NearInst.cartLift R c f) τ (actM (rotM co si) z) =
      srcNorm (NearInst.cartLift R c f) τ z := by
  unfold srcNorm
  congr 1
  have h : NearInst.cartLift R c f τ (actM (rotM co si) z) =
      rotM co si * NearInst.cartLift R c f τ z * (rotM co si).transpose := by
    simp only [NearInst.cartLift]
    rw [rot_chart R c co si hco z τ, rot_cyl co si hco z]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h]
  exact sd_tensorNorm_conj _ _ (rotM_orth hco)

theorem sd_exists_rot (y y' : Space) (h2 : y' 2 = y 2)
    (h : y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2) :
    ∃ co si : ℝ, co ^ 2 + si ^ 2 = 1 ∧ actM (rotM co si) y = y' := by
  by_cases h0 : y 0 ^ 2 + y 1 ^ 2 = 0
  · have a0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have a1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have b0 : y' 0 = 0 := by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]
    have b1 : y' 1 = 0 := by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]
    refine ⟨1, 0, by norm_num, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, rot_z0, a0, a1, b0]; ring
    · simp only [Fin.mk_one, rot_z1, a0, a1, b1]; ring
    · simp only [Fin.reduceFinMk, rot_z2, h2]
  · have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set ρ := y 0 ^ 2 + y 1 ^ 2 with hρ
    refine ⟨(y 0 * y' 0 + y 1 * y' 1) / ρ, (y 0 * y' 1 - y 1 * y' 0) / ρ, ?_, ?_⟩
    · field_simp
      nlinarith [h]
    · ext i
      fin_cases i
      · simp only [Fin.zero_eta, rot_z0]; field_simp; ring
      · simp only [Fin.mk_one, rot_z1]; field_simp; ring
      · simp only [Fin.reduceFinMk, rot_z2, h2]

open UnforcedLeray.Short.IIIa in
theorem sd_sepDom_rot (a : ℝ) (j : ℕ) (D : ℝ) (g : ℝ → Space → ℝ≥0∞) (co si : ℝ)
    (hco : co ^ 2 + si ^ 2 = 1) (hg : ∀ τ z, g τ (actM (rotM co si) z) = g τ z) (τ : ℝ)
    (y : Space) :
    sepDom a j D g τ (actM (rotM co si) y) = sepDom a j D g τ y := by
  have hM := rotM_orth hco
  unfold sepDom
  refine lintegral_congr (fun l => ?_)
  congr 1
  have hfun : ⇑(lieOf hM) = actM (rotM co si) := funext fun x => cleOf_apply hM x
  have mp : MeasurePreserving (actM (rotM co si)) volume volume := by
    have := (lieOf hM).measurePreserving
    rwa [hfun] at this
  have emb : MeasurableEmbedding (actM (rotM co si)) := by
    have := (cleOf hM).toHomeomorph.measurableEmbedding
    have hf2 : ⇑(cleOf hM).toHomeomorph = actM (rotM co si) :=
      funext fun x => cleOf_apply hM x
    rwa [hf2] at this
  have hlin : ∀ w : Space, actM (rotM co si) (y - l • w) =
      actM (rotM co si) y - l • actM (rotM co si) w := by
    intro w
    rw [← clmOf_apply, ← clmOf_apply, ← clmOf_apply, map_sub, map_smul]
  rw [← mp.lintegral_comp_emb emb]
  refine lintegral_congr (fun w => ?_)
  have e1 : sepKd j D (actM (rotM co si) y - l • actM (rotM co si) w) = sepKd j D (y - l • w) := by
    rw [← hlin]
    unfold sepKd
    rw [norm_actM hM]
  rw [e1, hg]


/-- `SepDomFacts` (source 2683, 3611-3617). -/
theorem sepDomFacts : SepDomFacts := by
  intro a j D R c hR hc f hf
  refine ⟨sd_measurable_sepDom a j D _ (sd_measurable_srcNorm R c f hf),
    sd_measurable_srcNorm R c f hf, sd_srcNorm_period R c hR hc f,
    sd_sepDom_period a j D R c hR hc f, ?_⟩
  intro τ y y' h2 h
  obtain ⟨co, si, hco, hy⟩ := sd_exists_rot y y' h2 h
  rw [← hy]
  exact sd_sepDom_rot a j D _ co si hco (fun τ z => sd_srcNorm_rot R c f co si hco τ z) τ y

end UnforcedLeray.Short.PartIIIb.Concrete
