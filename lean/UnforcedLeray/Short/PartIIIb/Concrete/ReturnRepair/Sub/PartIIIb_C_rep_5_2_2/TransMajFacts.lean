import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3_1

/-!
# `PartIII-b:C/rep/5/2/2/7` : `TransMajFacts`

Source `the November 2 reference manuscript` 2683, 3611-3617, 4171-4178: the three
components of the transition majorant of an axisymmetric separated source are jointly measurable,
`P`-periodic and axisymmetric.  Measurability: `sepAE_measurable_sepDom`, `srcNorm_measurable`;
periodicity from `IsSepSource.periodic`; axisymmetry: `sepDom` is invariant under the rotations
about the vertical axis (Lebesgue measure invariant, `sepKd` depends on the norm only), and
`outMaj`, `streamAnn` depend on `y` only through `ϱ y` and `y 2`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The linear isometry `actM M` of `Space` for orthogonal `M`. -/
def tmfIso {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1) : Space ≃ₗᵢ[ℝ] Space where
  toFun := actM M
  map_add' x y := by
    ext i
    simp [actM_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [actM_apply, Finset.mul_sum, mul_left_comm]
  invFun := actM M.transpose
  left_inv x := actM_actM hM x
  right_inv x := actM_actM' hM x
  norm_map' x := norm_actM hM x

theorem tmf_trace_sq (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i, ∑ j, B i j ^ 2) = (B * B.transpose).trace := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

theorem tmf_tensorNorm_conj {R A : Matrix (Fin 3) (Fin 3) ℝ} (hR : R * R.transpose = 1) :
    IIIa.tensorNorm (R * A * R.transpose) = IIIa.tensorNorm A := by
  have hR' : R.transpose * R = 1 := mul_eq_one_comm.1 hR
  unfold IIIa.tensorNorm
  congr 1
  rw [tmf_trace_sq, tmf_trace_sq]
  have h1 : (R * A * R.transpose) * (R * A * R.transpose).transpose =
      R * (A * A.transpose) * R.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc R * A * R.transpose * (R * (A.transpose * R.transpose))
        = R * A * (R.transpose * R) * (A.transpose * R.transpose) := by
          simp only [Matrix.mul_assoc]
      _ = R * (A * A.transpose) * R.transpose := by
          rw [hR', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hR', Matrix.one_mul]

theorem tmf_srcNorm_rot {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hT : IsAxiSource T)
    {co si : ℝ} (h : co ^ 2 + si ^ 2 = 1) (τ : ℝ) (z : Space) :
    IIIa.srcNorm T τ (actM (rotM co si) z) = IIIa.srcNorm T τ z := by
  unfold IIIa.srcNorm
  rw [hT.1 co si h τ z, tmf_tensorNorm_conj (rotM_orth h)]

theorem tmf_sepDom_actM {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M * M.transpose = 1)
    (a : ℝ) (j : ℕ) (D : ℝ) (g : ℝ → Space → ℝ≥0∞) (hg : ∀ τ z, g τ (actM M z) = g τ z)
    (τ : ℝ) (y : Space) :
    IIIa.sepDom a j D g τ (actM M y) = IIIa.sepDom a j D g τ y := by
  unfold IIIa.sepDom
  refine lintegral_congr fun l => ?_
  congr 1
  have key := (tmfIso hM).measurePreserving.lintegral_comp_emb
    (tmfIso hM).toHomeomorph.measurableEmbedding
    (fun z => IIIa.sepKd j D (actM M y - l • z) * g (τ + 2 * Real.log l) z)
  have key' : ∫⁻ w : Space, IIIa.sepKd j D (actM M y - l • actM M w) *
      g (τ + 2 * Real.log l) (actM M w) =
      ∫⁻ z : Space, IIIa.sepKd j D (actM M y - l • z) * g (τ + 2 * Real.log l) z := key
  rw [← key']
  refine lintegral_congr fun w => ?_
  have e : actM M y - l • actM M w = actM M (y - l • w) := by
    have h := (tmfIso hM).map_sub y (l • w)
    rw [(tmfIso hM).map_smul] at h
    exact h.symm
  rw [e, hg]
  have : IIIa.sepKd j D (actM M (y - l • w)) = IIIa.sepKd j D (y - l • w) := by
    unfold IIIa.sepKd; rw [norm_actM hM]
  rw [this]

theorem tmf_exists_rot (y y' : Space) (h2 : y' 2 = y 2)
    (hr : y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2) :
    ∃ co si : ℝ, co ^ 2 + si ^ 2 = 1 ∧ actM (rotM co si) y = y' := by
  by_cases hz : y 0 ^ 2 + y 1 ^ 2 = 0
  · have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h0' : y' 0 = 0 := by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]
    have h1' : y' 1 = 0 := by nlinarith [sq_nonneg (y' 0), sq_nonneg (y' 1)]
    refine ⟨1, 0, by norm_num, ?_⟩
    ext i
    fin_cases i <;> simp [actM_apply, rotM, Fin.sum_univ_three, h0, h1, h0', h1', h2]
  · have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
    refine ⟨(y 0 * y' 0 + y 1 * y' 1) / (y 0 ^ 2 + y 1 ^ 2),
      (y 0 * y' 1 - y 1 * y' 0) / (y 0 ^ 2 + y 1 ^ 2), ?_, ?_⟩
    · field_simp
      nlinarith [hr]
    · ext i
      fin_cases i
      · simp [actM_apply, rotM, Fin.sum_univ_three]
        field_simp
        ring
      · simp [actM_apply, rotM, Fin.sum_univ_three]
        field_simp
        ring
      · simp [actM_apply, rotM, Fin.sum_univ_three, h2]

theorem tmf_sepDom_periodic (a : ℝ) (j : ℕ) (D P : ℝ) (g : ℝ → Space → ℝ≥0∞)
    (hg : ∀ τ z, g (τ + P) z = g τ z) (τ : ℝ) (y : Space) :
    IIIa.sepDom a j D g (τ + P) y = IIIa.sepDom a j D g τ y := by
  unfold IIIa.sepDom
  refine lintegral_congr fun l => ?_
  congr 1
  refine lintegral_congr fun z => ?_
  rw [show τ + P + 2 * Real.log l = (τ + 2 * Real.log l) + P by ring, hg]

theorem tmf_meas_varrho : Measurable ϱ := by
  unfold ϱ
  have h0 : Continuous fun y : Space => y 0 := by fun_prop
  have h1 : Continuous fun y : Space => y 1 := by fun_prop
  exact (Real.continuous_sqrt.comp ((h0.pow 2).add (h1.pow 2))).measurable

theorem tmf_meas_streamAnn (ν R : ℝ) : MeasurableSet (streamAnn ν R) := by
  unfold streamAnn
  exact (measurableSet_le measurable_const tmf_meas_varrho).inter
    (measurableSet_le tmf_meas_varrho measurable_const)

theorem tmf_meas_ind {S : Set Space} (hS : MeasurableSet S) {f : ℝ → Space → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry fun τ y => S.indicator (f τ) y) := by
  have : Function.uncurry (fun τ y => S.indicator (f τ) y) =
      ({p : ℝ × Space | p.2 ∈ S}).indicator (Function.uncurry f) := by
    funext p
    simp [Set.indicator, Function.uncurry]
  rw [this]
  exact hf.indicator (measurable_snd hS)

theorem tmf_meas_pt : Measurable (fun q : ℝ × ℝ => (!₂[q.1, 0, q.2] : Space)) := by
  have : Continuous (fun q : ℝ × ℝ => (!₂[q.1, 0, q.2] : Space)) := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact this.measurable

theorem tmf_meas_outMaj (a D : ℝ) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × Space => outMaj a D g p.1 (ϱ p.2) (p.2 2)) := by
  have hs := IIIa.sepAE_measurable_sepDom a 0 D hg
  have h3 : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ =>
      if q.1.2.1 < q.2 then ENNReal.ofReal q.2 *
        IIIa.sepDom a 0 D g q.1.1 !₂[q.2, 0, q.1.2.2] else 0) := by
    refine Measurable.ite (measurableSet_lt (measurable_fst.comp (measurable_snd.comp measurable_fst))
      measurable_snd) (ENNReal.measurable_ofReal.comp measurable_snd |>.mul ?_) measurable_const
    have hq : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ =>
        (q.1.1, (!₂[q.2, 0, q.1.2.2] : Space))) :=
      (measurable_fst.comp measurable_fst).prodMk
        (tmf_meas_pt.comp (measurable_snd.prodMk (measurable_snd.comp (measurable_snd.comp
          measurable_fst))))
    have hc := hs.comp hq
    simpa only [Function.comp_def, Function.uncurry] using hc
  have h4 := Measurable.lintegral_prod_right (ν := (volume : Measure ℝ)) (f := fun (x : ℝ × ℝ × ℝ) (ρ : ℝ) =>
    if x.2.1 < ρ then ENNReal.ofReal ρ * IIIa.sepDom a 0 D g x.1 !₂[ρ, 0, x.2.2] else 0) h3
  have h5 : (fun x : ℝ × ℝ × ℝ => outMaj a D g x.1 x.2.1 x.2.2) =
      fun x => ∫⁻ ρ, (if x.2.1 < ρ then ENNReal.ofReal ρ *
        IIIa.sepDom a 0 D g x.1 !₂[ρ, 0, x.2.2] else 0) := by
    funext x
    unfold outMaj
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun ρ => ?_
    simp [Set.indicator]
  have h6 : Measurable (fun x : ℝ × ℝ × ℝ => outMaj a D g x.1 x.2.1 x.2.2) := by
    rw [h5]; exact h4
  have h7 : Measurable (fun y : Space => y 2) := (by fun_prop : Continuous fun y : Space => y 2).measurable
  exact h6.comp (measurable_fst.prodMk ((tmf_meas_varrho.comp measurable_snd).prodMk
    (h7.comp measurable_snd)))

theorem tmf_varrho_eq {y y' : Space} (hr : y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2) :
    ϱ y' = ϱ y := by
  unfold ϱ; rw [hr]

theorem tmf_chartGood {ν R P : ℝ} {f : ℝ → Space → ℝ≥0∞}
    (hm : Measurable (Function.uncurry f)) (hp : ∀ τ y, f (τ + P) y = f τ y)
    (ha : ∀ τ (y y' : Space), y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 →
      f τ y' = f τ y) :
    ChartGood P (fun τ y => (streamAnn ν R).indicator (f τ) y) := by
  refine ⟨tmf_meas_ind (tmf_meas_streamAnn ν R) hm, fun τ y => ?_, fun τ y y' h2 hr => ?_⟩
  · simp only [Set.indicator, hp]
  · have hv := tmf_varrho_eq hr
    have hmem : y' ∈ streamAnn ν R ↔ y ∈ streamAnn ν R := by
      unfold streamAnn; simp only [Set.mem_setOf_eq, hv]
    by_cases hy : y ∈ streamAnn ν R
    · simp [Set.indicator, hy, hmem.2 hy, ha τ y y' h2 hr]
    · simp [Set.indicator, hy, mt hmem.1 hy]

/-- **`TransMajFacts`** (source 2683, 3611-3617, 4171-4178). -/
theorem transMajFacts : TransMajFacts := by
  intro ν R P hν hR hP T hT hA
  have hmeas := srcNorm_measurable hT
  have hper : ∀ τ z, IIIa.srcNorm T (τ + P) z = IIIa.srcNorm T τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hT.periodic]
  have hax : ∀ (a : ℝ) (j : ℕ) (D : ℝ) τ (y y' : Space), y' 2 = y 2 →
      y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 →
      IIIa.sepDom a j D (IIIa.srcNorm T) τ y' = IIIa.sepDom a j D (IIIa.srcNorm T) τ y := by
    intro a j D τ y y' h2 hr
    obtain ⟨co, si, h, hy⟩ := tmf_exists_rot y y' h2 hr
    rw [← hy]
    exact tmf_sepDom_actM (rotM_orth h) a j D _ (fun τ z => tmf_srcNorm_rot hA h τ z) τ y
  refine ⟨?_, ?_, ?_⟩
  · unfold transMajW
    exact tmf_chartGood (f := fun τ y => IIIa.sepDom 0 0 (transGap ν R) (IIIa.srcNorm T) τ y)
      (IIIa.sepAE_measurable_sepDom 0 0 _ hmeas)
      (fun τ y => tmf_sepDom_periodic 0 0 _ P _ hper τ y) (fun τ y y' h2 hr => hax 0 0 _ τ y y' h2 hr)
  · unfold transMajD
    exact tmf_chartGood
      (f := fun τ y => ENNReal.ofReal (transLen ν R)⁻¹ *
        IIIa.sepDom 0 1 (transGap ν R) (IIIa.srcNorm T) τ y)
      (measurable_const.mul (IIIa.sepAE_measurable_sepDom 0 1 _ hmeas))
      (fun τ y => by simp only [tmf_sepDom_periodic 0 1 _ P _ hper τ y])
      (fun τ y y' h2 hr => by simp only [hax 0 1 _ τ y y' h2 hr])
  · unfold transMajS
    exact tmf_chartGood
      (f := fun τ y => ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
        outMaj 0 (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2))
      (measurable_const.mul (tmf_meas_outMaj 0 _ hmeas))
      (fun τ y => by
        unfold outMaj
        simp only [tmf_sepDom_periodic 0 0 _ P _ hper])
      (fun τ y y' h2 hr => by rw [h2, tmf_varrho_eq hr])

end UnforcedLeray.Short.PartIIIb.Concrete
