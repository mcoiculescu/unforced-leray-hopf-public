import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStepOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStep.PointMass
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.L223.Meas
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5

/-!
# `PartIII-b:C/rep/4/2/org/3/4/2`: the `L^{22/3}` kernel step `TransMajMassL223`

Source `the November 2 reference manuscript` 3631-3646 (`sep:young`, `p = 1`,
`q = b = 22/3`: `D^{-4+3/b} = D^{-79/22}`), 3669-3679 (`sep:thin-global`, `q = 22/3`),
3683-3701 (stream cutoff majorant), 5333-5340 (thin-to-repair entry).

Order zero and one: `sepDomYoung` with `p = 1`, `q = b = 22/3`, plus scalar Minkowski
`PmStep.ltauAt_minkowski_space`.  Primitive: reduction to the vertical profile (`outMajReduce`),
annulus Fubini (`annulusFubiniL223`), vertical Young with `p = 1`, `q = b = 22/3` (`vert1DYoung`,
`vertDil`, `vertMinkowski`), and `PmStep.ltauAt_Kint_le`.  Sum: `L223.ltauLq_add_le`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace MassL223

/-- The `22/3`-power of the vertical kernel. -/
theorem vkl223_pow_eq (rIn D t : ℝ) (hr : 0 < rIn) (hD : 0 < D) :
    vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ)) *
        ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ))) := by
  have hq : 0 < D ^ 2 + t ^ 2 := by positivity
  have hA : 0 < rIn / (2 * D) := by positivity
  have hnn : 0 ≤ rIn / (2 * D * (D ^ 2 + t ^ 2)) := by positivity
  have hx : rIn / (2 * D * (D ^ 2 + t ^ 2)) = (rIn / (2 * D)) * (D ^ 2 + t ^ 2) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    field_simp
  have key : (rIn / (2 * D * (D ^ 2 + t ^ 2))) ^ (22 / 3 : ℝ) =
      (rIn / (2 * D)) ^ (22 / 3 : ℝ) * (D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ)) := by
    rw [hx, Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul hq.le]
    norm_num
  unfold vertKern
  rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num), key,
    ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _)]

/-- The lintegral of `(D²+t²)^{-22/3}` in terms of the reference integral. -/
theorem vkl223_integral_eq {D : ℝ} (hD : 0 < D) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ))) =
      ENNReal.ofReal (D ^ (-(41 / 3 : ℝ))) *
        ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) := by
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal ((D ^ 2 + t ^ 2) ^ (-(22 / 3 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [vkl_lintegral_scale hD _ hmeas]
  have hpt : ∀ u : ℝ, ENNReal.ofReal ((D ^ 2 + (D * u) ^ 2) ^ (-(22 / 3 : ℝ))) =
      ENNReal.ofReal (D ^ (-(44 / 3 : ℝ))) * ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) := by
    intro u
    have h1 : D ^ 2 + (D * u) ^ 2 = D ^ 2 * (1 + u ^ 2) := by ring
    rw [h1, Real.mul_rpow (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := (D ^ 2) ^ (-(22 / 3 : ℝ))) (by positivity)]
    congr 2
    rw [← Real.rpow_natCast D 2, ← Real.rpow_mul hD.le]
    norm_num
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul hD.le,
    show D * D ^ (-(44 / 3 : ℝ)) = D ^ (-(41 / 3 : ℝ)) by
      rw [show (-(41 / 3 : ℝ)) = 1 + -(44 / 3 : ℝ) by norm_num, Real.rpow_add hD, Real.rpow_one]]

/-- The vertical kernel in `L^{22/3}(ℝ)` (source 3683-3701). -/
theorem vertKernLb223 :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D →
      lqNorm1 (22 / 3) (vertKern rIn D) ≤ ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) := by
  have hint : MeasureTheory.Integrable (fun u : ℝ => (1 + u ^ 2) ^ (-(22 / 3 : ℝ))) := by
    have h2 : (fun u : ℝ => (1 + u ^ 2) ^ (-(22 / 3 : ℝ))) =
        fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(44 / 3 : ℝ) / 2) := by
      funext u
      rw [Real.norm_eq_abs, sq_abs]
      norm_num
    rw [h2]
    exact integrable_rpow_neg_one_add_norm_sq (r := 44 / 3) (by
      simp only [Module.finrank_self, Nat.cast_one]
      norm_num)
  have hJ : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) ≠ ⊤ :=
    (hint.lintegral_lt_top).ne
  refine ⟨(1 / 2) * (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal ^ (3 / 22 : ℝ),
    mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _), ?_⟩
  intro rIn D hr hD
  have hA : 0 < rIn / (2 * D) := by positivity
  have hIt : ∫⁻ t : ℝ, vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ)) *
        (ENNReal.ofReal (D ^ (-(41 / 3 : ℝ))) *
          ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))) := by
    simp_rw [vkl223_pow_eq rIn D _ hr hD]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, vkl223_integral_eq hD]
  have hIr : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) =
      ENNReal.ofReal (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal :=
    (ENNReal.ofReal_toReal hJ).symm
  have hQ : ∫⁻ t : ℝ, vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ) * D ^ (-(41 / 3 : ℝ)) *
        (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal) := by
    rw [hIt]
    conv_lhs => rw [hIr]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  have heq : ((rIn / (2 * D)) ^ (22 / 3 : ℝ) * D ^ (-(41 / 3 : ℝ)) *
        (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal) ^ (1 / (22 / 3 : ℝ)) =
      (1 / 2) * (∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ)))).toReal ^ (3 / 22 : ℝ) *
        (rIn / D) * D ^ (-(41 / 22 : ℝ)) := by
    rw [show (1 / (22 / 3 : ℝ)) = 3 / 22 by norm_num,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hA.le, ← Real.rpow_mul hD.le,
      show (22 / 3 : ℝ) * (3 / 22) = 1 by norm_num,
      show (-(41 / 3 : ℝ)) * (3 / 22) = -(41 / 22) by norm_num, Real.rpow_one]
    ring
  unfold lqNorm1
  rw [hQ, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), heq]
  apply ENNReal.ofReal_le_ofReal
  rw [show (-2 + 3 / 22 : ℝ) = -(41 / 22) by norm_num]

/-- Scaled 1D Young inequality for the vertical kernel with `p = 1`, `q = b = 22/3`. -/
theorem vertKernYoungMass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D → ∀ l : ℝ, 0 < l → l < 1 →
      ∀ g' : ℝ → ℝ≥0∞, Measurable g' →
        lqNorm1 (22 / 3) (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * g' s) ≤
          ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * lqNorm1 1 g' := by
  obtain ⟨c, hc, hKb⟩ := vertKernLb223
  refine ⟨c + 1, by linarith, ?_⟩
  intro rIn D hrIn hD0 l hl0 _hl1 g' hg'
  have hepos : 0 < (c + 1) * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ) := by positivity
  by_cases htop : lqNorm1 1 g' = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hepos).ne']
    exact le_top
  · obtain ⟨hD1, hD2⟩ := vertDil l hl0
    set S := vertKern rIn D with hS
    set gl : ℝ → ℝ≥0∞ := fun w => g' (l⁻¹ * w) with hgl
    have hglm : Measurable gl := hg'.comp (measurable_const.mul measurable_id)
    have hSm : Measurable S := by
      rw [hS]; unfold vertKern
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    have hSt : ∀ x, S x ≠ ⊤ := fun x => by rw [hS]; unfold vertKern; exact ENNReal.ofReal_ne_top
    have hdil : lqNorm1 1 gl = ENNReal.ofReal (l ^ (1 / (1 : ℝ))) * lqNorm1 1 g' :=
      hD2 1 (by norm_num) g'
    have hgltop : lqNorm1 1 gl ≠ ⊤ := by
      rw [hdil]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
    have hfun : (fun z => ∫⁻ s : ℝ, S (z - l * s) * g' s) =
        fun z => ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * gl w := funext fun z => hD1 S g' z
    rw [hfun, lqNorm1_const_mul (by norm_num) ENNReal.ofReal_ne_top]
    have hy := vert1DYoung S gl hSm hSt hglm (22 / 3) 1 (22 / 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgltop
    have hKb' := hKb rIn D hrIn hD0
    have hid : ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (1 : ℝ))) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), div_one, Real.rpow_one,
        inv_mul_cancel₀ hl0.ne', ENNReal.ofReal_one]
    have hle : lqNorm1 (22 / 3) S ≤ ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) := by
      refine hKb'.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (rIn / D) * D ^ (-2 + 3 / 22 : ℝ) := by positivity
      nlinarith
    calc ENNReal.ofReal l⁻¹ * lqNorm1 (22 / 3) (fun z => ∫⁻ w : ℝ, S (z - w) * gl w)
        ≤ ENNReal.ofReal l⁻¹ * (lqNorm1 (22 / 3) S * lqNorm1 1 gl) := by gcongr
      _ ≤ ENNReal.ofReal l⁻¹ * (ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
            lqNorm1 1 gl) := by gcongr
      _ = ENNReal.ofReal ((c + 1) * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
            ((ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (1 : ℝ)))) * lqNorm1 1 g') := by
          rw [hdil]; ring
      _ = _ := by rw [hid, one_mul]

/-- The `L¹(ℝ)` norm of the vertical profile is the `L¹(Space)` mass of the slice. -/
theorem lqNorm1_one_vprof {g : ℝ → Space → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    lqNorm1 1 (vprof g τ) = ∫⁻ z' : Space, g τ z' := by
  unfold lqNorm1
  simp only [ENNReal.rpow_one, div_one]
  have hGm : Measurable (fun z' : Space => g τ z') :=
    hg.comp (measurable_const.prodMk measurable_id)
  have h := outRed_slice (fun _ : ℝ => (1 : ℝ≥0∞)) measurable_const (fun z' => g τ z') hGm
  simpa [vprof] using h.symm

/-- Phase-space bound for `vertRed 0 rIn D g` against the slice phase norms. -/
theorem vertRed_ltauLq1_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (rIn D P : ℝ), 0 < rIn → 0 < D → 0 < P →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
        ltauLq1 P (22 / 3) (vertRed 0 rIn D g) ≤
          ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
            ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
  obtain ⟨CY, hCY, hY⟩ := vertKernYoungMass
  refine ⟨CY, hCY, ?_⟩
  intro rIn D P hrIn hD0 hP g hgm hper
  have hvm := (vertMeasurable g hgm).1
  have hpt : ∀ τ, lqNorm1 (22 / 3) (vertRed 0 rIn D g τ) ≤
      ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * PmStep.Kint g τ := by
    intro τ
    unfold vertRed
    refine (vertMinkowski 0 rIn D (22 / 3) (by norm_num) (vprof g) hvm τ).trans ?_
    calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (0 : ℝ)) *
          lqNorm1 (22 / 3) (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) *
            vprof g (τ + 2 * Real.log l) s)
        ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
            ∫⁻ z' : Space, g (τ + 2 * Real.log l) z' := by
          refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
          rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul]
          have hvl : Measurable (vprof g (τ + 2 * Real.log l)) :=
            hvm.comp (measurable_const.prodMk measurable_id)
          refine (hY rIn D hrIn hD0 l hl.1 hl.2 _ hvl).trans_eq ?_
          rw [lqNorm1_one_vprof hgm]
      _ = ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * PmStep.Kint g τ := by
          unfold PmStep.Kint
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [← ltauAt_lqNorm1_eq P (22 / 3) (vertRed 0 rIn D g)]
  calc IIIa.ltauAt P (fun τ => lqNorm1 (22 / 3) (vertRed 0 rIn D g τ))
      ≤ IIIa.ltauAt P (fun τ =>
          ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * PmStep.Kint g τ) :=
        IIIa.ltauAt_mono P hpt
    _ = ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * IIIa.ltauAt P (PmStep.Kint g) :=
        IIIa.ltauAt_const_mul P _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (CY * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) :=
        mul_le_mul' le_rfl (PmStep.ltauAt_Kint_le hP hgm hper)

/-- Scalar power identity for the annulus-integrated outward primitive against the mass. -/
theorem outAnnMass_alg (Cy R ν : ℝ) (hν : 0 < ν) (hR : 0 < R) :
    (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) *
        (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 22 : ℝ)) =
      Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) *
        (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) *
        (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ)) := by
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hc : Real.pi * ν * R ^ 2 / 4 = (Real.pi / 4) * (R * Real.sqrt ν) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hA : (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) =
      (Real.pi / 4) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) := by
    rw [hc, Real.mul_rpow (show (0 : ℝ) ≤ Real.pi / 4 by positivity) (sq_nonneg _),
      outAnn7_alg_pow _ hrIn0]
  have hB : (R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) =
      (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ := by
    have h1 : (1 - Real.sqrt (5 / 6 : ℝ)) ≠ 0 := hd0.ne'
    have h2 : R * Real.sqrt ν ≠ 0 := hrIn0.ne'
    rw [hD]
    field_simp
  have hE : (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 22 : ℝ) =
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ) := by
    rw [hD, Real.mul_rpow hd0.le hrIn0.le]
  have hpow : (R * Real.sqrt ν) ^ (3 / 11 : ℝ) *
      (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ) = (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ)) := by
    rw [← Real.rpow_add hrIn0]
    norm_num
  rw [hA, hB, hE]
  calc (Real.pi / 4) ^ (3 / 22 : ℝ) * (R * Real.sqrt ν) ^ (3 / 11 : ℝ) *
        (Cy * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹ *
          ((1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) *
            (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ)))
      = Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) *
          (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹) *
          ((R * Real.sqrt ν) ^ (3 / 11 : ℝ) * (R * Real.sqrt ν) ^ (-2 + 3 / 22 : ℝ)) := by ring
    _ = _ := by rw [hpow]

/-- The outward primitive majorant on the annulus in `L²_τL^{22/3}` against the mass. -/
theorem outMajAnnulusMassL223 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R P : ℝ), 0 < ν → 0 < R → 0 < P →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
        (∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
          IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
              (fun y => outMaj 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
            ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(35 / 22 : ℝ))) *
              ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
  obtain ⟨Cy, hCy, hY⟩ := vertRed_ltauLq1_le
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  refine ⟨Cy * ((Real.pi / 4) ^ (3 / 22 : ℝ) *
      (1 - Real.sqrt (5 / 6 : ℝ)) ^ (-2 + 3 / 22 : ℝ) * (1 - Real.sqrt (5 / 6 : ℝ))⁻¹),
    mul_nonneg hCy (mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg hd0.le _)) (inv_nonneg.2 hd0.le)), ?_⟩
  intro ν R P hν hR hP0 g hg hper hsupp
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) =
      (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    rw [hrO]; ring
  have hD0 : 0 < R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) := by
    rw [hD]; exact mul_pos hd0 hrIn0
  have hrO0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by
    rw [hrO]; exact mul_nonneg hs0 hrIn0.le
  have hrOlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have := mul_lt_mul_of_pos_right hs1 hrIn0
    rw [hrO]; linarith
  have hunc : Measurable (Function.uncurry (vertRed 0 (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g)) :=
    (vertMeasurable g hg).2 0 (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))
  have stepA : IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
      (fun y => outMaj 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
      IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
      (fun y => vertRed 0 (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ
        (y 2))) := by
    refine IIIa.ltauLq_mono P (22 / 3) (by norm_num) (fun τ y => ?_)
    dsimp only
    by_cases hy : y ∈ streamAnn ν R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact outMajReduce 0 (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) hrO0 hrOlt g hg hsupp τ
        (ϱ y) (y 2) hy.1
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have stepB := annulusFubiniL223 ν R P hν hR hP0 (vertRed 0 (R * Real.sqrt ν)
      (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g) hunc
  have stepC := hY (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) P
    hrIn0 hD0 hP0 g hg hper
  have hA0 : (0 : ℝ) ≤ (Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hν.le) (sq_nonneg R))
      (by norm_num)) _
  calc IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
        (fun y => outMaj 0 (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2)))
      ≤ IIIa.ltauLq P (22 / 3) (fun τ => (streamAnn ν R).indicator
        (fun y => vertRed 0 (R * Real.sqrt ν) (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ
          (y 2))) := stepA
    _ = ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
        ltauLq1 P (22 / 3) (vertRed 0 (R * Real.sqrt ν)
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g) := stepB
    _ ≤ ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (3 / 22 : ℝ)) *
        (ENNReal.ofReal (Cy * ((R * Real.sqrt ν) / (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6))) *
          (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) ^ (-2 + 3 / 22 : ℝ)) *
          ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z)) :=
        mul_le_mul' le_rfl stepC
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hA0, outAnnMass_alg Cy R ν hν hR]

/-- Scalar Minkowski: `‖g‖_{L²_τL¹_z} ≤ ∫ ‖g(·,z)‖_{L²_τ} dz`. -/
theorem ltauLq_one_le {P : ℝ} (hP : 0 < P) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) :
    IIIa.ltauLq P 1 g ≤ ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) := by
  have heq : IIIa.ltauLq P 1 g = IIIa.ltauAt P (fun τ => ∫⁻ z : Space, g τ z) := by
    unfold IIIa.ltauLq IIIa.ltauAt
    simp [div_one]
  rw [heq]
  exact PmStep.ltauAt_minkowski_space hP hg

end MassL223

/-- **The `L^{22/3}` kernel step from the mass** (source 3669-3679, 3683-3701, 5333-5340). -/
theorem transMajMassL223 : TransMajMassL223 := by
  obtain ⟨C0, hC0, h0⟩ := sepDomYoung 0 1 (22 / 3) (22 / 3) 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C1, hC1, h1⟩ := sepDomYoung 1 1 (22 / 3) (22 / 3) 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, hS⟩ := MassL223.outMajAnnulusMassL223
  obtain ⟨s, _hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ s = Real.sqrt (5 / 6) := by
    refine ⟨_, Real.sqrt_nonneg _, ?_, rfl⟩
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hκ : 0 < 1 - s := by linarith
  have a1 := Real.rpow_nonneg hκ.le (-(79 / 22) : ℝ)
  have a2 := Real.rpow_nonneg hκ.le (-(101 / 22) : ℝ)
  refine ⟨C0 * (1 - s) ^ (-(79 / 22) : ℝ) + C1 * (1 - s) ^ (-(101 / 22) : ℝ) + Cs, 3,
    by positivity, ?_⟩
  intro ν R P hν hν1 hR1 hP g hgm hgp hgs
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := mul_pos hR hsq
  have hro : R * Real.sqrt (5 * ν / 6) = s * L := by
    rw [hLdef, hs, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hD : transGap ν R = (1 - s) * L := by
    unfold transGap; rw [hro]; ring
  have hDpos : 0 < transGap ν R := by rw [hD]; positivity
  set N := ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z) with hNdef
  have hNle : IIIa.ltauLq P 1 g ≤ N := MassL223.ltauLq_one_le hP hgm
  have hy0 : ∀ D' : ℝ, 0 < D' →
      IIIa.ltauLq P (22 / 3) (IIIa.sepDom 0 0 D' g) ≤
        ENNReal.ofReal (C0 * D' ^ (-(79 / 22) : ℝ)) * N := by
    intro D' hD'
    have := h0 0 le_rfl (by norm_num) D' P hD' hP g hgm hgp
    have e : (-4 - ((0 : ℕ) : ℝ) + 3 / (22 / 3) : ℝ) = -(79 / 22) := by norm_num
    rw [e] at this
    exact this.trans (mul_le_mul' le_rfl hNle)
  have hy1 : ∀ D' : ℝ, 0 < D' →
      IIIa.ltauLq P (22 / 3) (IIIa.sepDom 0 1 D' g) ≤
        ENNReal.ofReal (C1 * D' ^ (-(101 / 22) : ℝ)) * N := by
    intro D' hD'
    have := h1 0 le_rfl (by norm_num) D' P hD' hP g hgm hgp
    have e : (-4 - ((1 : ℕ) : ℝ) + 3 / (22 / 3) : ℝ) = -(101 / 22) := by norm_num
    rw [e] at this
    exact this.trans (mul_le_mul' le_rfl hNle)
  have hann := L223.measurableSet_ann ν R
  have mW : Measurable (Function.uncurry (transMajW ν R g)) := by
    have : Function.uncurry (transMajW ν R g) =
        (Prod.snd ⁻¹' streamAnn ν R).indicator
          (Function.uncurry (IIIa.sepDom 0 0 (transGap ν R) g)) := by
      funext p; by_cases h : p.2 ∈ streamAnn ν R <;>
        simp [transMajW, Set.indicator, Function.uncurry, h]
    rw [this]
    exact (sd_measurable_sepDom 0 0 _ g hgm).indicator (measurable_snd hann)
  have mD : Measurable (Function.uncurry (transMajD ν R g)) := by
    have : Function.uncurry (transMajD ν R g) =
        (Prod.snd ⁻¹' streamAnn ν R).indicator (fun p : ℝ × Space =>
          ENNReal.ofReal (transLen ν R)⁻¹ *
            (Function.uncurry (IIIa.sepDom 0 1 (transGap ν R) g)) p) := by
      funext p; by_cases h : p.2 ∈ streamAnn ν R <;>
        simp [transMajD, Set.indicator, Function.uncurry, h]
    rw [this]
    exact (measurable_const.mul (sd_measurable_sepDom 0 1 _ g hgm)).indicator (measurable_snd hann)
  have mS : Measurable (Function.uncurry (transMajS ν R g)) := by
    have hm := L223.measurable_outMaj3 0 (transGap ν R) hgm
    have h2 : Measurable (fun p : ℝ × Space => outMaj 0 (transGap ν R) g p.1 (ϱ p.2) (p.2 2)) :=
      hm.comp (measurable_fst.prodMk ((measurable_ϱ.comp measurable_snd).prodMk
        ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd)))
    have : Function.uncurry (transMajS ν R g) =
        (Prod.snd ⁻¹' streamAnn ν R).indicator (fun p : ℝ × Space =>
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            outMaj 0 (transGap ν R) g p.1 (ϱ p.2) (p.2 2)) := by
      funext p; by_cases h : p.2 ∈ streamAnn ν R <;>
        simp [transMajS, Set.indicator, Function.uncurry, h]
    rw [this]
    exact (measurable_const.mul h2).indicator (measurable_snd hann)
  set A : ℝ := ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ) with hAdef
  have hA : 0 ≤ A := mul_nonneg (by positivity) (Real.rpow_nonneg hR.le _)
  have bW : IIIa.ltauLq P (22 / 3) (transMajW ν R g) ≤
      ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ) * A) * N := by
    refine (IIIa.ltauLq_mono P _ (by norm_num) (fun τ y => ?_)).trans
      ((hy0 _ hDpos).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
    · exact Set.indicator_le_self' (fun _ _ => zero_le) y
    · rw [hD, Real.mul_rpow hκ.le hL.le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (PmStep.Lpow hν hν1 hR (by norm_num) (by norm_num))
        (by positivity)
  have bD : IIIa.ltauLq P (22 / 3) (transMajD ν R g) ≤
      ENNReal.ofReal (C1 * (1 - s) ^ (-(101 / 22) : ℝ) * A) * N := by
    have h1' : transMajD ν R g ≤ fun τ y =>
        ENNReal.ofReal L⁻¹ * IIIa.sepDom 0 1 (transGap ν R) g τ y :=
      fun τ y => by
        simp only [transMajD, transLen, hLdef]
        exact Set.indicator_le_self' (fun _ _ => zero_le) y
    refine (IIIa.ltauLq_mono P _ (by norm_num) h1').trans ?_
    rw [IIIa.ltauLq_const_mul P _ (by norm_num) _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (hy1 _ hDpos)).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hc1 : 0 ≤ C1 * (1 - s) ^ (-(101 / 22) : ℝ) := mul_nonneg hC1 a2
    have e0 : L⁻¹ * L ^ (-(101 / 22) : ℝ) = L ^ (-(123 / 22) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hL]; norm_num
    have e3 := PmStep.Lpow hν hν1 hR (e := -(123 / 22)) (by norm_num) (by norm_num)
    have e5 : R ^ (-(123 / 22) : ℝ) ≤ R ^ (-(79 / 22) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
    rw [hD, Real.mul_rpow hκ.le hL.le]
    calc L⁻¹ * (C1 * ((1 - s) ^ (-(101 / 22) : ℝ) * L ^ (-(101 / 22) : ℝ)))
        = C1 * (1 - s) ^ (-(101 / 22) : ℝ) * (L⁻¹ * L ^ (-(101 / 22) : ℝ)) := by ring
      _ = C1 * (1 - s) ^ (-(101 / 22) : ℝ) * L ^ (-(123 / 22) : ℝ) := by rw [e0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (e3.trans (mul_le_mul_of_nonneg_left e5 (by positivity))) hc1
  have bS : IIIa.ltauLq P (22 / 3) (transMajS ν R g) ≤
      ENNReal.ofReal (Cs * A) * N := by
    have hS' : transMajS ν R g = fun τ y => ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
        (streamAnn ν R).indicator
          (fun y => outMaj 0 (transGap ν R) g τ (ϱ y) (y 2)) y := by
      funext τ y
      by_cases hy : y ∈ streamAnn ν R <;> simp [transMajS, Set.indicator, hy]
    rw [hS', IIIa.ltauLq_const_mul P _ (by norm_num) _ ENNReal.ofReal_ne_top]
    have hO := hS ν R P hν hR hP g hgm hgp hgs
    refine (mul_le_mul' le_rfl hO).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e1 : (L⁻¹) ^ 2 * L ^ (-(35 / 22) : ℝ) = L ^ (-(79 / 22) : ℝ) := by
      rw [show (L⁻¹) ^ 2 = L ^ (-2 : ℝ) by rw [Real.rpow_neg hL.le, inv_pow]; norm_num,
        ← Real.rpow_add hL]
      norm_num
    have e3 := PmStep.Lpow hν hν1 hR (e := -(79 / 22)) (by norm_num) (by norm_num)
    simp only [transLen]
    calc (R * Real.sqrt ν)⁻¹ ^ 2 * (Cs * (R * Real.sqrt ν) ^ (-(35 / 22) : ℝ))
        = Cs * (L⁻¹ ^ 2 * L ^ (-(35 / 22) : ℝ)) := by rw [hLdef]; ring
      _ = Cs * L ^ (-(79 / 22) : ℝ) := by rw [e1]
      _ ≤ _ := mul_le_mul_of_nonneg_left e3 hCs
  have hsum : IIIa.ltauLq P (22 / 3) (transMaj ν R g) ≤
      IIIa.ltauLq P (22 / 3) (transMajW ν R g) + IIIa.ltauLq P (22 / 3) (transMajD ν R g) +
        IIIa.ltauLq P (22 / 3) (transMajS ν R g) := by
    have hWD : Measurable (Function.uncurry (fun τ y => transMajW ν R g τ y + transMajD ν R g τ y)) :=
      mW.add mD
    refine (L223.ltauLq_add_le (P := P) (by norm_num) hWD mS).trans ?_
    exact add_le_add (L223.ltauLq_add_le (by norm_num) mW mD) le_rfl
  refine hsum.trans ((add_le_add (add_le_add bW bD) bS).trans_eq ?_)
  have hna : 0 ≤ C0 * (1 - s) ^ (-(79 / 22) : ℝ) * A := mul_nonneg (mul_nonneg hC0 a1) hA
  have hnb : 0 ≤ C1 * (1 - s) ^ (-(101 / 22) : ℝ) * A := mul_nonneg (mul_nonneg hC1 a2) hA
  have hnc : 0 ≤ Cs * A := mul_nonneg hCs hA
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hna hnb,
    ← ENNReal.ofReal_add (add_nonneg hna hnb) hnc]
  congr 2
  rw [hAdef]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
