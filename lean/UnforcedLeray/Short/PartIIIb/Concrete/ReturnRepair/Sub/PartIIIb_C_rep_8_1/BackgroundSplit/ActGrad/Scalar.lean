import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_7
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_fub

/-!
# `ActGrad` helpers: the separated estimates with an `L¹` source (source 5282-5289)

Source `the November 2 reference manuscript` 5203-5217 (the gradient kernel has
`L^{22/3}` norm `C D^{-101/22}`: `-5 + 3/(22/3) = -101/22`), 5282-5289 (the general thin-source
estimate), 3624-3647 (`sep:young`), 5219-5221 (normalized phase estimate over `P ≤ 1`).

For a thin source the natural source norm is `L¹` in space (the first moment `N₁`), so the
separated estimates are used with `p = 1`, `b = q = 22/3`.  The source enters through
`agMass P g = ∫ ‖g(·,z)‖_{L²_τ} dz`.  Proved here, at every phase:
* `ag_dil_le`: `∫_0^1 λ^a ∫ g(τ+2logλ, z) dz dλ ≤ C agMass` (periodic dilation sum);
* `ag_sepDom_lq`: `‖sepDom a j D g (τ)‖_{L^{22/3}} ≤ C D^{-4-j+9/22} agMass`;
* `ag_vertKern_lq`, `ag_vert_lq`: the vertical reduction of the outward primitive in `L^{22/3}(ℝ)`
  with `‖vertKern rIn D‖_{L^{22/3}} ≤ c (rIn/D) D^{-2+3/22}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `∫ ‖g(·, z)‖_{L²_τ} dz`, the `L¹_z L²_τ` size of a space-time density. -/
def agMass (P : ℝ) (g : ℝ → Space → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z : Space, IIIa.ltauAt P (fun τ => g τ z)

/-- The periodic dilation sum, integrated in space. -/
theorem ag_dil_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → ∀ P : ℝ, 0 < P → P ≤ 1 →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∀ τ z, g (τ + P) z = g τ z) → ∀ τ : ℝ,
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z ≤
          ENNReal.ofReal C * agMass P g := by
  obtain ⟨C, hC, hD⟩ := periodicDilationSum_proved 1 one_pos
  refine ⟨C, hC, ?_⟩
  intro a ha P hP hP1 g hg hper τ
  have hjoint : Measurable (Function.uncurry fun (l : ℝ) (z : Space) =>
      ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) z) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const a)).mul ?_
    exact hg.comp ((measurable_const.add (measurable_const.mul
      (Real.measurable_log.comp measurable_fst))).prodMk measurable_snd)
  have hgz : ∀ z : Space, Measurable fun s => g s z := fun z => hg.of_uncurry_right
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z
      = ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z : Space, ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) z := by
        refine lintegral_congr fun l => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ z : Space, ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) z :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻ z : Space, ENNReal.ofReal C * IIIa.ltauAt P (fun τ => g τ z) := by
        refine lintegral_mono fun z => ?_
        exact hD a (by linarith) P hP hP1 (fun s => g s z) (hgz z) (fun s => hper s z) τ
    _ = ENNReal.ofReal C * agMass P g := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The separated majorant with an `L¹` source, at every phase** (`sep:young` with `p = 1`,
`b = q = 22/3`; Minkowski in `λ`; periodic dilation sum). -/
theorem ag_sepDom_lq (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → ∀ D P : ℝ, 0 < D → 0 < P →
    P ≤ 1 → ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∀ τ z, g (τ + P) z = g τ z) → ∀ τ : ℝ,
        lqNorm (22 / 3) (IIIa.sepDom a j D g τ) ≤
          ENNReal.ofReal (C * D ^ (-4 - (j : ℝ) + 9 / 22)) * agMass P g := by
  obtain ⟨Cd, hCd, hdil⟩ := ag_dil_le
  obtain ⟨Cy, hCy, hY⟩ := sepKdYoungScaled_proved j 1 (22 / 3) (22 / 3) le_rfl (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨Cy * Cd, by positivity, ?_⟩
  intro a ha D P hD hP hP1 g hg hper τ
  have hM := sepDomMinkowski_proved a j D (22 / 3) (by norm_num) g hg τ
  refine hM.trans ?_
  have hb : (3 : ℝ) / (22 / 3) = 9 / 22 := by norm_num
  set E : ℝ := Cy * D ^ (-4 - (j : ℝ) + 9 / 22) with hE
  have hE0 : 0 ≤ E := mul_nonneg hCy (Real.rpow_nonneg hD.le _)
  have hpt : ∀ l ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * lqNorm (22 / 3)
      (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) ≤
      ENNReal.ofReal E * (ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) := by
    intro l hl
    have h1 := hY D hD l hl.1 hl.2 (g (τ + 2 * Real.log l)) hg.of_uncurry_left
    rw [hb] at h1
    have e1 : l ^ (-3 + 3 / (1 : ℝ)) = 1 := by norm_num
    have e2 : lqNorm 1 (g (τ + 2 * Real.log l)) = ∫⁻ z : Space, g (τ + 2 * Real.log l) z := by
      simp [lqNorm]
    rw [e1, ENNReal.ofReal_one, one_mul, e2] at h1
    calc ENNReal.ofReal (l ^ a) * lqNorm (22 / 3)
          (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z)
        ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal E * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
          mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal E * (ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) := by
          ring
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * lqNorm (22 / 3)
        (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z)
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal E *
          (ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal E * ∫⁻ l in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal E * (ENNReal.ofReal Cd * agMass P g) :=
        mul_le_mul' le_rfl (hdil a ha P hP hP1 g hg hper τ)
    _ = ENNReal.ofReal (Cy * Cd * D ^ (-4 - (j : ℝ) + 9 / 22)) * agMass P g := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hE0, hE]
        congr 2
        ring

/-- `lqNorm1` of a constant multiple, the constant possibly infinite. -/
theorem ag_lq1_const_mul {q : ℝ} (hq : 0 < q) (c : ℝ≥0∞) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    lqNorm1 q (fun z => c * f z) = c * lqNorm1 q f := by
  unfold lqNorm1
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_const_mul _ (hf.pow_const q), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- Translation invariance of `lqNorm1`. -/
theorem ag_lq1_shift (q : ℝ) (f : ℝ → ℝ≥0∞) (c : ℝ) :
    lqNorm1 q (fun z => f (z - c)) = lqNorm1 q f := by
  unfold lqNorm1
  rw [lintegral_sub_right_eq_self (fun z => f z ^ q) c]

/-- Minkowski in the source variable for a dilated convolution on `ℝ`. -/
theorem ag_conv_lq1 {q : ℝ} (hq : 1 ≤ q) {K h : ℝ → ℝ≥0∞} (hK : Measurable K)
    (hh : Measurable h) (l : ℝ) :
    lqNorm1 q (fun z => ∫⁻ s : ℝ, K (z - l * s) * h s) ≤ lqNorm1 q K * ∫⁻ s : ℝ, h s := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hq
  have hF : Measurable (Function.uncurry fun (z s : ℝ) => K (z - l * s) * h s) :=
    (hK.comp (measurable_fst.sub (measurable_const.mul measurable_snd))).mul
      (hh.comp measurable_snd)
  rw [lqNorm1_eq_eLpNorm hq]
  refine (NonUniqueEuler.Conv.eLpNorm_lintegral_le hF.aemeasurable hp1 ENNReal.ofReal_ne_top).trans
    (le_of_eq ?_)
  have key : ∀ s : ℝ, eLpNorm (fun z => K (z - l * s) * h s) (ENNReal.ofReal q) volume =
      h s * lqNorm1 q K := by
    intro s
    rw [← lqNorm1_eq_eLpNorm hq]
    have e : (fun z => K (z - l * s) * h s) = fun z => h s * K (z - l * s) := by
      funext z; ring
    have hm : Measurable (fun z => K (z - l * s)) := hK.comp (measurable_id.sub measurable_const)
    rw [e]
    exact (ag_lq1_const_mul hq0 (h s) hm).trans (by rw [ag_lq1_shift q K (l * s)])
  rw [lintegral_congr key, lintegral_mul_const _ hh, mul_comm]

/-- The horizontal profile integrates to the space integral. -/
theorem ag_vprof_lint (g : ℝ → Space → ℝ≥0∞) (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    ∫⁻ s : ℝ, vprof g τ s = ∫⁻ z : Space, g τ z := by
  have hgτ : Measurable (g τ) := hg.of_uncurry_left
  have hF : Measurable fun q : ℝ × ℝ × ℝ => g τ !₂[q.1, q.2.1, q.2.2] :=
    hgτ.comp measurable_vecSpace
  unfold vprof
  rw [lintegral_space_xys (g τ) hgτ]
  exact (lintegral_xys_swap (fun q : ℝ × ℝ × ℝ => g τ !₂[q.1, q.2.1, q.2.2]) hF).symm

/-- The `22/3`-power of the vertical kernel. -/
theorem ag_vk_pow_eq (rIn D t : ℝ) (hr : 0 < rIn) (hD : 0 < D) :
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
theorem ag_vk_integral_eq {D : ℝ} (hD : 0 < D) :
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

/-- **The vertical kernel in `L^{22/3}(ℝ)`**: `‖vertKern rIn D‖_{L^{22/3}} = c (rIn/D) D^{-41/22}`. -/
theorem ag_vertKern_lq : ∃ c : ℝ, 0 ≤ c ∧ ∀ rIn D : ℝ, 0 < rIn → 0 < D →
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
  set J : ℝ≥0∞ := ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2) ^ (-(22 / 3 : ℝ))) with hJdef
  have hJ : J ≠ ⊤ := (hint.lintegral_lt_top).ne
  refine ⟨(1 / 2) * J.toReal ^ (3 / 22 : ℝ),
    mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _), ?_⟩
  intro rIn D hr hD
  have hA : 0 < rIn / (2 * D) := by positivity
  have hIt : ∫⁻ t : ℝ, vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ)) * (ENNReal.ofReal (D ^ (-(41 / 3 : ℝ))) * J) := by
    simp_rw [ag_vk_pow_eq rIn D _ hr hD]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ag_vk_integral_eq hD]
  have hIr : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ).symm
  have hQ : ∫⁻ t : ℝ, vertKern rIn D t ^ (22 / 3 : ℝ) =
      ENNReal.ofReal ((rIn / (2 * D)) ^ (22 / 3 : ℝ) * D ^ (-(41 / 3 : ℝ)) * J.toReal) := by
    rw [hIt]
    conv_lhs => rw [hIr]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  have heq : ((rIn / (2 * D)) ^ (22 / 3 : ℝ) * D ^ (-(41 / 3 : ℝ)) * J.toReal) ^
        (1 / (22 / 3 : ℝ)) =
      (1 / 2) * J.toReal ^ (3 / 22 : ℝ) * (rIn / D) * D ^ (-(41 / 22 : ℝ)) := by
    rw [show (1 / (22 / 3 : ℝ)) = 3 / 22 by norm_num,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hA.le, ← Real.rpow_mul hD.le,
      show (22 / 3 : ℝ) * (3 / 22) = 1 by norm_num,
      show (-(41 / 3 : ℝ)) * (3 / 22) = -(41 / 22) by norm_num, Real.rpow_one]
    field_simp
  unfold lqNorm1
  rw [hQ, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), heq]
  apply ENNReal.ofReal_le_ofReal
  rw [show (-2 + 3 / 22 : ℝ) = -(41 / 22) by norm_num]

/-- **The vertical reduction of the outward primitive with an `L¹` source, at every phase**:
`‖vertRed a rIn D g (τ,·)‖_{L^{22/3}(ℝ)} ≤ C (rIn/D) D^{-2+3/22} agMass`. -/
theorem ag_vert_lq : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → ∀ rIn D P : ℝ, 0 < rIn → 0 < D →
    0 < P → P ≤ 1 → ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∀ τ z, g (τ + P) z = g τ z) → ∀ τ : ℝ,
        lqNorm1 (22 / 3) (vertRed a rIn D g τ) ≤
          ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * agMass P g := by
  obtain ⟨c, hc, hK⟩ := ag_vertKern_lq
  obtain ⟨Cd, hCd, hdil⟩ := ag_dil_le
  refine ⟨c * Cd, by positivity, ?_⟩
  intro a ha rIn D P hr hD hP hP1 g hg hper τ
  have hh : Measurable (Function.uncurry (vprof g)) := (vertMeasurable g hg).1
  have hKm : Measurable (vertKern rIn D) := by
    unfold vertKern
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hM := vertMinkowski a rIn D (22 / 3) (by norm_num) (vprof g) hh τ
  set Kn : ℝ≥0∞ := lqNorm1 (22 / 3) (vertKern rIn D) with hKn
  have hKb : Kn ≤ ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) := hK rIn D hr hD
  have hpt : ∀ l ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * lqNorm1 (22 / 3)
      (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * vprof g (τ + 2 * Real.log l) s) ≤
      Kn * (ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) := by
    intro l _
    have h1 := ag_conv_lq1 (q := 22 / 3) (by norm_num) hKm
      (hh.of_uncurry_left (x := τ + 2 * Real.log l)) l
    rw [ag_vprof_lint g hg] at h1
    calc ENNReal.ofReal (l ^ a) * lqNorm1 (22 / 3)
          (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * vprof g (τ + 2 * Real.log l) s)
        ≤ ENNReal.ofReal (l ^ a) * (Kn * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
          mul_le_mul' le_rfl h1
      _ = Kn * (ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) := by ring
  calc lqNorm1 (22 / 3) (vertRed a rIn D g τ)
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * lqNorm1 (22 / 3)
          (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * vprof g (τ + 2 * Real.log l) s) := hM
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, Kn *
          (ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = Kn * ∫⁻ l in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, g (τ + 2 * Real.log l) z := by
        exact lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKb)
    _ ≤ ENNReal.ofReal (c * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) *
          (ENNReal.ofReal Cd * agMass P g) :=
        mul_le_mul' hKb (hdil a ha P hP hP1 g hg hper τ)
    _ = ENNReal.ofReal (c * Cd * (rIn / D) * D ^ (-2 + 3 / 22 : ℝ)) * agMass P g := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
