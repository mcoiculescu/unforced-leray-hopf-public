import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1_3
import UnforcedLeray.Lib.TrainB.WeakEmbedding

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

theorem m1_w0 : IsCoordWord ([] : List Plane) := by
  intro a ha
  simp at ha

theorem m1_w1 : IsCoordWord [((1 : ℝ), (0 : ℝ))] := by
  intro a ha
  rw [List.mem_singleton] at ha
  exact Or.inl ha

theorem m1_w2 : IsCoordWord [((0 : ℝ), (1 : ℝ))] := by
  intro a ha
  rw [List.mem_singleton] at ha
  exact Or.inr ha

theorem m1_w3 : IsCoordWord [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] := by
  intro a ha
  rcases List.mem_cons.mp ha with h | h
  · exact Or.inr h
  · rw [List.mem_singleton] at h
    exact Or.inl h

/-- A coordinate projection of `Vec2` is norm-decreasing. -/
theorem m1_proj_norm_le (i : Fin 2) (x : Vec2) :
    ‖(EuclideanSpace.proj i : Vec2 →L[ℝ] ℝ) x‖ ≤ ‖x‖ := by
  show ‖x i‖ ≤ ‖x‖
  exact PiLp.norm_apply_le x i

/-- Continuous linear functionals commute with classical iterated derivatives. -/
theorem m1_iterD_clm (L : Vec2 →L[ℝ] ℝ) {u : Plane → Vec2} (hu : ContDiff ℝ ∞ u) :
    ∀ vs : List Plane, UnforcedLeray.Sob.iterD vs (fun z => L (u z)) =
      fun z => L (UnforcedLeray.Sob.iterD vs u z)
  | [] => rfl
  | v :: vs => by
    funext z
    have hG : Differentiable ℝ (UnforcedLeray.Sob.iterD vs u) :=
      (UnforcedLeray.Sob.contDiff_iterD hu vs).differentiable (by simp)
    have hd : fderiv ℝ (fun w => L (UnforcedLeray.Sob.iterD vs u w)) z =
        L.comp (fderiv ℝ (UnforcedLeray.Sob.iterD vs u) z) :=
      (L.hasFDerivAt.comp z (hG z).hasFDerivAt).fderiv
    simp only [UnforcedLeray.Sob.iterD_cons]
    rw [m1_iterD_clm L hu vs, hd]
    rfl

/-- A continuous linear image of a smooth cylinder field is a smooth cylinder field. -/
theorem m1_clm_isCylSmooth {c : ℝ} {u : Plane → Vec2} (hu : UnforcedLeray.Sob.IsCylSmooth c u)
    (L : Vec2 →L[ℝ] ℝ) : UnforcedLeray.Sob.IsCylSmooth c (fun z => L (u z)) := by
  refine ⟨L.contDiff.comp hu.smooth, fun z => ?_, ?_⟩
  · show L (u (z + (c, 0))) = L (u z)
    rw [hu.periodic z]
  · obtain ⟨R, hR⟩ := hu.bounded
    exact ⟨R, fun z hz => by
      show L (u z) = 0
      rw [hR z hz, map_zero]⟩

/-- Scalar component bound: each `L`-component of a `Vec2` field with the coordinate `L²` data
bounded by `B` is bounded by `12 B` pointwise. -/
theorem m1_component_bound {c : ℝ} (hc1 : 1 ≤ c) {u : Plane → Vec2}
    (hu : UnforcedLeray.Sob.IsCylSmooth c u) {B : ℝ} (hB : 0 ≤ B)
    (hder : ∀ v : List Plane, IsCoordWord v → v.length ≤ 2 →
      eLpNorm (UnforcedLeray.Sob.iterD v u) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B)
    (L : Vec2 →L[ℝ] ℝ) (hL : ∀ y : Vec2, ‖L y‖ ≤ ‖y‖) (z : Plane) :
    ‖L (u z)‖ ≤ 12 * B := by
  have hg : UnforcedLeray.Sob.IsCylSmooth c (fun w => L (u w)) := m1_clm_isCylSmooth hu L
  have hL2 : ∀ v : List Plane, IsCoordWord v → v.length ≤ 2 →
      eLpNorm (UnforcedLeray.Sob.iterD v (fun w => L (u w))) 2 (UnforcedLeray.Cyl.cellμ c) ≤
        ENNReal.ofReal B := by
    intro v hv hvl
    rw [m1_iterD_clm L hu.smooth v]
    exact le_trans (eLpNorm_mono (fun w => hL (UnforcedLeray.Sob.iterD v u w))) (hder v hv hvl)
  have h0 : eLpNorm (fun w => L (u w)) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B :=
    hL2 [] m1_w0 (by simp)
  have h1 : eLpNorm (UnforcedLeray.Sob.iterD [((1 : ℝ), (0 : ℝ))] (fun w => L (u w))) 2
      (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B :=
    hL2 [((1 : ℝ), (0 : ℝ))] m1_w1 (by simp)
  have h2 : eLpNorm (UnforcedLeray.Sob.iterD [((0 : ℝ), (1 : ℝ))] (fun w => L (u w))) 2
      (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B :=
    hL2 [((0 : ℝ), (1 : ℝ))] m1_w2 (by simp)
  have h3 : eLpNorm (UnforcedLeray.Sob.iterD [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))]
      (fun w => L (u w))) 2 (UnforcedLeray.Cyl.cellμ c) ≤ ENNReal.ofReal B :=
    hL2 [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] m1_w3 (by simp)
  have hS := UnforcedLeray.TrainB.smooth_cyl_H2_bound hc1 hg z
  rw [← UnforcedLeray.TrainB.iterD_eta_q_eq_partialY_partialX hg,
    ← UnforcedLeray.TrainB.iterD_q_eq_partialX hg,
    ← UnforcedLeray.TrainB.iterD_eta_eq_partialY hg] at hS
  try dsimp only at hS
  have hfin : (3 : ℝ≥0∞) * (ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B +
      ENNReal.ofReal B) = ENNReal.ofReal (12 * B) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), ENNReal.ofReal_ofNat]
    ring
  have hsum : ‖L (u z)‖ₑ ≤ ENNReal.ofReal (12 * B) := by
    refine le_trans hS ?_
    calc _ ≤ (3 : ℝ≥0∞) * (ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B +
          ENNReal.ofReal B) := by gcongr
      _ = ENNReal.ofReal (12 * B) := hfin
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [toReal_enorm, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 12 * B)] at h3
  exact h3

/-- The Euclidean norm of a plane vector is at most the sum of its two coordinates' norms. -/
theorem m1_norm_le_two (x : Vec2) :
    ‖x‖ ≤ ‖(EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ) x‖ +
      ‖(EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ) x‖ := by
  have e : ∀ i : Fin 2, ‖(EuclideanSpace.proj i : Vec2 →L[ℝ] ℝ) x‖ = ‖x i‖ := fun i => rfl
  rw [e, e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 := norm_nonneg (x 0)
  have h1 := norm_nonneg (x 1)
  calc √(‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) ≤ √((‖x 0‖ + ‖x 1‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg h0 h1])
    _ = ‖x 0‖ + ‖x 1‖ := Real.sqrt_sq (by positivity)

theorem morreyTwoDerivsLarge_proof : MorreyTwoDerivsLarge := by
  unfold MorreyTwoDerivsLarge
  intro c hc1 f hf B hB hder x
  have h0 := m1_component_bound hc1 hf hB hder (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ)
    (m1_proj_norm_le 0) x
  have h1 := m1_component_bound hc1 hf hB hder (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ)
    (m1_proj_norm_le 1) x
  calc ‖f x‖ ≤ _ := m1_norm_le_two (f x)
    _ ≤ 12 * B + 12 * B := add_le_add h0 h1
    _ = 24 * B := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
