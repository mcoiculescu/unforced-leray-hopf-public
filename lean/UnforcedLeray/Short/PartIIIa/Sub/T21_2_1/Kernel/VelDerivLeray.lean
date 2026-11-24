import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.Unique
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDerivMeanZero
import UnforcedLeray.Lib.CylinderB.Leray

/-!


Source: `the November 2 reference manuscript`, lines 3056-3057, 2254-2259.

Route (for `k = 0`: `f = vec 0 ψ`; for `k = 1`: `f = vec (-ψ) 0`):
* `u := P₀ f` (the cylinder Leray projector, `Lib/CylinderB/Leray.lean`), so `div u = 0` by
  `mem_divFree` and `P0_mem`;
* `curl u = curl f` weakly by `curl_P0`, and `curl f` equals `∂_k ψ` after one periodic integration
  by parts (`integral_fderiv_mul_test`);
* the mean `∫ ∂_kψ = 0` (`kerVelDerivMeanZero`) so the mean shear vanishes;
* `‖u_j‖_{L²} ≤ ‖P₀ f‖ ≤ ‖f‖ = ‖ψ‖_{L²}` (`norm_P0_le`, `PiLp.norm_apply_le`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace
open UnforcedLeray.Cyl (Vec2 vec rotT gradT)

namespace UnforcedLeray.Short.IIIa

theorem vdl_memLp_congr {E : Type*} [NormedAddCommGroup E] {μ ν : Measure (ℝ × ℝ)}
    (h : μ = ν) {f : ℝ × ℝ → E} (hf : MemLp f 2 μ) : MemLp f 2 ν := by
  subst h
  exact hf

theorem vdl_ae_congr {E : Type*} {μ ν : Measure (ℝ × ℝ)}
    (h : μ = ν) {f g : ℝ × ℝ → E} (hfg : f =ᵐ[μ] g) : f =ᵐ[ν] g := by
  subst h
  exact hfg

theorem vdl_norm_vec0 (b : ℝ) : ‖(vec 0 b : Vec2)‖ = ‖b‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [vec, Real.sqrt_sq_eq_abs]

theorem vdl_norm_vec1 (b : ℝ) : ‖(vec (-b) 0 : Vec2)‖ = ‖b‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [vec, Real.sqrt_sq_eq_abs]

/-- Core: the Leray projection of an `L²` field `F` with the curl identity gives a kernel
Biot-Savart velocity, with components bounded by the `L²` norm of `F`. -/
theorem vdl_core {c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℝ) (F : ℝ × ℝ → Vec2)
    (hF : MemLp F 2 (volume.restrict (B0579.cell c)))
    (hg : ∫ y in B0579.cell c, g y = 0)
    (hcurl : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
      ∫ z in B0579.cell c, ⟪F z, rotT φ z⟫_ℝ = ∫ z in B0579.cell c, g z * φ z) :
    ∃ u : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart c g u ∧ ∀ j : Fin 2,
      MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun z => ‖F z‖) 2 (volume.restrict (B0579.cell c)) := by
  have hμ : UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) :=
    UnforcedLeray.Short.IIIa.CTE.T20_2.cellμ_eq_B0579 c
  have hF' : MemLp F 2 (UnforcedLeray.Cyl.cellμ c) := vdl_memLp_congr hμ.symm hF
  obtain ⟨f, hfF⟩ : ∃ f : UnforcedLeray.Cyl.L2v c,
      (f : ℝ × ℝ → Vec2) =ᵐ[volume.restrict (B0579.cell c)] F :=
    ⟨hF'.toLp F, vdl_ae_congr hμ hF'.coeFn_toLp⟩
  have hmem : ∀ j : Fin 2, MemLp (fun x => (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x j) 2
      (volume.restrict (B0579.cell c)) := fun j =>
    vdl_memLp_congr hμ (UnforcedLeray.Cyl.memLp_component (UnforcedLeray.Cyl.P0 c f) j)
  -- divergence clause
  have hdiv : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
      ∫ x in B0579.cell c, ((UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x 0 * B0579.pd 0 φ x +
        (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x 1 * B0579.pd 1 φ x) = 0 := by
    intro φ hφ
    have hφS := UnforcedLeray.Short.IIIa.CTE.T20_2.sob_of_B0579 hφ
    have h := (UnforcedLeray.Cyl.mem_divFree.1 (UnforcedLeray.Cyl.P0_mem f)) φ hφS
    rw [UnforcedLeray.Cyl.gradL, UnforcedLeray.Cyl.inner_toLp_left] at h
    rw [← UnforcedLeray.Short.IIIa.CTE.T20_2.cell_eq c] at h
    have e0 : ∀ z, B0579.pd 0 φ z = UnforcedLeray.Cyl.partialQ φ z := fun z => by
      rw [UnforcedLeray.Short.IIIa.CTE.T20_2.pd0_eq,
        UnforcedLeray.Cyl.partialQ_eq_fderiv hφ.differentiable]
    have e1 : ∀ z, B0579.pd 1 φ z = UnforcedLeray.Cyl.partialEta φ z := fun z => by
      rw [UnforcedLeray.Short.IIIa.CTE.T20_2.pd1_eq,
        UnforcedLeray.Cyl.partialEta_eq_fderiv hφ.differentiable]
    have key : ∀ z, ⟪gradT φ z, (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z⟫_ℝ =
        (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z 0 * B0579.pd 0 φ z +
          (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z 1 * B0579.pd 1 φ z := by
      intro z
      rw [e0 z, e1 z]
      unfold UnforcedLeray.Cyl.gradT
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_vec]
    simp only [key] at h
    exact h
  -- curl clause
  have hcurlK : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
      ∫ x in B0579.cell c, g x * φ x = ∫ x in B0579.cell c,
        ((UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x 0 * B0579.pd 1 φ x -
          (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x 1 * B0579.pd 0 φ x) := by
    intro φ hφ
    have hφS := UnforcedLeray.Short.IIIa.CTE.T20_2.sob_of_B0579 hφ
    have h1 := UnforcedLeray.Cyl.curl_P0 hc f hφS
    rw [← UnforcedLeray.Short.IIIa.CTE.T20_2.cell_eq c] at h1
    have h2 : ∫ z in B0579.cell c, ⟪(f : ℝ × ℝ → Vec2) z, rotT φ z⟫_ℝ =
        ∫ z in B0579.cell c, ⟪F z, rotT φ z⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hfF] with z hz
      rw [hz]
    have key : ∀ z, ⟪(UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z, rotT φ z⟫_ℝ =
        (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z 0 * B0579.pd 1 φ z -
          (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z 1 * B0579.pd 0 φ z := by
      intro z
      have e0 : B0579.pd 0 φ z = UnforcedLeray.Cyl.partialQ φ z := by
        rw [UnforcedLeray.Short.IIIa.CTE.T20_2.pd0_eq,
          UnforcedLeray.Cyl.partialQ_eq_fderiv hφ.differentiable]
      have e1 : B0579.pd 1 φ z = UnforcedLeray.Cyl.partialEta φ z := by
        rw [UnforcedLeray.Short.IIIa.CTE.T20_2.pd1_eq,
          UnforcedLeray.Cyl.partialEta_eq_fderiv hφ.differentiable]
      rw [e0, e1]
      unfold UnforcedLeray.Cyl.rotT
      rw [UnforcedLeray.Cyl.inner_vec]
      ring
    calc ∫ x in B0579.cell c, g x * φ x = ∫ z in B0579.cell c, ⟪F z, rotT φ z⟫_ℝ :=
          (hcurl φ hφ).symm
      _ = ∫ z in B0579.cell c, ⟪(f : ℝ × ℝ → Vec2) z, rotT φ z⟫_ℝ := h2.symm
      _ = ∫ z in B0579.cell c, ⟪(UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) z, rotT φ z⟫_ℝ :=
          h1.symm
      _ = _ := by simp only [key]
  refine ⟨fun x j => (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x j, ⟨?_, hdiv, hcurlK⟩, ?_⟩
  · intro j
    have hms : ∀ x : ℝ × ℝ, meanShear c 0 x j = 0 := fun x => by
      unfold meanShear
      split_ifs <;> simp
    simp only [hg, hms, sub_zero]
    exact hmem j
  · intro j
    refine ⟨hmem j, ?_⟩
    rw [← hμ]
    have hFf : F =ᵐ[UnforcedLeray.Cyl.cellμ c] (f : ℝ × ℝ → Vec2) :=
      vdl_ae_congr hμ.symm hfF.symm
    have hP : ‖UnforcedLeray.Cyl.P0 c f‖ ≤ ‖f‖ := by
      calc ‖UnforcedLeray.Cyl.P0 c f‖ ≤ ‖UnforcedLeray.Cyl.P0 c‖ * ‖f‖ :=
            (UnforcedLeray.Cyl.P0 c).le_opNorm f
        _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right UnforcedLeray.Cyl.norm_P0_le (norm_nonneg _)
        _ = ‖f‖ := one_mul _
    have hn : ∀ G : UnforcedLeray.Cyl.L2v c,
        eLpNorm (G : ℝ × ℝ → Vec2) 2 (UnforcedLeray.Cyl.cellμ c) = ENNReal.ofReal ‖G‖ := by
      intro G
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top G)]
    calc eLpNorm (fun x => (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x j) 2
          (UnforcedLeray.Cyl.cellμ c)
        ≤ eLpNorm (fun x => ‖(UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) x‖) 2
          (UnforcedLeray.Cyl.cellμ c) := eLpNorm_mono_real fun x => PiLp.norm_apply_le _ j
      _ = eLpNorm (UnforcedLeray.Cyl.P0 c f : ℝ × ℝ → Vec2) 2 (UnforcedLeray.Cyl.cellμ c) :=
          eLpNorm_norm _
      _ = ENNReal.ofReal ‖UnforcedLeray.Cyl.P0 c f‖ := hn _
      _ ≤ ENNReal.ofReal ‖f‖ := ENNReal.ofReal_le_ofReal hP
      _ = eLpNorm (f : ℝ × ℝ → Vec2) 2 (UnforcedLeray.Cyl.cellμ c) := (hn f).symm
      _ = eLpNorm F 2 (UnforcedLeray.Cyl.cellμ c) := (eLpNorm_congr_ae hFf).symm
      _ = eLpNorm (fun z => ‖F z‖) 2 (UnforcedLeray.Cyl.cellμ c) := (eLpNorm_norm F).symm

/-- The case `k = 0`: `f = vec 0 ψ`. -/
theorem vdl_k0 (d : ℝ) (hd : 1 ≤ d) (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest d ψ) :
    ∃ u : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart d (B0579.pd 0 ψ) u ∧ ∀ j : Fin 2,
      MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ≤
        eLpNorm ψ 2 (volume.restrict (B0579.cell d)) := by
  have hc : 0 < d := by linarith
  have hψS := UnforcedLeray.Short.IIIa.CTE.T20_2.sob_of_B0579 hψ
  have hmean : ∫ y in B0579.cell d, B0579.pd 0 ψ y = 0 := kerVelDerivMeanZero d hd ψ hψ 0
  have hψc : Continuous ψ := hψ.continuous
  have hcont : Continuous (fun z : ℝ × ℝ => (vec 0 (ψ z) : Vec2)) := by
    have hc2 : Continuous (fun w : Fin 2 → ℝ => (WithLp.toLp 2 w : Vec2)) :=
      PiLp.continuous_toLp _ _
    have hc3 : Continuous (fun z : ℝ × ℝ => (![0, ψ z] : Fin 2 → ℝ)) :=
      continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
    exact hc2.comp hc3
  obtain ⟨R, hR⟩ := hψ.band
  have hv : UnforcedLeray.Cyl.VanishesOutside R (fun z : ℝ × ℝ => (vec 0 (ψ z) : Vec2)) := by
    intro z hz
    show (vec 0 (ψ z) : Vec2) = 0
    rw [hR z hz]
    ext i
    fin_cases i <;> simp [vec]
  have hF : MemLp (fun z : ℝ × ℝ => (vec 0 (ψ z) : Vec2)) 2
      (volume.restrict (B0579.cell d)) :=
    vdl_memLp_congr (UnforcedLeray.Short.IIIa.CTE.T20_2.cellμ_eq_B0579 d)
      (UnforcedLeray.Cyl.memLp_of_vanishes (c := d) hcont hv 2)
  have hcurl0 : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ →
      ∫ z in B0579.cell d, ⟪(vec 0 (ψ z) : Vec2), rotT φ z⟫_ℝ =
        ∫ z in B0579.cell d, B0579.pd 0 ψ z * φ z := by
    intro φ hφ
    have hφS := UnforcedLeray.Short.IIIa.CTE.T20_2.sob_of_B0579 hφ
    have hrot : ∀ z, ⟪(vec 0 (ψ z) : Vec2), rotT φ z⟫_ℝ =
        -(ψ z * UnforcedLeray.Cyl.partialQ φ z) := by
      intro z
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_vec]
      unfold UnforcedLeray.Cyl.rotT
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, PiLp.toLp_apply,
        mul_zero, zero_add]
      ring
    have e1 : ∫ z in B0579.cell d, B0579.pd 0 ψ z * φ z =
        -∫ z in B0579.cell d, ψ z * UnforcedLeray.Cyl.partialQ φ z := by
      rw [UnforcedLeray.Short.IIIa.CTE.T20_2.cell_eq d]
      have h := UnforcedLeray.Cyl.integral_fderiv_mul_test hc hψS hφS (1, 0)
      simp only [UnforcedLeray.Cyl.partialQ_eq_fderiv hφ.differentiable]
      exact h
    simp only [hrot]
    rw [integral_neg, e1]
  obtain ⟨u, hu, hj⟩ := vdl_core hc (B0579.pd 0 ψ) (fun z => (vec 0 (ψ z) : Vec2)) hF hmean
    hcurl0
  refine ⟨u, hu, fun j => ⟨(hj j).1, ?_⟩⟩
  have h2 : eLpNorm (fun z => ‖(vec 0 (ψ z) : Vec2)‖) 2 (volume.restrict (B0579.cell d)) =
      eLpNorm ψ 2 (volume.restrict (B0579.cell d)) := by
    simp only [vdl_norm_vec0]
    exact eLpNorm_norm ψ
  exact (hj j).2.trans h2.le

/-- The case `k = 1`: `f = vec (-ψ) 0`. -/
theorem vdl_k1 (d : ℝ) (hd : 1 ≤ d) (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest d ψ) :
    ∃ u : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart d (B0579.pd 1 ψ) u ∧ ∀ j : Fin 2,
      MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ≤
        eLpNorm ψ 2 (volume.restrict (B0579.cell d)) := by
  have hc : 0 < d := by linarith
  have hψS := UnforcedLeray.Short.IIIa.CTE.T20_2.sob_of_B0579 hψ
  have hmean : ∫ y in B0579.cell d, B0579.pd 1 ψ y = 0 := kerVelDerivMeanZero d hd ψ hψ 1
  have hψc : Continuous ψ := hψ.continuous
  have hcont : Continuous (fun z : ℝ × ℝ => (vec (-ψ z) 0 : Vec2)) := by
    have hc2 : Continuous (fun w : Fin 2 → ℝ => (WithLp.toLp 2 w : Vec2)) :=
      PiLp.continuous_toLp _ _
    have hc3 : Continuous (fun z : ℝ × ℝ => (![-ψ z, 0] : Fin 2 → ℝ)) :=
      continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
    exact hc2.comp hc3
  obtain ⟨R, hR⟩ := hψ.band
  have hv : UnforcedLeray.Cyl.VanishesOutside R (fun z : ℝ × ℝ => (vec (-ψ z) 0 : Vec2)) := by
    intro z hz
    show (vec (-ψ z) 0 : Vec2) = 0
    rw [hR z hz]
    ext i
    fin_cases i <;> simp [vec]
  have hF : MemLp (fun z : ℝ × ℝ => (vec (-ψ z) 0 : Vec2)) 2
      (volume.restrict (B0579.cell d)) :=
    vdl_memLp_congr (UnforcedLeray.Short.IIIa.CTE.T20_2.cellμ_eq_B0579 d)
      (UnforcedLeray.Cyl.memLp_of_vanishes (c := d) hcont hv 2)
  have hcurl1 : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ →
      ∫ z in B0579.cell d, ⟪(vec (-ψ z) 0 : Vec2), rotT φ z⟫_ℝ =
        ∫ z in B0579.cell d, B0579.pd 1 ψ z * φ z := by
    intro φ hφ
    have hφS := UnforcedLeray.Short.IIIa.CTE.T20_2.sob_of_B0579 hφ
    have hrot : ∀ z, ⟪(vec (-ψ z) 0 : Vec2), rotT φ z⟫_ℝ =
        -(ψ z * UnforcedLeray.Cyl.partialEta φ z) := by
      intro z
      rw [real_inner_comm, UnforcedLeray.Cyl.inner_vec]
      unfold UnforcedLeray.Cyl.rotT
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, PiLp.toLp_apply,
        mul_zero, add_zero]
      ring
    have e1 : ∫ z in B0579.cell d, B0579.pd 1 ψ z * φ z =
        -∫ z in B0579.cell d, ψ z * UnforcedLeray.Cyl.partialEta φ z := by
      rw [UnforcedLeray.Short.IIIa.CTE.T20_2.cell_eq d]
      have h := UnforcedLeray.Cyl.integral_fderiv_mul_test hc hψS hφS (0, 1)
      simp only [UnforcedLeray.Cyl.partialEta_eq_fderiv hφ.differentiable]
      exact h
    simp only [hrot]
    rw [integral_neg, e1]
  obtain ⟨u, hu, hj⟩ := vdl_core hc (B0579.pd 1 ψ) (fun z => (vec (-ψ z) 0 : Vec2)) hF hmean
    hcurl1
  refine ⟨u, hu, fun j => ⟨(hj j).1, ?_⟩⟩
  have h2 : eLpNorm (fun z => ‖(vec (-ψ z) 0 : Vec2)‖) 2 (volume.restrict (B0579.cell d)) =
      eLpNorm ψ 2 (volume.restrict (B0579.cell d)) := by
    simp only [vdl_norm_vec1]
    exact eLpNorm_norm ψ
  exact (hj j).2.trans h2.le

theorem kerVelDerivLeray : UnforcedLeray.Short.IIIa.KerVelDerivLeray := by
  intro d hd ψ hψ k
  fin_cases k
  · exact vdl_k0 d hd ψ hψ
  · exact vdl_k1 d hd ψ hψ

end UnforcedLeray.Short.IIIa
