import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3_1.ReImFar

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3/1/3`: far-field derivative bounds for `projPot`

Source `the November 2 reference manuscript`
lines 1393-1400.  The spatial slice `y ↦ projPot Ψ (τ, y)` is `ofReal(Re) + I * ofReal(Im)` of the
real path potentials, whose far-field derivative bounds are `projectedPotentialPath_deriv_far`
(ReImFar).  The dy-iterates of `projPot Ψ` at `(τ, y)` are iterated Fréchet derivatives of the slice
evaluated at unit coordinate vectors, hence bounded by the iterated derivative norm of the slice.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly

/-- The spatial slice `y ↦ Φ (τ, y)`. -/
abbrev sliceF (Φ : ℝ × UnforcedLeray.Space → ℂ) (τ : ℝ) : UnforcedLeray.Space → ℂ :=
  fun w => Φ (τ, w)

section Helpers

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fderiv_apply_const_vec {c : E → (F →L[ℝ] G)} {x : E} (hc : DifferentiableAt ℝ c x)
    (u : F) : fderiv ℝ (fun y => c y u) x = (fderiv ℝ c x).flip u := by
  have hu : HasFDerivAt (fun _ : E => u) (0 : E →L[ℝ] F) x := hasFDerivAt_const u x
  rw [(hc.hasFDerivAt.clm_apply hu).fderiv]
  simp

end Helpers

theorem norm_e3 (i : Fin 3) : ‖UnforcedLeray.coordinateVector i‖ = 1 :=
  UnforcedLeray.RieszLp.norm_coordinateVector i

theorem dy_eq_slice {Θ : ℝ × UnforcedLeray.Space → ℂ} {τ : ℝ} {z : UnforcedLeray.Space}
    (hΘ : DifferentiableAt ℝ Θ (τ, z)) (j : Fin 3) :
    dy j Θ (τ, z) = fderiv ℝ (fun w => Θ (τ, w)) z (UnforcedLeray.coordinateVector j) := by
  have h : HasFDerivAt (fun w : UnforcedLeray.Space => ((τ, w) : ℝ × UnforcedLeray.Space))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) z :=
    (hasFDerivAt_const τ z).prodMk (hasFDerivAt_id z)
  have h2 := hΘ.hasFDerivAt.comp z h
  rw [show (fun w => Θ (τ, w)) =
      Θ ∘ (fun w : UnforcedLeray.Space => ((τ, w) : ℝ × UnforcedLeray.Space)) from rfl, h2.fderiv]
  simp [dy]

theorem sliceF_contDiff {Φ : ℝ × UnforcedLeray.Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ) :
    ContDiff ℝ ∞ (sliceF Φ τ) :=
  hΦ.comp (contDiff_const.prodMk contDiff_id)

variable {Fv : Type*} [NormedAddCommGroup Fv] [NormedSpace ℝ Fv]

theorem iter_one_vec {G : UnforcedLeray.Space → Fv} (y w : UnforcedLeray.Space) :
    iteratedFDeriv ℝ 1 G y ![w] = fderiv ℝ G y w := by
  rw [iteratedFDeriv_one_apply]
  rfl

theorem iter_two_vec {G : UnforcedLeray.Space → Fv} (y w u : UnforcedLeray.Space) :
    iteratedFDeriv ℝ 2 G y ![w, u] = fderiv ℝ (fun z => fderiv ℝ G z) y w u := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

theorem iter_three_vec {G : UnforcedLeray.Space → Fv} (y w u v : UnforcedLeray.Space) :
    iteratedFDeriv ℝ 3 G y ![w, u, v] =
      fderiv ℝ (fun z => fderiv ℝ (fun z' => fderiv ℝ G z') z) y w u v := by
  have hinit : Fin.init ![w, u, v] = ![w, u] := by
    funext i
    fin_cases i <;> rfl
  rw [iteratedFDeriv_succ_apply_right, hinit, iter_two_vec]
  rfl

theorem dy_slice_one {Φ : ℝ × UnforcedLeray.Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ)
    (y : UnforcedLeray.Space) (j : Fin 3) :
    dy j Φ (τ, y) =
      iteratedFDeriv ℝ 1 (sliceF Φ τ) y ![UnforcedLeray.coordinateVector j] := by
  rw [iter_one_vec, dy_eq_slice ((hΦ.differentiable (by simp)) (τ, y)) j]

theorem dy_slice_two {Φ : ℝ × UnforcedLeray.Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ)
    (y : UnforcedLeray.Space) (i j : Fin 3) :
    dy i (dy j Φ) (τ, y) =
      iteratedFDeriv ℝ 2 (sliceF Φ τ) y
        ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector j] := by
  have hd : ContDiff ℝ ∞ (dy j Φ) := contDiff_dyC hΦ j
  have hK : ContDiff ℝ ∞ (fderiv ℝ (sliceF Φ τ)) :=
    (sliceF_contDiff hΦ τ).fderiv_right (m := ∞) (by simp)
  have hfun : (fun w => dy j Φ (τ, w)) =
      fun w => fderiv ℝ (sliceF Φ τ) w (UnforcedLeray.coordinateVector j) := by
    funext w
    exact dy_eq_slice ((hΦ.differentiable (by simp)) (τ, w)) j
  rw [iter_two_vec, dy_eq_slice ((hd.differentiable (by simp)) (τ, y)) i, hfun,
    fderiv_apply_const_vec ((hK.differentiable (by simp)) y)]
  simp [ContinuousLinearMap.flip_apply]

theorem dy_slice_three {Φ : ℝ × UnforcedLeray.Space → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ)
    (y : UnforcedLeray.Space) (i j k : Fin 3) :
    dy i (dy j (dy k Φ)) (τ, y) =
      iteratedFDeriv ℝ 3 (sliceF Φ τ) y
        ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector j,
          UnforcedLeray.coordinateVector k] := by
  have hK : ContDiff ℝ ∞ (fderiv ℝ (sliceF Φ τ)) :=
    (sliceF_contDiff hΦ τ).fderiv_right (m := ∞) (by simp)
  have hKK : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (sliceF Φ τ))) :=
    hK.fderiv_right (m := ∞) (by simp)
  have hdk : ContDiff ℝ ∞ (dy k Φ) := contDiff_dyC hΦ k
  have hdjk : ContDiff ℝ ∞ (dy j (dy k Φ)) := contDiff_dyC hdk j
  have hslice2 : (fun w => dy j (dy k Φ) (τ, w)) =
      fun w => fderiv ℝ (fderiv ℝ (sliceF Φ τ)) w (UnforcedLeray.coordinateVector j)
        (UnforcedLeray.coordinateVector k) := by
    funext w
    rw [dy_eq_slice ((hdk.differentiable (by simp)) (τ, w)) j]
    have hfk : (fun w' => dy k Φ (τ, w')) =
        fun w' => fderiv ℝ (sliceF Φ τ) w' (UnforcedLeray.coordinateVector k) := by
      funext w'
      exact dy_eq_slice ((hΦ.differentiable (by simp)) (τ, w')) k
    rw [hfk, fderiv_apply_const_vec ((hK.differentiable (by simp)) w)
      (UnforcedLeray.coordinateVector k)]
    simp [ContinuousLinearMap.flip_apply]
  have hA : DifferentiableAt ℝ
      (fun w => fderiv ℝ (fderiv ℝ (sliceF Φ τ)) w (UnforcedLeray.coordinateVector j)) y :=
    ((hKK.differentiable (by simp)) y).clm_apply (differentiableAt_const _)
  have hB : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (sliceF Φ τ))) y :=
    (hKK.differentiable (by simp)) y
  rw [dy_eq_slice ((hdjk.differentiable (by simp)) (τ, y)) i, hslice2,
    fderiv_apply_const_vec hA (UnforcedLeray.coordinateVector k),
    fderiv_apply_const_vec hB (UnforcedLeray.coordinateVector j), iter_three_vec]
  simp [ContinuousLinearMap.flip_apply]

theorem norm_iter_vec_le {n : ℕ} (G : UnforcedLeray.Space → ℂ) (y : UnforcedLeray.Space)
    (m : Fin n → UnforcedLeray.Space) (hm : ∀ t, ‖m t‖ = 1) :
    ‖iteratedFDeriv ℝ n G y m‖ ≤ ‖iteratedFDeriv ℝ n G y‖ :=
  (ContinuousMultilinearMap.le_opNorm _ m).trans (by simp [hm])

theorem norm_iteratedFDeriv_complexPair {a b : UnforcedLeray.Space → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (k : ℕ) (y : UnforcedLeray.Space) :
    ‖iteratedFDeriv ℝ k (fun z => ((a z : ℝ) : ℂ) + Complex.I * ((b z : ℝ) : ℂ)) y‖ ≤
      ‖iteratedFDeriv ℝ k a y‖ + ‖iteratedFDeriv ℝ k b y‖ := by
  have hA : ContDiff ℝ ∞ (fun z => ((a z : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp ha
  have hB : ContDiff ℝ ∞ (fun z => Complex.I * ((b z : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hb)
  have hsplit : (fun z => ((a z : ℝ) : ℂ) + Complex.I * ((b z : ℝ) : ℂ)) =
      (fun z => ((a z : ℝ) : ℂ)) + (fun z => Complex.I * ((b z : ℝ) : ℂ)) := rfl
  rw [hsplit, iteratedFDeriv_add_apply (i := k) (hA.contDiffAt.of_le (by exact_mod_cast le_top))
    (hB.contDiffAt.of_le (by exact_mod_cast le_top))]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.ofRealCLM
      (f := a) (x := y) (N := ∞) (n := k) ha.contDiffAt (by exact_mod_cast le_top)
    rw [Complex.ofRealCLM_norm, one_mul] at h
    exact h
  · have hLn : ‖ContinuousLinearMap.mul ℝ ℂ Complex.I‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
    have hcomp : (fun z => Complex.I * ((b z : ℝ) : ℂ)) =
        (ContinuousLinearMap.mul ℝ ℂ Complex.I) ∘ (fun z => ((b z : ℝ) : ℂ)) := by
      funext z
      simp
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (ContinuousLinearMap.mul ℝ ℂ Complex.I)
      (f := fun z => ((b z : ℝ) : ℂ)) (x := y) (N := ∞) (n := k)
      (Complex.ofRealCLM.contDiff.comp hb).contDiffAt (by exact_mod_cast le_top)
    rw [← hcomp] at h
    have h2 : ‖iteratedFDeriv ℝ k (fun z => ((b z : ℝ) : ℂ)) y‖ ≤ ‖iteratedFDeriv ℝ k b y‖ := by
      have h3 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.ofRealCLM
        (f := b) (x := y) (N := ∞) (n := k) hb.contDiffAt (by exact_mod_cast le_top)
      rw [Complex.ofRealCLM_norm, one_mul] at h3
      exact h3
    calc _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ Complex.I‖ *
          ‖iteratedFDeriv ℝ k (fun z => ((b z : ℝ) : ℂ)) y‖ := h
      _ ≤ 1 * ‖iteratedFDeriv ℝ k b y‖ := mul_le_mul hLn h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem iter_projPot_bound {P : ℝ}
    {Ψ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hΨ : UnforcedLeray.PhaseSpace.IsPhaseTest P Ψ) (k : ℕ) (τ : ℝ)
    (y : UnforcedLeray.Space) (C : ℝ)
    (hre : ‖iteratedFDeriv ℝ k
        (fun z => UnforcedLeray.Cons.C03.Concrete.projectedPotentialRePath Ψ (τ, z)) y‖ ≤
        C * ‖y‖ ^ (-(2 + (k : ℝ))))
    (him : ‖iteratedFDeriv ℝ k
        (fun z => UnforcedLeray.Cons.C03.Concrete.projectedPotentialImPath Ψ (τ, z)) y‖ ≤
        C * ‖y‖ ^ (-(2 + (k : ℝ)))) :
    ‖iteratedFDeriv ℝ k (sliceF (UnforcedLeray.Short.PartIIIb.Concrete.projPot Ψ) τ) y‖ ≤
      2 * |C| * ‖y‖ ^ (-(2 + (k : ℝ))) := by
  have ha : ContDiff ℝ ∞
      (fun z : UnforcedLeray.Space => UnforcedLeray.Cons.C03.Concrete.projectedPotentialRePath Ψ (τ, z)) :=
    (UnforcedLeray.Cons.C03.Concrete.contDiff_projectedPotentialRePath hΨ).comp
      (contDiff_const.prodMk contDiff_id)
  have hb : ContDiff ℝ ∞
      (fun z : UnforcedLeray.Space => UnforcedLeray.Cons.C03.Concrete.projectedPotentialImPath Ψ (τ, z)) :=
    (UnforcedLeray.Cons.C03.Concrete.contDiff_projectedPotentialImPath hΨ).comp
      (contDiff_const.prodMk contDiff_id)
  have hsl : sliceF (UnforcedLeray.Short.PartIIIb.Concrete.projPot Ψ) τ =
      fun z => ((UnforcedLeray.Cons.C03.Concrete.projectedPotentialRePath Ψ (τ, z) : ℝ) : ℂ) +
        Complex.I * ((UnforcedLeray.Cons.C03.Concrete.projectedPotentialImPath Ψ (τ, z) : ℝ) : ℂ) :=
    rfl
  rw [hsl]
  have hp : (0 : ℝ) ≤ ‖y‖ ^ (-(2 + (k : ℝ))) := Real.rpow_nonneg (norm_nonneg y) _
  refine (norm_iteratedFDeriv_complexPair ha hb k y).trans ?_
  have hC : C ≤ |C| := le_abs_self C
  calc _ ≤ C * ‖y‖ ^ (-(2 + (k : ℝ))) + C * ‖y‖ ^ (-(2 + (k : ℝ))) := add_le_add hre him
    _ ≤ 2 * |C| * ‖y‖ ^ (-(2 + (k : ℝ))) := by nlinarith [abs_nonneg C]

theorem piFarDeriv : UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly.PiFarDeriv := by
  intro P _ Ψ hΨ
  have hΦ : ContDiff ℝ ∞ (UnforcedLeray.Short.PartIIIb.Concrete.projPot Ψ) :=
    UnforcedLeray.Short.PartIIIb.Concrete.contDiff_projPot hΨ
  obtain ⟨ρ1, C1, h1⟩ := projectedPotentialPath_deriv_far hΨ 1
  obtain ⟨ρ2, C2, h2⟩ := projectedPotentialPath_deriv_far hΨ 2
  obtain ⟨ρ3, C3, h3⟩ := projectedPotentialPath_deriv_far hΨ 3
  refine ⟨max (max (max ρ1 ρ2) ρ3) 0 + 1, 2 * (|C1| + |C2| + |C3|), ?_⟩
  intro τ hτ y hy
  have hm0 : (0 : ℝ) ≤ max (max (max ρ1 ρ2) ρ3) 0 := le_max_right _ _
  have hy0 : 0 < ‖y‖ := by linarith
  have hρ1 : ρ1 ≤ ‖y‖ := by
    have := le_max_left ρ1 ρ2
    have := le_max_left (max ρ1 ρ2) ρ3
    have := le_max_left (max (max ρ1 ρ2) ρ3) (0 : ℝ)
    linarith
  have hρ2 : ρ2 ≤ ‖y‖ := by
    have := le_max_right ρ1 ρ2
    have := le_max_left (max ρ1 ρ2) ρ3
    have := le_max_left (max (max ρ1 ρ2) ρ3) (0 : ℝ)
    linarith
  have hρ3 : ρ3 ≤ ‖y‖ := by
    have := le_max_right (max ρ1 ρ2) ρ3
    have := le_max_left (max (max ρ1 ρ2) ρ3) (0 : ℝ)
    linarith
  have hp : (0 : ℝ) ≤ ‖y‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg y) _
  have hq : (0 : ℝ) ≤ ‖y‖ ^ (-4 : ℝ) := Real.rpow_nonneg (norm_nonneg y) _
  have hr : (0 : ℝ) ≤ ‖y‖ ^ (-5 : ℝ) := Real.rpow_nonneg (norm_nonneg y) _
  have hM1 : 2 * |C1| ≤ 2 * (|C1| + |C2| + |C3|) := by
    linarith [abs_nonneg C2, abs_nonneg C3]
  have hM2 : 2 * |C2| ≤ 2 * (|C1| + |C2| + |C3|) := by
    linarith [abs_nonneg C1, abs_nonneg C3]
  have hM3 : 2 * |C3| ≤ 2 * (|C1| + |C2| + |C3|) := by
    linarith [abs_nonneg C1, abs_nonneg C2]
  have e1 : (-(2 + ((1 : ℕ) : ℝ))) = (-3 : ℝ) := by norm_num
  have e2 : (-(2 + ((2 : ℕ) : ℝ))) = (-4 : ℝ) := by norm_num
  have e3 : (-(2 + ((3 : ℕ) : ℝ))) = (-5 : ℝ) := by norm_num
  have b1 : ‖iteratedFDeriv ℝ 1 (sliceF (UnforcedLeray.Short.PartIIIb.Concrete.projPot Ψ) τ) y‖ ≤
      2 * (|C1| + |C2| + |C3|) * ‖y‖ ^ (-3 : ℝ) := by
    have h := iter_projPot_bound hΨ 1 τ y C1 ((h1 τ hτ y hρ1 hy0).1) ((h1 τ hτ y hρ1 hy0).2)
    rw [e1] at h
    exact h.trans (mul_le_mul_of_nonneg_right hM1 hp)
  have b2 : ‖iteratedFDeriv ℝ 2 (sliceF (UnforcedLeray.Short.PartIIIb.Concrete.projPot Ψ) τ) y‖ ≤
      2 * (|C1| + |C2| + |C3|) * ‖y‖ ^ (-4 : ℝ) := by
    have h := iter_projPot_bound hΨ 2 τ y C2 ((h2 τ hτ y hρ2 hy0).1) ((h2 τ hτ y hρ2 hy0).2)
    rw [e2] at h
    exact h.trans (mul_le_mul_of_nonneg_right hM2 hq)
  have b3 : ‖iteratedFDeriv ℝ 3 (sliceF (UnforcedLeray.Short.PartIIIb.Concrete.projPot Ψ) τ) y‖ ≤
      2 * (|C1| + |C2| + |C3|) * ‖y‖ ^ (-5 : ℝ) := by
    have h := iter_projPot_bound hΨ 3 τ y C3 ((h3 τ hτ y hρ3 hy0).1) ((h3 τ hτ y hρ3 hy0).2)
    rw [e3] at h
    exact h.trans (mul_le_mul_of_nonneg_right hM3 hr)
  have hunit1 : ∀ t : Fin 1, ‖(![UnforcedLeray.coordinateVector (0 : Fin 3)] : Fin 1 → UnforcedLeray.Space) t‖ = 1 := by
    intro t; fin_cases t; simp [norm_e3]
  refine ⟨fun j => ?_, fun j k => ?_, fun i j k => ?_⟩
  · rw [dy_slice_one hΦ τ y j]
    refine (norm_iter_vec_le _ y _ (fun t => ?_)).trans b1
    fin_cases t
    simp [norm_e3]
  · rw [dy_slice_two hΦ τ y j k]
    refine (norm_iter_vec_le _ y _ (fun t => ?_)).trans b2
    fin_cases t <;> simp [norm_e3]
  · rw [dy_slice_three hΦ τ y i j k]
    refine (norm_iter_vec_le _ y _ (fun t => ?_)).trans b3
    fin_cases t <;> simp [norm_e3]

end UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly
