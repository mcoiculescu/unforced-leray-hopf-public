import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinConvTPhaseTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldMeas
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp

/-!
# `GELinFieldLp`: the `L^{q₀}` bound of the linear-term field (source 2525-2533, 1217-1219)

Task `PartIII-b:C/ward/12/3/1/2/6/10`.  The coefficients `raw`, `rawD`, `rawDD` are bounded uniformly
(from `GELinRawOK`, through `iteratedFDeriv`), and the `rep` components are `L^{q₀}` on the phase cell,
so each component of `GELinField` is `L^{q₀}` on the cell; a norm bound by coordinates then gives
the vector, and `lintegral_prod` turns the cell integral into the iterated one.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params rep phaseCell memLp_rep_periodCell stronglyMeasurable_rep)

/-- A vector is bounded by the sum of its coordinate norms. -/
theorem gAdj_norm_le_sum_coord (x : UnforcedLeray.PhaseSpace.CVec3) :
    ‖x‖ ≤ ∑ i : Fin 3, ‖x i‖ := by
  have hx : x = ∑ i : Fin 3,
      x i • (EuclideanSpace.single i (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc ‖x‖ = ‖∑ i : Fin 3,
        x i • (EuclideanSpace.single i (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)‖ := by
          rw [← hx]
    _ ≤ ∑ i : Fin 3,
        ‖x i • (EuclideanSpace.single i (1 : ℂ) : UnforcedLeray.PhaseSpace.CVec3)‖ :=
          norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ := by
          simp [norm_smul]

/-- A bounded measurable coefficient times an `L^q` function is `L^q`. -/
theorem gAdj_memLp_mul {X : Type*} [MeasurableSpace X] {μ : Measure X} {q : ℝ≥0∞}
    {c r : X → ℂ} {C : ℝ} (hc : Measurable c) (hcC : ∀ x, ‖c x‖ ≤ C) (hr : MemLp r q μ) :
    MemLp (fun x => c x * r x) q μ := by
  have hg : MemLp (fun x => C * ‖r x‖) q μ := hr.norm.const_mul C
  have hf : AEStronglyMeasurable (fun x => c x * r x) μ :=
    (hc.aestronglyMeasurable).mul hr.aestronglyMeasurable
  refine MemLp.of_le hg hf (ae_of_all _ fun x => ?_)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hcC x)
  have hn : ‖C * ‖r x‖‖ = C * ‖r x‖ := Real.norm_of_nonneg (mul_nonneg hC0 (norm_nonneg _))
  rw [norm_mul, hn]
  exact mul_le_mul_of_nonneg_right (hcC x) (norm_nonneg (r x))

/-- A component of a representative is `L^{q₀}` on the phase cell. -/
theorem gAdj_memLp_rep_comp {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E)
    (k : Fin 3) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2 k) UnforcedLeray.B0412.q0E
      (volume.restrict (phaseCell P)) := by
  have h := memLp_rep_periodCell UnforcedLeray.B0412.q0E_ne_top w
  have hf : AEStronglyMeasurable (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2 k)
      (volume.restrict (phaseCell P)) :=
    ((EuclideanSpace.proj k : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_rep w)).aestronglyMeasurable
  refine MemLp.of_le h.norm hf (ae_of_all _ fun x => ?_)
  rw [norm_norm]
  exact PiLp.norm_apply_le _ _


theorem gAdj_raw_contDiff {p : Params}
    (hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => p.raw τ y) := by
  have h2 : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => ((τ, y) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk contDiff_id
  have h3 := hC.comp h2
  simpa only [Function.comp_def] using h3

/-- The first derivatives `rawD` are bounded by the first-order bound of `raw`. -/
theorem gAdj_rawD_bound {p : Params} {C1 : ℝ}
    (hC1 : ∀ (τ : ℝ) (y : UnforcedLeray.Space), ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ ≤ C1)
    (x : ℝ × UnforcedLeray.Space) (k i : Fin 3) :
    ‖((rawD p k x i : ℝ) : ℂ)‖ ≤ C1 := by
  rw [Complex.norm_real]
  calc ‖rawD p k x i‖ ≤ ‖rawD p k x‖ := PiLp.norm_apply_le _ _
    _ = ‖fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1)‖ := rfl
    _ ≤ ‖fderiv ℝ (p.raw x.1) x.2‖ * ‖(EuclideanSpace.single k 1 : UnforcedLeray.Space)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 1 (p.raw x.1) x.2‖ := by
        rw [norm_iteratedFDeriv_one, PiLp.norm_single]
        simp
    _ ≤ C1 := hC1 x.1 x.2

/-- The second derivatives `rawDD` are bounded by the second-order bound of `raw`. -/
theorem gAdj_rawDD_bound {p : Params}
    (hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)) {C2 : ℝ}
    (hC2 : ∀ (τ : ℝ) (y : UnforcedLeray.Space), ‖iteratedFDeriv ℝ 2 (p.raw τ) y‖ ≤ C2)
    (x : ℝ × UnforcedLeray.Space) (a b i : Fin 3) :
    ‖((rawDD p a b x i : ℝ) : ℂ)‖ ≤ C2 := by
  rw [Complex.norm_real]
  have hs : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => p.raw x.1 y) :=
    gAdj_raw_contDiff hC x.1
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (fun y : UnforcedLeray.Space => p.raw x.1 y)) x.2 :=
    (hs.fderiv_right (m := ∞) (by simp)).contDiffAt
  have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ (fun y : UnforcedLeray.Space => p.raw x.1 y))
    (c := (EuclideanSpace.single b 1 : UnforcedLeray.Space)) (x := x.2) (N := ∞) (n := 1) hfd
    (by simp)
  rw [norm_iteratedFDeriv_fderiv, PiLp.norm_single, norm_one, one_mul] at h1
  have h2 : ‖iteratedFDeriv ℝ (1 + 1) (fun y : UnforcedLeray.Space => p.raw x.1 y) x.2‖ ≤ C2 :=
    hC2 x.1 x.2
  have h3 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := x.2)
    (fun y : UnforcedLeray.Space => fderiv ℝ (fun y' : UnforcedLeray.Space => p.raw x.1 y') y
      (EuclideanSpace.single b 1))
  have hkey : ‖fderiv ℝ (fun y : UnforcedLeray.Space =>
      fderiv ℝ (fun y' : UnforcedLeray.Space => p.raw x.1 y') y (EuclideanSpace.single b 1)) x.2‖ ≤ C2 := by
    rw [← h3]
    exact h1.trans h2
  calc ‖rawDD p a b x i‖ ≤ ‖rawDD p a b x‖ := PiLp.norm_apply_le _ _
    _ = ‖fderiv ℝ (fun y : UnforcedLeray.Space =>
          fderiv ℝ (fun y' : UnforcedLeray.Space => p.raw x.1 y') y (EuclideanSpace.single b 1)) x.2
          (EuclideanSpace.single a 1)‖ := rfl
    _ ≤ ‖fderiv ℝ (fun y : UnforcedLeray.Space =>
          fderiv ℝ (fun y' : UnforcedLeray.Space => p.raw x.1 y') y (EuclideanSpace.single b 1)) x.2‖ *
          ‖(EuclideanSpace.single a 1 : UnforcedLeray.Space)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun y : UnforcedLeray.Space =>
          fderiv ℝ (fun y' : UnforcedLeray.Space => p.raw x.1 y') y (EuclideanSpace.single b 1)) x.2‖ := by
        rw [PiLp.norm_single]
        simp
    _ ≤ C2 := hkey

theorem gELinFieldLp : GELinFieldLp := by
  intro p z g h j hraw
  obtain ⟨hsm, hbd⟩ := hraw
  have hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) := hsm.1
  obtain ⟨C0, hC0⟩ := hbd 0
  obtain ⟨C1, hC1⟩ := hbd 1
  obtain ⟨C2, hC2⟩ := hbd 2
  have hrawb : ∀ (τ : ℝ) (y : UnforcedLeray.Space) (m : Fin 3),
      ‖((p.raw τ y m : ℝ) : ℂ)‖ ≤ C0 := by
    intro τ y m
    rw [Complex.norm_real]
    calc ‖p.raw τ y m‖ ≤ ‖p.raw τ y‖ := PiLp.norm_apply_le _ _
      _ = ‖iteratedFDeriv ℝ 0 (p.raw τ) y‖ := (norm_iteratedFDeriv_zero (𝕜 := ℝ)).symm
      _ ≤ C0 := hC0 τ y
  have hmeasc : ∀ {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}, ContDiff ℝ ∞ F →
      ∀ i : Fin 3, Measurable (fun x : ℝ × UnforcedLeray.Space => ((F x i : ℝ) : ℂ)) := by
    intro F hF i
    exact (Complex.continuous_ofReal.comp ((contDiff_piLp 2).1 hF i).continuous).measurable
  have hrD : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => rawD p k x) :=
    fun k => gELinConvT_partial hC k
  have hrDD : ∀ a b : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => rawDD p a b x) :=
    fun a b => gELinConvT_partial (hrD b) a
  -- T1: `∑ₖ ∂ₖ raw_i · rep (g j)_k`
  have T1 : ∀ (i : Fin 3) (w : Yq p.period UnforcedLeray.B0412.q0E),
      MemLp (fun x : ℝ × UnforcedLeray.Space => ∑ k : Fin 3,
        ((rawD p k x i : ℝ) : ℂ) * rep w x.1 x.2 k)
        UnforcedLeray.B0412.q0E (volume.restrict (phaseCell p.period)) := by
    intro i w
    apply memLp_finsetSum
    intro k _
    exact gAdj_memLp_mul (hmeasc (hrD k) i) (fun x => gAdj_rawD_bound hC1 x k i)
      (gAdj_memLp_rep_comp w k)
  -- T2: `∑ₘ (∂ₘ raw_m · rep v_i + raw_m · rep (w m)_i)`
  have T2 : ∀ (i : Fin 3) (w : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
      (v : Yq p.period UnforcedLeray.B0412.q0E),
      MemLp (fun x : ℝ × UnforcedLeray.Space => ∑ m : Fin 3,
        (((rawD p m x m : ℝ) : ℂ) * rep v x.1 x.2 i +
          ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (w m) x.1 x.2 i))
        UnforcedLeray.B0412.q0E (volume.restrict (phaseCell p.period)) := by
    intro i w v
    apply memLp_finsetSum
    intro m _
    refine MemLp.add ?_ ?_
    · exact gAdj_memLp_mul (hmeasc (hrD m) m) (fun x => gAdj_rawD_bound hC1 x m m)
        (gAdj_memLp_rep_comp v i)
    · exact gAdj_memLp_mul (hmeasc hC m) (fun x => hrawb x.1 x.2 m)
        (gAdj_memLp_rep_comp (w m) i)
  -- T3: `∑ₖ ∂ₖ∂ⱼ raw_i · rep w_k`
  have T3 : ∀ (i j : Fin 3) (w : Yq p.period UnforcedLeray.B0412.q0E),
      MemLp (fun x : ℝ × UnforcedLeray.Space => ∑ k : Fin 3,
        ((rawDD p k j x i : ℝ) : ℂ) * rep w x.1 x.2 k)
        UnforcedLeray.B0412.q0E (volume.restrict (phaseCell p.period)) := by
    intro i j w
    apply memLp_finsetSum
    intro k _
    exact gAdj_memLp_mul (hmeasc (hrDD k j) i) (fun x => gAdj_rawDD_bound hC hC2 x k j i)
      (gAdj_memLp_rep_comp w k)
  -- T4: `∑ₘ (∂ₘ∂ⱼ raw_m · rep w_i + ∂ⱼ raw_m · rep (u m)_i)`
  have T4 : ∀ (i j : Fin 3) (w : Yq p.period UnforcedLeray.B0412.q0E)
      (u : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E),
      MemLp (fun x : ℝ × UnforcedLeray.Space => ∑ m : Fin 3,
        (((rawDD p m j x m : ℝ) : ℂ) * rep w x.1 x.2 i +
          ((rawD p j x m : ℝ) : ℂ) * rep (u m) x.1 x.2 i))
        UnforcedLeray.B0412.q0E (volume.restrict (phaseCell p.period)) := by
    intro i j w u
    apply memLp_finsetSum
    intro m _
    refine MemLp.add ?_ ?_
    · exact gAdj_memLp_mul (hmeasc (hrDD m j) m) (fun x => gAdj_rawDD_bound hC hC2 x m j m)
        (gAdj_memLp_rep_comp w i)
    · exact gAdj_memLp_mul (hmeasc (hrD j) m) (fun x => gAdj_rawD_bound hC1 x j m)
        (gAdj_memLp_rep_comp (u m) i)
  have hcomp : ∀ i : Fin 3, MemLp (fun x : ℝ × UnforcedLeray.Space => GELinField p z g h j x i)
      UnforcedLeray.B0412.q0E (volume.restrict (phaseCell p.period)) := by
    intro i
    simp only [GELinField, PiLp.toLp_apply]
    exact (MemLp.add (MemLp.add (T1 i (g j)) (T2 i (h j) (g j)))
      (MemLp.add (T3 i j (p.wOf z)) (T4 i j (p.wOf z) g))).neg
  -- the vector field: a norm bound by the coordinate norms
  have hsum : MemLp (fun x : ℝ × UnforcedLeray.Space => ∑ i : Fin 3,
      ‖GELinField p z g h j x i‖) UnforcedLeray.B0412.q0E
      (volume.restrict (phaseCell p.period)) :=
    memLp_finsetSum Finset.univ (fun i _ => (hcomp i).norm)
  have hmeasF : StronglyMeasurable (GELinField p z g h j) := gELinFieldMeas p z g h j hsm
  have hF : MemLp (GELinField p z g h j) UnforcedLeray.B0412.q0E
      (volume.restrict (phaseCell p.period)) := by
    refine MemLp.of_le hsum hmeasF.aestronglyMeasurable.restrict (ae_of_all _ fun x => ?_)
    have hnn : 0 ≤ ∑ i : Fin 3, ‖GELinField p z g h j x i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact gAdj_norm_le_sum_coord (GELinField p z g h j x)
  -- from the cell `L^{q₀}` bound to the iterated integral
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one UnforcedLeray.B0412.one_lt_q0E)
  have hfin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0
    UnforcedLeray.B0412.q0E_ne_top).1 hF.eLpNorm_lt_top
  have hprod : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict (phaseCell p.period) =
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) p.period)).prod
        (volume : Measure UnforcedLeray.Space) := by
    simpa only [phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure UnforcedLeray.Space)) (Ioc (0 : ℝ) p.period)).symm
  have hmeasE : Measurable (fun x : ℝ × UnforcedLeray.Space =>
      ‖GELinField p z g h j x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal) :=
    (hmeasF.measurable.enorm).pow_const _
  have hconv : ∫⁻ x in phaseCell p.period, ‖GELinField p z g h j x‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal =
      ∫⁻ τ in Ioc (0 : ℝ) p.period, ∫⁻ y, ‖GELinField p z g h j (τ, y)‖ₑ ^
        UnforcedLeray.B0412.q0E.toReal := by
    rw [hprod, lintegral_prod _ hmeasE.aemeasurable]
  rw [← hconv]
  exact hfin

end UnforcedLeray.Short.PartIIIb.Concrete
