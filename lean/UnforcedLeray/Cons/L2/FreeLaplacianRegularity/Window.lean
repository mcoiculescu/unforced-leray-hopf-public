import UnforcedLeray.Cons.L2.FreeLaplacianRegularity.TestCalculus

/-!
# C08-reg, part 3: the fixed-window Laplacian (`eq:free-stress-13`–`eq:free-stress-15`, `q = 2`)

`paper/main.tex` lines 7479–7517 (blueprint unit B0424): for a distributional solution `w` of the
free equation with an `L²` right side and a phase cutoff `χ`, the field
`u(θ, x) = χ(t) e^{-t/2} w(t, e^{-t/2} x)`, `t = log θ`, solves the heat equation
`(∂_θ - hΔ_x) u = F` with
`F(θ, x) = θ^{-3/2} [(χ' - μχ) w - χ 𝔓g](t, θ^{-1/2} x)` (`eq:free-stress-14` with the right
side `-𝔓g` of `IsWeakFreeSolution`), and `u, F ∈ L²(ℝ × ℝ³)`. The heat estimate
`eq:free-stress-11` (unit B0423, `B0423.heat_estimate_componentwise`, drafted from
`Lib/ParabolicB`) gives `Δ_x u ∈ L²`, and transporting back gives a function `L` with

`∫∫ χ(t) ⟨w, Δψ⟩ = ∫∫ ⟨L, ψ⟩` for every similarity test `ψ` (`window_laplacian`),

with `L` square integrable on every slab `[a, b] × ℝ³`. This is the regularity content of
`eq:free-stress-15` at `q = 2` (the bound itself is not recorded: `FreeLaplacianRegularity` asks
only for membership). Each component `w_c` is treated separately (the manuscript applies the
scalar lemma componentwise).

Hypotheses: `w, 𝔓g ∈ 𝒴₂` (real, `P`-periodic, any `P > 0`), `h > 0`, any real `μ`, and the
weak free equation in the form `∫ weakModeIntegrand + ∫ ⟨pg, ψ⟩ = 0` against all similarity
tests (`pg` a representative of `𝔓g`). Periodicity is used only through square integrability
on slabs (`IsY2.memLp_slab`); no restriction `P ≤ 1` and no sign of `μ` enter.

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Cons.L2.FreeLapReg

open UnforcedLeray.Blueprint
open UnforcedLeray.Parabolic (IsSTTest tD sD sD2 sLap dirD sdir tdir ev)

/-! ## Elementary facts -/

theorem inner_eq_sum (x v : Space) : inner ℝ x v = ∑ c : Fin 3, x c * v c := by
  simp [PiLp.inner_apply, mul_comm]

theorem memLp_component {μ' : Measure SpaceTime} {f : SpaceTime → Space} (hf : MemLp f 2 μ')
    (c : Fin 3) : MemLp (fun z => f z c) 2 μ' :=
  (EuclideanSpace.proj c : Space →L[ℝ] ℝ).comp_memLp' hf

/-- A continuous phase weight preserves square integrability on a slab. -/
theorem memLp_weight_slab {g : SpaceTime → ℝ} {a b : ℝ}
    (hg : MemLp g 2 (volume.restrict (slab a b))) {k : ℝ → ℝ} (hk : Continuous k) :
    MemLp (fun z => k z.1 * g z) 2 (volume.restrict (slab a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hk.continuousOn
  refine hg.of_le_mul (c := max C 0)
    ((hk.comp continuous_fst).aestronglyMeasurable.mul hg.1) ?_
  refine (ae_restrict_iff' (measurableSet_slab a b)).mpr (Eventually.of_forall fun z hz => ?_)
  calc ‖k z.1 * g z‖ = ‖k z.1‖ * ‖g z‖ := norm_mul _ _
    _ ≤ max C 0 * ‖g z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (hC _ hz.1).trans (le_max_left _ _)

theorem exp_comb_u (t : ℝ) :
    Real.exp (5 / 2 * t) * Real.exp (-(t / 2)) = Real.exp t * Real.exp t := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem exp_comb_F (t : ℝ) : Real.exp (5 / 2 * t) * Real.exp (-(3 / 2 * t)) = Real.exp t := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem exp_comb_L (t : ℝ) :
    Real.exp (5 / 2 * t) * Real.exp (-t) = Real.exp (3 / 2 * t) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## The heat fields -/

/-- `u_c(θ, x) = χ(t) e^{-t/2} w_c(t, e^{-t/2} x)`, `t = log θ` (tex 7486, 7495–7497). -/
def heatField (χ : ℝ → ℝ) (w : ℝ → SpatialField) (c : Fin 3) : SpaceTime → ℝ :=
  push fun z => χ z.1 * Real.exp (-(z.1 / 2)) * w z.1 z.2 c

/-- `F_c(θ, x) = θ^{-3/2} [(χ' - μχ) w_c - χ pg_c](t, θ^{-1/2} x)` (tex 7488, 7495–7497). -/
def heatForce (μ : ℝ) (χ : ℝ → ℝ) (w pg : ℝ → SpatialField) (c : Fin 3) : SpaceTime → ℝ :=
  push fun z => Real.exp (-(3 / 2 * z.1)) *
    ((deriv χ z.1 - μ * χ z.1) * w z.1 z.2 c - χ z.1 * pg z.1 z.2 c)

theorem isSTTest_sLap {φ : SpaceTime → ℝ} (hφ : IsSTTest (d := 3) φ) :
    IsSTTest (d := 3) (sLap φ) := by
  have e : sLap φ = ∑ i : Fin 3, sD2 i i φ := by
    funext X
    simp [sLap]
  rw [e]
  exact Finset.sum_induction _ (fun f => IsSTTest (d := 3) f) (fun f g hf hg => hf.add hg)
    UnforcedLeray.Parabolic.IsSTTest.zero fun i _ => hφ.sD2 i i

section Window

variable {h P μ : ℝ} {w pg : ℝ → SpatialField} {χ : ℝ → ℝ}

theorem support_weight_subset {k : ℝ → ℝ} (hk : ∀ t, χ t = 0 → deriv χ t = 0 → k t = 0) :
    Function.support k ⊆ tsupport χ := by
  intro t ht
  by_contra hn
  apply ht
  refine hk t (image_eq_zero_of_notMem_tsupport hn) ?_
  by_contra hd
  exact hn (support_deriv_subset hd)

theorem hasCompactSupport_weight (hχc : HasCompactSupport χ) {k : ℝ → ℝ}
    (hk : ∀ t, χ t = 0 → deriv χ t = 0 → k t = 0) : HasCompactSupport k :=
  hχc.mono' (support_weight_subset hk)

/-- A bound `A` with `χ = χ' = 0` outside `[-A, A]`. -/
theorem exists_bound_cutoff (hχc : HasCompactSupport χ) :
    ∃ A : ℝ, ∀ t, t ∉ Icc (-A) A → χ t = 0 ∧ deriv χ t = 0 := by
  obtain ⟨A, hA⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine ⟨A, fun t ht => ?_⟩
  have hnot : t ∉ tsupport χ := by
    intro hmem
    have := hA hmem
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_⟩
  by_contra hd
  exact hnot (support_deriv_subset hd)

theorem memLp_heatField (hP : 0 < P) (hw : B0005.IsY2 P w) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (c : Fin 3) : MemLp (heatField χ w c) 2 volume := by
  obtain ⟨A, hA⟩ := exists_bound_cutoff hχc
  have hf : MemLp (fun z : SpaceTime => χ z.1 * Real.exp (-(z.1 / 2)) * w z.1 z.2 c) 2
      (volume.restrict (slab (-A) A)) := by
    have hk : Continuous (fun t => χ t * Real.exp (-(t / 2))) := by
      fun_prop
    have hbase : MemLp (fun z : SpaceTime =>
        (χ z.1 * Real.exp (-(z.1 / 2))) * w z.1 z.2 c) 2
        (volume.restrict (slab (-A) A)) := by
      simpa only [Function.comp_apply] using
        (memLp_weight_slab (memLp_component (IsY2.memLp_slab hP hw (-A) A) c) hk)
    exact hbase
  have h0 : ∀ z, z ∉ slab (-A) A →
      χ z.1 * Real.exp (-(z.1 / 2)) * w z.1 z.2 c = 0 := by
    intro z hz
    have hz1 : z.1 ∉ Icc (-A) A := fun h1 => hz ⟨h1, mem_univ _⟩
    simp [(hA _ hz1).1]
  exact memLp_push (memLp_simMeasure_of_slab hf h0)

theorem memLp_heatForce (hP : 0 < P) (hw : B0005.IsY2 P w) (hpg : B0005.IsY2 P pg)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (c : Fin 3) :
    MemLp (heatForce μ χ w pg c) 2 volume := by
  obtain ⟨A, hA⟩ := exists_bound_cutoff hχc
  have hd : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have e : (fun z : SpaceTime => Real.exp (-(3 / 2 * z.1)) *
      ((deriv χ z.1 - μ * χ z.1) * w z.1 z.2 c - χ z.1 * pg z.1 z.2 c)) =
      fun z => (fun t => Real.exp (-(3 / 2 * t)) * (deriv χ t - μ * χ t)) z.1 * w z.1 z.2 c -
        (fun t => Real.exp (-(3 / 2 * t)) * χ t) z.1 * pg z.1 z.2 c := by
    funext z
    ring
  have hf : MemLp (fun z : SpaceTime => Real.exp (-(3 / 2 * z.1)) *
      ((deriv χ z.1 - μ * χ z.1) * w z.1 z.2 c - χ z.1 * pg z.1 z.2 c)) 2
      (volume.restrict (slab (-A) A)) := by
    rw [e]
    change MemLp ((fun z : SpaceTime =>
      (Real.exp (-(3 / 2 * z.1)) * (deriv χ z.1 - μ * χ z.1)) * w z.1 z.2 c) -
      (fun z => (Real.exp (-(3 / 2 * z.1)) * χ z.1) * pg z.1 z.2 c)) 2
      (volume.restrict (slab (-A) A))
    exact (memLp_weight_slab
      (memLp_component (IsY2.memLp_slab hP hw (-A) A) c)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hd.sub (continuous_const.mul hχ.continuous)))).sub
      (memLp_weight_slab (memLp_component (IsY2.memLp_slab hP hpg (-A) A) c)
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
          hχ.continuous))
  have h0 : ∀ z, z ∉ slab (-A) A → Real.exp (-(3 / 2 * z.1)) *
      ((deriv χ z.1 - μ * χ z.1) * w z.1 z.2 c - χ z.1 * pg z.1 z.2 c) = 0 := by
    intro z hz
    have hz1 : z.1 ∉ Icc (-A) A := fun h1 => hz ⟨h1, mem_univ _⟩
    simp [(hA _ hz1).1, (hA _ hz1).2]
  exact memLp_push (memLp_simMeasure_of_slab hf h0)

/-- **`eq:free-stress-14` in distributions** (tex 7491–7497, B0424): `(∂_θ - hΔ_x) u_c = F_c`
tested against every heat test. -/
theorem isWeakHeatSol_heatField (hP : 0 < P) (hw : B0005.IsY2 P w) (hpg : B0005.IsY2 P pg)
    (heq : ∀ Ψ, IsSimilarityTest Ψ →
      (∫ z, weakModeIntegrand h μ w Ψ z) + (∫ z, pairTerm pg Ψ z) = 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (c : Fin 3) :
    B0423.IsWeakHeatSol h (heatField χ w c) (heatForce μ χ w pg c) := by
  intro φ hφ
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable
  have hderiv : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  -- the three lifted tests
  set aC : ℝ → ℝ := fun t => χ t * Real.exp t with haC
  set aA : ℝ → ℝ := fun t => Real.exp t * (μ * χ t - deriv χ t) with haA
  set aB : ℝ → ℝ := fun t => χ t * Real.exp t * Real.exp t with haB
  set ΦB : SpaceTime → ℝ := fun X => tD φ X + h * sLap φ X with hΦB
  have hΦB : IsSTTest (d := 3) ΦB := by
    have h2 := (hφ.dirD tdir).add ((isSTTest_sLap hφ).smul h)
    change IsSTTest (dirD tdir φ + h • sLap φ)
    exact h2
  have hC : IsSimilarityTest (liftTest aC φ c) :=
    isSimilarityTest_liftTest (hχ.mul Real.contDiff_exp)
      (hasCompactSupport_weight hχc fun t h0 _ => by simp [haC, h0]) hφ.1 hφ.2
  have hA : IsSimilarityTest (liftTest aA φ c) :=
    isSimilarityTest_liftTest (Real.contDiff_exp.mul ((contDiff_const.mul hχ).sub hderiv))
      (hasCompactSupport_weight hχc fun t h0 h1 => by simp [haA, h0, h1]) hφ.1 hφ.2
  have hB : IsSimilarityTest (liftTest aB ΦB c) :=
    isSimilarityTest_liftTest ((hχ.mul Real.contDiff_exp).mul Real.contDiff_exp)
      (hasCompactSupport_weight hχc fun t h0 _ => by simp [haB, h0]) hΦB.1 hΦB.2
  have iA := C08.integrable_pairTerm_of_isY2 hP hw hA
  have iB := C08.integrable_pairTerm_of_isY2 hP hw hB
  have iC := C08.integrable_pairTerm_of_isY2 hP hpg hC
  -- the pointwise identity for the free equation
  have haCDiff : Differentiable ℝ aC := by
    change Differentiable ℝ (fun t => χ t * Real.exp t)
    fun_prop
  have hdC : ∀ t, deriv aC t = deriv χ t * Real.exp t + χ t * Real.exp t := fun t => by
    change deriv (χ * Real.exp) t = _
    rw [deriv_mul (hχd t) Real.differentiableAt_exp, Real.deriv_exp]
  have hpt : ∀ z, weakModeIntegrand h μ w (liftTest aC φ c) z =
      pairTerm w (liftTest aA φ c) z - pairTerm w (liftTest aB ΦB c) z := by
    rintro ⟨t, y⟩
    simp only [weakModeIntegrand, driftAdjointTerm, temporalTerm, dilationTerm, diffusionTerm,
      pairTerm_liftTest]
    dsimp only [ΦB]
    rw [timeDerivative_liftTest haCDiff hφd,
      spatialDerivative_liftTest hφd, spatialLaplacian_liftTest hφ.1, hdC,
      inner_smul_coordinateVector, inner_smul_coordinateVector, inner_smul_coordinateVector]
    simp only [pairTerm, liftTest, inner_smul_coordinateVector, haC, haA, haB, hΦB]
    ring
  have hfree := heq _ hC
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub iA iB] at hfree
  -- the heat side, left
  have hL : ∫ X, heatField χ w c X * (-tD φ X - h * sLap φ X) =
      ∫ z, -pairTerm w (liftTest aB ΦB c) z := by
    rw [integral_eq_of_vanish fun X hX => by rw [heatField, push_of_nonpos _ hX, zero_mul]]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [heatField, push_simE, pairTerm_liftTest, haB, hΦB]
    linear_combination (-(χ z.1 * w z.1 z.2 c * (tD φ (simE z) + h * sLap φ (simE z)))) *
      exp_comb_u z.1
  -- the heat side, right
  have hR : ∫ X, heatForce μ χ w pg c X * φ X =
      ∫ z, (-pairTerm w (liftTest aA φ c) z - pairTerm pg (liftTest aC φ c) z) := by
    rw [integral_eq_of_vanish fun X hX => by rw [heatForce, push_of_nonpos _ hX, zero_mul]]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [heatForce, push_simE, pairTerm_liftTest, haA, haC]
    linear_combination (((deriv χ z.1 - μ * χ z.1) * w z.1 z.2 c - χ z.1 * pg z.1 z.2 c) *
      φ (simE z)) * exp_comb_F z.1
  have hkey : (∫ z : SpaceTime, -pairTerm w (liftTest aB ΦB c) z) =
      (∫ z : SpaceTime, -pairTerm w (liftTest aA φ c) z) -
        ∫ z : SpaceTime, pairTerm pg (liftTest aC φ c) z := by
    rw [integral_neg, integral_neg]
    linarith [hfree]
  rw [hL, hR]
  calc (∫ z : SpaceTime, -pairTerm w (liftTest aB ΦB c) z) =
        (∫ z : SpaceTime, -pairTerm w (liftTest aA φ c) z) -
          ∫ z : SpaceTime, pairTerm pg (liftTest aC φ c) z := hkey
    _ = ∫ z : SpaceTime, -pairTerm w (liftTest aA φ c) z -
          pairTerm pg (liftTest aC φ c) z := (integral_sub iA.neg iC).symm

/-- **The Laplacian of the heat field** (`eq:free-stress-11`, unit B0423, applied to
`eq:free-stress-14`): there is `Lap ∈ L²(ℝ × ℝ³)` with `∫ u_c Δ_xφ = ∫ Lap φ` for every heat
test `φ`. -/
theorem exists_heat_laplacian (hh : 0 < h) (hP : 0 < P) (hw : B0005.IsY2 P w)
    (hpg : B0005.IsY2 P pg)
    (heq : ∀ Ψ, IsSimilarityTest Ψ →
      (∫ z, weakModeIntegrand h μ w Ψ z) + (∫ z, pairTerm pg Ψ z) = 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (c : Fin 3) :
    ∃ Lap : SpaceTime → ℝ, MemLp Lap 2 volume ∧ ∀ φ : SpaceTime → ℝ, IsSTTest (d := 3) φ →
      ∫ X, heatField χ w c X * sLap φ X = ∫ X, Lap X * φ X := by
  obtain ⟨C, hC⟩ := B0423.heat_estimate_componentwise (d := 3) (q := 2) one_lt_two
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have hu := memLp_heatField hP hw hχ hχc c
  have hF := memLp_heatForce (μ := μ) hP hw hpg hχ hχc c
  obtain ⟨D2, Dt, hD2, -, -, -, -⟩ := hC h hh (heatField χ w c) (heatForce μ χ w pg c)
    (by rw [e2]; exact hu) (by rw [e2]; exact hF) (isWeakHeatSol_heatField hP hw hpg heq hχ hχc c)
  refine ⟨fun X => ∑ i : Fin 3, D2 i i X, ?_, fun φ hφ => ?_⟩
  · refine memLp_finsetSum _ fun i _ => ?_
    simpa only [e2] using (hD2 i i).1
  · have hint : ∀ i : Fin 3, Integrable (fun X => heatField χ w c X * sD2 i i φ X) := fun i =>
      hu.integrable_mul ((hφ.sD2 i i).memLp 2)
    have hint' : ∀ i : Fin 3, Integrable (fun X => D2 i i X * φ X) := fun i => by
      have h1 : MemLp (D2 i i) 2 volume := by simpa only [e2] using (hD2 i i).1
      exact h1.integrable_mul (hφ.memLp 2)
    calc ∫ X, heatField χ w c X * sLap φ X
        = ∫ X, ∑ i : Fin 3, heatField χ w c X * sD2 i i φ X := by
          refine integral_congr_ae (Eventually.of_forall fun X => ?_)
          simp only [sLap, Finset.mul_sum]
      _ = ∑ i : Fin 3, ∫ X, heatField χ w c X * sD2 i i φ X :=
          integral_finsetSum _ fun i _ => hint i
      _ = ∑ i : Fin 3, ∫ X, D2 i i X * φ X :=
          Finset.sum_congr rfl fun i _ => (hD2 i i).2 φ hφ
      _ = ∫ X, ∑ i : Fin 3, D2 i i X * φ X := (integral_finsetSum _ fun i _ => hint' i).symm
      _ = ∫ X, (∑ i : Fin 3, D2 i i X) * φ X := by
          refine integral_congr_ae (Eventually.of_forall fun X => ?_)
          simp only [Finset.sum_mul]

/-- The heat test `φ_c(θ, x) = θ^{-1} Ψ_c(log θ, θ^{-1/2} x)` of a similarity test `Ψ`. -/
def pullTest (Ψ : SpaceTime → Space) (c : Fin 3) : SpaceTime → ℝ :=
  push fun z => Real.exp (-z.1) * Ψ z c

theorem isSTTest_pullTest {Ψ : SpaceTime → Space} (hΨ : IsSimilarityTest Ψ) (c : Fin 3) :
    IsSTTest (d := 3) (pullTest Ψ c) := by
  refine isSTTest_push ((Real.contDiff_exp.comp contDiff_fst.neg).mul
    ((EuclideanSpace.proj c : Space →L[ℝ] ℝ).contDiff.comp hΨ.smooth)) ?_
  have h1 : HasCompactSupport (fun z => (EuclideanSpace.proj c : Space →L[ℝ] ℝ) (Ψ z)) :=
    hΨ.compact.comp_left (map_zero _)
  exact h1.mul_left

/-- **Transport of the Laplacian** (tex 7498–7517, B0424): for a similarity test `Ψ`,
`∫∫ w_c χ(t) (ΔΨ)_c = ∫∫ L_c Ψ_c` with `L_c(t, y) = e^{3t/2} Lap(e^t, e^{t/2} y)`. -/
theorem window_component (hh : 0 < h) (hP : 0 < P) (hw : B0005.IsY2 P w)
    (hpg : B0005.IsY2 P pg)
    (heq : ∀ Ψ, IsSimilarityTest Ψ →
      (∫ z, weakModeIntegrand h μ w Ψ z) + (∫ z, pairTerm pg Ψ z) = 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (c : Fin 3) :
    ∃ Lc : SpaceTime → ℝ, (∀ a b, MemLp Lc 2 (volume.restrict (slab a b))) ∧
      ∀ Ψ, IsSimilarityTest Ψ →
        Integrable (fun (z : SpaceTime) => w z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c)) ∧
        Integrable (fun (z : SpaceTime) => Lc z * Ψ z c) ∧
        ∫ z : SpaceTime, w z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) =
          ∫ z : SpaceTime, Lc z * Ψ z c := by
  obtain ⟨Lap, hLap, hLapEq⟩ := exists_heat_laplacian hh hP hw hpg heq hχ hχc c
  have hu := memLp_heatField hP hw hχ hχc c
  refine ⟨fun z => Real.exp (3 / 2 * z.1) * Lap (simE z), fun a b => ?_, fun Ψ hΨ => ?_⟩
  · exact memLp_weight_slab (k := fun t => Real.exp (3 / 2 * t))
      (memLp_slab_of_simMeasure (memLp_comp_simE hLap) a b)
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  set φc := pullTest Ψ c with hφc
  have hφ := isSTTest_pullTest hΨ c
  -- the lifted test is `χ Ψ_c e_c`
  have hlift : liftTest (fun t => χ t * Real.exp t) φc c =
      fun z => (χ z.1 * Ψ z c) • coordinateVector c := by
    funext z
    simp only [liftTest, hφc, pullTest, push_simE]
    congr 1
    rw [mul_assoc, ← mul_assoc (Real.exp z.1), ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      one_mul]
  have hlap : ∀ z : SpaceTime, χ z.1 * Real.exp z.1 * Real.exp z.1 * sLap φc (simE z) =
      χ z.1 * spatialLaplacian Ψ z.1 z.2 c := by
    intro z
    have h1 := spatialLaplacian_liftTest (a := fun t => χ t * Real.exp t) (c := c) hφ.1 z.1 z.2
    rw [hlift, spatialLaplacian_component hΨ.smooth] at h1
    have h2 := congrArg (fun v : Space => v c) h1
    simp only [coordinateVector_apply_self] at h2
    rw [h2]
  -- left side
  have hvL : ∀ X : SpaceTime, X.1 ≤ 0 → heatField χ w c X * sLap φc X = 0 := fun X hX => by
    rw [heatField, push_of_nonpos _ hX, zero_mul]
  have iL0 : Integrable (fun X => heatField χ w c X * sLap φc X) :=
    hu.integrable_mul ((isSTTest_sLap hφ).memLp 2)
  have ptL : ∀ z : SpaceTime, Real.exp (5 / 2 * z.1) * (heatField χ w c (simE z) *
      sLap φc (simE z)) = w z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) := by
    intro z
    rw [← hlap z, heatField, push_simE]
    linear_combination (χ z.1 * w z.1 z.2 c * sLap φc (simE z)) * exp_comb_u z.1
  -- right side
  have hvR : ∀ X : SpaceTime, X.1 ≤ 0 → Lap X * φc X = 0 := fun X hX => by
    rw [hφc, pullTest, push_of_nonpos _ hX, mul_zero]
  have iR0 : Integrable (fun X => Lap X * φc X) := hLap.integrable_mul (hφ.memLp 2)
  have ptR : ∀ z : SpaceTime, Real.exp (5 / 2 * z.1) * (Lap (simE z) * φc (simE z)) =
      Real.exp (3 / 2 * z.1) * Lap (simE z) * Ψ z c := by
    intro z
    rw [hφc, pullTest, push_simE]
    linear_combination (Lap (simE z) * Ψ z c) * exp_comb_L z.1
  have iL := integrable_of_vanish hvL iL0
  have iR := integrable_of_vanish hvR iR0
  simp_rw [ptL] at iL
  simp_rw [ptR] at iR
  refine ⟨iL, iR, ?_⟩
  have key := hLapEq φc hφ
  rw [integral_eq_of_vanish hvL, integral_eq_of_vanish hvR] at key
  simp_rw [ptL, ptR] at key
  exact key

/-- **The fixed-window Laplacian** (`eq:free-stress-13`–`eq:free-stress-15` at `q = 2`, tex
7479–7517, unit B0424): for a phase cutoff `χ ∈ C_c^∞(ℝ)` there is `L`, square integrable on
every slab, with `∫∫ χ(t) ⟨w, Δψ⟩ = ∫∫ ⟨L, ψ⟩` for every similarity test `ψ`. -/
theorem window_laplacian (hh : 0 < h) (hP : 0 < P) (hw : B0005.IsY2 P w)
    (hpg : B0005.IsY2 P pg)
    (heq : ∀ Ψ, IsSimilarityTest Ψ →
      (∫ z, weakModeIntegrand h μ w Ψ z) + (∫ z, pairTerm pg Ψ z) = 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ L : ℝ → SpatialField,
      (∀ a b, MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (slab a b))) ∧
      ∀ Ψ, IsSimilarityTest Ψ → Integrable (fun z => χ z.1 * diffusionTerm w Ψ z) ∧
        Integrable (pairTerm L Ψ) ∧
        ∫ z, χ z.1 * diffusionTerm w Ψ z = ∫ z, pairTerm L Ψ z := by
  choose Lc hLc hEq using fun c : Fin 3 => window_component hh hP hw hpg heq hχ hχc c
  refine ⟨fun t y => ∑ c : Fin 3, Lc c (t, y) • coordinateVector c, fun a b => ?_,
    fun Ψ hΨ => ?_⟩
  · refine memLp_finsetSum _ fun c _ => ?_
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector c)).comp_memLp' (hLc c a b)
  have hptL : ∀ z : SpaceTime, χ z.1 * diffusionTerm w Ψ z =
      ∑ c : Fin 3, w z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) := by
    intro z
    rw [diffusionTerm, inner_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  have hptR : ∀ z : SpaceTime, pairTerm (fun t y => ∑ c : Fin 3, Lc c (t, y) •
      coordinateVector c) Ψ z = ∑ c : Fin 3, Lc c z * Ψ z c := by
    intro z
    rw [pairTerm, sum_inner]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [real_inner_smul_left, real_inner_comm, inner_coordinateVector]
  have iL : Integrable (fun z => χ z.1 * diffusionTerm w Ψ z) := by
    simp_rw [hptL]
    exact integrable_finsetSum _ fun c _ => (hEq c Ψ hΨ).1
  have iR : Integrable (pairTerm (fun t y => ∑ c : Fin 3, Lc c (t, y) •
      coordinateVector c) Ψ) := by
    have e : pairTerm (fun t y => ∑ c : Fin 3, Lc c (t, y) • coordinateVector c) Ψ =
        fun z => ∑ c : Fin 3, Lc c z * Ψ z c := funext hptR
    rw [e]
    exact integrable_finsetSum _ fun c _ => (hEq c Ψ hΨ).2.1
  refine ⟨iL, iR, ?_⟩
  simp_rw [hptL, hptR]
  calc ∫ z : SpaceTime, ∑ c : Fin 3, w z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c)
      = ∑ c : Fin 3, ∫ z : SpaceTime, w z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) :=
        integral_finsetSum Finset.univ fun c hc => (hEq c Ψ hΨ).1
    _ = ∑ c : Fin 3, ∫ z : SpaceTime, Lc c z * Ψ z c :=
        Finset.sum_congr rfl fun c _ => (hEq c Ψ hΨ).2.2
    _ = ∫ z : SpaceTime, ∑ c : Fin 3, Lc c z * Ψ z c :=
        (integral_finsetSum Finset.univ fun c hc => (hEq c Ψ hΨ).2.1).symm

end Window

end UnforcedLeray.Cons.L2.FreeLapReg
