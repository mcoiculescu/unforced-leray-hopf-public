import UnforcedLeray.Lib.CZL2.Decay

/-!
# The Leray projection of a compact smooth vector test (INF01 level L0)

Blueprint: INF01 (scoping note `INF01-CZ.md` §4.2 and §5 targets T2/T4); decision D5 of
`scoping/README.md` §3. Manuscript: `𝔓` is the Leray projection
(`paper/main.tex` lines 107–111); `(I - 𝔓)` is the gradient part
`-∇(-Δ)^{-1} div`.

For a compact smooth vector test `φ = Σⱼ φⱼ eⱼ` put `ψ = N ∗ div φ`. We prove that the
compiled orthogonal Leray projection satisfies

  `𝔓 φ = φ + ∇(N ∗ div φ)`,

so `(I - 𝔓)φ = -∇(N ∗ div φ)`. The proof uses `Leray.projection_eq_of_orthogonal`
(`LerayProjection/Basic.lean:130`): `φ + ∇ψ` is weakly divergence free because
`Δψ = -div φ`, and `∇ψ` is orthogonal to every solenoidal L² field
(`toL2_gradField_mem_orthogonal`), because `ψ` and `∇ψ` decay like `|y|⁻²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.RieszLp

open PressureAnalysis

/-- The vector field `Σⱼ fⱼ eⱼ` with components `fⱼ`. -/
def vecField (f : Fin 3 → Space → ℝ) : SpatialField :=
  fun x => ∑ j : Fin 3, f j x • coordinateVector j

/-- The divergence `Σⱼ ∂ⱼ fⱼ` of a component family. -/
def divTest (f : Fin 3 → Space → ℝ) : Space → ℝ :=
  fun x => ∑ j : Fin 3, spatialTestDerivative j (f j) x

/-- The potential `ψ = N ∗ div φ`, with `(I - 𝔓)φ = -∇ψ`. -/
def lerayPotential (f : Fin 3 → Space → ℝ) : Space → ℝ := newtonConv (divTest f)

theorem vecField_apply (f : Fin 3 → Space → ℝ) (x : Space) (i : Fin 3) :
    vecField f x i = f i x := sum_smul_coordinateVector_apply (fun j => f j x) i

theorem gradField_apply (ψ : Space → ℝ) (x : Space) (i : Fin 3) :
    gradField ψ x i = spatialTestDerivative i ψ x :=
  sum_smul_coordinateVector_apply (fun j => spatialTestDerivative j ψ x) i

/-- Every vector `v : Space` is `Σⱼ vⱼ eⱼ`. -/
theorem eq_sum_coordinateVector (v : Space) : v = ∑ j : Fin 3, v j • coordinateVector j := by
  ext i
  rw [sum_smul_coordinateVector_apply (fun j => v j) i]

/-- A field equals the `vecField` of its components. -/
theorem vecField_components (φ : SpatialField) : vecField (fun j x => φ x j) = φ := by
  funext x
  exact (eq_sum_coordinateVector (φ x)).symm

theorem isSpatialTest_divTest {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    IsSpatialTest (divTest f) := by
  have he : divTest f = ∑ j : Fin 3, spatialTestDerivative j (f j) := by
    funext x; simp [divTest]
  rw [he]
  constructor
  · convert (ContDiff.sum (s := Finset.univ) (fun j _ => ((hf j).derivative j).smooth)) using 1
    funext x
    simp only [Finset.sum_apply]
  · exact HasCompactSupport.finset_sum (fun j _ => ((hf j).derivative j).compact)

theorem lerayPotential_contDiff {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    ContDiff ℝ ∞ (lerayPotential f) :=
  newtonConv_contDiff (isSpatialTest_divTest hf)

theorem continuous_vecField {f : Fin 3 → Space → ℝ} (hf : ∀ j, Continuous (f j)) :
    Continuous (vecField f) :=
  continuous_finsetSum _ fun j _ => (hf j).smul continuous_const

theorem hasCompactSupport_vecField {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, HasCompactSupport (f j)) : HasCompactSupport (vecField f) := by
  have he : vecField f = ∑ j : Fin 3, fun x => f j x • coordinateVector j := by
    funext x; simp [vecField]
  rw [he]
  exact HasCompactSupport.finset_sum (fun j _ => (hf j).smul_right)

theorem memLp_vecField {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j))
    (p : ℝ≥0∞) : MemLp (vecField f) p volume :=
  (continuous_vecField fun j => (hf j).continuous).memLp_of_hasCompactSupport
    (hasCompactSupport_vecField fun j => (hf j).compact)

/-- `ψ = N ∗ div φ = -Σⱼ ∫ ∂ⱼN(x - ·) φⱼ(x) dx`. -/
theorem lerayPotential_eq {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j))
    (y : Space) : lerayPotential f y = -∑ j : Fin 3, newtonPair j (f j) y := by
  have h := newtonConv_sum Finset.univ (f := fun j => spatialTestDerivative j (f j))
    (fun j => (hf j).derivative j)
  rw [lerayPotential, show divTest f = fun x => ∑ j : Fin 3, spatialTestDerivative j (f j) x
    from rfl, h]
  simp only [newtonConv_partial (hf _), Finset.sum_neg_distrib]

/-- `∂ᵢψ = N ∗ ∂ᵢ div φ = -∫ ∂ᵢN(x - ·) div φ(x) dx`. -/
theorem spatialTestDerivative_lerayPotential {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) (i : Fin 3) (y : Space) :
    spatialTestDerivative i (lerayPotential f) y = -newtonPair i (divTest f) y := by
  rw [lerayPotential, spatialTestDerivative_newtonConv (isSpatialTest_divTest hf) i,
    newtonConv_partial (isSpatialTest_divTest hf) i y]

/-- `ψ` and `∇ψ` decay like `(1 + |y|)⁻²`. -/
theorem lerayPotential_decay {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    ∃ M, (∀ y, |lerayPotential f y| ≤ M * decayWeight y) ∧
      ∀ i y, |spatialTestDerivative i (lerayPotential f) y| ≤ M * decayWeight y := by
  have h1 := fun j => newtonPair_decay j (hf j)
  choose A hA using h1
  have h2 := fun i => newtonPair_decay i (isSpatialTest_divTest hf)
  choose B hB using h2
  refine ⟨∑ j : Fin 3, |A j| + ∑ i : Fin 3, |B i|, fun y => ?_, fun i y => ?_⟩
  · have hw := decayWeight_pos y
    rw [lerayPotential_eq hf y, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hs : ∑ j : Fin 3, |newtonPair j (f j) y| ≤ ∑ j : Fin 3, |A j| * decayWeight y :=
      Finset.sum_le_sum fun j _ => (hA j y).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) hw.le)
    rw [← Finset.sum_mul] at hs
    have hB0 : 0 ≤ ∑ i : Fin 3, |B i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    nlinarith
  · have hw := decayWeight_pos y
    rw [spatialTestDerivative_lerayPotential hf i y, abs_neg]
    have hs : |B i| ≤ ∑ i : Fin 3, |B i| :=
      Finset.single_le_sum (f := fun i => |B i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hA0 : 0 ≤ ∑ j : Fin 3, |A j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have := (hB i y).trans (mul_le_mul_of_nonneg_right (le_abs_self (B i)) hw.le)
    nlinarith

/-- `∇ψ ∈ L²`. -/
theorem memLp_gradField_lerayPotential {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) : MemLp (gradField (lerayPotential f)) 2 volume := by
  obtain ⟨M, -, hM⟩ := lerayPotential_decay hf
  exact memLp_gradField (lerayPotential_contDiff hf) hM

/-- `∇ψ` is orthogonal to every solenoidal L² field. -/
theorem toL2_gradField_lerayPotential_mem_orthogonal {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) :
    toL2 (gradField (lerayPotential f)) ∈ Leray.solenoidalSubspaceᗮ := by
  obtain ⟨M, hM0, hM⟩ := lerayPotential_decay hf
  exact toL2_gradField_mem_orthogonal (lerayPotential_contDiff hf) hM0 hM

theorem spatialTestDerivative_add {a b : Space → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => a y + b y) x =
      spatialTestDerivative i a x + spatialTestDerivative i b x := by
  unfold spatialTestDerivative
  rw [fderiv_fun_add ((ha.differentiable (by simp)).differentiableAt)
    ((hb.differentiable (by simp)).differentiableAt)]
  simp

/-- `φ + ∇(N ∗ div φ)` is weakly divergence free. -/
theorem isSolenoidal_vecField_add_gradField {f : Fin 3 → Space → ℝ}
    (hf : ∀ j, IsSpatialTest (f j)) :
    IsSolenoidal (vecField f + gradField (lerayPotential f)) := by
  set ψ := lerayPotential f with hψdef
  have hψ : ContDiff ℝ ∞ ψ := lerayPotential_contDiff hf
  let g : Fin 3 → Space → ℝ := fun i x => f i x + spatialTestDerivative i ψ x
  have hg : ∀ i, ContDiff ℝ ∞ (g i) := fun i =>
    (hf i).smooth.add (contDiff_spatialTestDerivative hψ i)
  have hpt : ∀ (θ : Space → ℝ) (x : Space),
      ∑ i : Fin 3, ((vecField f + gradField ψ) x) i * spatialTestDerivative i θ x =
        ∑ i : Fin 3, g i x * spatialTestDerivative i θ x := by
    intro θ x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, PiLp.add_apply, vecField_apply, gradField_apply]
  have hint : ∀ θ, IsSpatialTest θ → ∀ i,
      Integrable (fun x => g i x * spatialTestDerivative i θ x) volume := fun θ hθ i =>
    ((hg i).continuous.mul (hθ.derivative i).continuous).integrable_of_hasCompactSupport
      (hθ.derivative i).compact.mul_left
  -- `Σᵢ ∂ᵢ gᵢ = div φ + Δψ = 0`
  have hdiv : ∀ x, ∑ i : Fin 3, spatialTestDerivative i (g i) x = 0 := by
    intro x
    have hΔ := congrFun (laplacian_newtonConv (isSpatialTest_divTest hf)) x
    have hΔ' : Heat.laplacian ψ x =
        ∑ i : Fin 3, spatialTestDerivative i (spatialTestDerivative i ψ) x := rfl
    simp only [g]
    simp_rw [spatialTestDerivative_add (hf _).smooth (contDiff_spatialTestDerivative hψ _)]
    rw [Finset.sum_add_distrib, ← hΔ', hψdef,
      show lerayPotential f = newtonConv (divTest f) from rfl, hΔ]
    simp [divTest]
  constructor
  · intro θ hθ
    simp_rw [hpt θ]
    exact integrable_finsetSum _ fun i _ => hint θ hθ i
  · intro θ hθ
    simp_rw [hpt θ]
    rw [integral_finsetSum _ fun i _ => hint θ hθ i]
    have hibp : ∀ i, ∫ x, g i x * spatialTestDerivative i θ x =
        -∫ x, spatialTestDerivative i (g i) x * θ x := fun i => by
      rw [integral_partial_mul_test (hg i) hθ i, neg_neg]
    simp_rw [hibp]
    have hsum := integral_finsetSum (μ := volume) Finset.univ
      (f := fun i x => spatialTestDerivative i (g i) x * θ x) (fun i _ =>
        ((contDiff_spatialTestDerivative (hg i) i).continuous.mul hθ.continuous
          ).integrable_of_hasCompactSupport hθ.compact.mul_left)
    rw [Finset.sum_neg_distrib, ← hsum]
    simp_rw [← Finset.sum_mul, hdiv, zero_mul, integral_zero, neg_zero]

theorem toL2_add' {a b : SpatialField} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    toL2 (a + b) = toL2 a + toL2 b := by
  rw [toL2_of_memLp (ha.add hb), toL2_of_memLp ha, toL2_of_memLp hb]
  exact MemLp.toLp_add ha hb

/-- **Leray projection of a test field.** For a compact smooth vector test `φ = Σⱼ fⱼ eⱼ`,
`𝔓φ = φ + ∇(N ∗ div φ)` (INF01 §4.2, decision D5). -/
theorem projection_toL2_vecField {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    Leray.projection (toL2 (vecField f)) =
      toL2 (vecField f + gradField (lerayPotential f)) := by
  have hφ := memLp_vecField hf 2
  have hW := memLp_gradField_lerayPotential hf
  apply Leray.projection_eq_of_orthogonal
  · exact Leray.solenoidal_congr_ae (isSolenoidal_vecField_add_gradField hf)
      (coeFn_toL2 (hφ.add hW)).symm
  · rw [toL2_add' hφ hW, sub_add_cancel_left]
    exact Submodule.neg_mem _ (toL2_gradField_lerayPotential_mem_orthogonal hf)

/-- `(I - 𝔓)φ = -∇(N ∗ div φ)` for a compact smooth vector test. -/
theorem toL2_sub_projection_vecField {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) :
    toL2 (vecField f) - Leray.projection (toL2 (vecField f)) =
      -toL2 (gradField (lerayPotential f)) := by
  rw [projection_toL2_vecField hf, toL2_add' (memLp_vecField hf 2)
    (memLp_gradField_lerayPotential hf), sub_add_cancel_left]

end UnforcedLeray.RieszLp
