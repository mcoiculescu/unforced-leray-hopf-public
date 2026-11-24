import UnforcedLeray.Short.PartIIb.Sub.T12_1_1_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.LerayOfRiesz.PlaneRieszGL2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.LerayOfRiesz.PlaneRieszGLr
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.LerayOfRiesz.PlaneRieszGDiv

/-!
# Part II-b, task `PartII-b:T12/1/1/3` (`PlaneLerayOfRiesz`): the unconditional target

Source: `the November 2 reference manuscript` lines 1670, 1923-1926 (Grafakos,
*Classical Fourier Analysis*, Cor. 5.2.8).  The four leaves are `PlaneRieszGL2`, `PlaneRieszGLr`,
`PlaneRieszGDiv` (imported) and `PlaneRieszGOrth`.  The leaf `PlaneRieszGOrth.lean` and
`PlaneRieszGDiv.lean` both declare the helper family `rieszOrth_*` in the same namespace, so they
cannot be imported together.  The `PlaneRieszGOrth` proof is therefore reproduced below with its
helpers renamed `rieszOrthB_*` (text identical otherwise).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb


/-- The `k`-th component of `F` transported, as an element of `L²(Fin 2 → ℝ)`. -/
def rieszOrthB_f {F : ℝ × ℝ → RMerid} (hF : MemLp F 2 volume) : Fin 2 → PlaneL2 :=
  fun k => (planeComp_memLp hF k).toLp _

theorem rieszOrthB_f_ae {F : ℝ × ℝ → RMerid} (hF : MemLp F 2 volume) (k : Fin 2) :
    (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) =ᵐ[volume] planeComp F k :=
  (planeComp_memLp hF k).coeFn_toLp

/-- The `i`-th component of a planar test field, transported to `Fin 2 → ℝ`. -/
def rieszOrthB_test (Ψ : ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2) : (Fin 2 → ℝ) → ℝ :=
  fun x => Ψ (MeasurableEquiv.finTwoArrow x) i

/-- The linear change of variables `Fin 2 → ℝ ≃ ℝ × ℝ`. -/
def rieszOrthB_L : (Fin 2 → ℝ) ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

theorem rieszOrthB_L_apply (x : Fin 2 → ℝ) : rieszOrthB_L x = MeasurableEquiv.finTwoArrow x := rfl

theorem rieszOrthB_test_smooth {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (i : Fin 2) :
    ContDiff ℝ ∞ (rieszOrthB_test Ψ i) :=
  (hΨ.comp i).smooth.comp rieszOrthB_L.contDiff

theorem rieszOrthB_test_compact {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (i : Fin 2) :
    HasCompactSupport (rieszOrthB_test Ψ i) :=
  (hΨ.comp i).compact.comp_homeomorph rieszOrthB_L.toHomeomorph

theorem rieszOrthB_test_memLp {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (i : Fin 2) :
    MemLp (rieszOrthB_test Ψ i) 2 volume :=
  (rieszOrthB_test_smooth hΨ i).continuous.memLp_of_hasCompactSupport (rieszOrthB_test_compact hΨ i)

/-- Chain rule for the linear change of variables. -/
theorem rieszOrthB_fderiv (g : ℝ × ℝ → ℝ) (hg : Differentiable ℝ g) (x v : Fin 2 → ℝ) :
    fderiv ℝ (fun y => g (rieszOrthB_L y)) x v = fderiv ℝ g (rieszOrthB_L x) (rieszOrthB_L v) := by
  have h1 : HasFDerivAt (fun y => g (rieszOrthB_L y))
      ((fderiv ℝ g (rieszOrthB_L x)).comp rieszOrthB_L.toContinuousLinearMap) x :=
    (hg (rieszOrthB_L x)).hasFDerivAt.comp x rieszOrthB_L.toContinuousLinearMap.hasFDerivAt
  rw [h1.fderiv]
  rfl

theorem rieszOrthB_L_single0 : rieszOrthB_L (Pi.single 0 1) = (1, 0) := by
  ext <;> simp [rieszOrthB_L, Pi.single_apply]

theorem rieszOrthB_L_single1 : rieszOrthB_L (Pi.single 1 1) = (0, 1) := by
  ext <;> simp [rieszOrthB_L, Pi.single_apply]

/-- A planar solenoidal test has transported divergence zero. -/
theorem rieszOrthB_div {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (x : Fin 2 → ℝ) :
    ∑ i : Fin 2, fderiv ℝ (rieszOrthB_test Ψ i) x (Pi.single i 1) = 0 := by
  have hdiff : ∀ j : Fin 2, Differentiable ℝ (fun z => Ψ z j) := fun j =>
    (hΨ.comp j).smooth.differentiable (by simp)
  have hd := hΨ.div_free (rieszOrthB_L x)
  rw [Fin.sum_univ_two]
  have e0 : rieszOrthB_test Ψ 0 = fun y => (fun z => Ψ z 0) (rieszOrthB_L y) := rfl
  have e1 : rieszOrthB_test Ψ 1 = fun y => (fun z => Ψ z 1) (rieszOrthB_L y) := rfl
  rw [e0, e1, rieszOrthB_fderiv _ (hdiff 0) x (Pi.single 0 1),
    rieszOrthB_fderiv _ (hdiff 1) x (Pi.single 1 1), rieszOrthB_L_single0, rieszOrthB_L_single1]
  exact hd

theorem rieszOrthB_G_eq (S : Fin 2 → Fin 2 → (PlaneL2 →L[ℝ] PlaneL2)) {F : ℝ × ℝ → RMerid}
    (hF : MemLp F 2 volume) :
    planeRieszG S F = fun z => WithLp.toLp 2 (fun i =>
      ((rieszOrthB_f hF i - ∑ k, S i k (rieszOrthB_f hF k) : PlaneL2) :
        (Fin 2 → ℝ) → ℝ) (MeasurableEquiv.finTwoArrow.symm z)) := by
  rw [planeRieszG, dif_pos hF]
  rfl

/-- **Leaf `PartII-b:T12/1/1/3/4`**: `F - G` is orthogonal to compactly supported smooth solenoidal
fields. -/
theorem planeRieszGOrth : PlaneRieszGOrth := by
  intro S B hS F hF Ψ hΨ
  have hΨm : ∀ i : Fin 2, MemLp (rieszOrthB_test Ψ i) 2 volume := fun i => rieszOrthB_test_memLp hΨ i
  -- the solenoidal identity of the family
  have hW : ∀ k : Fin 2, ∑ i, S k i ((hΨm i).toLp _) = 0 := by
    intro k
    exact hS.2.2.2.2 (rieszOrthB_test Ψ) (fun i => ⟨rieszOrthB_test_smooth hΨ i, rieszOrthB_test_compact hΨ i⟩)
      (rieszOrthB_div hΨ) hΨm k
  -- pointwise identity `F_i - G_i = Σ_k S_{ik} f_k` a.e. on the transported plane
  have hae : ∀ i : Fin 2, ∀ᵐ x ∂volume, planeComp F i x -
      (rieszOrthB_f hF i - ∑ k, S i k (rieszOrthB_f hF k) : PlaneL2) x = ∑ k, S i k (rieszOrthB_f hF k) x := by
    intro i
    filter_upwards [rieszOrthB_f_ae hF i, Lp.coeFn_sub (rieszOrthB_f hF i) (∑ k, S i k (rieszOrthB_f hF k)),
      Lp.coeFn_fun_finsetSum Finset.univ (fun k => S i k (rieszOrthB_f hF k))] with x h1 h2 h3
    rw [h2, Pi.sub_apply, h3, h1]
    ring
  have hall := ae_all_iff.2 hae
  have hΦe : ∀ x : Fin 2 → ℝ, (∑ i : Fin 2, (F (MeasurableEquiv.finTwoArrow x) i -
      planeRieszG S F (MeasurableEquiv.finTwoArrow x) i) * Ψ (MeasurableEquiv.finTwoArrow x) i) =
      ∑ i : Fin 2, (planeComp F i x - (rieszOrthB_f hF i - ∑ k, S i k (rieszOrthB_f hF k) : PlaneL2) x) *
        rieszOrthB_test Ψ i x := by
    intro x
    rw [rieszOrthB_G_eq S hF]
    simp only [MeasurableEquiv.symm_apply_apply, rieszOrthB_test, planeComp, PiLp.toLp_apply]
  have hQ2 : ∀ᵐ x ∂volume, (∑ i : Fin 2, (F (MeasurableEquiv.finTwoArrow x) i -
      planeRieszG S F (MeasurableEquiv.finTwoArrow x) i) * Ψ (MeasurableEquiv.finTwoArrow x) i) =
      ∑ i : Fin 2, ∑ k : Fin 2, (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x * rieszOrthB_test Ψ i x := by
    filter_upwards [hall] with x hx
    rw [hΦe x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i, Finset.sum_mul]
  -- integrability of each transported product
  have hterm : ∀ i k : Fin 2, Integrable (fun x => (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x *
      rieszOrthB_test Ψ i x) volume :=
    fun i k => (Lp.memLp (S i k (rieszOrthB_f hF k))).integrable_mul (hΨm i)
  have hA : ∀ i k : Fin 2, ∫ x, (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x * rieszOrthB_test Ψ i x =
      ∫ x, (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) x * (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x := by
    intro i k
    have h1 : (fun x => (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x * rieszOrthB_test Ψ i x) =ᵐ[volume]
        (fun x => (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x * ((hΨm i).toLp _ : (Fin 2 → ℝ) → ℝ) x) := by
      filter_upwards [(hΨm i).coeFn_toLp] with x hx
      rw [hx]
    rw [integral_congr_ae h1]
    exact hS.2.1 i k _ _
  have hB : ∀ k : Fin 2, ∑ i, ∫ x, (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) x *
      (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x = 0 := by
    intro k
    have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i => S k i ((hΨm i).toLp _))
    rw [hW k] at hsum
    have hz : ∀ᵐ x ∂volume, ∑ i, (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x = 0 := by
      filter_upwards [hsum, Lp.coeFn_zero ℝ 2 volume] with x h1 h2
      rw [← h1]
      simp
    have hint_k : ∀ i : Fin 2, Integrable (fun x => (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) x *
        (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x) volume :=
      fun i => (Lp.memLp (rieszOrthB_f hF k)).integrable_mul (Lp.memLp (S k i ((hΨm i).toLp _)))
    rw [← integral_finset_sum Finset.univ (fun i _ => hint_k i)]
    have hz' : (fun x => ∑ i, (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) x *
        (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hz] with x hx
      rw [← Finset.mul_sum, hx, mul_zero]
    rw [integral_congr_ae hz']
    simp
  -- the transported integrand
  have hI : ∫ x, ∑ i : Fin 2, ∑ k : Fin 2, (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x *
      rieszOrthB_test Ψ i x = 0 := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ => hterm i k)]
    calc ∑ i : Fin 2, ∫ x, ∑ k : Fin 2, (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x *
          rieszOrthB_test Ψ i x
        = ∑ i : Fin 2, ∑ k : Fin 2, ∫ x, (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x *
          rieszOrthB_test Ψ i x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum _ fun k _ => hterm i k]
      _ = ∑ i : Fin 2, ∑ k : Fin 2, ∫ x, (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) x *
          (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hA i k
      _ = ∑ k : Fin 2, ∑ i : Fin 2, ∫ x, (rieszOrthB_f hF k : (Fin 2 → ℝ) → ℝ) x *
          (S k i ((hΨm i).toLp _) : (Fin 2 → ℝ) → ℝ) x := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun k _ => hB k
  -- transport back to `ℝ²`
  have hmp := volume_preserving_finTwoArrow ℝ
  have hint_Q : Integrable (fun x => ∑ i : Fin 2, ∑ k : Fin 2, (S i k (rieszOrthB_f hF k) : (Fin 2 → ℝ) → ℝ) x *
      rieszOrthB_test Ψ i x) volume :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ => hterm i k
  have hint_Φe : Integrable (fun x => ∑ i : Fin 2, (F (MeasurableEquiv.finTwoArrow x) i -
      planeRieszG S F (MeasurableEquiv.finTwoArrow x) i) * Ψ (MeasurableEquiv.finTwoArrow x) i) volume :=
    hint_Q.congr (hQ2.mono fun x hx => hx.symm)
  refine ⟨?_, ?_⟩
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (g := fun z : ℝ × ℝ => ∑ i : Fin 2, (F z i - planeRieszG S F z i) * Ψ z i)).1 hint_Φe
  · have key := hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z : ℝ × ℝ => ∑ i : Fin 2, (F z i - planeRieszG S F z i) * Ψ z i)
    simp only at key
    rw [← key, integral_congr_ae hQ2, hI]


/-- The planar Leray projection from Riesz operators (leaf `T12/1/1/3`, all four leaves). -/
theorem planeLerayOfRiesz : UnforcedLeray.Short.IIb.PlaneLerayOfRiesz :=
  planeLerayOfRiesz_of planeRieszGL2 planeRieszGLr planeRieszGDiv planeRieszGOrth

end UnforcedLeray.Short.IIb
