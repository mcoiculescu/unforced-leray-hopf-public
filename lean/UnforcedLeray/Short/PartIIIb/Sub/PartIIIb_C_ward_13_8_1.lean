import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Pw6

/-!
# `BgDmuL2Sol` from the `L²` membership of `D₀U` (task `PartIII-b:C/ward/13/8/1`)

Source of record: `the November 2 reference manuscript` (73 pages).
Source 2612-2635: `Q = U - H_a ∈ C_per H²`, `(∂_τ - y·∇/2)Q ∈ C_per L²`, `D₀H_a = 0`, so
`D₀U = D₀Q ∈ L²`.  This analytic fact is isolated as `BgDmuMemL2`.  Solenoidality of `D₀U`
is then proved here: `U` is smooth with `div U = 0` pointwise (`IsExactProfile`), `D₀` preserves
pointwise divergence-freeness (`pwDmuDivFree_proved`), and a `C¹` pointwise divergence-free field
is weakly solenoidal (integration by parts against a compactly supported test function), so the
Leray projection fixes it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`D₀U ∈ C_per L²` at the ball levels** (source 2612-2635: `D₀U = D₀Q` with `Q ∈ C_per H²`,
`(∂_τ - y·∇/2)Q ∈ C_per L²`, `D₀H_a = 0`).  Analytic input not yet in Lean. -/
def BgDmuMemL2 : Prop :=
  AtBallLevels fun p V rb _ => ∀ τ : ℝ,
    MemLp (physDmu p.ν 0 (fun t y => V t y + rb t y) τ) 2 volume

/-- Derivatives of a smooth field are smooth (as a map into `Space`). -/
theorem contDiff_pd' {h : Space → Space} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (v : Space) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

/-- Derivatives of a smooth field are smooth. -/
theorem contDiff_pd {h : Space → Space} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (v : Space) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

/-- `D_μ X` is smooth for a jointly smooth `X`. -/
theorem contDiff_physDmu (ν μ : ℝ) (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physDmu ν μ X τ) := by
  have hXt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (X τ) :=
    hX.comp (contDiff_const.prodMk contDiff_id)
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => deriv (fun t => X t y) τ) := by
    have : (fun y => deriv (fun t => X t y) τ) =
        fun y => fderiv ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, y) (1, 0) := by
      funext y
      have hd : DifferentiableAt ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, y) :=
        hX.differentiable (by simp) _
      have hs : HasFDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) (ContinuousLinearMap.inl ℝ ℝ Space) τ :=
        hasFDerivAt_prodMk_left τ y
      have := hd.hasFDerivAt.comp τ hs
      rw [show (fun t => X t y) = (fun x : ℝ × Space => X x.1 x.2) ∘ (fun t : ℝ => ((t, y) : ℝ × Space)) from rfl,
        this.hasDerivAt.deriv]
      simp
    rw [this]
    exact (hX.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
      |>.comp (contDiff_const.prodMk contDiff_id)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ (X τ) y y) :=
    (hXt.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_id
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (physLap (X τ)) := by
    unfold physLap physPd2 physPd
    refine ContDiff.sum fun j _ => ?_
    exact contDiff_pd (contDiff_pd' hXt _) _
  unfold physDmu
  exact ((h1.sub (h2.const_smul (1 / 2 : ℝ))).sub (h3.const_smul ν)).add (hXt.const_smul (μ - 1 / 2))

/-- A `C¹` field with pointwise vanishing divergence is weakly solenoidal. -/
theorem isSolenoidal_of_pointwise {f : Space → Space} (hf : ContDiff ℝ 1 f)
    (hdiv : ∀ y, ∑ j : Fin 3, physPd f j y j = 0) : UnforcedLeray.IsSolenoidal f := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg : ∀ j : Fin 3, ContDiff ℝ 1 (fun y => f y j) := fun j =>
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ)).contDiff.comp hf
  have hgd : ∀ j : Fin 3, Differentiable ℝ (fun y => f y j) := fun j =>
    (hg j).differentiable (by norm_num)
  have hcomp : ∀ (j : Fin 3) (y v : Space), fderiv ℝ (fun y' => f y' j) y v = fderiv ℝ f y v j := by
    intro j y v
    have hl : HasFDerivAt (fun y' => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (f y'))
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ f y)) y :=
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hfd y).hasFDerivAt
    have : (fun y' => f y' j) = fun y' => (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (f y') := rfl
    rw [this, hl.fderiv]; rfl
  have hgc : ∀ j : Fin 3, Continuous (fun y => f y j) := fun j => (hgd j).continuous
  have hgfc : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ (fun y' => f y' j) y) :=
    fun j => (hg j).continuous_fderiv (by norm_num)
  have hgvcont : ∀ j : Fin 3,
      Continuous (fun y => fderiv ℝ (fun y' => f y' j) y (coordinateVector j)) :=
    fun j => (hgfc j).clm_apply continuous_const
  have hzero : ∀ y, ∑ j : Fin 3, fderiv ℝ (fun y' => f y' j) y (coordinateVector j) = 0 := by
    intro y
    refine (Finset.sum_congr rfl fun j _ => hcomp j y _).trans (hdiv y)
  have key : ∀ φ, UnforcedLeray.IsSpatialTest φ →
      (∀ j : Fin 3, Integrable (fun y => f y j * UnforcedLeray.spatialTestDerivative j φ y)) ∧
      (∀ j : Fin 3, Integrable (fun y => φ y * fderiv ℝ (fun y' => f y' j) y (coordinateVector j))) ∧
      (∀ j : Fin 3, ∫ y, f y j * UnforcedLeray.spatialTestDerivative j φ y =
        -∫ y, φ y * fderiv ℝ (fun y' => f y' j) y (coordinateVector j)) := by
    intro φ hφ
    have hψc : HasCompactSupport φ := hφ.compact
    have hψd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hψcont : Continuous φ := hψd.continuous
    have hψfc : Continuous (fun y => fderiv ℝ φ y) := hφ.smooth.continuous_fderiv (by simp)
    have hψvc : ∀ v : Space, HasCompactSupport (fun y => fderiv ℝ φ y v) :=
      fun v => hψc.fderiv_apply ℝ v
    have hψvcont : ∀ v : Space, Continuous (fun y => fderiv ℝ φ y v) :=
      fun v => hψfc.clm_apply continuous_const
    have int1 : ∀ j : Fin 3, Integrable (fun y => φ y * f y j) := fun j =>
      Continuous.integrable_of_hasCompactSupport (hψcont.mul (hgc j)) hψc.mul_right
    have int2 : ∀ j : Fin 3, Integrable (fun y => φ y *
        fderiv ℝ (fun y' => f y' j) y (coordinateVector j)) := fun j =>
      Continuous.integrable_of_hasCompactSupport (hψcont.mul (hgvcont j)) hψc.mul_right
    have int3 : ∀ j : Fin 3, Integrable (fun y =>
        fderiv ℝ φ y (coordinateVector j) * f y j) := fun j =>
      Continuous.integrable_of_hasCompactSupport ((hψvcont _).mul (hgc j))
        (hψvc _).mul_right
    refine ⟨fun j => ?_, int2, fun j => ?_⟩
    · unfold UnforcedLeray.spatialTestDerivative
      simpa [mul_comm] using int3 j
    · have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (int3 j) (int2 j) (int1 j) (fun y _ => hψd y) (fun y _ => hgd j y)
      unfold UnforcedLeray.spatialTestDerivative
      simp only [mul_comm (f _ j)]
      rw [neg_eq_iff_eq_neg.mp h.symm]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨k1, -, -⟩ := key φ hφ
    exact integrable_finsetSum _ (fun j _ => k1 j)
  · obtain ⟨k1, k2, k3⟩ := key φ hφ
    rw [integral_finsetSum _ (fun j _ => k1 j)]
    simp only [k3]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => k2 j)]
    have : ∀ y, ∑ j : Fin 3, φ y * fderiv ℝ (fun y' => f y' j) y (coordinateVector j) = 0 := by
      intro y
      rw [← Finset.mul_sum, hzero y, mul_zero]
    simp [this]

/-- **`BgDmuL2Sol` from the `L²` membership of `D₀U`.** -/
theorem bgDmuL2Sol_of (h : BgDmuMemL2) : BgDmuL2Sol := by
  refine AtBallLevels.mono' h ?_
  intro p V rb pres hU hL τ
  refine ⟨hL τ, ?_⟩
  refine UnforcedLeray.Leray.projection_toL2_eq_self (hL τ) ?_
  have hD := pwDmuDivFree_proved p.ν 0 (fun t y => V t y + rb t y) hU.smoothU hU.div_free τ
  have hsm : ContDiff ℝ 1 (physDmu p.ν 0 (fun t y => V t y + rb t y) τ) :=
    (contDiff_physDmu p.ν 0 _ hU.smoothU τ).of_le (by exact_mod_cast le_top)
  exact isSolenoidal_of_pointwise hsm hD

end UnforcedLeray.Short.PartIIIb.Concrete
