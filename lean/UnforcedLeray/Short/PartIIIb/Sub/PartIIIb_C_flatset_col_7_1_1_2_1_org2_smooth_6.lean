import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# `ParamIntegralSmooth` from two joint-continuity facts (decomposition of
`PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/6`)

Generic calculus (no source).  Differentiation under the integral sign is
`UnforcedLeray.L09.contDiffOn_integral` with `μ = volume.restrict (Ioc 0 S)`.  Its hypotheses
(measurability and local domination of all `y`-derivatives of the integrand
`F τ y = ρ(y.1,τ) * H τ y`) follow from joint continuity of `(τ,y) ↦ iteratedFDeriv n (F τ) y`
on `[0,S] × U`, which is obtained from
* `ProdJointCont` (Leibniz: joint continuity of derivatives of a product), and
* `ShiftJointCont` (the `y`-derivatives of `y ↦ ρ(y.1,τ)` are jointly continuous).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Leibniz, joint continuity.**  If all `y`-derivatives of two families `A τ`, `B τ`
(smooth on the open `U`) are jointly continuous in `(τ,y)` on `S × U`, so are those of the
pointwise product.  (Induct on the order `n`, using `iteratedFDeriv_succ_eq_comp_right`, or
`norm`-free Leibniz by `ContinuousLinearMap.iteratedFDeriv_comp_left`/bilinear maps.) -/
def ProdJointCont : Prop :=
  ∀ (A B : ℝ → ℝ × (ℝ × ℝ) → ℂ) (S : Set ℝ) (U : Set (ℝ × (ℝ × ℝ))), IsOpen U →
    (∀ i : ℕ, ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ i (A q.1) q.2)
      (S ×ˢ U)) →
    (∀ i : ℕ, ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ i (B q.1) q.2)
      (S ×ˢ U)) →
    (∀ τ ∈ S, ContDiffOn ℝ ∞ (A τ) U) → (∀ τ ∈ S, ContDiffOn ℝ ∞ (B τ) U) →
    ∀ n : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ n (fun y => A q.1 y * B q.1 y) q.2)
      (S ×ˢ U)

/-- **Shift, joint continuity.**  For `ρ` smooth on `Ioi 0 × ℝ`, all `y`-derivatives of
`y ↦ ρ(y.1,τ)` are jointly continuous in `(τ,y)` on `univ × (Ioi 0 × univ)`
(the map `(τ,y) ↦ (y.1,τ)` is linear). -/
def ShiftJointCont : Prop :=
  ∀ (ρ : ℝ × ℝ → ℂ), ContDiffOn ℝ ∞ ρ (Ioi (0 : ℝ) ×ˢ univ) → ∀ n : ℕ,
    ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
      iteratedFDeriv ℝ n (fun y : ℝ × (ℝ × ℝ) => ρ (y.1, q.1)) q.2)
      (univ ×ˢ (Ioi (0 : ℝ) ×ˢ univ))

theorem paramIntegralSmooth_of (hP : ProdJointCont) (hS : ShiftJointCont) :
    ParamIntegralSmooth := by
  intro S ρ H hρ hHs _hHb hHc
  set U : Set (ℝ × (ℝ × ℝ)) := Ioo (0 : ℝ) S ×ˢ univ with hU
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hUsub : U ⊆ Ioi (0 : ℝ) ×ˢ univ := fun y hy => ⟨hy.1.1, trivial⟩
  set A : ℝ → ℝ × (ℝ × ℝ) → ℂ := fun τ y => ρ (y.1, τ) with hA
  set B : ℝ → ℝ × (ℝ × ℝ) → ℂ := H with hB
  -- smoothness of the shifted `ρ` on `U`
  have hAs : ∀ τ : ℝ, ContDiffOn ℝ ∞ (A τ) U := by
    intro τ
    have h1 : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => (y.1, τ)) U :=
      (contDiff_fst.prodMk contDiff_const).contDiffOn
    refine hρ.comp h1 ?_
    intro y hy
    exact ⟨hy.1.1, trivial⟩
  have hAc : ∀ i : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ i (A q.1) q.2) (Ici (0 : ℝ) ×ˢ U) :=
    fun i => (hS ρ hρ i).mono (fun q hq => ⟨trivial, hUsub hq.2⟩)
  have hBc : ∀ i : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ i (B q.1) q.2) (Ici (0 : ℝ) ×ˢ U) :=
    fun i => (hHc i).mono (fun q hq => ⟨hq.1, trivial⟩)
  have hFc : ∀ n : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × (ℝ × ℝ)) =>
        iteratedFDeriv ℝ n (fun y => A q.1 y * B q.1 y) q.2) (Ici (0 : ℝ) ×ˢ U) :=
    hP A B (Ici 0) U hUo hAc hBc (fun τ _ => hAs τ) (fun τ hτ => (hHs τ hτ).contDiffOn)
  -- differentiate under the integral sign
  have key : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => ∫ τ in Ioc (0 : ℝ) S, A τ y * B τ y) U := by
    refine UnforcedLeray.L09.contDiffOn_integral (μ := volume.restrict (Ioc (0 : ℝ) S))
      (F := fun τ y => A τ y * B τ y) hUo ?_ ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
      exact (hAs τ).mul (hHs τ hτ.1.le).contDiffOn
    · intro n x hx
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      have h := (hFc n).comp (f := fun τ : ℝ => (τ, x)) (continuousOn_id.prodMk continuousOn_const)
        (s := Ioc (0 : ℝ) S) (fun τ hτ => ⟨le_of_lt hτ.1, hx⟩)
      exact h
    · intro n x hx
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo x hx
      have hcpt : IsCompact (Icc (0 : ℝ) S ×ˢ Metric.closedBall x (r / 2)) :=
        isCompact_Icc.prod (isCompact_closedBall _ _)
      have hsub : Icc (0 : ℝ) S ×ˢ Metric.closedBall x (r / 2) ⊆ Ici (0 : ℝ) ×ˢ U := by
        rintro ⟨τ, y⟩ ⟨hτ, hy⟩
        refine ⟨hτ.1, hball ?_⟩
        rw [Metric.mem_ball]
        have := Metric.mem_closedBall.1 hy
        linarith
      obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn ((hFc n).mono hsub)
      refine ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (by linarith),
        fun _ => C, integrable_const _, ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ y hy => ?_)
      exact hC (τ, y) ⟨⟨hτ.1.le, hτ.2⟩, hy⟩
  refine key.congr ?_
  intro y hy
  simp only [A, B]
  rw [intervalIntegral.integral_of_le (hy.1.1.trans hy.1.2).le]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
