import UnforcedLeray.Short.PartI.Sub.PartI_S18

/-!
# `PartI:S18/1` decomposed: `dilX0_strongCont`

Source `the November 2 reference manuscript`
lines 946-953.  Strong continuity of `a ↦ J_a f` on `X0` by the `ε/3` argument:
the local operator bound `‖J_a‖ ≤ dilConst M a` (`Planar.norm_dilW_le`, continuous in `a > 0`),
density of compactly supported continuous functions in `L2w M` (leaf `L2wCcDense`), and
dominated convergence for those functions (leaf `DilWCcCont`).

Proved here: `dilX0_strongCont_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace UnforcedLeray.Short.PartI

/-- `G ∈ L²_M` has a continuous compactly supported representative. -/
def IsCcRep {M : ℝ} (G : Planar.L2w M) : Prop :=
  ∃ g : ℂ → ℂ, Continuous g ∧ HasCompactSupport g ∧ ⇑G =ᵐ[Planar.wMeasure M] g

/-- **Leaf A** (source 946-953): continuous compactly supported functions are dense in `L²_M`
(Mathlib `Lp` density for the weighted measure `wMeasure M`, which is finite on compacts and
regular as a density measure on `ℂ`). -/
def L2wCcDense : Prop :=
  ∀ (M : ℝ) (_ : 1 < M) (F : Planar.L2w M) (ε : ℝ), 0 < ε →
    ∃ G : Planar.L2w M, IsCcRep G ∧ ‖G - F‖ < ε

/-- **Leaf B** (source 946-953): for a continuous compactly supported `G`, `a ↦ J_a G` is
continuous at every `a₀ > 0` (dominated convergence for `dilWFun`: the integrand
`a⁻⁴ |g(y/√a)|² w(y)` is dominated on `a` near `a₀` by a constant times the indicator of a
large ball). -/
def DilWCcCont : Prop :=
  ∀ (M : ℝ) (hM : 1 < M) (G : Planar.L2w M), IsCcRep G → ∀ (a₀ : ℝ) (ha₀ : 0 < a₀),
    Tendsto (fun a : Set.Ioi (0 : ℝ) => Planar.dilW hM a.2 G) (𝓝 ⟨a₀, ha₀⟩)
      (𝓝 (Planar.dilW hM ha₀ G))

theorem dilConst_continuousAt (M a₀ : ℝ) (ha₀ : 0 < a₀) :
    ContinuousAt (Planar.dilConst M) a₀ := by
  unfold Planar.dilConst
  have h1 : ContinuousAt (fun a : ℝ => max 1 a) a₀ := by fun_prop
  have h2 : ContinuousAt (fun a : ℝ => max 1 a ^ M) a₀ :=
    h1.rpow_const (Or.inl (lt_max_of_lt_left one_pos).ne')
  have h3 : ContinuousAt (fun a : ℝ => (a ^ 3)⁻¹) a₀ :=
    (continuousAt_id.pow 3).inv₀ (pow_pos ha₀ 3).ne'
  exact (h3.mul h2).sqrt

theorem dilX0_strongCont_of (h1 : L2wCcDense) (h2 : DilWCcCont) : DilX0StrongCont := by
  intro M hM f
  rw [continuous_iff_continuousAt]
  intro a₁
  obtain ⟨a₀, ha₀⟩ := a₁
  have hcc : ContinuousAt (fun a : Set.Ioi (0 : ℝ) => Planar.dilConst M a.1) ⟨a₀, ha₀⟩ :=
    ContinuousAt.comp (f := fun a : Set.Ioi (0 : ℝ) => a.1) (x := ⟨a₀, ha₀⟩)
      (dilConst_continuousAt M a₀ ha₀) continuous_subtype_val.continuousAt
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := Planar.dilConst M a₀ + 1 with hC
  have hC0 : 0 < C := by
    have := Planar.dilConst_nonneg M a₀
    rw [hC]; linarith
  have hev1 : ∀ᶠ a : Set.Ioi (0 : ℝ) in 𝓝 ⟨a₀, ha₀⟩, Planar.dilConst M a.1 < C :=
    hcc.eventually (gt_mem_nhds (by rw [hC]; linarith))
  have hδ : 0 < ε / (4 * C) := by positivity
  obtain ⟨G, hG, hGF⟩ := h1 M hM (f : Planar.L2w M) (ε / (4 * C)) hδ
  have hev2 := (Metric.tendsto_nhds.1 (h2 M hM G hG a₀ ha₀)) (ε / 2) (by positivity)
  filter_upwards [hev1, hev2] with a ha1 ha2
  have hJ0 : ‖Planar.dilW hM ha₀‖ ≤ Planar.dilConst M a₀ := Planar.norm_dilW_le hM ha₀
  have hJa : ‖Planar.dilW hM a.2‖ ≤ Planar.dilConst M a.1 := Planar.norm_dilW_le hM a.2
  have hFG : ‖(f : Planar.L2w M) - G‖ < ε / (4 * C) := by rw [norm_sub_rev]; exact hGF
  have hN : 0 ≤ ‖(f : Planar.L2w M) - G‖ := norm_nonneg _
  have e1 : ‖Planar.dilW hM a.2 ((f : Planar.L2w M) - G)‖ ≤ C * ‖(f : Planar.L2w M) - G‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJa.trans ha1.le) hN)
  have e2 : ‖Planar.dilW hM ha₀ ((f : Planar.L2w M) - G)‖ ≤ C * ‖(f : Planar.L2w M) - G‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJ0.trans (by rw [hC]; linarith)) hN)
  have e3 : C * ‖(f : Planar.L2w M) - G‖ < ε / 4 := by
    calc C * ‖(f : Planar.L2w M) - G‖ < C * (ε / (4 * C)) := mul_lt_mul_of_pos_left hFG hC0
      _ = ε / 4 := by field_simp
  rw [dist_eq_norm] at ha2
  have key : ((Planar.dilX0 hM a.2 f : Planar.X0 hM) : Planar.L2w M) -
        ((Planar.dilX0 hM ha₀ f : Planar.X0 hM) : Planar.L2w M) =
      Planar.dilW hM a.2 ((f : Planar.L2w M) - G) + (Planar.dilW hM a.2 G - Planar.dilW hM ha₀ G)
        - Planar.dilW hM ha₀ ((f : Planar.L2w M) - G) := by
    simp only [Planar.coe_dilX0_apply, map_sub]; abel
  rw [dist_eq_norm]
  show ‖((Planar.dilX0 hM a.2 f : Planar.X0 hM) : Planar.L2w M) -
        ((Planar.dilX0 hM ha₀ f : Planar.X0 hM) : Planar.L2w M)‖ < ε
  rw [key]
  calc _ ≤ ‖Planar.dilW hM a.2 ((f : Planar.L2w M) - G) +
        (Planar.dilW hM a.2 G - Planar.dilW hM ha₀ G)‖ +
        ‖Planar.dilW hM ha₀ ((f : Planar.L2w M) - G)‖ := norm_sub_le _ _
    _ ≤ ‖Planar.dilW hM a.2 ((f : Planar.L2w M) - G)‖ +
        ‖Planar.dilW hM a.2 G - Planar.dilW hM ha₀ G‖ +
        ‖Planar.dilW hM ha₀ ((f : Planar.L2w M) - G)‖ := by gcongr; exact norm_add_le _ _
    _ < ε := by linarith

end UnforcedLeray.Short.PartI
