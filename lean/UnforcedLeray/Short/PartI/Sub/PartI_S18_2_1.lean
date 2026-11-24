import UnforcedLeray.Short.PartI.Sub.PartI_S18_2
import UnforcedLeray.Short.PartI.Sub.PartI_S18_1

/-!
# `PartI:S18/2` decomposed: `dilX0_adjStrongCont_of`

Source `the November 2 reference manuscript`
lines 946-953 ("their dilates are norm continuous by dominated convergence").

Route B.  (1) On `X0` the adjoint of `J_a` is controlled by the `L²_M`-adjoint of `dilW`:
for `v, v' ∈ X0`, `‖(J_a|X0)^* v - (J_b|X0)^* v'‖ ≤ ‖J_a^* v - J_b^* v'‖` (test against the `X0`
difference and use `dilW_mem_X0`); proved here.  (2) The `L²_M` adjoint family is strongly
continuous by the `ε/3` argument from `L2wCcDense` and the leaf `DilWAdjCcCont` (dominated
convergence for `C_c` data); proved here.  Only `DilWAdjCcCont` remains.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

/-- **Leaf** (source 946-953): for a continuous compactly supported `G`, `a ↦ (J_a)^* G` is
continuous at every `a₀ > 0` in `L²_M` (Hilbert adjoint of `Planar.dilW`).  Explicitly
`(J_a)^* G (z) = a⁻¹ (ρ(√a z)/ρ(z)) G(√a z)` a.e. (change of variables `y = √a z` against
`Planar.dilWFun`, `Planar.density_smul_dilWFun`, `Planar.integral_density_dilWFun`), the ratio is
`≤ max 1 a ^ M`, and dominated convergence applies (compact support of `G`). -/
def DilWAdjCcCont : Prop :=
  ∀ (M : ℝ) (hM : 1 < M) (G : Planar.L2w M), IsCcRep G → ∀ (a₀ : ℝ) (ha₀ : 0 < a₀),
    Tendsto (fun a : Set.Ioi (0 : ℝ) => ContinuousLinearMap.adjoint (Planar.dilW hM a.2) G)
      (𝓝 ⟨a₀, ha₀⟩) (𝓝 (ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) G))

/-- **Leaf** (source 946-953): the Hilbert adjoint of `Planar.dilW` on `L²_M` is, almost everywhere,
`(J_a)^* g (z) = a⁻¹ ((1+|√a z|²)/(1+|z|²))^M g(√a z)` (change of variables `y = √a z` against
`Planar.dilWFun`, using `Planar.density_smul_dilWFun`, `Planar.integral_density_dilWFun`). -/
def DilWAdjFormula : Prop :=
  ∀ (M : ℝ) (hM : 1 < M) {a : ℝ} (ha : 0 < a) (g : Planar.L2w M),
    ⇑(ContinuousLinearMap.adjoint (Planar.dilW hM ha) g) =ᵐ[Planar.wMeasure M]
      fun z : ℂ => (((a⁻¹ * ((1 + ‖(√a : ℝ) • z‖ ^ 2) ^ M / (1 + ‖z‖ ^ 2) ^ M) : ℝ)) : ℂ) *
        g ((√a : ℝ) • z)

theorem dilWAdjStrongCont_of (h1 : L2wCcDense) (h2 : DilWAdjCcCont) (M : ℝ) (hM : 1 < M)
    (f : Planar.L2w M) :
    Continuous (fun a : Set.Ioi (0 : ℝ) => ContinuousLinearMap.adjoint (Planar.dilW hM a.2) f) := by
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
  obtain ⟨G, hG, hGF⟩ := h1 M hM f (ε / (4 * C)) hδ
  have hev2 := (Metric.tendsto_nhds.1 (h2 M hM G hG a₀ ha₀)) (ε / 2) (by positivity)
  filter_upwards [hev1, hev2] with a ha1 ha2
  have hJ0 : ‖ContinuousLinearMap.adjoint (Planar.dilW hM ha₀)‖ ≤ Planar.dilConst M a₀ := by
    rw [LinearIsometryEquiv.norm_map]; exact Planar.norm_dilW_le hM ha₀
  have hJa : ‖ContinuousLinearMap.adjoint (Planar.dilW hM a.2)‖ ≤ Planar.dilConst M a.1 := by
    rw [LinearIsometryEquiv.norm_map]; exact Planar.norm_dilW_le hM a.2
  have hFG : ‖f - G‖ < ε / (4 * C) := by rw [norm_sub_rev]; exact hGF
  have hN : 0 ≤ ‖f - G‖ := norm_nonneg _
  have e1 : ‖ContinuousLinearMap.adjoint (Planar.dilW hM a.2) (f - G)‖ ≤ C * ‖f - G‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJa.trans ha1.le) hN)
  have e2 : ‖ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) (f - G)‖ ≤ C * ‖f - G‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hJ0.trans (by rw [hC]; linarith)) hN)
  have e3 : C * ‖f - G‖ < ε / 4 := by
    calc C * ‖f - G‖ < C * (ε / (4 * C)) := mul_lt_mul_of_pos_left hFG hC0
      _ = ε / 4 := by field_simp
  rw [dist_eq_norm] at ha2
  have key : ContinuousLinearMap.adjoint (Planar.dilW hM a.2) f -
        ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) f =
      ContinuousLinearMap.adjoint (Planar.dilW hM a.2) (f - G) +
        (ContinuousLinearMap.adjoint (Planar.dilW hM a.2) G -
          ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) G)
        - ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) (f - G) := by
    simp only [map_sub]; abel
  rw [dist_eq_norm, key]
  calc _ ≤ ‖ContinuousLinearMap.adjoint (Planar.dilW hM a.2) (f - G) +
        (ContinuousLinearMap.adjoint (Planar.dilW hM a.2) G -
          ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) G)‖ +
        ‖ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) (f - G)‖ := norm_sub_le _ _
    _ ≤ ‖ContinuousLinearMap.adjoint (Planar.dilW hM a.2) (f - G)‖ +
        ‖ContinuousLinearMap.adjoint (Planar.dilW hM a.2) G -
          ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) G‖ +
        ‖ContinuousLinearMap.adjoint (Planar.dilW hM ha₀) (f - G)‖ := by gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- The `X0`-adjoint is dominated by the `L²_M`-adjoint (test against the `X0` difference). -/
theorem norm_adjDilX0_sub_le (M : ℝ) (hM : 1 < M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (v : Planar.X0 hM) :
    ‖ContinuousLinearMap.adjoint (Planar.dilX0 hM ha : Planar.X0 hM →L[ℂ] Planar.X0 hM) v -
        ContinuousLinearMap.adjoint (Planar.dilX0 hM hb : Planar.X0 hM →L[ℂ] Planar.X0 hM) v‖ ≤
      ‖ContinuousLinearMap.adjoint (Planar.dilW hM ha) (v : Planar.L2w M) -
        ContinuousLinearMap.adjoint (Planar.dilW hM hb) (v : Planar.L2w M)‖ := by
  set d : Planar.X0 hM :=
    ContinuousLinearMap.adjoint (Planar.dilX0 hM ha : Planar.X0 hM →L[ℂ] Planar.X0 hM) v -
        ContinuousLinearMap.adjoint (Planar.dilX0 hM hb : Planar.X0 hM →L[ℂ] Planar.X0 hM) v
    with hd
  have hin : ∀ c (hc : 0 < c) (w : Planar.X0 hM),
      inner ℂ (ContinuousLinearMap.adjoint (Planar.dilX0 hM hc : Planar.X0 hM →L[ℂ] Planar.X0 hM) v) w =
      inner ℂ (ContinuousLinearMap.adjoint (Planar.dilW hM hc) (v : Planar.L2w M)) (w : Planar.L2w M) := by
    intro c hc w
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    simp [Planar.coe_dilX0_apply]
  have h1 : inner ℂ d d =
      inner ℂ (ContinuousLinearMap.adjoint (Planar.dilW hM ha) (v : Planar.L2w M) -
        ContinuousLinearMap.adjoint (Planar.dilW hM hb) (v : Planar.L2w M)) (d : Planar.L2w M) := by
    conv_lhs => rw [hd, inner_sub_left, hin, hin]
    rw [inner_sub_left]
  have h2 : ‖d‖ * ‖d‖ ≤ ‖ContinuousLinearMap.adjoint (Planar.dilW hM ha) (v : Planar.L2w M) -
        ContinuousLinearMap.adjoint (Planar.dilW hM hb) (v : Planar.L2w M)‖ * ‖d‖ := by
    calc ‖d‖ * ‖d‖ = ‖(inner ℂ d d : ℂ)‖ := by simp [inner_self_eq_norm_sq_to_K, sq]
      _ = _ := by rw [h1]
      _ ≤ _ := by
        have := norm_inner_le_norm (𝕜 := ℂ)
          (ContinuousLinearMap.adjoint (Planar.dilW hM ha) (v : Planar.L2w M) -
            ContinuousLinearMap.adjoint (Planar.dilW hM hb) (v : Planar.L2w M)) (d : Planar.L2w M)
        simpa using this
  by_cases h0 : ‖d‖ = 0
  · rw [h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h2 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

theorem dilX0_adjStrongCont_of (h1 : L2wCcDense) (h2 : DilWAdjCcCont) : DilX0AdjStrongCont := by
  intro M hM v
  have hc := dilWAdjStrongCont_of h1 h2 M hM (v : Planar.L2w M)
  have hinv : Continuous (fun a : Set.Ioi (0 : ℝ) => (⟨a.1⁻¹, Set.mem_Ioi.2 (inv_pos.2 a.2)⟩ : Set.Ioi (0 : ℝ))) :=
    Continuous.subtype_mk ((continuous_subtype_val).inv₀ (fun a => a.2.ne')) _
  have hc' := hc.comp hinv
  rw [Metric.continuous_iff] at hc' ⊢
  intro a ε hε
  obtain ⟨δ, hδ, H⟩ := hc' a ε hε
  exact ⟨δ, hδ, fun b hb => by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (norm_adjDilX0_sub_le M hM (inv_pos.2 b.2) (inv_pos.2 a.2) v) ?_
    rw [← dist_eq_norm]; exact H b hb⟩

end UnforcedLeray.Short.PartI
