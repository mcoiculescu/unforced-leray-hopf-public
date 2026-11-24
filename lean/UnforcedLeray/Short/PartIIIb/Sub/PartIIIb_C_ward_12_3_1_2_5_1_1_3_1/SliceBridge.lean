import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# Slice bridge (pure calculus)

Proves `SliceBridge` from `FarOrg.lean` (source `shorter-proof-2026-11-02.tex`, lines 2563-2569):
spatial phase-space derivatives of a `C^∞` function on an open set are bounded by the norms of
the iterated Fréchet derivatives of its slice `y ↦ G(x.1, y)` at `x.2`.

The argument: for `G` smooth on the open `U`, the slice `S = G(x.1, ·)` is smooth on the open
set `V = {y | (x.1, y) ∈ U}`, and `∂_{y_j} H (x.1, y) = fderiv S y e_j` for every smooth `H`
on `U`. Iterating this (with `Filter`-free pointwise identities on `V`) gives the exact
identities `∂_j G(x) = S'(x.2) e_j`, `∂_j∂_k G(x) = S''(x.2) e_j e_k` and
`∂_j∂_k∂_l G(x) = S'''(x.2) e_j e_k e_l`, and the norm bounds follow from
`ContinuousMultilinearMap.le_opNorm` with `‖e_j‖ = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

section Helpers

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sb_norm_coord (j : Fin 3) : ‖UnforcedLeray.coordinateVector j‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

theorem sb_diff_of_contDiffOn {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : X → M} {V : Set X} (hV : IsOpen V)
    {b : X} (hb : b ∈ V) (hf : ContDiffOn ℝ ∞ f V) :
    DifferentiableAt ℝ f b :=
  (hf.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hb)

/-- Chain rule for a slice: the derivative of `y ↦ H(a, y)` is the partial derivative of `H`. -/
theorem sb_slice_fderiv (H : ℝ × UnforcedLeray.Space → F) (a : ℝ) (b : UnforcedLeray.Space)
    (hH : DifferentiableAt ℝ H (a, b)) (v : UnforcedLeray.Space) :
    fderiv ℝ (fun y : UnforcedLeray.Space => H (a, y)) b v = fderiv ℝ H (a, b) (0, v) := by
  have hmap : HasFDerivAt (fun y : UnforcedLeray.Space => (a, y))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) b :=
    (hasFDerivAt_const a b).prodMk (hasFDerivAt_id b)
  have hcomp := hH.hasFDerivAt.comp b hmap
  have h := congrArg (fun A : UnforcedLeray.Space →L[ℝ] F => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply] using h

/-- Derivative of `y ↦ A y w` for a CLM-valued `A`. -/
theorem sb_clm_chain {M N : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {A : UnforcedLeray.Space → (M →L[ℝ] N)} {b : UnforcedLeray.Space}
    (hA : DifferentiableAt ℝ A b) (w : M) (v : UnforcedLeray.Space) :
    fderiv ℝ (fun y => A y w) b v = fderiv ℝ A b v w := by
  have h : fderiv ℝ (fun y => A y w) b =
      (A b).comp (fderiv ℝ (fun _ : UnforcedLeray.Space => w) b) + (fderiv ℝ A b).flip w :=
    fderiv_clm_apply hA (differentiableAt_const w)
  rw [h]
  simp

theorem sb_opnorm {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => UnforcedLeray.Space) F)
    (v : Fin n → UnforcedLeray.Space) (hv : ∀ i, ‖v i‖ = 1) : ‖f v‖ ≤ ‖f‖ := by
  have h := f.le_opNorm v
  simpa [hv] using h

theorem sb_iter2 (S : UnforcedLeray.Space → F) (b a1 a2 : UnforcedLeray.Space) :
    iteratedFDeriv ℝ 2 S b ![a1, a2] = fderiv ℝ (fderiv ℝ S) b a1 a2 := by
  rw [iteratedFDeriv_two_apply]
  rfl

theorem sb_iter3 (S : UnforcedLeray.Space → F) (b a1 a2 a3 : UnforcedLeray.Space) :
    iteratedFDeriv ℝ 3 S b ![a1, a2, a3] =
      fderiv ℝ (fderiv ℝ (fderiv ℝ S)) b a1 a2 a3 := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

theorem sb_v2 (j k : Fin 3) :
    ∀ i, ‖(![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector k] :
      Fin 2 → UnforcedLeray.Space) i‖ = 1 := by
  intro i
  fin_cases i <;> simp [sb_norm_coord]

theorem sb_v3 (j k l : Fin 3) :
    ∀ i, ‖(![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector k,
      UnforcedLeray.coordinateVector l] : Fin 3 → UnforcedLeray.Space) i‖ = 1 := by
  intro i
  fin_cases i <;> simp [sb_norm_coord]

theorem sb_dy_contDiffOn {G : ℝ × UnforcedLeray.Space → F}
    {U : Set (ℝ × UnforcedLeray.Space)} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (j : Fin 3) :
    ContDiffOn ℝ ∞ (UnforcedLeray.PhaseSpace.dy j G) U := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by simp)
  have hc : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ G z (0, UnforcedLeray.coordinateVector j)) U :=
    hd.clm_apply contDiffOn_const
  exact hc

theorem sb_slice_contDiffOn {H : ℝ × UnforcedLeray.Space → F}
    {U : Set (ℝ × UnforcedLeray.Space)} (hH : ContDiffOn ℝ ∞ H U) (a : ℝ) :
    ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => H (a, y)) {y | (a, y) ∈ U} := by
  have hc : ContDiffOn ℝ ∞
      (fun y : UnforcedLeray.Space => ((a, y) : ℝ × UnforcedLeray.Space))
      {y | (a, y) ∈ U} :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  exact hH.comp hc (fun y hy => hy)

/-- Pointwise slice identity: `∂_j H(a, y) = ∂_j(H(a, ·))(y)` for `(a, y) ∈ U`. -/
theorem sb_slice_dy {H : ℝ × UnforcedLeray.Space → F}
    {U : Set (ℝ × UnforcedLeray.Space)} (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (a : ℝ) (y : UnforcedLeray.Space) (hy : (a, y) ∈ U) (j : Fin 3) :
    UnforcedLeray.PhaseSpace.dy j H (a, y) =
      fderiv ℝ (fun y' : UnforcedLeray.Space => H (a, y')) y
        (UnforcedLeray.coordinateVector j) :=
  (sb_slice_fderiv H a y (sb_diff_of_contDiffOn hU hy hH) (UnforcedLeray.coordinateVector j)).symm

/-- Second level: `∂_j (∂_k G)` on the slice is the second derivative of the slice. -/
theorem sb_core2 {S T1 : UnforcedLeray.Space → F} {V : Set UnforcedLeray.Space}
    (hV : IsOpen V) {b : UnforcedLeray.Space} (hb : b ∈ V) (hS : ContDiffOn ℝ ∞ S V)
    (j k : Fin 3)
    (h1 : ∀ y ∈ V, T1 y = fderiv ℝ S y (UnforcedLeray.coordinateVector k)) :
    fderiv ℝ T1 b (UnforcedLeray.coordinateVector j) =
      fderiv ℝ (fderiv ℝ S) b (UnforcedLeray.coordinateVector j)
        (UnforcedLeray.coordinateVector k) := by
  have hQ : ContDiffOn ℝ ∞ (fderiv ℝ S) V := hS.fderiv_of_isOpen hV (by simp)
  have dQ : DifferentiableAt ℝ (fderiv ℝ S) b := sb_diff_of_contDiffOn hV hb hQ
  have hev : T1 =ᶠ[nhds b] (fun y => fderiv ℝ S y (UnforcedLeray.coordinateVector k)) :=
    Filter.eventually_of_mem (hV.mem_nhds hb) h1
  rw [hev.fderiv_eq]
  exact sb_clm_chain dQ (UnforcedLeray.coordinateVector k) (UnforcedLeray.coordinateVector j)

/-- Third level, from the first-order slice identity `T1 = Q(·) e_l` and the second-order one
`T2 = ∂T1(·) e_k` on the open set `V`, with `Q = fderiv S` smooth on `V`. -/
theorem sb_core3 {Q : UnforcedLeray.Space → (UnforcedLeray.Space →L[ℝ] F)}
    {T1 T2 : UnforcedLeray.Space → F} {V : Set UnforcedLeray.Space}
    (hV : IsOpen V) {b : UnforcedLeray.Space} (hb : b ∈ V) (hQ : ContDiffOn ℝ ∞ Q V)
    (j k l : Fin 3)
    (h1 : ∀ y ∈ V, T1 y = Q y (UnforcedLeray.coordinateVector l))
    (h2 : ∀ y ∈ V, T2 y = fderiv ℝ T1 y (UnforcedLeray.coordinateVector k)) :
    fderiv ℝ T2 b (UnforcedLeray.coordinateVector j) =
      fderiv ℝ (fderiv ℝ Q) b (UnforcedLeray.coordinateVector j)
        (UnforcedLeray.coordinateVector k) (UnforcedLeray.coordinateVector l) := by
  have dQ' : DifferentiableAt ℝ (fderiv ℝ Q) b :=
    sb_diff_of_contDiffOn hV hb (hQ.fderiv_of_isOpen hV (by simp))
  have hT1 : T1 =ᶠ[nhds b] (fun y => Q y (UnforcedLeray.coordinateVector l)) :=
    Filter.eventually_of_mem (hV.mem_nhds hb) h1
  have hT2 : T2 =ᶠ[nhds b] (fun y => fderiv ℝ T1 y (UnforcedLeray.coordinateVector k)) :=
    Filter.eventually_of_mem (hV.mem_nhds hb) h2
  have hdT1 : fderiv ℝ T1 =ᶠ[nhds b]
      fderiv ℝ (fun y => Q y (UnforcedLeray.coordinateVector l)) :=
    hT1.fderiv
  have hfun1 : (fun y => fderiv ℝ T1 y (UnforcedLeray.coordinateVector k)) =ᶠ[nhds b]
      (fun y => fderiv ℝ (fun y => Q y (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector k)) := by
    filter_upwards [hdT1] with y hy
    rw [hy]
  have hpt : ∀ y ∈ V,
      fderiv ℝ (fun y => Q y (UnforcedLeray.coordinateVector l)) y
          (UnforcedLeray.coordinateVector k) =
        fderiv ℝ Q y (UnforcedLeray.coordinateVector k) (UnforcedLeray.coordinateVector l) := by
    intro y hy
    exact sb_clm_chain (sb_diff_of_contDiffOn hV hy hQ) (UnforcedLeray.coordinateVector l)
      (UnforcedLeray.coordinateVector k)
  have hfun2 : (fun y => fderiv ℝ (fun y => Q y (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector k)) =ᶠ[nhds b]
      (fun y => fderiv ℝ Q y (UnforcedLeray.coordinateVector k)
        (UnforcedLeray.coordinateVector l)) := by
    filter_upwards [hV.mem_nhds hb] with y hy
    exact hpt y hy
  have hfun2' : fderiv ℝ (fun y => fderiv ℝ (fun y => Q y (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector k)) b =
      fderiv ℝ (fun y => fderiv ℝ Q y (UnforcedLeray.coordinateVector k)
        (UnforcedLeray.coordinateVector l)) b :=
    hfun2.fderiv_eq
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ Q y (UnforcedLeray.coordinateVector k)) b :=
    dQ'.clm_apply (differentiableAt_const _)
  have hD : fderiv ℝ (fun y => fderiv ℝ Q y (UnforcedLeray.coordinateVector k)
        (UnforcedLeray.coordinateVector l)) b (UnforcedLeray.coordinateVector j) =
      (fderiv ℝ (fun y => fderiv ℝ Q y (UnforcedLeray.coordinateVector k)) b
        (UnforcedLeray.coordinateVector j)) (UnforcedLeray.coordinateVector l) :=
    sb_clm_chain hA (UnforcedLeray.coordinateVector l) (UnforcedLeray.coordinateVector j)
  have hE : fderiv ℝ (fun y => fderiv ℝ Q y (UnforcedLeray.coordinateVector k)) b
        (UnforcedLeray.coordinateVector j) =
      fderiv ℝ (fderiv ℝ Q) b (UnforcedLeray.coordinateVector j)
        (UnforcedLeray.coordinateVector k) :=
    sb_clm_chain dQ' (UnforcedLeray.coordinateVector k) (UnforcedLeray.coordinateVector j)
  rw [hT2.fderiv_eq, hfun1.fderiv_eq, hfun2', hD, hE]

end Helpers

/-- **Slice bridge** (pure calculus; source 2563-2569): spatial phase-space derivatives of order
`1, 2, 3` of a `C^∞` function on an open set are bounded by the norms of the first, second and
third derivatives of its slice `G(x.1, ·)` at `x.2`. -/
theorem sliceBridge : SliceBridge := by
  intro F _ _ G U hU hG x hx j k l
  obtain ⟨a, b⟩ := x
  have hab : (a, b) ∈ U := hx
  have hV : IsOpen {y : UnforcedLeray.Space | (a, y) ∈ U} :=
    hU.preimage (continuous_const.prodMk continuous_id)
  have hbV : b ∈ {y : UnforcedLeray.Space | (a, y) ∈ U} := hab
  have hS : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => G (a, y))
      {y : UnforcedLeray.Space | (a, y) ∈ U} :=
    sb_slice_contDiffOn hG a
  have hQ : ContDiffOn ℝ ∞ (fderiv ℝ (fun y : UnforcedLeray.Space => G (a, y)))
      {y : UnforcedLeray.Space | (a, y) ∈ U} :=
    hS.fderiv_of_isOpen hV (by simp)
  have hG1 : ContDiffOn ℝ ∞ (UnforcedLeray.PhaseSpace.dy l G) U :=
    sb_dy_contDiffOn hU hG l
  have hG2 : ContDiffOn ℝ ∞ (UnforcedLeray.PhaseSpace.dy k (UnforcedLeray.PhaseSpace.dy l G)) U :=
    sb_dy_contDiffOn hU hG1 k
  have hG3 : ContDiffOn ℝ ∞ (UnforcedLeray.PhaseSpace.dy k G) U :=
    sb_dy_contDiffOn hU hG k
  have o1 := sb_slice_dy hU hG a b hab j
  have o2 : UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k G) (a, b) =
      fderiv ℝ (fderiv ℝ (fun y : UnforcedLeray.Space => G (a, y))) b
        (UnforcedLeray.coordinateVector j) (UnforcedLeray.coordinateVector k) :=
    (sb_slice_dy hU hG3 a b hab j).trans
      (sb_core2 hV hbV hS j k (fun y hy => sb_slice_dy hU hG a y hy k))
  have o3 : UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k
      (UnforcedLeray.PhaseSpace.dy l G)) (a, b) =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y : UnforcedLeray.Space => G (a, y)))) b
        (UnforcedLeray.coordinateVector j) (UnforcedLeray.coordinateVector k)
        (UnforcedLeray.coordinateVector l) :=
    (sb_slice_dy hU hG2 a b hab j).trans
      (sb_core3 hV hbV hQ j k l (fun y hy => sb_slice_dy hU hG a y hy l)
        (fun y hy => sb_slice_dy hU hG1 a y hy k))
  show ‖UnforcedLeray.PhaseSpace.dy j G (a, b)‖ ≤
      ‖iteratedFDeriv ℝ 1 (fun y : UnforcedLeray.Space => G (a, y)) b‖ ∧
    ‖UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k G) (a, b)‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun y : UnforcedLeray.Space => G (a, y)) b‖ ∧
    ‖UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k
        (UnforcedLeray.PhaseSpace.dy l G)) (a, b)‖ ≤
      ‖iteratedFDeriv ℝ 3 (fun y : UnforcedLeray.Space => G (a, y)) b‖
  refine ⟨?_, ?_, ?_⟩
  · rw [o1, norm_iteratedFDeriv_one]
    have h := (fderiv ℝ (fun y : UnforcedLeray.Space => G (a, y)) b).le_opNorm
      (UnforcedLeray.coordinateVector j)
    rw [sb_norm_coord, mul_one] at h
    exact h
  · have h := sb_opnorm (iteratedFDeriv ℝ 2 (fun y : UnforcedLeray.Space => G (a, y)) b)
      ![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector k] (sb_v2 j k)
    rw [sb_iter2] at h
    rw [o2]
    exact h
  · have h := sb_opnorm (iteratedFDeriv ℝ 3 (fun y : UnforcedLeray.Space => G (a, y)) b)
      ![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector k,
        UnforcedLeray.coordinateVector l] (sb_v3 j k l)
    rw [sb_iter3] at h
    rw [o3]
    exact h

end UnforcedLeray.Short.PartIIIb.Concrete
