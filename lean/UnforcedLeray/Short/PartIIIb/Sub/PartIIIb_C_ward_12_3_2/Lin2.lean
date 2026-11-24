import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEqSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.RawSmoothBdd3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinLeibniz
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinPairDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinAdjoint
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinRawDVSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinConvTPhaseTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinFieldLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq

/-!
# `GELin2`: order-2 linear term from `RawSmoothBdd3` (source 2525-2531, 2552-2559, 1217-1219, 1322-1325)

Task `PartIII-b:C/ward/12/3/2/2/3`.  Source of record
`the November 2 reference manuscript`.

For any smooth periodic field `V`, the Leibniz rule `∂_l(convT V Ψ) = convT V (∂_lΨ) + convT (∂_lV) Ψ`
and `gELinPairDeriv` give the one-step reduction
`⟪convT V (∂_lΨ), v⟫ = -⟪convT V Ψ, v'_l⟫ - ⟪convT (∂_lV) Ψ, v⟫`.
Applying this twice to `⟪convT p.raw (∂_l∂_jΦ), w⟫` expresses it as a sum of four pairings
`⟪convT V Φ, v⟫` with `V ∈ {raw, ∂_j raw, ∂_l raw, ∂_j∂_l raw}` and `(v, v') ∈ {(k_lj, t_lj),
(g_l, k_l), (g_j, k_j), (w, g)}`.  Each such pairing equals `phasePair Φ F` for some `F ∈ Y_{q₀}`
by `gELinAdjoint` and Hölder (`convTAdj` in `L^{q₀}` on the period cell whenever `V` and `DV` are
bounded, which holds for `raw`, `∂ raw`, `∂² raw` by `RawSmoothBdd3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseCell)
open UnforcedLeray.Cons.C03.Concrete (rep_add_period rep_slice stronglyMeasurable_rep phasePair_eq_pairF_rep)

namespace Lin2Sub

/-- Spatial partial derivative `∂_j V` of a time-dependent spatial vector field `V`. -/
def partialV (V : ℝ → UnforcedLeray.SpatialField) (j : Fin 3) : ℝ → UnforcedLeray.SpatialField :=
  fun τ y => fderiv ℝ (V τ) y (EuclideanSpace.single j 1)

/-- If `V` is jointly smooth and `P`-periodic, so is `partialV V j`. -/
theorem partialV_smoothPer {P : ℝ} {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (j : Fin 3) : IsSmoothPer P (partialV V j) := by
  obtain ⟨hC, hPer⟩ := hV
  refine ⟨gELinRawDVSmooth_partial hC j, fun τ y => ?_⟩
  show fderiv ℝ (V (τ + P)) y (EuclideanSpace.single j 1) =
    fderiv ℝ (V τ) y (EuclideanSpace.single j 1)
  rw [show V (τ + P) = V τ from funext (hPer τ)]

/-- General-`V` Leibniz identity for `convT`: `∂_j(convT V Φ) = convT V (∂_jΦ) + convT (∂_jV) Φ`. -/
theorem gLeib_general {P : ℝ} {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (j : Fin 3) (Φ : ℝ × UnforcedLeray.Space → CVec3)
    (hΦ : ContDiff ℝ ∞ Φ) :
    dy j (convT V Φ) = convT V (dy j Φ) + convT (partialV V j) Φ := by
  obtain ⟨hF, -⟩ := hV
  have hFd : Differentiable ℝ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) :=
    hF.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΦi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Φ z i) :=
    fun i => (contDiff_piLp 2).1 hΦ i
  have hdyΦ : ∀ m : Fin 3, ContDiff ℝ ∞ (dy m Φ) := fun m => gLeib_dy_smooth Φ hΦ m
  have hdyΦd : ∀ m : Fin 3, Differentiable ℝ (dy m Φ) := fun m => (hdyΦ m).differentiable (by simp)
  have hdyΦc : ∀ m k : Fin 3,
      ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => dy m Φ z k) :=
    fun m k => (contDiff_piLp 2).1 (hdyΦ m) k
  have hVc : ∀ m : Fin 3,
      ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => ((V z.1 z.2 m : ℝ) : ℂ)) :=
    fun m => gLeib_ofReal_c ((contDiff_piLp 2).1 hF m)
  have hVr : ∀ m : Fin 3,
      ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => V z.1 z.2 m) :=
    fun m => (contDiff_piLp 2).1 hF m
  have hPk : ∀ k : Fin 3, ContDiff ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1)) :=
    fun k => gLeib_partial hF k
  have hDr : ∀ k i : Fin 3, ContDiff ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1) i) :=
    fun k i => (contDiff_piLp 2).1 (hPk k) i
  have hDc : ∀ k i : Fin 3, ContDiff ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space =>
        ((fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) :=
    fun k i => gLeib_ofReal_c (hDr k i)
  have hG1 : ContDiff ℝ ∞ (convT V Φ) := gLeib_convT_smooth hF hΦ
  have hGj : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ
      (fun w : ℝ × UnforcedLeray.Space => V w.1 w.2) z (0, EuclideanSpace.single j 1)) :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  funext x
  ext k
  simp only [Pi.add_apply, PiLp.add_apply]
  rw [gLeib_comp_dy (hG1.differentiable (by simp)) j k x]
  have e1 : (fun z : ℝ × UnforcedLeray.Space => convT V Φ z k) = fun z =>
      (∑ i : Fin 3, Φ z i * ((fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) -
        ∑ m : Fin 3, ((V z.1 z.2 m : ℝ) : ℂ) * dy m Φ z k :=
    funext fun z => gLeib_hconvK V Φ z k
  rw [e1]
  have hS1 : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space =>
      ∑ i : Fin 3, Φ z i * ((fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) :=
    ContDiff.sum (fun i _ => (hΦi i).mul (hDc k i))
  have hS2 : ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space =>
      ∑ m : Fin 3, ((V z.1 z.2 m : ℝ) : ℂ) * dy m Φ z k) :=
    ContDiff.sum (fun m _ => (hVc m).mul (hdyΦc m k))
  rw [gLeib_sub_dy hS1 hS2 j x]
  rw [gLeib_sum_dy _ (fun i _ => (hΦi i).mul (hDc k i)) j x]
  rw [gLeib_sum_dy _ (fun m _ => (hVc m).mul (hdyΦc m k)) j x]
  have hGeq : (fun z : ℝ × UnforcedLeray.Space => fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1)) =
      fun z => fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => V w.1 w.2) z
        (0, EuclideanSpace.single k 1) :=
    funext fun z => gLeib_slice hFd z (EuclideanSpace.single k 1)
  have hA : ∀ i : Fin 3,
      dy j (fun z : ℝ × UnforcedLeray.Space => ((fderiv ℝ (V z.1) z.2
        (EuclideanSpace.single k 1) i : ℝ) : ℂ)) x =
        ((fderiv ℝ (partialV V j x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ) := by
    intro i
    rw [gLeib_ofReal_dy (hDr k i) j x]
    congr 1
    rw [← gLeib_comp_dyR ((hPk k).differentiable (by simp)) j i x, hGeq]
    have hsym := gLeib_sym hF x (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)
    have hfun2 : partialV V j x.1 = fun y => fderiv ℝ
        (fun w : ℝ × UnforcedLeray.Space => V w.1 w.2) (x.1, y) (0, EuclideanSpace.single j 1) :=
      funext fun y => gLeib_slice hFd (x.1, y) (EuclideanSpace.single j 1)
    have hsl : fderiv ℝ (partialV V j x.1) x.2 (EuclideanSpace.single k 1) =
        fderiv ℝ (fun z => fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => V w.1 w.2) z
          (0, EuclideanSpace.single j 1)) x (0, EuclideanSpace.single k 1) := by
      rw [hfun2, gLeib_slice (hGj.differentiable (by simp)) x (EuclideanSpace.single k 1)]
    simp only [dy, UnforcedLeray.coordinateVector]
    rw [hsym, hsl]
  have hB : ∀ m : Fin 3,
      dy j (fun z : ℝ × UnforcedLeray.Space => ((V z.1 z.2 m : ℝ) : ℂ)) x =
        ((partialV V j x.1 x.2 m : ℝ) : ℂ) := by
    intro m
    rw [gLeib_ofReal_dy (hVr m) j x]
    congr 1
    rw [← gLeib_comp_dyR hFd j m x]
    simp only [dy, UnforcedLeray.coordinateVector]
    rw [← gLeib_slice hFd x (EuclideanSpace.single j 1)]
    rfl
  have hCm : ∀ m : Fin 3, dy j (fun z : ℝ × UnforcedLeray.Space => dy m Φ z k) x =
      dy m (dy j Φ) x k := by
    intro m
    rw [← gLeib_comp_dy (hdyΦd m) j k x, PhaseSpace.dy_dy_comm hΦ j m]
  have hsumA : ∑ i : Fin 3, dy j (fun z : ℝ × UnforcedLeray.Space =>
      Φ z i * ((fderiv ℝ (V z.1) z.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) x =
      ∑ i : Fin 3, (dy j Φ x i * ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ) +
        Φ x i * ((fderiv ℝ (partialV V j x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [gLeib_mul_dy (hΦi i) (hDc k i) j x, ← gLeib_comp_dy hΦd j i x, hA i]
  have hsumB : ∑ m : Fin 3, dy j (fun z : ℝ × UnforcedLeray.Space =>
      ((V z.1 z.2 m : ℝ) : ℂ) * dy m Φ z k) x =
      ∑ m : Fin 3, (((partialV V j x.1 x.2 m : ℝ) : ℂ) * dy m Φ x k +
        ((V x.1 x.2 m : ℝ) : ℂ) * dy m (dy j Φ) x k) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [gLeib_mul_dy (hVc m) (hdyΦc m k) j x, hB m, hCm m]
  rw [hsumA, hsumB, gLeib_hconvK V (dy j Φ) x k, gLeib_hconvK (partialV V j) Φ x k]
  simp only [Finset.sum_add_distrib]
  ring

/-- One-step derivative reduction for `pairF P (convT V (dy l Ψ)) (rep v)`. -/
theorem step_convT {P : ℝ} [Fact (0 < P)] {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (v : Yq P UnforcedLeray.B0412.q0E)
    (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E)
    (hv : ∀ m, HasPhaseOp (fun Φ => -dy m Φ) v (v' m))
    (l : Fin 3) (Ψ : ℝ × UnforcedLeray.Space → CVec3) (hΨ : IsPhaseTest P Ψ) :
    pairF P (convT V (dy l Ψ)) (fun x => rep v x.1 x.2) =
      -pairF P (convT V Ψ) (fun x => rep (v' l) x.1 x.2) -
        pairF P (convT (partialV V l) Ψ) (fun x => rep v x.1 x.2) := by
  have hPV : IsSmoothPer P (partialV V l) := partialV_smoothPer hV l
  have hLeib := gLeib_general hV l Ψ hΨ.smooth
  have hdyΨ : IsPhaseTest P (dy l Ψ) := hΨ.dy l
  have hsplit : dy l (convT V Ψ) = fun x => convT V (dy l Ψ) x + convT (partialV V l) Ψ x :=
    funext fun x => congrFun hLeib x
  have hΘ : IsPhaseTest P (convT V Ψ) := gELinConvTPhaseTest P V hV Ψ hΨ
  have hI1 := (gELinAdjoint P V hV v v' hv (dy l Ψ) hdyΨ).2.1
  have hI2 := (gELinAdjoint P (partialV V l) hPV v v' hv Ψ hΨ).2.1
  have e1 : pairF P (dy l (convT V Ψ)) (fun x => rep v x.1 x.2) =
      pairF P (convT V (dy l Ψ)) (fun x => rep v x.1 x.2) +
        pairF P (convT (partialV V l) Ψ) (fun x => rep v x.1 x.2) := by
    rw [hsplit]
    have hFG : Integrable (fun x => dotL (convT V (dy l Ψ) x + convT (partialV V l) Ψ x)
        (rep v x.1 x.2)) (volume.restrict (phaseCell P)) := by
      refine (hI1.add hI2).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
    exact UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable
      (F := convT V (dy l Ψ)) (G := convT (partialV V l) Ψ)
      (H := fun x => rep v x.1 x.2) hI1 hI2 hFG
  have e2 := gELinPairDeriv P v (v' l) l (hv l) (convT V Ψ) hΘ
  linear_combination -e1 + e2

/-- Uniform bounds on spatial derivatives of orders `0` and `1` of `V`. -/
def HasBdd01 (V : ℝ → UnforcedLeray.SpatialField) : Prop :=
  (∃ C0 : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space), ‖iteratedFDeriv ℝ 0 (V τ) y‖ ≤ C0) ∧
  (∃ C1 : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space), ‖iteratedFDeriv ℝ 1 (V τ) y‖ ≤ C1)

theorem slice_contDiff {V : ℝ → UnforcedLeray.SpatialField}
    (hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => V τ y) := by
  have h2 : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => ((τ, y) : ℝ × UnforcedLeray.Space)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using hC.comp h2

theorem iteratedFDeriv_partialV_le {V : ℝ → UnforcedLeray.SpatialField}
    (hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    (b : Fin 3) (n : ℕ) (τ : ℝ) (y : UnforcedLeray.Space) :
    ‖iteratedFDeriv ℝ n (partialV V b τ) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) (V τ) y‖ := by
  have hs : ContDiff ℝ ∞ (fun y' : UnforcedLeray.Space => V τ y') := slice_contDiff hC τ
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (fun y' : UnforcedLeray.Space => V τ y')) y :=
    (hs.fderiv_right (m := ∞) (by simp)).contDiffAt
  have h1 := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ (fun y' : UnforcedLeray.Space => V τ y'))
    (c := (EuclideanSpace.single b 1 : UnforcedLeray.Space)) (x := y) (N := ∞) (n := n) hfd
    (by simp)
  rw [norm_iteratedFDeriv_fderiv, PiLp.norm_single, norm_one, one_mul] at h1
  exact h1

theorem convTAdj_stronglyMeasurable {P : ℝ} [Fact (0 < P)] {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (v : Yq P UnforcedLeray.B0412.q0E)
    (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E) :
    StronglyMeasurable (convTAdj V v v') := by
  have hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) := hV.1
  have hrD : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => partialV V k x.1 x.2) :=
    fun k => gELinRawDVSmooth_partial hC k
  have hcomp : ∀ {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}, ContDiff ℝ ∞ F →
      ∀ i : Fin 3, Measurable (fun x : ℝ × UnforcedLeray.Space => ((F x i : ℝ) : ℂ)) := by
    intro F hF i
    exact (Complex.continuous_ofReal.comp ((contDiff_piLp 2).1 hF i).continuous).measurable
  have hrep : ∀ (w : Yq P UnforcedLeray.B0412.q0E) (k : Fin 3),
      Measurable (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2 k) := by
    intro w k
    exact ((EuclideanSpace.proj k : UnforcedLeray.PhaseSpace.CVec3 →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_rep w)).measurable
  have htl : Measurable (WithLp.toLp 2 : (Fin 3 → ℂ) → UnforcedLeray.PhaseSpace.CVec3) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℂ)).measurable
  apply stronglyMeasurable_iff_measurable.2
  unfold convTAdj
  apply htl.comp
  apply measurable_pi_iff.2
  intro i
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun k _ => (hcomp (hrD k) i).mul (hrep v k))
  · exact Finset.measurable_sum _ (fun m _ =>
      ((hcomp (hrD m) m).mul (hrep v i)).add ((hcomp hC m).mul (hrep (v' m) i)))

theorem convTAdj_periodic {P : ℝ} [Fact (0 < P)] {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (v : Yq P UnforcedLeray.B0412.q0E)
    (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E) (τ : ℝ) (y : UnforcedLeray.Space) :
    convTAdj V v v' (τ + P, y) = convTAdj V v v' (τ, y) := by
  have hVp : V (τ + P) = V τ := funext (hV.2 τ)
  simp only [convTAdj, hVp, rep_add_period]

theorem convTAdj_lp {P : ℝ} [Fact (0 < P)] {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (hb : HasBdd01 V)
    (v : Yq P UnforcedLeray.B0412.q0E) (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E) :
    ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖convTAdj V v v' (τ, y)‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal < ⊤ := by
  have hC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) := hV.1
  obtain ⟨⟨C0, hC0⟩, ⟨C1, hC1⟩⟩ := hb
  have hVb : ∀ (τ : ℝ) (y : UnforcedLeray.Space) (m : Fin 3),
      ‖((V τ y m : ℝ) : ℂ)‖ ≤ C0 := by
    intro τ y m
    rw [Complex.norm_real]
    calc ‖V τ y m‖ ≤ ‖V τ y‖ := PiLp.norm_apply_le _ _
      _ = ‖iteratedFDeriv ℝ 0 (V τ) y‖ := (norm_iteratedFDeriv_zero (𝕜 := ℝ)).symm
      _ ≤ C0 := hC0 τ y
  have hDVb : ∀ (x : ℝ × UnforcedLeray.Space) (k i : Fin 3),
      ‖((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i : ℝ) : ℂ)‖ ≤ C1 := by
    intro x k i
    rw [Complex.norm_real]
    calc ‖fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) i‖
        ≤ ‖fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ (V x.1) x.2‖ * ‖(EuclideanSpace.single k 1 : UnforcedLeray.Space)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (V x.1) x.2‖ := by
          rw [norm_iteratedFDeriv_one, PiLp.norm_single]
          simp
      _ ≤ C1 := hC1 x.1 x.2
  have hmeasc : ∀ {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}, ContDiff ℝ ∞ F →
      ∀ i : Fin 3, Measurable (fun x : ℝ × UnforcedLeray.Space => ((F x i : ℝ) : ℂ)) := by
    intro F hF i
    exact (Complex.continuous_ofReal.comp ((contDiff_piLp 2).1 hF i).continuous).measurable
  have hrD : ∀ k : Fin 3, ContDiff ℝ ∞
      (fun x : ℝ × UnforcedLeray.Space => fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1)) :=
    fun k => gELinRawDVSmooth_partial hC k
  have hcomp : ∀ i : Fin 3, MemLp (fun x : ℝ × UnforcedLeray.Space => convTAdj V v v' x i)
      UnforcedLeray.B0412.q0E (volume.restrict (phaseCell P)) := by
    intro i
    simp only [convTAdj, PiLp.toLp_apply]
    refine MemLp.add ?_ ?_
    · apply memLp_finsetSum
      intro k _
      exact gAdj_memLp_mul (hmeasc (hrD k) i) (fun x => hDVb x k i) (gAdj_memLp_rep_comp v k)
    · apply memLp_finsetSum
      intro m _
      refine MemLp.add ?_ ?_
      · exact gAdj_memLp_mul (hmeasc (hrD m) m) (fun x => hDVb x m m) (gAdj_memLp_rep_comp v i)
      · exact gAdj_memLp_mul (hmeasc hC m) (fun x => hVb x.1 x.2 m) (gAdj_memLp_rep_comp (v' m) i)
  have hsum : MemLp (fun x : ℝ × UnforcedLeray.Space => ∑ i : Fin 3, ‖convTAdj V v v' x i‖)
      UnforcedLeray.B0412.q0E (volume.restrict (phaseCell P)) :=
    memLp_finsetSum Finset.univ (fun i _ => (hcomp i).norm)
  have hmeasF : StronglyMeasurable (convTAdj V v v') := convTAdj_stronglyMeasurable hV v v'
  have hF : MemLp (convTAdj V v v') UnforcedLeray.B0412.q0E (volume.restrict (phaseCell P)) := by
    refine MemLp.of_le hsum hmeasF.aestronglyMeasurable.restrict (ae_of_all _ fun x => ?_)
    have hnn : 0 ≤ ∑ i : Fin 3, ‖convTAdj V v v' x i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact gAdj_norm_le_sum_coord (convTAdj V v v' x)
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one UnforcedLeray.B0412.one_lt_q0E)
  have hfin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0
    UnforcedLeray.B0412.q0E_ne_top).1 hF.eLpNorm_lt_top
  have hprod : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict (phaseCell P) =
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod
        (volume : Measure UnforcedLeray.Space) := by
    simpa only [phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure UnforcedLeray.Space)) (Ioc (0 : ℝ) P)).symm
  have hmeasE : Measurable (fun x : ℝ × UnforcedLeray.Space =>
      ‖convTAdj V v v' x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal) :=
    (hmeasF.measurable.enorm).pow_const _
  have hconv : ∫⁻ x in phaseCell P, ‖convTAdj V v v' x‖ₑ ^
      UnforcedLeray.B0412.q0E.toReal =
      ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ y, ‖convTAdj V v v' (τ, y)‖ₑ ^
        UnforcedLeray.B0412.q0E.toReal := by
    rw [hprod, lintegral_prod _ hmeasE.aemeasurable]
  rw [← hconv]
  exact hfin

/-- General-`V` `Y_{q₀}` representation of `pairF P (convT V Φ) (rep v)`. -/
theorem convT_pair_yq {P : ℝ} [Fact (0 < P)] {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) (hb : HasBdd01 V)
    (v : Yq P UnforcedLeray.B0412.q0E) (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E)
    (hv : ∀ m, HasPhaseOp (fun Φ => -dy m Φ) v (v' m)) :
    ∃ F : Yq P UnforcedLeray.B0412.q0E, ∀ Φ, IsPhaseTest P Φ →
      pairF P (convT V Φ) (fun x => rep v x.1 x.2) =
        phasePair P UnforcedLeray.B0412.q0E Φ F := by
  have hΛm : StronglyMeasurable (convTAdj V v v') := convTAdj_stronglyMeasurable hV v v'
  have hper : ∀ᵐ τ : ℝ, (fun y => convTAdj V v v' (τ + P, y)) =ᵐ[volume]
      (fun y => convTAdj V v v' (τ, y)) :=
    ae_of_all _ (fun τ => ae_of_all _ (fun y => convTAdj_periodic hV v v' τ y))
  have hfin := convTAdj_lp hV hb v v'
  obtain ⟨F, hF⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof
    UnforcedLeray.B0412.q0E UnforcedLeray.B0412.q0E_ne_top P
    (convTAdj V v v') hΛm hper hfin
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [(gELinAdjoint P V hV v v' hv Φ hΦ).2.2, phasePair_eq_pairF_rep hΦ F]
  have hae : ∀ᵐ τ : ℝ, (fun y => convTAdj V v v' (τ, y)) =ᵐ[volume]
      (fun y => rep F τ y) := by
    filter_upwards [hF.slice] with τ hτ
    exact hτ.trans (rep_slice F τ).symm
  unfold UnforcedLeray.Cons.C03.Concrete.pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [hae] with τ hτ _
  apply integral_congr_ae
  filter_upwards [hτ] with y hy
  exact congrArg (dotL (Φ (τ, y))) hy

end Lin2Sub

/-- **`GELin2` from `RawSmoothBdd3`** (source 2525-2531, 2552-2559, 1217-1219, 1322-1325). -/
theorem gELin2_of (h : RawSmoothBdd3) : GELin2 := by
  intro lam q _ dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν _ z g hd k t hk ht j l => ?_⟩
  obtain ⟨hC, hPer, hB⟩ := H p d hreg hν
  have hV0 : IsSmoothPer p.period p.raw := ⟨hC, hPer⟩
  have hV1j : IsSmoothPer p.period (Lin2Sub.partialV p.raw j) := Lin2Sub.partialV_smoothPer hV0 j
  have hV1l : IsSmoothPer p.period (Lin2Sub.partialV p.raw l) := Lin2Sub.partialV_smoothPer hV0 l
  have hV2 : IsSmoothPer p.period (Lin2Sub.partialV (Lin2Sub.partialV p.raw l) j) :=
    Lin2Sub.partialV_smoothPer hV1l j
  obtain ⟨C0, hC0⟩ := hB 0
  obtain ⟨C1, hC1⟩ := hB 1
  obtain ⟨C2, hC2⟩ := hB 2
  obtain ⟨C3, hC3⟩ := hB 3
  have hb0 : Lin2Sub.HasBdd01 p.raw := ⟨⟨C0, hC0⟩, ⟨C1, hC1⟩⟩
  have hb1 : ∀ a : Fin 3, Lin2Sub.HasBdd01 (Lin2Sub.partialV p.raw a) := fun a =>
    ⟨⟨C1, fun τ y => (Lin2Sub.iteratedFDeriv_partialV_le hC a 0 τ y).trans (hC1 τ y)⟩,
     ⟨C2, fun τ y => (Lin2Sub.iteratedFDeriv_partialV_le hC a 1 τ y).trans (hC2 τ y)⟩⟩
  have hb2 : Lin2Sub.HasBdd01 (Lin2Sub.partialV (Lin2Sub.partialV p.raw l) j) :=
    ⟨⟨C2, fun τ y =>
      (Lin2Sub.iteratedFDeriv_partialV_le hV1l.1 j 0 τ y).trans
        ((Lin2Sub.iteratedFDeriv_partialV_le hC l 1 τ y).trans (hC2 τ y))⟩,
     ⟨C3, fun τ y =>
      (Lin2Sub.iteratedFDeriv_partialV_le hV1l.1 j 1 τ y).trans
        ((Lin2Sub.iteratedFDeriv_partialV_le hC l 2 τ y).trans (hC3 τ y))⟩⟩
  obtain ⟨F1, hF1⟩ := Lin2Sub.convT_pair_yq hV0 hb0 (k l j) (t l j) (ht l j)
  obtain ⟨F2, hF2⟩ := Lin2Sub.convT_pair_yq hV1j (hb1 j) (g l) (k l) (hk l)
  obtain ⟨F3, hF3⟩ := Lin2Sub.convT_pair_yq hV1l (hb1 l) (g j) (k j) (hk j)
  obtain ⟨F4, hF4⟩ := Lin2Sub.convT_pair_yq hV2 hb2 (p.wOf z) g hd.2
  refine ⟨F1 + F2 + F3 + F4, fun Φ hΦ => ?_⟩
  have hΦt : IsPhaseTest p.period Φ := hΦ.1
  have hdyΦ : IsPhaseTest p.period (dy j Φ) := hΦt.dy j
  have s1 := Lin2Sub.step_convT hV0 (p.wOf z) g hd.2 l (dy j Φ) hdyΦ
  have s2 := Lin2Sub.step_convT hV0 (g l) (k l) (hk l) j Φ hΦt
  have s3 := Lin2Sub.step_convT hV1l (p.wOf z) g hd.2 j Φ hΦt
  rw [s1, s2, s3, hF1 Φ hΦt, hF2 Φ hΦt, hF3 Φ hΦt, hF4 Φ hΦt]
  simp only [map_add]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.gELin2_of
