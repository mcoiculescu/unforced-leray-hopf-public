import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Du
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Main

/-!
# `gEQIbp2_step : GEQIbp2Step` (`PartIII-b:C/ward/12/3/2/2/4`)

Source `the November 2 reference manuscript`,
lines 2552-2559, 2531, 1515-1531.

Because `g_a ∈ D_p` with weak gradient `k_a` and weak Hessian `t_a`, the supremum embedding
`graphSupEmbedding` (`rep_ae_bound`) bounds `rep (g_a)` in `L^∞`, and `gradL2pIBP` applied to the
triple `(g_a, k_a, t_a)` places `rep (k a b)` in `L^{2q₀}` on the phase cell.  Consequently
`GEQDdu p z g k a b ∈ L^{2q₀}_loc` and `GEQD3u p z t a b c ∈ L^{q₀}_loc`, so `weakMulRule`
(`WeakMulRule`) applies in direction `j` to all four products in `GEQuadField p z g k l`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF advT rep phaseInt phaseCell)

namespace Quad2IbpSub

/-- Any element `v ∈ D_p` has an a.e. bounded joint representative on `phaseμ p.period` when
`p.period ≤ 1` (by `graphSupEmbedding` and `rep_ae_bound`, source 1515-1531). -/
theorem rep_ae_bound_of_mem_D {p : Params} (hP1 : p.period ≤ 1)
    {v : Yq p.period UnforcedLeray.B0412.q0E}
    (hvD : v ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂(phaseμ p.period), ‖rep v x.1 x.2‖ ≤ M := by
  have h52 : (5 / 2 : ℝ≥0∞) < UnforcedLeray.B0412.q0E := by
    unfold UnforcedLeray.B0412.q0E
    rw [show (5 / 2 : ℝ≥0∞) = ENNReal.ofReal (5 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [UnforcedLeray.B0281.q0_eq])).2
      (by norm_num [UnforcedLeray.B0281.q0_eq])
  obtain ⟨C, -, hS⟩ := UnforcedLeray.Short.PartIIa.graphSupEmbedding
    UnforcedLeray.B0412.q0E h52 UnforcedLeray.B0412.q0E_ne_top
  obtain ⟨W, -, hWae, hWb⟩ := hS p.period hP1 p.ν p.ν_pos ⟨v, hvD⟩
  refine ⟨|C * p.ν ^ (-(3 / (2 * UnforcedLeray.B0412.q0E.toReal))) *
    UnforcedLeray.B0411.graphNormD (⟨v, hvD⟩ : UnforcedLeray.B0411.D p.period p.ν
      UnforcedLeray.B0412.q0E)|, abs_nonneg _, ?_⟩
  exact rep_ae_bound v W _ hWae (fun τ y => (hWb τ y).trans (le_abs_self _))

/-- Under `GEQHyp2 p z g k t` and `p.period ≤ 1`, `rep (k a b) ∈ L^{2q₀}(phaseμ p.period)` by
`gradL2pIBP` applied to `(g a, k a, t a)` (source 2531, 2552-2559). -/
theorem rep_k_memLp_2q0 {p : Params} {z : p.Z}
    {g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    {k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    {t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    (hP1 : p.period ≤ 1) (hyp : GEQHyp2 p z g k t) (a b : Fin 3) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep (k a b) x.1 x.2)
      (2 * UnforcedLeray.B0412.q0E) (phaseμ p.period) := by
  obtain ⟨M, hM0, hM⟩ := rep_ae_bound_of_mem_D hP1 (hyp.1 a)
  exact (gradL2pIBP p.period (g a) (k a) (t a) M hM0 hM (hyp.2.1 a) (hyp.2.2 a) b).1

/-- Smoothness of the affine inlet `p.eFun (p.coord z)` for `p.ν ≤ 1`. -/
theorem eFun_contDiff {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
  unfold Params.eFun
  refine contDiff_realC.comp ?_
  refine ContDiff.sum fun l _ => ?_
  exact (inlet_contDiff_joint lam q hq hreg hν1 hmode l).const_smul _

/-- Under `GEQHyp2 p z g k t`, `p.ν ≤ 1`, and `p.period ≤ 1`,
`GEQDdu p z g k a b · i ∈ L^{2q₀}_loc`. -/
theorem memLpLoc_ddu_2q0 {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hP1 : p.period ≤ 1)
    (hmode : p.mode = q) (z : p.Z)
    {g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    {k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    {t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    (hyp : GEQHyp2 p z g k t) (a b i : Fin 3) :
    MemLpLoc p.period (fun x => GEQDdu p z g k a b x i) (2 * UnforcedLeray.B0412.q0E) := by
  intro R
  have hsm := eFun_contDiff hq hreg hν1 hmode z
  have hcd : ContDiff ℝ ∞ (dy a (dy b (p.eFun (p.coord z)))) :=
    contDiff_dyT (contDiff_dyT hsm b) a
  have hcont : Continuous (fun x : ℝ × UnforcedLeray.Space =>
      dy a (dy b (p.eFun (p.coord z))) x i) :=
    (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hcd.continuous
  have hA := memLp_ddu_loc p.period R (f := fun x => dy a (dy b (p.eFun (p.coord z))) x i) hcont
    (2 * UnforcedLeray.B0412.q0E)
  have hle : ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤ phaseμ p.period :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hB0 := MemLp.mono_measure hle (rep_k_memLp_2q0 hP1 hyp a b)
  have hB : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (k a b) x.1 x.2 i)
      (2 * UnforcedLeray.B0412.q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp (by simp) hB0 : _)
  exact hA.add hB

/-- Under `p.ν ≤ 1`, `GEQD3u p z t a b c · i ∈ L^{q₀}_loc`. -/
theorem memLpLoc_d3u_q0 {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) (t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (a b c i : Fin 3) :
    MemLpLoc p.period (fun x => GEQD3u p z t a b c x i) UnforcedLeray.B0412.q0E := by
  intro R
  have hsm := eFun_contDiff hq hreg hν1 hmode z
  have hcd : ContDiff ℝ ∞ (dy c (dy b (dy a (p.eFun (p.coord z))))) :=
    contDiff_dyT (contDiff_dyT (contDiff_dyT hsm a) b) c
  have hcont : Continuous (fun x : ℝ × UnforcedLeray.Space =>
      dy c (dy b (dy a (p.eFun (p.coord z)))) x i) :=
    (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hcd.continuous
  have hA := memLp_ddu_loc p.period R
    (f := fun x => dy c (dy b (dy a (p.eFun (p.coord z)))) x i) hcont
    UnforcedLeray.B0412.q0E
  have hrep := UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell
    (q := UnforcedLeray.B0412.q0E) (by simp [UnforcedLeray.B0412.q0E]) (t a b c)
  have hle : ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤
      (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
        (Ioc (0 : ℝ) p.period ×ˢ (univ : Set UnforcedLeray.Space)) := by
    have : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
        (Ioc (0 : ℝ) p.period ×ˢ (univ : Set UnforcedLeray.Space)) =
        (volume.restrict (Ioc (0 : ℝ) p.period)).prod volume := by
      simpa only [Measure.volume_eq_prod] using
        (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
          (ν := (volume : Measure UnforcedLeray.Space)) (Ioc 0 p.period)).symm
    rw [this]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hB0 := hrep.mono_measure hle
  have hB : MemLp (fun x : ℝ × UnforcedLeray.Space => rep (t a b c) x.1 x.2 i)
      UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) :=
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp (by simp) hB0 : _)
  exact hA.add hB

/-- A phase test times a locally `L²` function is integrable on the phase cell. -/
theorem integrable_test_mul1 {P : ℝ} [Fact (0 < P)] {ψ f : ℝ × UnforcedLeray.Space → ℂ}
    (hψ : IsPhaseTest P ψ) (hf : MemLpLoc P f 2) :
    Integrable (fun x => ψ x * f x) (volume.restrict (phaseCell P)) := by
  have h1 : MemLpLoc P (fun _ : ℝ × UnforcedLeray.Space => (1 : ℂ)) 2 :=
    fun R => memLp_ddu_loc P R continuous_const 2
  have h := integrable_test_mul2 hψ hf h1
  refine h.congr (ae_of_all _ fun x => ?_)
  simp

/-- Sum of weak derivatives for `MemLpLoc P _ 2` summands. -/
theorem weakDyS_add_loc2 {P : ℝ} [Fact (0 < P)] (c : Fin 3)
    {e e' r r' : ℝ × UnforcedLeray.Space → ℂ}
    (he : MemLpLoc P e 2) (he' : MemLpLoc P e' 2)
    (hr : MemLpLoc P r 2) (hr' : MemLpLoc P r' 2)
    (H1 : WeakDyS P c e e') (H2 : WeakDyS P c r r') :
    WeakDyS P c (fun x => e x + r x) (fun x => e' x + r' x) := by
  intro φ hφ
  have hd : IsPhaseTest P (dy c φ) := hφ.dy c
  have I1 := integrable_test_mul1 hd he
  have I2 := integrable_test_mul1 hd hr
  have J1 := integrable_test_mul1 hφ he'
  have J2 := integrable_test_mul1 hφ hr'
  have hL : (fun x => dy c φ x * (e x + r x)) =
      fun x => dy c φ x * e x + dy c φ x * r x := by
    funext x; ring
  have hR : (fun x => φ x * (e' x + r' x)) =
      fun x => φ x * e' x + φ x * r' x := by
    funext x; ring
  rw [hL, phaseInt_add_cell I1 I2, H1 φ hφ, H2 φ hφ, hR, phaseInt_add_cell J1 J2]
  ring

/-- Weak `y_c`-derivative of `GEQDdu p z g k a b · i` is `GEQD3u p z t a b c · i`. -/
theorem weakDyS_ddu {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z)
    {g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    {k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    {t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E}
    (hyp : GEQHyp2 p z g k t) (a b c i : Fin 3) :
    WeakDyS p.period c (fun x => GEQDdu p z g k a b x i)
      (fun x => GEQD3u p z t a b c x i) := by
  have hef := eFun_contDiff hq hreg hν1 hmode z
  have hcomm : dy a (dy b (p.eFun (p.coord z))) = dy b (dy a (p.eFun (p.coord z))) :=
    dy_dy_comm hef a b
  have he2 : ContDiff ℝ ∞ (dy b (dy a (p.eFun (p.coord z)))) :=
    contDiff_dy' (contDiff_dy' hef a) b
  let cC : CVec3 →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  have hs : ContDiff ℝ ∞ (fun x => dy b (dy a (p.eFun (p.coord z))) x i) :=
    cC.contDiff.comp he2
  have hc : dy c (fun x => dy b (dy a (p.eFun (p.coord z))) x i) =
      fun x => dy c (dy b (dy a (p.eFun (p.coord z)))) x i :=
    dy_clm cC (he2.differentiable (by simp)) c
  have hw_e : WeakDyS p.period c (fun x => dy a (dy b (p.eFun (p.coord z))) x i)
      (fun x => dy c (dy b (dy a (p.eFun (p.coord z)))) x i) := by
    rw [hcomm, ← hc]
    exact weakDyS_of_smooth p.period c hs
  obtain ⟨hw_r, hm, hm'⟩ := gEQRepWeak p.period c (k a b) (t a b c) (hyp.2.2 a b c) i
  have he_loc : MemLpLoc p.period (fun x => dy a (dy b (p.eFun (p.coord z))) x i) 2 := by
    intro R
    rw [hcomm]
    exact memLp_ddu_loc p.period R hs.continuous 2
  have he'_loc : MemLpLoc p.period
      (fun x => dy c (dy b (dy a (p.eFun (p.coord z)))) x i) 2 := by
    intro R
    rw [← hc]
    exact memLp_ddu_loc p.period R (contDiff_dy' hs c).continuous 2
  have hle : ∀ R, ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume.restrict (Metric.closedBall (0 : UnforcedLeray.Space) R))) ≤
      (volume.restrict (Ioc (0 : ℝ) p.period)).prod volume :=
    fun _ => Measure.prod_mono le_rfl Measure.restrict_le_self
  have hr_loc : MemLpLoc p.period (fun x => rep (k a b) x.1 x.2 i) 2 :=
    memLpLoc_mono (fun R => hm.mono_measure (hle R)) q0E_two_le
  have hr'_loc : MemLpLoc p.period (fun x => rep (t a b c) x.1 x.2 i) 2 :=
    memLpLoc_mono (fun R => hm'.mono_measure (hle R)) q0E_two_le
  exact weakDyS_add_loc2 c he_loc he'_loc hr_loc hr'_loc hw_e hw_r

/-- Abstract core of `GEQIbp2Step`: one weak integration by parts in `y_j` on each of the four
products in `GEQuadField`. -/
theorem gEQIbp2_step_core {P : ℝ} [Fact (0 < P)]
    (U : Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (D : Fin 3 → Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (DD : Fin 3 → Fin 3 → Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (D3 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ × UnforcedLeray.Space → ℂ)
    (hU2 : ∀ i, MemLpLoc P (U i) (2 * UnforcedLeray.B0412.q0E))
    (hD2 : ∀ a b, MemLpLoc P (D a b) (2 * UnforcedLeray.B0412.q0E))
    (hDD2 : ∀ a b c, MemLpLoc P (DD a b c) (2 * UnforcedLeray.B0412.q0E))
    (hD3q : ∀ a b c d, MemLpLoc P (D3 a b c d) UnforcedLeray.B0412.q0E)
    (hWU : ∀ a b, WeakDyS P a (U b) (D a b))
    (hWD : ∀ a b c, WeakDyS P b (D a c) (DD a b c))
    (hWDD : ∀ a b c d, WeakDyS P c (DD a b d) (D3 a b c d))
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (hΦ : IsPhaseTest P Φ) (j l : Fin 3) :
    pairF P (dy j Φ) (fun x => WithLp.toLp 2 (fun i => -∑ m : Fin 3,
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))) =
      pairF P Φ (fun x => WithLp.toLp 2 (fun i => ∑ m : Fin 3,
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x))) := by
  have hU2' : ∀ i, MemLpLoc P (U i) 2 := fun i => memLpLoc_mono (hU2 i) two_le_two_mul_q0E
  have hD2' : ∀ a b, MemLpLoc P (D a b) 2 := fun a b => memLpLoc_mono (hD2 a b) two_le_two_mul_q0E
  have hDD2' : ∀ a b c, MemLpLoc P (DD a b c) 2 :=
    fun a b c => memLpLoc_mono (hDD2 a b c) two_le_two_mul_q0E
  have hD32' : ∀ a b c d, MemLpLoc P (D3 a b c d) 2 :=
    fun a b c d => memLpLoc_mono (hD3q a b c d) q0E_two_le
  have hDq : ∀ a b, MemLpLoc P (D a b) UnforcedLeray.B0412.q0E :=
    fun a b => memLpLoc_mono (hD2 a b) q0E_le_two_mul_q0E
  have hDDq : ∀ a b c, MemLpLoc P (DD a b c) UnforcedLeray.B0412.q0E :=
    fun a b c => memLpLoc_mono (hDD2 a b c) q0E_le_two_mul_q0E
  have hφ : ∀ i, IsPhaseTest P (fun y => Φ y i) := fun i => isPhaseTest_comp_coord hΦ i
  have hφd : ∀ i, IsPhaseTest P (dy j (fun y => Φ y i)) := fun i => (hφ i).dy j
  have hdyc : ∀ i, dy j (fun y => Φ y i) = fun y => dy j Φ y i := fun i =>
    funext fun y => dy_comp_coord hΦ.smooth j i y
  have hIBP : ∀ i m, phaseInt P (fun x => dy j (fun y => Φ y i) x *
      (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x)) =
      -phaseInt P (fun x => Φ x i *
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x)) := by
    intro i m
    have h1 := ((weakMulRule : WeakMulRule) P j (DD m l m) (U i) (D3 m l j m) (D j i)
      (hDD2 m l m) (hU2 i) (hD3q m l j m) (hDq j i) (hWDD m l j m) (hWU j i)) _ (hφ i)
    have h2 := ((weakMulRule : WeakMulRule) P j (D m m) (D l i) (DD m j m) (DD l j i)
      (hD2 m m) (hD2 l i) (hDDq m j m) (hDDq l j i) (hWD m j m) (hWD l j i)) _ (hφ i)
    have h3 := ((weakMulRule : WeakMulRule) P j (D l m) (D m i) (DD l j m) (DD m j i)
      (hD2 l m) (hD2 m i) (hDDq l j m) (hDDq m j i) (hWD l j m) (hWD m j i)) _ (hφ i)
    have h4 := ((weakMulRule : WeakMulRule) P j (U m) (DD m l i) (D j m) (D3 m l j i)
      (hU2 m) (hDD2 m l i) (hDq j m) (hD3q m l j i) (hWU j m) (hWDD m l j i)) _ (hφ i)
    have intL1 := integrable_test_mul2 (hφd i) (hDD2' m l m) (hU2' i)
    have intL2 := integrable_test_mul2 (hφd i) (hD2' m m) (hD2' l i)
    have intL3 := integrable_test_mul2 (hφd i) (hD2' l m) (hD2' m i)
    have intL4 := integrable_test_mul2 (hφd i) (hU2' m) (hDD2' m l i)
    have intL12 := integrable_test_mul_sum2 (hφd i) (hDD2' m l m) (hU2' i) (hD2' m m) (hD2' l i)
    have intL123 : Integrable (fun x => dy j (fun y => Φ y i) x *
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x))
        (volume.restrict (phaseCell P)) := by
      refine (intL12.add intL3).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply]; ring
    have intR1 := integrable_test_mul_sum2 (hφ i) (hD32' m l j m) (hU2' i) (hDD2' m l m) (hD2' j i)
    have intR2 := integrable_test_mul_sum2 (hφ i) (hDD2' m j m) (hD2' l i) (hD2' m m) (hDD2' l j i)
    have intR3 := integrable_test_mul_sum2 (hφ i) (hDD2' l j m) (hD2' m i) (hD2' l m) (hDD2' m j i)
    have intR4 := integrable_test_mul_sum2 (hφ i) (hD2' j m) (hDD2' m l i) (hU2' m) (hD32' m l j i)
    have intR12 := integrable_test_mul_sum4 (hφ i) (hD32' m l j m) (hU2' i)
      (hDD2' m l m) (hD2' j i) (hDD2' m j m) (hD2' l i) (hD2' m m) (hDD2' l j i)
    have intR34 := integrable_test_mul_sum4 (hφ i) (hDD2' l j m) (hD2' m i)
      (hD2' l m) (hDD2' m j i) (hD2' j m) (hDD2' m l i) (hU2' m) (hD32' m l j i)
    have hsplitL : phaseInt P (fun x => dy j (fun y => Φ y i) x *
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x)) =
        phaseInt P (fun x => dy j (fun y => Φ y i) x * (DD m l m x * U i x)) +
        phaseInt P (fun x => dy j (fun y => Φ y i) x * (D m m x * D l i x)) +
        phaseInt P (fun x => dy j (fun y => Φ y i) x * (D l m x * D m i x)) +
        phaseInt P (fun x => dy j (fun y => Φ y i) x * (U m x * DD m l i x)) := by
      rw [← phaseInt_add_cell intL1 intL2]
      have h12 : (fun x => dy j (fun y => Φ y i) x * (DD m l m x * U i x) +
          dy j (fun y => Φ y i) x * (D m m x * D l i x)) =
          fun x => dy j (fun y => Φ y i) x * (DD m l m x * U i x + D m m x * D l i x) := by
        funext x; ring
      rw [h12, ← phaseInt_add_cell intL12 intL3]
      have h123 : (fun x => dy j (fun y => Φ y i) x * (DD m l m x * U i x + D m m x * D l i x) +
          dy j (fun y => Φ y i) x * (D l m x * D m i x)) =
          fun x => dy j (fun y => Φ y i) x *
            (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x) := by
        funext x; ring
      rw [h123, ← phaseInt_add_cell intL123 intL4]
      congr 1; funext x; ring
    have hsplitR : phaseInt P (fun x => Φ x i *
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x)) =
        phaseInt P (fun x => Φ x i * (D3 m l j m x * U i x + DD m l m x * D j i x)) +
        phaseInt P (fun x => Φ x i * (DD m j m x * D l i x + D m m x * DD l j i x)) +
        phaseInt P (fun x => Φ x i * (DD l j m x * D m i x + D l m x * DD m j i x)) +
        phaseInt P (fun x => Φ x i * (D j m x * DD m l i x + U m x * D3 m l j i x)) := by
      have e12 : phaseInt P (fun x => Φ x i * (D3 m l j m x * U i x + DD m l m x * D j i x)) +
          phaseInt P (fun x => Φ x i * (DD m j m x * D l i x + D m m x * DD l j i x)) =
          phaseInt P (fun x => Φ x i * (D3 m l j m x * U i x + DD m l m x * D j i x +
            DD m j m x * D l i x + D m m x * DD l j i x)) := by
        rw [← phaseInt_add_cell intR1 intR2]; congr 1; funext x; ring
      have e34 : phaseInt P (fun x => Φ x i * (DD l j m x * D m i x + D l m x * DD m j i x)) +
          phaseInt P (fun x => Φ x i * (D j m x * DD m l i x + U m x * D3 m l j i x)) =
          phaseInt P (fun x => Φ x i * (DD l j m x * D m i x + D l m x * DD m j i x +
            D j m x * DD m l i x + U m x * D3 m l j i x)) := by
        rw [← phaseInt_add_cell intR3 intR4]; congr 1; funext x; ring
      rw [add_assoc (phaseInt P _ + phaseInt P _), e12, e34, ← phaseInt_add_cell intR12 intR34]
      congr 1; funext x; ring
    rw [hsplitL, h1, h2, h3, h4, hsplitR]
    ring
  -- expand left and right sides into sums over i, m
  have hLint : ∀ i m, Integrable (fun x => dy j (fun y => Φ y i) x *
      (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))
      (volume.restrict (phaseCell P)) := fun i m =>
    integrable_test_mul_sum4 (hφd i) (hDD2' m l m) (hU2' i) (hD2' m m) (hD2' l i)
      (hD2' l m) (hD2' m i) (hU2' m) (hDD2' m l i)
  have hLint_all : Integrable (fun x => ∑ i : Fin 3, ∑ m : Fin 3, dy j (fun y => Φ y i) x *
      (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))
      (volume.restrict (phaseCell P)) :=
    integrable_sum_cell Finset.univ (fun i _ =>
      integrable_sum_cell Finset.univ (fun m _ => hLint i m))
  have hdotL : ∀ x, dotL (dy j Φ x) (WithLp.toLp 2 (fun i => -∑ m : Fin 3,
      (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))) =
      -∑ i : Fin 3, ∑ m : Fin 3, dy j (fun y => Φ y i) x *
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x) := by
    intro x
    simp only [hdyc, dotL_apply, PiLp.toLp_apply, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  have hLHS : pairF P (dy j Φ) (fun x => WithLp.toLp 2 (fun i => -∑ m : Fin 3,
      (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))) =
      -∑ i : Fin 3, ∑ m : Fin 3, phaseInt P (fun x => dy j (fun y => Φ y i) x *
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x)) := by
    unfold pairF
    simp only [hdotL]
    rw [phaseInt_neg_cell hLint_all]
    congr 1
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ m : Fin 3, dy j (fun y => Φ y i) x *
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))
      (fun i _ => integrable_sum_cell Finset.univ (fun m _ => hLint i m))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun m x => dy j (fun y => Φ y i) x *
        (DD m l m x * U i x + D m m x * D l i x + D l m x * D m i x + U m x * DD m l i x))
      (fun m _ => hLint i m)]
  have hRint : ∀ i m, Integrable (fun x => Φ x i *
      (D3 m l j m x * U i x + DD m l m x * D j i x +
        DD m j m x * D l i x + D m m x * DD l j i x +
        DD l j m x * D m i x + D l m x * DD m j i x +
        D j m x * DD m l i x + U m x * D3 m l j i x))
      (volume.restrict (phaseCell P)) := by
    intro i m
    have intR12 := integrable_test_mul_sum4 (hφ i) (hD32' m l j m) (hU2' i)
      (hDD2' m l m) (hD2' j i) (hDD2' m j m) (hD2' l i) (hD2' m m) (hDD2' l j i)
    have intR34 := integrable_test_mul_sum4 (hφ i) (hDD2' l j m) (hD2' m i)
      (hD2' l m) (hDD2' m j i) (hD2' j m) (hDD2' m l i) (hU2' m) (hD32' m l j i)
    refine (intR12.add intR34).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]; ring
  have hdotR : ∀ x, dotL (Φ x) (WithLp.toLp 2 (fun i => ∑ m : Fin 3,
      (D3 m l j m x * U i x + DD m l m x * D j i x +
        DD m j m x * D l i x + D m m x * DD l j i x +
        DD l j m x * D m i x + D l m x * DD m j i x +
        D j m x * DD m l i x + U m x * D3 m l j i x))) =
      ∑ i : Fin 3, ∑ m : Fin 3, Φ x i *
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x) := by
    intro x
    simp only [dotL_apply, PiLp.toLp_apply, Finset.mul_sum]
  have hRHS : pairF P Φ (fun x => WithLp.toLp 2 (fun i => ∑ m : Fin 3,
      (D3 m l j m x * U i x + DD m l m x * D j i x +
        DD m j m x * D l i x + D m m x * DD l j i x +
        DD l j m x * D m i x + D l m x * DD m j i x +
        D j m x * DD m l i x + U m x * D3 m l j i x))) =
      ∑ i : Fin 3, ∑ m : Fin 3, phaseInt P (fun x => Φ x i *
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x)) := by
    unfold pairF
    simp only [hdotR]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ m : Fin 3, Φ x i *
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x))
      (fun i _ => integrable_sum_cell Finset.univ (fun m _ => hRint i m))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun m x => Φ x i *
        (D3 m l j m x * U i x + DD m l m x * D j i x +
          DD m j m x * D l i x + D m m x * DD l j i x +
          DD l j m x * D m i x + D l m x * DD m j i x +
          D j m x * DD m l i x + U m x * D3 m l j i x))
      (fun m _ => hRint i m)]
  rw [hLHS, hRHS, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hIBP i m, neg_neg]

end Quad2IbpSub

/-- **`gEQIbp2_step : GEQIbp2Step`** (source 2552-2559, 2531, 1515-1531). -/
theorem gEQIbp2_step : GEQIbp2Step := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := gEQWeakU lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := gEQWeakDu lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := gEQMem lam q hq dm dp hdm
  obtain ⟨n4, hn4, H4⟩ := gEGradL2p lam q hq dm dp hdm
  have hn5 : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min (min n1 n2) (min n3 n4)) (min 1 (dm ^ 3 / 12)),
    lt_min (lt_min (lt_min hn1 hn2) (lt_min hn3 hn4)) (lt_min one_pos hn5), ?_⟩
  intro p d hreg hν hmode z g hd k t hyp j l Φ hΦ
  have e1 : p.ν ≤ n1 :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have e2 : p.ν ≤ n2 :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have e3 : p.ν ≤ n3 :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e4 : p.ν ≤ n4 :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have e5 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e6 : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg e6
  have hyp1 : GEQHyp p z g k := ⟨hyp.2.1, H4 p d hreg e4 hmode z g hd⟩
  have hU := H1 p d hreg e1 hmode z g hd k hyp1
  have hD := H2 p d hreg e2 hmode z g hd k hyp1
  obtain ⟨hMu, hMd, -⟩ := H3 p d hreg e3 hmode z g hd k hyp1
  exact Quad2IbpSub.gEQIbp2_step_core (P := p.period)
    (U := fun i x => p.uOf z x i)
    (D := fun a b x => GEQDu p z g a x b)
    (DD := fun a b c x => GEQDdu p z g k a b x c)
    (D3 := fun a b c m x => GEQD3u p z t a b c x m)
    hMu hMd
    (fun a b c => Quad2IbpSub.memLpLoc_ddu_2q0 hq hreg e5 hP1 hmode z hyp a b c)
    (fun a b c m => Quad2IbpSub.memLpLoc_d3u_q0 hq hreg e5 hmode z t a b c m)
    (fun a b => hU a b)
    (fun a b c => hD a b c)
    (fun a b c m => Quad2IbpSub.weakDyS_ddu hq hreg e5 hmode z hyp a b c m)
    Φ hΦ j l

end UnforcedLeray.Short.PartIIIb.Concrete
