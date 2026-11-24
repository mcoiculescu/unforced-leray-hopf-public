import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.U
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.RepWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.WeakMulRule
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Sub.PartIIIb_C_ward_12_3_1_2_7_6.Holder

/-!
# Pointwise quadratic convection field and one-step weak IBP (`PartII-b:Q1` helper)

Defines the unprojected bilinear convection field
`quadFieldPtw p z z' g g' x_i = ∑_k (GEQDu p z g k x_k · uOf z' x_i + uOf z x_k · GEQDu p z' g' k x_i)`
and proves:
* `quadFieldPtw_pairF`: `-pairF (advT (p.uOf z) Φ) (p.uOf z') = pairF Φ (quadFieldPtw p z z' g g')`
  for every phase test `Φ`, by one weak integration by parts (`weakMulRule`);
* `quadFieldPtw_periodic`: `P`-periodicity in `τ`;
* `stronglyMeasurable_quadFieldPtw`: joint strong measurability on `ℝ × ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.B0412
open UnforcedLeray.Cons.C03.Concrete (Params pairF advT phaseInt phaseCell rep)
open UnforcedLeray.Short.PartIIa (HasGrad)
open UnforcedLeray.Short.PartIIIb.Concrete

/-- Pointwise bilinear convection field after one spatial integration by parts:
`i ↦ ∑_k ((∂_k u_k) u'_i + u_k (∂_k u'_i))`. -/
def quadFieldPtw (p : Params) (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E)
    (x : ℝ × Space) : CVec3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    ∑ k : Fin 3, (GEQDu p z g k x k * p.uOf z' x i + p.uOf z x k * GEQDu p z' g' k x i)

@[simp]
theorem quadFieldPtw_apply (p : Params) (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E)
    (x : ℝ × Space) (i : Fin 3) :
    quadFieldPtw p z z' g g' x i =
      ∑ k : Fin 3, (GEQDu p z g k x k * p.uOf z' x i + p.uOf z x k * GEQDu p z' g' k x i) :=
  rfl

/-- Local `L^r` membership of a coordinate of `p.eFun (p.coord z)` when `p.ν ≤ 1`. -/
theorem memLpLoc_eFun_coord (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) (i : Fin 3) (r : ℝ≥0∞) :
    MemLpLoc p.period (fun x => p.eFun (p.coord z) x i) r := by
  intro R
  have hsm : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  exact memLp_ddu_loc p.period R
    (f := fun x => p.eFun (p.coord z) x i)
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hsm.continuous) r

/-- Local `L^r` membership of a coordinate of `dy j (p.eFun (p.coord z))` when `p.ν ≤ 1`. -/
theorem memLpLoc_dy_eFun_coord (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) (j i : Fin 3) (r : ℝ≥0∞) :
    MemLpLoc p.period (fun x => dy j (p.eFun (p.coord z)) x i) r := by
  intro R
  have hsm : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  have hcont : Continuous (dy j (p.eFun (p.coord z))) := (contDiff_dyT hsm j).continuous
  exact memLp_ddu_loc p.period R
    (f := fun x => dy j (p.eFun (p.coord z)) x i)
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).continuous.comp hcont) r

/-- Local `L^{q₀}` membership of a coordinate of `rep f` for `f : Yq p.period q0E`. -/
theorem memLpLoc_rep_coord_q0E (p : Params) (f : Yq p.period q0E) (i : Fin 3) :
    MemLpLoc p.period (fun x => rep f x.1 x.2 i) q0E := by
  intro R
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hrep := UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell
    (q := q0E) (by simp [q0E]) f
  have hle : ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume.restrict (Metric.closedBall (0 : Space) R))) ≤
      (volume : Measure (ℝ × Space)).restrict
        (Ioc (0 : ℝ) p.period ×ˢ (univ : Set Space)) := by
    have : (volume : Measure (ℝ × Space)).restrict
        (Ioc (0 : ℝ) p.period ×ˢ (univ : Set Space)) =
        (volume.restrict (Ioc (0 : ℝ) p.period)).prod volume := by
      simpa only [Measure.volume_eq_prod] using
        (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
          (ν := (volume : Measure Space)) (Ioc 0 p.period)).symm
    rw [this]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have h1 := hrep.mono_measure hle
  exact ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp
    (by simp) h1 : _)

/-- Local `L^{q₀}` membership of `GEQDu p z g j` without `GEQHyp`: the inlet derivative is
smooth (`inlet_contDiff_joint`), and `rep (g j)` is in `L^{q₀}` on the period cell. -/
theorem memLpLoc_geqDu_q0E (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) (g : Fin 3 → Yq p.period q0E) (j i : Fin 3) :
    MemLpLoc p.period (fun x => GEQDu p z g j x i) q0E := by
  intro R
  have hA := memLpLoc_dy_eFun_coord lam q hq hreg hν hmode z j i q0E R
  have hB := memLpLoc_rep_coord_q0E p (g j) i R
  have hfun : (fun x : ℝ × Space => GEQDu p z g j x i) =
      fun x => dy j (p.eFun (p.coord z)) x i + rep (g j) x.1 x.2 i := by
    funext x
    simp [GEQDu]
  rw [hfun]
  exact hA.add hB

/-- Local `L^{2q₀}` membership of `p.uOf z` from an a.e. bound on `rep (p.wOf z)`. -/
theorem memLpLoc_uOf_of_bound (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) {M : ℝ} (hM : ∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ M)
    (i : Fin 3) :
    MemLpLoc p.period (fun x => p.uOf z x i) (2 * q0E) := by
  intro R
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hA := memLpLoc_eFun_coord lam q hq hreg hν hmode z i (2 * q0E) R
  have hB : MemLp (fun x : ℝ × Space => rep (p.wOf z) x.1 x.2)
      (2 * q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : Space) R))) :=
    memLp_phaseLoc_of_bound p.period R
      (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf z)) M hM _
  have hBi : MemLp (fun x : ℝ × Space => rep (p.wOf z) x.1 x.2 i)
      (2 * q0E)
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod
        (volume.restrict (Metric.closedBall (0 : Space) R))) :=
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).lipschitzWith.comp_memLp
      (by simp) hB : _)
  have hfun : (fun x : ℝ × Space => p.uOf z x i) =
      fun x => p.eFun (p.coord z) x i + rep (p.wOf z) x.1 x.2 i := by
    funext x
    simp [Params.uOf]
  rw [hfun]
  exact hA.add hBi

/-- A phase test times a locally `L²` function is integrable on the phase cell. -/
theorem integrable_test_mul1 {P : ℝ} [Fact (0 < P)] {ψ f : ℝ × Space → ℂ}
    (hψ : IsPhaseTest P ψ) (hf : MemLpLoc P f 2) :
    Integrable (fun x => ψ x * f x) (volume.restrict (phaseCell P)) := by
  have h1 : MemLpLoc P (fun _ : ℝ × Space => (1 : ℂ)) 2 :=
    fun R => memLp_ddu_loc P R continuous_const 2
  have h := integrable_test_mul2 hψ hf h1
  refine h.congr (ae_of_all _ fun x => ?_)
  simp

/-- Weak spatial derivative of `p.uOf z` when `p.ν ≤ 1`. -/
theorem weakDyS_uOf (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) (g : Fin 3 → Yq p.period q0E) (hd : HasGrad (p.wOf z) g)
    (a b : Fin 3) :
    WeakDyS p.period a (fun x => p.uOf z x b) (fun x => GEQDu p z g a x b) := by
  intro φ hφ
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hef : ContDiff ℝ ∞ (p.eFun (p.coord z)) := by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  let cC : CVec3 →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) b).restrictScalars ℝ
  have hs0 : ContDiff ℝ ∞ (fun x => p.eFun (p.coord z) x b) := cC.contDiff.comp hef
  have hc0 : dy a (fun x => p.eFun (p.coord z) x b) = fun x => dy a (p.eFun (p.coord z)) x b :=
    dy_clm cC (hef.differentiable (by simp)) a
  have hE : phaseInt p.period (fun x => dy a φ x * p.eFun (p.coord z) x b) =
      -phaseInt p.period (fun x => φ x * dy a (p.eFun (p.coord z)) x b) := by
    have h := weakDyS_of_smooth p.period a hs0 φ hφ
    rwa [hc0] at h
  have hW : phaseInt p.period (fun x => dy a φ x * rep (p.wOf z) x.1 x.2 b) =
      -phaseInt p.period (fun x => φ x * rep (g a) x.1 x.2 b) :=
    (gEQRepWeak p.period a (p.wOf z) (g a) (hd a) b).1 φ hφ
  have hE2 := memLpLoc_eFun_coord lam q hq hreg hν hmode z b 2
  have hW2 := memLpLoc_mono (memLpLoc_rep_coord_q0E p (p.wOf z) b) q0E_two_le
  have hDE2 := memLpLoc_dy_eFun_coord lam q hq hreg hν hmode z a b 2
  have hDW2 := memLpLoc_mono (memLpLoc_rep_coord_q0E p (g a) b) q0E_two_le
  have i1 := integrable_test_mul1 (hφ.dy a) hE2
  have i2 := integrable_test_mul1 (hφ.dy a) hW2
  have i3 := integrable_test_mul1 hφ hDE2
  have i4 := integrable_test_mul1 hφ hDW2
  have hL : phaseInt p.period (fun x => dy a φ x * p.uOf z x b) =
      phaseInt p.period (fun x => dy a φ x * p.eFun (p.coord z) x b) +
      phaseInt p.period (fun x => dy a φ x * rep (p.wOf z) x.1 x.2 b) := by
    rw [← phaseInt_add_cell i1 i2]
    congr 1
    funext x
    simp only [Params.uOf, PiLp.add_apply]
    ring
  have hR2 : phaseInt p.period (fun x => φ x * GEQDu p z g a x b) =
      phaseInt p.period (fun x => φ x * dy a (p.eFun (p.coord z)) x b) +
      phaseInt p.period (fun x => φ x * rep (g a) x.1 x.2 b) := by
    rw [← phaseInt_add_cell i3 i4]
    congr 1
    funext x
    simp only [GEQDu, PiLp.add_apply]
    ring
  rw [hL, hR2, hE, hW, neg_add]

/-- Abstract one-step weak integration by parts for the bilinear convection pairing. -/
theorem quadIbp_core {P : ℝ} [Fact (0 < P)]
    (U U' : Fin 3 → ℝ × Space → ℂ)
    (D D' : Fin 3 → Fin 3 → ℝ × Space → ℂ)
    (hU2 : ∀ i, MemLpLoc P (U i) (2 * q0E))
    (hU'2 : ∀ i, MemLpLoc P (U' i) (2 * q0E))
    (hDq : ∀ a b, MemLpLoc P (D a b) q0E)
    (hD'q : ∀ a b, MemLpLoc P (D' a b) q0E)
    (hWU : ∀ a b, WeakDyS P a (U b) (D a b))
    (hWU' : ∀ a b, WeakDyS P a (U' b) (D' a b))
    (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    -pairF P (advT (fun x => WithLp.toLp 2 (fun i => U i x)) Φ)
        (fun x => WithLp.toLp 2 (fun i => U' i x)) =
      pairF P Φ (fun x => WithLp.toLp 2 (fun i => ∑ k : Fin 3,
        (D k k x * U' i x + U k x * D' k i x))) := by
  have hU2' : ∀ i, MemLpLoc P (U i) 2 := fun i => memLpLoc_mono (hU2 i) two_le_two_mul_q0E
  have hU'2' : ∀ i, MemLpLoc P (U' i) 2 := fun i => memLpLoc_mono (hU'2 i) two_le_two_mul_q0E
  have hD2' : ∀ a b, MemLpLoc P (D a b) 2 := fun a b => memLpLoc_mono (hDq a b) q0E_two_le
  have hD'2' : ∀ a b, MemLpLoc P (D' a b) 2 := fun a b => memLpLoc_mono (hD'q a b) q0E_two_le
  have hφ : ∀ i, IsPhaseTest P (fun y => Φ y i) := fun i => isPhaseTest_comp_coord hΦ i
  have hIBP1 : ∀ i k, phaseInt P (fun x => dy k (fun y => Φ y i) x * (U k x * U' i x)) =
      -phaseInt P (fun x => Φ x i * (D k k x * U' i x + U k x * D' k i x)) := by
    intro i k
    exact (weakMulRule : WeakMulRule) P k (fun x => U k x) (fun x => U' i x) (D k k) (D' k i)
      (hU2 k) (hU'2 i) (hDq k k) (hD'q k i) (hWU k k) (hWU' k i) _ (hφ i)
  have hpt : ∀ x, dotL (advT (fun x => WithLp.toLp 2 (fun i => U i x)) Φ x)
      (WithLp.toLp 2 (fun i => U' i x)) =
      ∑ i : Fin 3, ∑ k : Fin 3, dy k (fun y => Φ y i) x * (U k x * U' i x) := by
    intro x
    simp only [advT, dotL_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, smul_eq_mul,
      Finset.sum_mul, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [dy_comp_coord hΦ.smooth k i x]
    ring
  have hL_expand : pairF P (advT (fun x => WithLp.toLp 2 (fun i => U i x)) Φ)
      (fun x => WithLp.toLp 2 (fun i => U' i x)) =
      ∑ i : Fin 3, ∑ k : Fin 3, phaseInt P
        (fun x => dy k (fun y => Φ y i) x * (U k x * U' i x)) := by
    unfold pairF
    simp only [hpt]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ k : Fin 3, dy k (fun y => Φ y i) x * (U k x * U' i x))
      (fun i _ => integrable_sum_cell Finset.univ (fun k _ =>
        integrable_test_mul2 ((hφ i).dy k) (hU2' k) (hU'2' i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun k x => dy k (fun y => Φ y i) x * (U k x * U' i x))
      (fun k _ => integrable_test_mul2 ((hφ i).dy k) (hU2' k) (hU'2' i))]
  have hdotF : ∀ x, dotL (Φ x) (WithLp.toLp 2 (fun i => ∑ k : Fin 3,
      (D k k x * U' i x + U k x * D' k i x))) =
      ∑ i : Fin 3, ∑ k : Fin 3, Φ x i * (D k k x * U' i x + U k x * D' k i x) := by
    intro x
    simp only [dotL_apply, Finset.mul_sum]
  have hTint : ∀ i k, Integrable (fun x => Φ x i *
      (D k k x * U' i x + U k x * D' k i x))
      (volume.restrict (phaseCell P)) := fun i k =>
    integrable_test_mul_sum2 (hφ i) (hD2' k k) (hU'2' i) (hU2' k) (hD'2' k i)
  have hRHS : pairF P Φ (fun x => WithLp.toLp 2 (fun i => ∑ k : Fin 3,
      (D k k x * U' i x + U k x * D' k i x))) =
      ∑ i : Fin 3, ∑ k : Fin 3, phaseInt P (fun x => Φ x i *
        (D k k x * U' i x + U k x * D' k i x)) := by
    unfold pairF
    simp only [hdotF]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ k : Fin 3, Φ x i * (D k k x * U' i x + U k x * D' k i x))
      (fun i _ => integrable_sum_cell Finset.univ (fun k _ => hTint i k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun k x => Φ x i * (D k k x * U' i x + U k x * D' k i x))
      (fun k _ => hTint i k)]
  rw [hL_expand, hRHS, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hIBP1 i k, neg_neg]

/-- One-step weak integration by parts for `(p.uOf z, p.uOf z')` against any phase test `Φ`. -/
theorem quadFieldPtw_pairF (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E)
    (hd : HasGrad (p.wOf z) g) (hd' : HasGrad (p.wOf z') g')
    {M M' : ℝ}
    (hM : ∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z) x.1 x.2‖ ≤ M)
    (hM' : ∀ᵐ x ∂(phaseμ p.period), ‖rep (p.wOf z') x.1 x.2‖ ≤ M')
    (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest p.period Φ) :
    -pairF p.period (advT (p.uOf z) Φ) (p.uOf z') =
      pairF p.period Φ (quadFieldPtw p z z' g g') := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hU2 : ∀ i, MemLpLoc p.period (fun x => p.uOf z x i) (2 * q0E) :=
    fun i => memLpLoc_uOf_of_bound lam q hq hreg hν hmode z hM i
  have hU'2 : ∀ i, MemLpLoc p.period (fun x => p.uOf z' x i) (2 * q0E) :=
    fun i => memLpLoc_uOf_of_bound lam q hq hreg hν hmode z' hM' i
  have hDq : ∀ a b, MemLpLoc p.period (fun x => GEQDu p z g a x b) q0E :=
    fun a b => memLpLoc_geqDu_q0E lam q hq hreg hν hmode z g a b
  have hD'q : ∀ a b, MemLpLoc p.period (fun x => GEQDu p z' g' a x b) q0E :=
    fun a b => memLpLoc_geqDu_q0E lam q hq hreg hν hmode z' g' a b
  have hWU := weakDyS_uOf lam q hq hreg hν hmode z g hd
  have hWU' := weakDyS_uOf lam q hq hreg hν hmode z' g' hd'
  have hu : (fun x => WithLp.toLp 2 (fun i => p.uOf z x i)) = p.uOf z := rfl
  have hu' : (fun x => WithLp.toLp 2 (fun i => p.uOf z' x i)) = p.uOf z' := rfl
  have key := quadIbp_core (fun i x => p.uOf z x i) (fun i x => p.uOf z' x i)
    (fun a b x => GEQDu p z g a x b) (fun a b x => GEQDu p z' g' a x b)
    hU2 hU'2 hDq hD'q hWU hWU' Φ hΦ
  rw [hu, hu'] at key
  exact key

/-- `quadFieldPtw` is `p.period`-periodic in `τ` everywhere. -/
theorem quadFieldPtw_periodic (p : Params) (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E)
    (x : ℝ × Space) :
    quadFieldPtw p z z' g g' (x.1 + p.period, x.2) = quadFieldPtw p z z' g g' x := by
  have hper_e : ∀ w : p.Z, ∀ y : ℝ × Space,
      p.eFun (p.coord w) (y.1 + p.period, y.2) = p.eFun (p.coord w) y :=
    fun w y => eFun_period' p (p.coord w) y
  have hper_de : ∀ w : p.Z, ∀ k : Fin 3, ∀ y : ℝ × Space,
      dy k (p.eFun (p.coord w)) (y.1 + p.period, y.2) = dy k (p.eFun (p.coord w)) y :=
    fun w k y => dy_periodic' (hper_e w) k y
  have hU : ∀ w : p.Z, ∀ y : ℝ × Space,
      p.uOf w (y.1 + p.period, y.2) = p.uOf w y := by
    intro w y
    show p.eFun (p.coord w) (y.1 + p.period, y.2) + rep (p.wOf w) (y.1 + p.period) y.2 =
      p.eFun (p.coord w) y + rep (p.wOf w) y.1 y.2
    rw [hper_e w y, UnforcedLeray.Cons.C03.Concrete.rep_add_period]
  have hDu : ∀ (w : p.Z) (gw : Fin 3 → Yq p.period q0E) (k : Fin 3) (y : ℝ × Space),
      GEQDu p w gw k (y.1 + p.period, y.2) = GEQDu p w gw k y := by
    intro w gw k y
    show dy k (p.eFun (p.coord w)) (y.1 + p.period, y.2) + rep (gw k) (y.1 + p.period) y.2 =
      dy k (p.eFun (p.coord w)) y + rep (gw k) y.1 y.2
    rw [hper_de w k y, UnforcedLeray.Cons.C03.Concrete.rep_add_period]
  simp only [quadFieldPtw, hU, hDu]

/-- Joint strong measurability of `quadFieldPtw` for `p.ν ≤ 1`. -/
theorem stronglyMeasurable_quadFieldPtw (lam : ℂ) (q : Planar.Profile)
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z z' : p.Z) (g g' : Fin 3 → Yq p.period q0E) :
    StronglyMeasurable (quadFieldPtw p z z' g g') := by
  have : Fact (0 < p.period) := ⟨p.period_pos⟩
  have heC : ∀ w : p.Z, ContDiff ℝ ∞ (p.eFun (p.coord w)) := fun w => by
    unfold Params.eFun
    refine contDiff_realC.comp ?_
    refine ContDiff.sum fun l _ => ?_
    exact (inlet_contDiff_joint lam q hq hreg hν hmode l).const_smul _
  have hsU : ∀ w : p.Z, StronglyMeasurable (fun x : ℝ × Space => p.uOf w x) := fun w =>
    (heC w).continuous.stronglyMeasurable.add
      (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (p.wOf w))
  have hsDu : ∀ (w : p.Z) (gw : Fin 3 → Yq p.period q0E) (k : Fin 3),
      StronglyMeasurable (GEQDu p w gw k) := fun w gw k =>
    (dy_contDiff' (heC w) k).continuous.stronglyMeasurable.add
      (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep (gw k))
  have hmcomp : ∀ i : Fin 3, Measurable (fun x => quadFieldPtw p z z' g g' x i) := by
    intro i
    simp only [quadFieldPtw_apply]
    refine Finset.measurable_sum _ fun k _ => ?_
    have m1 := measurable_coord' (hsDu z g k).measurable k
    have m2 := measurable_coord' (hsU z').measurable i
    have m3 := measurable_coord' (hsU z).measurable k
    have m4 := measurable_coord' (hsDu z' g' k).measurable i
    exact (m1.mul m2).add (m3.mul m4)
  have hSMpi : StronglyMeasurable (fun x => fun i : Fin 3 => quadFieldPtw p z z' g g' x i) :=
    (measurable_pi_lambda _ hmcomp).stronglyMeasurable
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp_stronglyMeasurable hSMpi

end UnforcedLeray.Short.IIb
