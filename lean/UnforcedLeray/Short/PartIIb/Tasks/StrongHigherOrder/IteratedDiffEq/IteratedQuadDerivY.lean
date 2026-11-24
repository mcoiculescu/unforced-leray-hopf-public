import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedQuadDerivY.Jets

/-!
# `PartII-b:S2/1/4`: `IteratedQuadDerivY` (all-order quadratic advection in `Y_{q₀}`)

Source of record: `the November 2 reference manuscript`,
lines 2552-2559: "Inductively, if derivatives through order `k` are in the graph, all factors
through order `k` are bounded and derivatives through order `k+2` are in `Y_p`. In each
order-`(k+1)` derivative of `w·∇w`, one factor has order at most `k`. Put it in `L^∞` and the
other in `Y_p`".

For a solenoidal test `Φ`, `iterDy β Φ` is solenoidal, so `QuadRel` gives
`⟪∂^β Φ, gQ⟫ = -⟪(u·∇)∂^β Φ, u⟫ = -∑_{i,m} ∫ ∂_m ∂^β Φ_i · u_m u_i`.  All `k + 2` derivatives
are moved onto `u_m u_i` (`IterQuadSub.ibp_lb`, one `weakMulRule` per step), giving
`⟪Φ, F⟫` with `F_i = (-1)^{k+1} ∑_m D^{m::β}(u_m u_i)` expanded by Leibniz (`IterQuadSub.lb`).
Each Leibniz product `D^a u_m · D^b u_i` (`|a| + |b| = k + 2`) is in `L^{q₀}` of the cell
(`IterQuadSub.uWord_prod`): if both orders are in `1, …, k + 1`, both factors are in `L^{2q₀}`
(`gradL2pIBP` from the bounded order `≤ k`, and the inlet decay `(1+|y|)^{-1}`); otherwise one
factor is `u ∈ L^∞` and the other has order `k + 2`.  Hence `F` represents some `Fq ∈ Y_{q₀}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Cons.C03.Concrete (Params phaseInt phaseCell pairF advT rep)
open IterQuadSub IterDiffEqSub
open scoped ContDiff ENNReal

namespace IterQuadSub

theorem phaseInt_const_mul (P : ℝ) (c : ℂ) (G : ℝ × UnforcedLeray.Space → ℂ) :
    phaseInt P (fun x => c * G x) = c * phaseInt P G := by
  unfold phaseInt
  simp only [MeasureTheory.integral_const_mul]
  rw [mul_smul_comm]

end IterQuadSub

/-- **`PartII-b:S2/1/4`** (SP 2552-2559). -/
theorem iteratedQuadDerivY_proof : UnforcedLeray.Short.IIb.IteratedQuadDerivY := by
  intro Sig lam q _hSig hq dm dp hdm
  refine ⟨min 1 (dm ^ 3 / 12), lt_min one_pos (by positivity), ?_⟩
  intro p d hreg hν _hSigp hmode z k _hk g hg G hG gQ hQ β
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg (hν.trans (min_le_right _ _))
  have hT : HasPhaseGradTower p.period UnforcedLeray.B0412.q0E (k + 1) (p.wOf z) :=
    wOf_hasPhaseGradTower p hP1 z k (g k le_rfl) (hg k le_rfl) G hG
  have hD : ∀ a : List (Fin 3), a.length ≤ k →
      dWord a (p.wOf z) ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E := by
    intro a ha
    have h1 := dWord_ofFn_of_iterated a.length (p.wOf z)
      (fun α => (g a.length ha α : Yq p.period UnforcedLeray.B0412.q0E)) (hg a.length ha) a.get
    rw [List.ofFn_get] at h1
    rw [h1]
    exact (g a.length ha a.get).2
  set L : List (Fin 3) := List.ofFn β with hL
  have hLlen : ∀ m : Fin 3, (m :: L).length = k + 2 := fun m => by
    simp [hL]
  -- the Leibniz products
  set fW : Fin 3 → List (Fin 3) → ℝ × UnforcedLeray.Space → ℂ :=
    fun c a x => uWord p z a x c with hfW
  set s : ℂ := (-1) ^ (k + 1) with hs
  set F : ℝ × UnforcedLeray.Space → CVec3 := fun x =>
    WithLp.toLp 2 (fun i => ∑ m : Fin 3, s * lb (fW m) (fW i) (m :: L) x) with hFdef
  have hFi : ∀ (i : Fin 3) (x : ℝ × UnforcedLeray.Space),
      F x i = ∑ m : Fin 3, s * lb (fW m) (fW i) (m :: L) x := fun i x => rfl
  -- measurability
  have hlbM : ∀ m i : Fin 3, Measurable (lb (fW m) (fW i) (m :: L)) := by
    intro m i
    refine lb_closure (fun G => Measurable G) (fun F G hF hG => hF.add hG) (m :: L) _ _ ?_
    intro a b _
    exact (measurable_coord' (uWord_measurable hq hreg hν1 hmode z a).measurable m).mul
      (measurable_coord' (uWord_measurable hq hreg hν1 hmode z b).measurable i)
  have hmcomp : ∀ i : Fin 3, Measurable (fun x => F x i) := by
    intro i
    have e1 : (fun x => F x i) = fun x => ∑ m : Fin 3, s * lb (fW m) (fW i) (m :: L) x :=
      funext fun x => hFi i x
    rw [e1]
    exact Finset.measurable_sum _ fun m _ => (hlbM m i).const_mul s
  have hSMpi : StronglyMeasurable (fun x => (fun i : Fin 3 => F x i)) :=
    (measurable_pi_lambda _ hmcomp).stronglyMeasurable
  have hSM : StronglyMeasurable F :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp_stronglyMeasurable hSMpi
  -- periodicity
  have hlbP : ∀ m i : Fin 3, ∀ x : ℝ × UnforcedLeray.Space,
      lb (fW m) (fW i) (m :: L) (x.1 + p.period, x.2) = lb (fW m) (fW i) (m :: L) x := by
    intro m i
    refine lb_closure (fun G => ∀ x : ℝ × UnforcedLeray.Space, G (x.1 + p.period, x.2) = G x)
      (fun F G hF hG x => by simp only [hF x, hG x]) (m :: L) _ _ ?_
    intro a b _ x
    simp only [hfW, uWord_periodic]
  have hper : ∀ x : ℝ × UnforcedLeray.Space, F (x.1 + p.period, x.2) = F x := by
    intro x
    simp only [hFdef, hlbP]
  -- integrability
  have hlbL : ∀ m i : Fin 3, MemLp (lb (fW m) (fW i) (m :: L)) UnforcedLeray.B0412.q0E
      (cellMeasure p.period) := by
    intro m i
    refine lb_closure (fun G => MemLp G UnforcedLeray.B0412.q0E (cellMeasure p.period))
      (fun F G hF hG => hF.add hG) (m :: L) _ _ ?_
    intro a b hab
    exact uWord_prod hq hreg hν1 hmode hP1 z k hT hD a b (by rw [hab, hLlen]) m i
  have hcomp : ∀ i : Fin 3, MemLp (fun x => F x i) UnforcedLeray.B0412.q0E (cellMeasure p.period) := by
    intro i
    have e1 : (fun x => F x i) = fun x => ∑ m ∈ Finset.univ, s * lb (fW m) (fW i) (m :: L) x :=
      funext fun x => hFi i x
    rw [e1]
    exact memLp_finsetSum Finset.univ fun m _ => (hlbL m i).const_mul s
  have hLF : MemLp F UnforcedLeray.B0412.q0E (cellMeasure p.period) := MeasureTheory.memLp_piLp_iff.2 hcomp
  obtain ⟨Fq, hFq⟩ := exists_Yq_of_field F hSM hper hLF
  refine ⟨Fq, fun Φ hΦ => ?_⟩
  rw [hQ (iterDy β Φ) (isSolTest_iterDy β hΦ), hFq Φ hΦ.1, ← uWord_nil p z]
  -- the integration by parts for every pair of components
  have hφ : ∀ i : Fin 3, IsPhaseTest p.period (fun x => Φ x i) := fun i => isPhaseTest_comp_coord hΦ.1 i
  have hloc2 : ∀ (c : Fin 3) (a : List (Fin 3)), MemLpLoc p.period (fW c a) 2 := fun c a =>
    memLpLoc_mono (uWord_locq hq hreg hν1 hmode z a c) q0E_two_le
  have key : ∀ i m : Fin 3,
      phaseInt p.period (fun x => iterDyL (m :: L) (fun y => Φ y i) x *
        (fW m [] x * fW i [] x)) =
        (-1) ^ (k + 2) * phaseInt p.period (fun x => Φ x i * lb (fW m) (fW i) (m :: L) x) := by
    intro i m
    rw [← hLlen m]
    refine ibp_lb (m :: L) (fW m) (fW i) ?_ ?_ ?_ ?_ ?_ ?_ (fun y => Φ y i) (hφ i)
    · intro a ha j
      exact uWord_weak hq hreg hν1 hmode z k hT a (by rw [hLlen m] at ha; omega) j m
    · intro a ha j
      exact uWord_weak hq hreg hν1 hmode z k hT a (by rw [hLlen m] at ha; omega) j i
    · intro a ha
      exact uWord_loc2 hq hreg hν1 hmode hP1 z k hT hD a (by rw [hLlen m] at ha; omega) m
    · intro a ha
      exact uWord_loc2 hq hreg hν1 hmode hP1 z k hT hD a (by rw [hLlen m] at ha; omega) i
    · intro a _
      exact uWord_locq hq hreg hν1 hmode z a m
    · intro a _
      exact uWord_locq hq hreg hν1 hmode z a i
  -- expansion of the left side
  have hΨ : ContDiff ℝ ∞ (iterDy β Φ) := contDiff_iterDy β hΦ.1.smooth
  have hcomp_d : ∀ (m i : Fin 3) (x : ℝ × UnforcedLeray.Space),
      dy m (iterDy β Φ) x i = iterDyL (m :: L) (fun y => Φ y i) x := by
    intro m i x
    rw [← dy_comp_coord hΨ m i x, iterDy_eq_iterDyL β Φ,
      iterDyL_comp_coord (List.ofFn β) hΦ.1.smooth i]
    rfl
  have hpt : ∀ x, dotL (advT (uWord p z []) (iterDy β Φ) x) (uWord p z [] x) =
      ∑ i : Fin 3, ∑ m : Fin 3, iterDyL (m :: L) (fun y => Φ y i) x *
        (fW m [] x * fW i [] x) := by
    intro x
    simp only [advT, dotL_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, smul_eq_mul,
      Finset.sum_mul, Finset.sum_apply, Pi.smul_apply, PiLp.smul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    rw [hcomp_d m i x]
    simp only [hfW]
    ring
  have hint1 : ∀ i m : Fin 3, Integrable (fun x => iterDyL (m :: L) (fun y => Φ y i) x *
      (fW m [] x * fW i [] x)) (volume.restrict (phaseCell p.period)) := fun i m =>
    integrable_test_mul2 (isPhaseTest_iterDyL (m :: L) (hφ i)) (hloc2 m []) (hloc2 i [])
  have hLHS : pairF p.period (advT (uWord p z []) (iterDy β Φ)) (uWord p z []) =
      ∑ i : Fin 3, ∑ m : Fin 3, phaseInt p.period (fun x => iterDyL (m :: L) (fun y => Φ y i) x *
        (fW m [] x * fW i [] x)) := by
    unfold pairF
    simp only [hpt]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ m : Fin 3, iterDyL (m :: L) (fun y => Φ y i) x *
        (fW m [] x * fW i [] x))
      (fun i _ => integrable_sum_cell Finset.univ (fun m _ => hint1 i m))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun m x => iterDyL (m :: L) (fun y => Φ y i) x * (fW m [] x * fW i [] x))
      (fun m _ => hint1 i m)]
  -- the right side
  have hQint : ∀ (i : Fin 3) (F G : ℝ × UnforcedLeray.Space → ℂ),
      Integrable (fun x => Φ x i * F x) (volume.restrict (phaseCell p.period)) →
      Integrable (fun x => Φ x i * G x) (volume.restrict (phaseCell p.period)) →
      Integrable (fun x => Φ x i * (F x + G x)) (volume.restrict (phaseCell p.period)) := by
    intro i F G hF hG
    refine (hF.add hG).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hint2 : ∀ i m : Fin 3, Integrable (fun x => Φ x i * lb (fW m) (fW i) (m :: L) x)
      (volume.restrict (phaseCell p.period)) := by
    intro i m
    refine lb_closure (fun G => Integrable (fun x => Φ x i * G x) (volume.restrict (phaseCell p.period)))
      (hQint i) (m :: L) _ _ ?_
    intro a b _
    exact integrable_test_mul2 (hφ i) (hloc2 m a) (hloc2 i b)
  have hint3 : ∀ i m : Fin 3, Integrable (fun x => s * (Φ x i * lb (fW m) (fW i) (m :: L) x))
      (volume.restrict (phaseCell p.period)) := fun i m => (hint2 i m).const_mul s
  have hdotF : ∀ x, dotL (Φ x) (F x) =
      ∑ i : Fin 3, ∑ m : Fin 3, s * (Φ x i * lb (fW m) (fW i) (m :: L) x) := by
    intro x
    rw [dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi i x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hRHS : pairF p.period Φ F = ∑ i : Fin 3, ∑ m : Fin 3,
      s * phaseInt p.period (fun x => Φ x i * lb (fW m) (fW i) (m :: L) x) := by
    unfold pairF
    simp only [hdotF]
    rw [phaseInt_sum_cell Finset.univ
      (F := fun i x => ∑ m : Fin 3, s * (Φ x i * lb (fW m) (fW i) (m :: L) x))
      (fun i _ => integrable_sum_cell Finset.univ (fun m _ => hint3 i m))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phaseInt_sum_cell Finset.univ
      (F := fun m x => s * (Φ x i * lb (fW m) (fW i) (m :: L) x)) (fun m _ => hint3 i m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact phaseInt_const_mul p.period s _
  rw [hLHS, hRHS, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [key i m, hs, pow_succ (-1 : ℂ) (k + 1)]
  ring

end UnforcedLeray.Short.IIb
