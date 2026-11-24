import UnforcedLeray.Short.PartIIb.Sub.R1_3
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.ComposeFree

/-!
# Helper `ResponseOperator/RealGraph`: `realPhaseProjection` on the free graph `D`

Since `ofReV`, `reV`, and `imV` are continuous `ℝ`-linear maps on `Space` / `CVec3`, they commute
with `dτ`, `dy j`, `lapT`, `radialT`, and `driftT` on smooth phase tests. Consequently
`realPhaseProjection` preserves `HasPhaseOp (nuLapT ν)` and `HasPhaseOp driftT`, maps `D P ν q0E` to
itself, and commutes with `bodyOp P ν q0E 0`. By injectivity of `bodyOp P ν q0E 0` (`P ≤ 1`,
`0 < ν`), any `w : D P ν q0E` with `bodyOp P ν q0E 0 w ∈ realSub P q0E` satisfies
`(w : Yq P q0E) ∈ realSub P q0E`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.RespOp

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp UnforcedLeray.Short.PartIIa UnforcedLeray.Short.IIb

section ClmComm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {P : ℝ}

theorem dτ_comp_clm (L : E →L[ℝ] F) {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) :
    dτ (fun p => L (ψ p)) = fun p => L (dτ ψ p) := by
  funext p
  unfold dτ
  have hd : DifferentiableAt ℝ ψ p := (hψ.smooth.differentiable (by decide)) p
  exact congrArg (fun D => D (1, 0)) (L.hasFDerivAt.comp p hd.hasFDerivAt).fderiv

theorem dy_comp_clm (L : E →L[ℝ] F) {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) (j : Fin 3) :
    dy j (fun p => L (ψ p)) = fun p => L (dy j ψ p) := by
  funext p
  unfold dy
  have hd : DifferentiableAt ℝ ψ p := (hψ.smooth.differentiable (by decide)) p
  exact congrArg (fun D => D (0, coordinateVector j)) (L.hasFDerivAt.comp p hd.hasFDerivAt).fderiv

theorem lapT_comp_clm (L : E →L[ℝ] F) {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) :
    lapT (fun p => L (ψ p)) = fun p => L (lapT ψ p) := by
  funext p
  unfold lapT
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_comp_clm L hψ j, dy_comp_clm L (hψ.dy j) j]

theorem radialT_comp_clm (L : E →L[ℝ] F) {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) :
    radialT (fun p => L (ψ p)) = fun p => L (radialT ψ p) := by
  funext p
  unfold radialT
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_comp_clm L hψ j, map_smul]

theorem driftT_comp_clm (L : E →L[ℝ] F) {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) :
    driftT (fun p => L (ψ p)) = fun p => L (driftT ψ p) := by
  funext p
  unfold driftT
  rw [dτ_comp_clm L hψ, radialT_comp_clm L hψ, map_add, map_add, map_neg, map_smul, map_smul]

end ClmComm

theorem hasPhaseOp_realPhaseProjection {P : ℝ} [Fact (0 < P)]
    {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3}
    {LtR : (ℝ × Space → Space) → ℝ × Space → Space}
    (hTestR : ∀ φ, IsPhaseTest P φ → IsPhaseTest P (LtR φ))
    (hofReV : ∀ φ, IsPhaseTest P φ → Lt (fun x => ofReV (φ x)) = fun x => ofReV (LtR φ x))
    (hreV : ∀ Φ, IsPhaseTest P Φ → (fun x => UnforcedLeray.RieszLp.reV (Lt Φ x)) =
      LtR (fun x => UnforcedLeray.RieszLp.reV (Φ x)))
    (himV : ∀ Φ, IsPhaseTest P Φ → (fun x => UnforcedLeray.RieszLp.imV (Lt Φ x)) =
      LtR (fun x => UnforcedLeray.RieszLp.imV (Φ x)))
    {w a : Yq P q0E} (h : HasPhaseOp Lt w a) :
    HasPhaseOp Lt (realPhaseProjection w) (realPhaseProjection a) := by
  have hreal (φ : ℝ × Space → Space) (hφ : IsPhaseTest P φ) :
      phasePair P q0E (Lt (fun x => ofReV (φ x))) (realPhaseProjection w) =
        phasePair P q0E (fun x => ofReV (φ x)) (realPhaseProjection a) := by
    rw [hofReV φ hφ, phasePair_realPhaseProjection_of_realTest (LtR φ) (hTestR φ hφ) w,
      ← hofReV φ hφ, h (fun x => ofReV (φ x)) (hφ.clm_comp ofReV),
      ← phasePair_realPhaseProjection_of_realTest φ hφ a]
  intro Φ hΦ
  let φR : ℝ × Space → Space := fun x => UnforcedLeray.RieszLp.reV (Φ x)
  let φI : ℝ × Space → Space := fun x => UnforcedLeray.RieszLp.imV (Φ x)
  have hR : IsPhaseTest P φR := hΦ.clm_comp UnforcedLeray.RieszLp.reV
  have hI : IsPhaseTest P φI := hΦ.clm_comp UnforcedLeray.RieszLp.imV
  have hdecomp : Φ = (fun x => ofReV (φR x)) + Complex.I • (fun x => ofReV (φI x)) := by
    funext x
    have hd := ofReV_reV_add_ofImV_imV (Φ x)
    simpa [φR, φI, Pi.add_apply, Pi.smul_apply, I_smul_ofReV] using hd.symm
  have hdecompLt : Lt Φ =
      Lt (fun x => ofReV (φR x)) + Complex.I • Lt (fun x => ofReV (φI x)) := by
    funext x
    have hd := (ofReV_reV_add_ofImV_imV (Lt Φ x)).symm
    rw [← I_smul_ofReV] at hd
    have er := congrFun (hreV Φ hΦ) x
    have ei := congrFun (himV Φ hΦ) x
    have e1 := congrFun (hofReV φR hR) x
    have e2 := congrFun (hofReV φI hI) x
    dsimp only [φR, φI, Pi.add_apply, Pi.smul_apply] at er ei e1 e2 ⊢
    rw [hd, er, ei, ← e1, ← e2]
  have hRc : IsPhaseTest P (fun x => ofReV (φR x)) := hR.clm_comp ofReV
  have hIc : IsPhaseTest P (fun x => ofReV (φI x)) := hI.clm_comp ofReV
  have hLtRc : IsPhaseTest P (Lt (fun x => ofReV (φR x))) := by
    rw [hofReV φR hR]
    exact (hTestR φR hR).clm_comp ofReV
  have hLtIc : IsPhaseTest P (Lt (fun x => ofReV (φI x))) := by
    rw [hofReV φI hI]
    exact (hTestR φI hI).clm_comp ofReV
  rw [hdecompLt, phasePair_add hLtRc (hLtIc.const_smul Complex.I), phasePair_const_smul hLtIc,
    hreal φR hR, hreal φI hI, ← phasePair_const_smul hIc,
    ← phasePair_add hRc (hIc.const_smul Complex.I), ← hdecomp]

theorem hasPhaseOp_nuLapT_realPhaseProjection {P ν : ℝ} [Fact (0 < P)] {w a : Yq P q0E}
    (h : HasPhaseOp (nuLapT ν) w a) :
    HasPhaseOp (nuLapT ν) (realPhaseProjection w) (realPhaseProjection a) := by
  refine hasPhaseOp_realPhaseProjection (LtR := fun φ p => ν • lapT φ p)
    (fun φ hφ => hφ.lapT.const_smul ν) ?_ ?_ ?_ h
  · intro φ hφ
    funext p
    unfold nuLapT
    simp only [Pi.smul_apply, lapT_comp_clm ofReV hφ, map_smul]
  · intro Φ hΦ
    funext p
    unfold nuLapT
    simp only [Pi.smul_apply, lapT_comp_clm UnforcedLeray.RieszLp.reV hΦ, map_smul]
  · intro Φ hΦ
    funext p
    unfold nuLapT
    simp only [Pi.smul_apply, lapT_comp_clm UnforcedLeray.RieszLp.imV hΦ, map_smul]

theorem hasPhaseOp_driftT_realPhaseProjection {P : ℝ} [Fact (0 < P)] {w b : Yq P q0E}
    (h : HasPhaseOp driftT w b) :
    HasPhaseOp driftT (realPhaseProjection w) (realPhaseProjection b) :=
  hasPhaseOp_realPhaseProjection (LtR := driftT)
    (fun _ hφ => hφ.driftT)
    (fun _ hφ => driftT_comp_clm ofReV hφ)
    (fun _ hΦ => (driftT_comp_clm UnforcedLeray.RieszLp.reV hΦ).symm)
    (fun _ hΦ => (driftT_comp_clm UnforcedLeray.RieszLp.imV hΦ).symm) h

theorem realPhaseProjection_mem_D {P ν : ℝ} [Fact (0 < P)] (w : D P ν q0E) :
    realPhaseProjection (w : Yq P q0E) ∈ D P ν q0E :=
  mem_D.2 ⟨⟨realPhaseProjection (nuLapD w),
      hasPhaseOp_nuLapT_realPhaseProjection (hasPhaseOp_nuLapD w)⟩,
    ⟨realPhaseProjection (T0D w),
      hasPhaseOp_driftT_realPhaseProjection (hasPhaseOp_T0D w)⟩⟩

/-- Action of `realPhaseProjection` on `D P ν q0E`. -/
def realProjD {P ν : ℝ} [Fact (0 < P)] (w : D P ν q0E) : D P ν q0E :=
  ⟨realPhaseProjection (w : Yq P q0E), realPhaseProjection_mem_D w⟩

theorem bodyOp_zero_realProjD {P ν : ℝ} [Fact (0 < P)] (w : D P ν q0E) :
    bodyOp P ν q0E 0 (realProjD w) = realPhaseProjection (bodyOp P ν q0E 0 w) := by
  have ha : nuLapD (realProjD w) = realPhaseProjection (nuLapD w) :=
    nuLapD_eq (hasPhaseOp_nuLapT_realPhaseProjection (hasPhaseOp_nuLapD w))
  have hb : T0D (realProjD w) = realPhaseProjection (T0D w) :=
    T0D_eq (hasPhaseOp_driftT_realPhaseProjection (hasPhaseOp_T0D w))
  have hsmul : ∀ u : Yq P q0E, (1 / 2 : ℂ) • u = (1 / 2 : ℝ) • u := by
    intro u
    have hc : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hc]
    rfl
  show (0 : ℂ) • (realProjD w : Yq P q0E) +
      (T0D (realProjD w) - nuLapD (realProjD w) - (1 / 2 : ℂ) • (realProjD w : Yq P q0E)) =
    realPhaseProjection ((0 : ℂ) • (w : Yq P q0E) +
      (T0D w - nuLapD w - (1 / 2 : ℂ) • (w : Yq P q0E)))
  rw [zero_smul, zero_add, zero_smul, zero_add, ha, hb, hsmul, hsmul, map_sub, map_sub, map_smul]
  rfl

theorem q0E_lt_three : q0E < 3 := by
  unfold q0E B0281.q0
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)

theorem gammaR_q0E_pos : 0 < (0 : ℂ).re + gammaR q0E := by
  unfold q0E B0281.q0 gammaR
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem bodyOp_zero_injective {P ν : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) (hν : 0 < ν) :
    Function.Injective (bodyOp P ν q0E 0) :=
  bodyOp_injective_of_bound commonBodyGraphBound q0E one_lt_q0E q0E_lt_three
    P hP1 ν hν 0 gammaR_q0E_pos

theorem mem_realSub_of_bodyOp_zero {P ν : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) (hν : 0 < ν)
    (w : D P ν q0E) (hg : bodyOp P ν q0E 0 w ∈ realSub P q0E) :
    (w : Yq P q0E) ∈ realSub P q0E := by
  have hfixg : bodyOp P ν q0E 0 w = realPhaseProjection (bodyOp P ν q0E 0 w) :=
    realPhaseProjection_eq_of_realSub _ hg
  have heq : bodyOp P ν q0E 0 (realProjD w) = bodyOp P ν q0E 0 w := by
    rw [bodyOp_zero_realProjD, ← hfixg]
  have hw : realProjD w = w := bodyOp_zero_injective hP1 hν heq
  exact mem_realSub_of_fixed P (w : Yq P q0E) (congrArg Subtype.val hw).symm

end UnforcedLeray.Short.IIb.RespOp

end
