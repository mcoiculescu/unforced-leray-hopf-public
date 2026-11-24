import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualCartesianNS
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RawIsRingLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_1

/-!
# `rawEqOffAxis` (`PartIII-b:C/rep/8/2/pres/3/2/1/3`)

Source of record: `the November 2 reference manuscript`
1213-1225, 1263 (`F_R = s^{3/2} r`), 1217 (`p_raw = (R/r)²p`).

Proof plan. (a) The body of `IIb.ringResidualCartesianNS_of` (`Sub/R1_7.lean`), with the proved
leaves of `RingResidualCartesianNS` and the explicit lift fields `W`, `Q` in place of the global
`U`, `Pw` (the body never needs global smoothness of the lift). (b) `W` and `Q` agree with
`realC ∘ rawU` and `liftP` on the open set `{ϱ ≠ 0}`, so `operatorLocality` transfers the
identity. (c) `realCOpsBridge` and injectivity of `realC` give the Cartesian identity.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-- **The local Cartesian identity for the explicit lift** (body of `ringResidualCartesianNS_of`,
`Sub/R1_7.lean:268-360`, with the global `U, Pw` replaced by the lift fields; no
`operatorLocality` step is needed). -/
theorem ringResidual_explicit_lift (ν c R : ℝ) (ψ pr : ProfilePoint → ℝ) (hν : 0 < ν)
    (hc : 0 < c) (hR : 2 ≤ R) (hTr : IsExactPlanarTrain ν c ψ pr) (τ : ℝ) (y : Space)
    (hy : Axi.ϱ y ≠ 0) :
    realC (ringResidual R ν ψ pr τ y) =
      L0 ν (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity R ψ) q.1 q.2)) (τ, y) +
      advT (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity R ψ) q.1 q.2))
        (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity R ψ) q.1 q.2)) (τ, y) +
      gradT (fun q : ℝ × Space => ((UnforcedLeray.B0190.simProfile 2
          (UnforcedLeray.B0185.liftPressure R pr) q.1 q.2 : ℝ) : ℂ)) (τ, y) := by
  have h0 : SimT0Scaling := simT0Scaling
  have hLp : SimLapScaling := simLapScaling
  have hA : SimAdvScaling := simAdvScaling
  have hG : SimGradScaling := simGradScaling
  have hT : CylTimeFormula := cylTimeFormula
  have hAd : CylAdvFormula := cylAdvFormula
  have hL : CylLapFormula := cylLapFormula
  have hGr : CylGradFormula := cylGradFormula
  have hLift : LiftMeridSmooth := liftMeridSmooth
  have hCyl : CylFieldSmooth := cylFieldSmooth
  have hP : TrainPressureSmooth := trainPressureSmooth
  have hS : TrainStreamSmoothBUC := trainStreamSmoothBUC_of UnforcedLeray.Short.PartI.trainStreamSmooth
  obtain ⟨T, hBUC, rfl, rfl⟩ := hTr
  set t : ℝ := Real.exp τ with ht_def
  set x : Space := Real.exp (τ / 2) • y with hx_def
  have ht : 0 < t := Real.exp_pos τ
  have hx : x ∉ Axi.axis := by
    rw [Axi.mem_axis_iff, hx_def, Axi.ϱ_smul, abs_of_pos (Real.exp_pos _)]
    exact mul_ne_zero (Real.exp_pos _).ne' hy
  -- smoothness of the profiles at positive age
  have hψ3 : ContDiffOn ℝ 3 (UnforcedLeray.B0190.trainProfile T.ψ) ageDomain :=
    (hS ν c hν hc T hBUC).of_le (by simp)
  have hp2 : ContDiffOn ℝ 2 (UnforcedLeray.B0190.trainProfile T.p) ageDomain :=
    (hP ν c T).of_le (by simp)
  obtain ⟨m1, m2, m3⟩ := hLift R (UnforcedLeray.B0190.trainProfile T.ψ)
    (UnforcedLeray.B0190.trainProfile T.p) hR hψ3 hp2
  obtain ⟨hu0, hπ0⟩ := hCyl _ _ _ t x ht hx m1 m2 m3
  have hveq : liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) =
      cylField (liftUr R (UnforcedLeray.B0190.trainProfile T.ψ))
        (liftUz R (UnforcedLeray.B0190.trainProfile T.ψ)) := by
    funext s w
    exact liftVelocity_apply R _ s w
  have hpeq : liftPressure R (UnforcedLeray.B0190.trainProfile T.p) =
      cylPressure (rawPressure R (UnforcedLeray.B0190.trainProfile T.p)) := by
    funext s w
    rfl
  have hu : ContDiffAt ℝ 2 (fun q : ℝ × Space =>
      liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) q.1 q.2) (t, x) := by
    rw [hveq]; exact hu0
  have hπ : ContDiffAt ℝ 2 (fun q : ℝ × Space =>
      liftPressure R (UnforcedLeray.B0190.trainProfile T.p) q.1 q.2) (t, x) := by
    rw [hpeq]; exact hπ0
  -- scaling
  have s0a := h0 (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) τ y
    (hu.differentiableAt (by norm_num))
  have s0b := hLp (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) τ y hu
  have s0 : L0 ν (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
        (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) q.1 q.2)) (τ, y) =
      realC (Real.exp (τ / 2) ^ 3 •
        (deriv (fun s => liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) s x) t
          - ν • Axi.vecLap (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t) x)) := by
    simp only [L0]
    rw [s0a, s0b]
    simp only [UnforcedLeray.B0190.simProfile, pow_one]
    rw [← realC_smul_aux, ← realC_smul_aux, ← realC_sub_aux, ← realC_sub_aux]
    congr 1
    module
  have s1 := hA (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ)) τ y
    (hu.differentiableAt (by norm_num))
  have s2 := hG (liftPressure R (UnforcedLeray.B0190.trainProfile T.p)) τ y
    (hπ.differentiableAt (by norm_num))
  -- cylindrical formulas
  have c0 := hT _ _ t x ht hx (m1.of_le (by norm_num)) (m2.of_le (by norm_num))
  have c1 := hAd _ _ t x ht hx (m1.of_le (by norm_num)) (m2.of_le (by norm_num))
  have c2 := hL _ _ t x ht hx m1 m2
  have c3 := hGr _ t x ht hx (m3.of_le (by norm_num))
  rw [← hveq] at c0 c1 c2
  rw [← hpeq] at c3
  -- the residual as a Space identity
  have hres : ringResidual R ν (UnforcedLeray.B0190.trainProfile T.ψ)
        (UnforcedLeray.B0190.trainProfile T.p) τ y =
      Real.exp (τ / 2) ^ 3 •
        (deriv (fun s => liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) s x) t
          - ν • Axi.vecLap (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t) x) +
      Real.exp (τ / 2) ^ 3 •
        Axi.advection (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t)
          (liftVelocity R (UnforcedLeray.B0190.trainProfile T.ψ) t) x +
      Real.exp (τ / 2) ^ 3 •
        cartGrad (liftPressure R (UnforcedLeray.B0190.trainProfile T.p) t) x := by
    rw [c0, c1, c2, c3]
    simp only [ringResidual, physResidualField, cylRadialResidual, cylAxialResidual]
    module
  rw [s0, s1, s2, hres, realC_add_aux, realC_add_aux]

end UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.PartIIIb.Concrete

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.B0411 UnforcedLeray.B0412

variable (Pl : PlanarData) (L : ReturnLevel)

/-- **The raw lift equation at one level, off the axis** (`RawEqOffAxisAt`, source 1213-1225,
1263). -/
theorem rawEqOffAxisAt_of (hR : 2 ≤ L.ε⁻¹) : RawEqOffAxisAt Pl L := by
  intro τ y hy
  have hϱ : Axi.ϱ y ≠ 0 := fun h => hy ((Axi.mem_axis_iff y).2 h)
  have hTr := pf2_exactPlanarTrain Pl L
  have hc : 0 < L.ν ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos L.ν_pos _
  have hν : 0 < L.ν := L.ν_pos
  have hR' : 2 ≤ (L.params Pl).R := hR
  have hloc : realC (rawResidF Pl L τ y) =
      L0 L.ν (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity (L.params Pl).R
            (UnforcedLeray.Short.IIb.trainStream (L.params Pl))) q.1 q.2)) (τ, y) +
      UnforcedLeray.Cons.C03.Concrete.advT
        (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity (L.params Pl).R
            (UnforcedLeray.Short.IIb.trainStream (L.params Pl))) q.1 q.2))
        (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity (L.params Pl).R
            (UnforcedLeray.Short.IIb.trainStream (L.params Pl))) q.1 q.2)) (τ, y) +
      UnforcedLeray.PhaseSpace.gradT
        (fun q : ℝ × Space => ((UnforcedLeray.B0190.simProfile 2
          (UnforcedLeray.B0185.liftPressure (L.params Pl).R
            (UnforcedLeray.Short.IIb.trainPressure (L.params Pl))) q.1 q.2 : ℝ) : ℂ)) (τ, y) :=
    UnforcedLeray.Short.IIb.ringResidual_explicit_lift L.ν (L.ν ^ (-(2 : ℝ))) (L.params Pl).R
      (UnforcedLeray.Short.IIb.trainStream (L.params Pl))
      (UnforcedLeray.Short.IIb.trainPressure (L.params Pl)) hν hc hR' hTr τ y hϱ
  have hopen : IsOpen {q : ℝ × Space | Axi.ϱ q.2 ≠ 0} :=
    isOpen_ne_fun (Axi.continuous_ϱ.comp continuous_snd) continuous_const
  have hmem : (τ, y) ∈ {q : ℝ × Space | Axi.ϱ q.2 ≠ 0} := hϱ
  have hWX : (fun q : ℝ × Space => realC (UnforcedLeray.B0190.simProfile 1
          (UnforcedLeray.B0185.liftVelocity (L.params Pl).R
            (UnforcedLeray.Short.IIb.trainStream (L.params Pl))) q.1 q.2)) =ᶠ[𝓝 (τ, y)]
      (fun q : ℝ × Space => realC (rawU Pl L q.1 q.2)) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun q hq => by
      have h := UnforcedLeray.Short.IIb.rawIsRingLift_proof (L.params Pl) L.train_buc q.1 q.2 hq
      show _ = realC ((L.params Pl).raw q.1 q.2)
      rw [h]
  have hps : LiftPSimAt L := liftPSim L
  have hQX : (fun q : ℝ × Space => ((UnforcedLeray.B0190.simProfile 2
          (UnforcedLeray.B0185.liftPressure (L.params Pl).R
            (UnforcedLeray.Short.IIb.trainPressure (L.params Pl))) q.1 q.2 : ℝ) : ℂ)) =ᶠ[𝓝 (τ, y)]
      (fun q : ℝ × Space => ((liftP L q.1 q.2 : ℝ) : ℂ)) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun q hq => by
      have hq' : q.2 ∉ Axi.axis := fun h => hq ((Axi.mem_axis_iff q.2).1 h)
      show ((_ : ℝ) : ℂ) = ((liftP L q.1 q.2 : ℝ) : ℂ)
      rw [hps q.1 q.2 hq']
      rfl
  have hψ : ContDiffOn ℝ 3 (fun x : ℝ × UnforcedLeray.Cyl.Plane => L.train.ψ x.1 x.2)
      (Set.Ioi 0 ×ˢ Set.univ) :=
    L.train_stream_smooth.of_le (by simp)
  have hX : ContDiffAt ℝ 2 (fun q : ℝ × Space => rawU Pl L q.1 q.2) (τ, y) :=
    (rawU_contDiffOn_offAxis_of (L.params Pl) L.ε_pos hψ).contDiffAt
      (isOpen_offAxisSet.mem_nhds hy)
  have hPr : DifferentiableAt ℝ (fun q : ℝ × Space => liftP L q.1 q.2) (τ, y) :=
    ((liftP_contDiffOn L L.ε_pos).contDiffAt (isOpen_offAxisSet.mem_nhds hy)).differentiableAt
      (by simp)
  have hBr := realCOpsBridge L.ν (rawU Pl L) (liftP L) (τ, y) hX hPr
  have key : realC (rawResidF Pl L τ y) = realC (physDmu L.ν 0 (rawU Pl L) τ y +
      fderiv ℝ (rawU Pl L τ) y (rawU Pl L τ y) + physGrad (liftP L τ) y) := by
    rw [hloc, UnforcedLeray.Short.IIb.operatorLocality L.ν _ _ _ _ (τ, y) hWX hQX, hBr]
  exact realCLI.injective key

/-- **`rawEqOffAxis`** (`PartIII-b:C/rep/8/2/pres/3/2/1/3`, source 1213-1225, 1263): along the
sequence, the raw lift equation holds off the axis. The regime `2 ≤ ε⁻¹` holds eventually. -/
theorem rawEqOffAxis (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.RawEqOffAxis := by
  unfold SeqData.RawEqOffAxis
  filter_upwards [D.pf2_eventually_regime hst one_pos] with n hn
  exact rawEqOffAxisAt_of D.Pl (D.level n) hn.2

end UnforcedLeray.Short.PartIIIb.Concrete
