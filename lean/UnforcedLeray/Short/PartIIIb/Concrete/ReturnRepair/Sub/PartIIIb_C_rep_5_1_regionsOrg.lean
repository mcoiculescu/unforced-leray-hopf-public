import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinParts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq

/-!
# `PartIII-b:C/rep/5/1/regions/org`: the thin far velocity on the shared region split

Source `the November 2 reference manuscript` 5303-5316 (the age rectangles and the
two stream transitions), 4171-4214 (the Ward fields, `ward:shifted-resolvent`,
`ward:cutoff-source`), 3888-3920 and 5785 (the near split), 5569-5605, 5618-5619 (the far thin
velocity and its margins).

## Reconciliation with `PartIII-b:C/rep/5/1/cancel/org`

The leaves `AgeVelSopThin` (`S_μ - S_N` alone) and `AgeVelWardThin` (`Y` alone) of
`Sub/PartIII-b_C_rep_5_1Org.lean` are not source statements: both contain the young-old
rectangle `χ_yS_μχ_o` (young output, old source), which the source cancels in `S_far + Y`
(5303-5316) and bounds nowhere by itself.  The concurrent organizer
`PartIII-b:C/rep/5/1/cancel/org` restructures `AgeVelThin` through the sum on logarithmic output
bins (`Sub/PartIII-b_C_rep_5_1_cancelOrg.lean`): late bins `ν s_{j+1} ≥ 2/3` (far mask and `Y`
separately, late-output margin) and plateau bins (early source, margin `γ/10`), with the
cancellation of the rectangle on output ages `s ≤ 4/(5ν)` as the Prop `SeqData.PlateauCancel`.
That decomposition is the region split of 5306-5316 read bin by bin, so this file does not build a
second one.  It supplies the two links to the split already used by `AgeError` (rep/4) and
`AgeVelRep` (rep/5/2), so that the three chains share their leaves:

1. `youngOldCancel_thin` (proved): the cancellation `Y(T₁,0) + S_far(χ_o(T₁,0)) = 0` a.e. on output
   ages `s ≤ 4/(5ν)` (the body of `SeqData.PlateauCancel`) from
   * `SepYoungThin`, `ShiftedResolventThin` (`Org/YThinTrans.lean`, tasks rep/4/2/org/1-2) and the
     Ward pin: through `transOp_coef`, `(Y + χ_yS_μχ_o)(T₁,0)` has the coefficient of the two
     stream transitions `transField` (4203-4214);
   * `TransFieldLate` (proved below, `transFieldLate`): both transitions vanish at output ages
     `s < 4/(5ν)`, where `χ_y = 1` near the receiver (5312-5316: "They are supported on
     `0.8/ν<s<1/ν`");
   * `NearYoungOldZero` (`Org/FarThinParts.lean`, task rep/4/1/org/6): `χ_yS_Nχ_o = 0` (5303-5306:
     "The young-old rectangle is contained in this mask").
   On `s ≤ 4/(5ν)` (`χ_y = 1`) these give `Y = -S_μ(χ_oT) = -S_far(χ_oT)`.
2. `sopSubIsFarSeq_of_nearSplit` (proved): `SopSubIsFarSeq` from the family-neutral near split
   `SeqNearSplit` (`ReturnInst/Inverses/Seq.lean`; `seqNearSplitStanding`, task rep/5/2/1/13), as
   in `ageVelFarRep_of` of `Sub/PartIII-b_C_rep_5_2_1Org.lean`.

The `Concrete.ThinMassBound` clash: `Sub/PartIII-b_C_rep_5_1_1Org.lean` now has
`ThinMassBoundSlice` (renamed by cancel/org) and `Org/FarThinParts.lean` has `ThinMassN0Bound`
(renamed here), so the AgeVelocity chain imports with the AgeError chain.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The family-neutral near split -/

/-- **`S_μ - S_N = S_far`** (3888-3920, 5785) from the near split pin `SeqNearSplit` of the concrete
base (`B.S = Sop`, `B.SN = SNop` by `rfl`), for every sequence with the standing hypotheses. -/
theorem sopSubIsFarSeq_of_nearSplit (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hS : ∀ D : SeqData, D.RepairStanding dm dp → SeqNearSplit D dm dp) :
    SopSubIsFarSeq Pl σ₀ mZ dm dp := by
  intro D _ _ _ hst
  filter_upwards [hS D hst hst.actual, hst.near] with n hn hnear z hz
  obtain ⟨Sf, hSf, hsn⟩ := hn z hz (hnear z hz)
  refine ⟨Sf, hSf, ?_⟩
  have e1 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).S
      = Sop D.Pl D.K (D.level n) (D.mu n z) := rfl
  have e2 : (concreteBase D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)).SN
      = SNop D.Pl D.K (D.level n) (D.mu n z) := rfl
  rw [e1, e2] at hsn
  rw [hsn, sub_sub_cancel]

/-! ## 2. Both stream transitions vanish at young-plateau outputs -/

/-- **Both stream transitions vanish on the plateau `s < 4/(5ν)`** (source 5312-5316: "They are
supported on `0.8/ν<s<1/ν`"; 4180-4186, 4203-4214).  At a chart point of age `0 < s < 4/(5ν)` the
receiver `y = (R/√s, 0, η/√s)` has `νR²/|y'|² = νs < 4/5`, so `χ̂_y ≡ 1` and `χ̂_y' ≡ 0` on a
neighbourhood of `y` (`IsStreamCutoff.one`).  Hence the first transition `(𝒞_χ-χ)W_μ`
(`transCut`, factor `χ̂_y'`) vanishes at `y`, and `𝒞_y` is the identity near `y`, so the commutator
`[D_{μ+1}, 𝒞_y]X₀` (`transComm`; `physDmu` is a differential operator in `y` and reads the phase
derivative at the fixed point `y`) vanishes at `y`.  No property of the source `g` is used. -/
def TransFieldLate : Prop :=
  ∀ (ν μ R c : ℝ) {χy : ℝ → ℝ}, IsStreamCutoff χy → 0 < ν → 0 < R →
    ∀ (g : Chart → Ten3) (p : Chart), 0 < p.1 → ν * p.1 < 4 / 5 →
      coefOf R (transField ν μ R c χy g) p = 0

/-- `χ̂_y ≡ 1` below `4/5`, so `χ̂_y = 1` and `χ̂_y' = 0` at every `t < 4/5`. -/
theorem streamCut_one_of_lt {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ) {t : ℝ} (ht : t < 4 / 5) :
    χ t = 1 ∧ deriv χ t = 0 := by
  refine ⟨hχ.one t ht.le, ?_⟩
  have hev : χ =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (Iio_mem_nhds ht) (fun u hu => hχ.one u (le_of_lt hu))
  rw [hev.deriv_eq, deriv_const]

/-- On the plateau `νs < 4/5` the Ward stream cutoff is the identity: `𝒞_yZ = Z`. -/
theorem wardStreamCut_plateau {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : ν * age R y < 4 / 5) :
    wardStreamCut ν R χy Z τ y = Z τ y := by
  obtain ⟨h1, h2⟩ := streamCut_one_of_lt hχ hy
  unfold wardStreamCut
  rw [h1, h2]
  simp

/-- **`TransFieldLate`** (proof of the Prop above). -/
theorem transFieldLate : TransFieldLate := by
  intro ν μ R c χy hχ hν hR g p hp hlt
  set y := NearInst.chartY R p with hydef
  have hϱ : 0 < ϱ y := by rw [hydef, ϱ_chartY hR hp]; positivity
  have hage : ν * age R y < 4 / 5 := by rw [hydef, age_chartY hR hp]; exact hlt
  have hc1 : ContinuousAt (fun y' => ν * age R y') y := by
    unfold age
    exact continuousAt_const.mul
      (continuousAt_const.div (continuous_ϱ.continuousAt.pow 2) (pow_pos hϱ 2).ne')
  have hev : ∀ᶠ y' in 𝓝 y, ν * age R y' < 4 / 5 := hc1.eventually_lt continuousAt_const hage
  have hX : ∀ τ, wardX ν μ R c χy g τ =ᶠ[𝓝 y] wardX0 ν μ R c g τ := by
    intro τ
    filter_upwards [hev] with y' hy'
    exact wardStreamCut_plateau hχ _ τ hy'
  have hD : ∀ τ, physDmu ν (μ + 1) (wardX ν μ R c χy g) τ y =
      physDmu ν (μ + 1) (wardX0 ν μ R c g) τ y := by
    intro τ
    have e1 : (fun t => wardX ν μ R c χy g t y) = fun t => wardX0 ν μ R c g t y :=
      funext fun t => (hX t).self_of_nhds
    have e2 : fderiv ℝ (wardX ν μ R c χy g τ) y = fderiv ℝ (wardX0 ν μ R c g τ) y :=
      (hX τ).fderiv_eq
    have e3 : physLap (wardX ν μ R c χy g τ) y = physLap (wardX0 ν μ R c g τ) y := by
      unfold physLap physPd2
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hfd : fderiv ℝ (wardX ν μ R c χy g τ) =ᶠ[𝓝 y] fderiv ℝ (wardX0 ν μ R c g τ) :=
        (hX τ).fderiv
      have hpd : (fun y' => physPd (wardX ν μ R c χy g τ) j y') =ᶠ[𝓝 y]
          fun y' => physPd (wardX0 ν μ R c g τ) j y' := by
        filter_upwards [hfd] with y' h
        unfold physPd
        rw [h]
      show fderiv ℝ (fun y' => physPd (wardX ν μ R c χy g τ) j y') y (coordinateVector j) =
        fderiv ℝ (fun y' => physPd (wardX0 ν μ R c g τ) j y') y (coordinateVector j)
      rw [hpd.fderiv_eq]
    unfold physDmu
    rw [e1, e2, e3, (hX τ).self_of_nhds]
  have hF0 : ∀ τ, transField ν μ R c χy g τ y = 0 := by
    intro τ
    have hcut : transCut ν μ R c χy g τ y = 0 := by
      unfold transCut streamCorr
      rw [(streamCut_one_of_lt hχ hage).2]
      simp
    have hcomm : transComm ν μ R c χy g τ y = 0 := by
      unfold transComm
      rw [hD τ, wardStreamCut_plateau hχ _ τ hage, sub_self]
    unfold transField
    rw [hcut, hcomm, add_zero]
  unfold coefOf
  rw [← hydef, hF0]
  ext i
  fin_cases i <;> simp

/-- Output ages avoid a fixed value almost everywhere. -/
theorem bodyMeasure_ae_fst_ne (c γ ν a : ℝ) : ∀ᵐ p ∂(bodyMeasure c γ ν), p.1 ≠ a := by
  have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))), s ≠ a :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_of_ae (Measure.ae_ne volume a))
  have h2 : ∀ᵐ p ∂(ageμ c (-3 / 2)), p.1 ≠ a := by
    unfold ageμ
    exact Measure.quasiMeasurePreserving_fst.ae h1
  unfold bodyMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le h2

/-! ## 3. The cancellation of the young-old rectangle on thin sources -/

/-- **The young-old rectangle cancels on the plateau** (source 4171-4214, 5303-5316): for large `n`,
every `z ∈ [-1,1]` and every stress `T`, almost every output point of age `s ≤ 4/(5ν)` has
`Y(T₁,0) + S_far(χ_o(T₁,0)) = 0`, `S_far = S_μ - S_N`.  This is the body of `SeqData.PlateauCancel`
of `Sub/PartIII-b_C_rep_5_1_cancel/Bridge.lean`, stated in full here.  Proof: by `transOp_coef`
the coefficient of `transOp (T₁,0) = Y(T₁,0) + χ_yS_μ(χ_o(T₁,0))` is the transition field, zero at
`s < 4/(5ν)` (`TransFieldLate`); `χ_y(νs) = 1` there, and `χ_yS_N(χ_o ·) = 0`
(`NearYoungOldZero`); the age `s = 4/(5ν)` is a null set. -/
theorem youngOldCancel_thin (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : SepYoungThin dm dp) (h2 : ShiftedResolventThin dm dp) (h0 : NearYoungOldZero dm dp) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
      ∀ᵐ p ∂(bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν),
        p.1 ≤ 4 / (5 * (D.level n).ν) →
          ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T) : Chart → Merid) p +
            (((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
              (chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
                (D.level n).ν D.K.hχo (thinPart T)) : LVel D.Pl (D.level n)) :
                  Chart → Merid) p = 0 := by
  filter_upwards [h1 D hst, h2 D hst, h0 D hst, hst.pins] with n s1 s2 s0 pins z hz T
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1 (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2
      (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U (D.level n).pres :=
    Classical.epsilon_spec (pins z hz).ward
  have hg : IsRep D.Pl D.K (D.level n) (oldThin D.Pl D.K (D.level n) T)
      ((oldThin D.Pl D.K (D.level n) T).fst : Chart → Ten3)
      ((oldThin D.Pl D.K (D.level n) T).snd : Chart → Ten3) :=
    ⟨EventuallyEq.rfl, EventuallyEq.rfl⟩
  have hc := transOp_coef D.Pl D.K (D.level n) (D.mu n z) hst.chiY hW (s1 z hz) (s2 z hz) T hg
  have hadd := Lp.coeFn_add ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T))
    (youngOldOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T))
  have hM := youngMul_ae (c := cOf (D.level n).ν) (γ := gRate D.Pl) (ν := (D.level n).ν)
    hst.chiY (Sop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T))
  have hN := youngMul_ae (c := cOf (D.level n).ν) (γ := gRate D.Pl) (ν := (D.level n).ν)
    hst.chiY (SNop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T))
  have e0 : youngMul (c := cOf (D.level n).ν) (γ := gRate D.Pl) (ν := (D.level n).ν) hst.chiY
      (SNop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T)) = 0 :=
    s0 z hz (thinPart T)
  have hN0 : (youngMul (c := cOf (D.level n).ν) (γ := gRate D.Pl) (ν := (D.level n).ν) hst.chiY
      (SNop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T)) : Chart → Merid)
        =ᵐ[bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν] 0 := by
    rw [e0]
    exact Lp.coeFn_zero _ _ _
  have hsub := Lp.coeFn_sub (Sop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T))
    (SNop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T))
  filter_upwards [hc, hadd, hM, hN, hN0, hsub, bodyMeasure_ae_pos (cOf (D.level n).ν)
    (gRate D.Pl) (D.level n).ν, bodyMeasure_ae_fst_ne (cOf (D.level n).ν) (gRate D.Pl)
    (D.level n).ν (4 / (5 * (D.level n).ν))] with p hcp haddp hMp hNp hN0p hsubp hp hne hle
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hlt : (D.level n).ν * p.1 < 4 / 5 := by
    have h' : p.1 < 4 / (5 * (D.level n).ν) := lt_of_le_of_ne hle hne
    rw [lt_div_iff₀ (by positivity)] at h'
    linarith
  have hχ1 : cutFun D.K.χy (D.level n).ν p = 1 := hst.chiY.one _ hlt.le
  have hzero := transFieldLate (D.level n).ν (D.mu n z) (D.level n).ε⁻¹ (cOf (D.level n).ν) hst.chiY hν
    (inv_pos.2 (D.level n).ε_pos)
    (((oldThin D.Pl D.K (D.level n) T).fst : Chart → Ten3) +
      ((oldThin D.Pl D.K (D.level n) T).snd : Chart → Ten3)) p hp hlt
  -- the transition operator vanishes at `p`
  have hT0 : ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T) : Chart → Merid) p +
      (youngMul (c := cOf (D.level n).ν) (γ := gRate D.Pl) (ν := (D.level n).ν) hst.chiY
        (Sop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T)) :
          Chart → Merid) p = 0 := by
    have e : (transOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T) : Chart → Merid) p =
        ((wardOps D.Pl D.K (D.level n) (D.mu n z)).1 (thinPart T) : Chart → Merid) p +
          (youngMul (c := cOf (D.level n).ν) (γ := gRate D.Pl) (ν := (D.level n).ν) hst.chiY
            (Sop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T)) :
              Chart → Merid) p := haddp
    rw [← e, hcp, hzero]
  rw [hMp, hχ1, one_smul] at hT0
  rw [hNp, hχ1, one_smul] at hN0p
  have e2 : ((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
      (chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
        (D.level n).ν D.K.hχo (thinPart T)) : LVel D.Pl (D.level n)) =
      Sop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T) -
        SNop D.Pl D.K (D.level n) (D.mu n z) (oldThin D.Pl D.K (D.level n) T) := rfl
  rw [e2, hsubp, Pi.sub_apply, hN0p, Pi.zero_apply, sub_zero]
  exact hT0

end UnforcedLeray.Short.PartIIIb.Concrete
