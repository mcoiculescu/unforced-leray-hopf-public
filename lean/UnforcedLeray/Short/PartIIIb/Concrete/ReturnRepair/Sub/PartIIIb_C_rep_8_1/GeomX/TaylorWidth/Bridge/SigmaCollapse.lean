import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace TWBridge

open PhasePrim

section Aux

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

theorem thinG_ae (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
      thinG Pl K L T p = cutFun K.χo L.ν p • ((WithLp.ofLp T).1 p) := by
  have hρ : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  set Tc := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T with hTc
  have hGdef : thinG Pl K L T = strSum (thinPart Tc) := by
    show strSum (chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)) = _
    rw [ftk_chiO_thinPart K.hχo T]
  have h1 := FarBridge.strSum_thinPart hρ Tc
  have hc1 : ((Tc.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) :
      Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      cutFun K.χo L.ν • ((T.fst : Lp (α := Chart) Ten3 2
        (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun K.χo L.ν) (cutFun_measurable K.hχo L.ν) 1
      (cutFun_bound K.hχo L.ν) T.fst
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at hc1
  filter_upwards [h1, hc1] with p hp1 hp2
  rw [hGdef, hp1, hp2]
  rfl


theorem plFrame_eq_rotQ (x' : ℝ × ℝ) : plFrame x' = rotQ x' := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [plFrame, rotQ, NearInst.cylFrame, hRad_pl]

theorem cellμ_eq_smul (c : ℝ) (hc : 0 < c) :
    Cyl.cellμ c = ENNReal.ofReal c • Cyl.avgμ c := by
  unfold Cyl.avgμ
  rw [smul_smul, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]

theorem ae_cell_of_avg (c : ℝ) (hc : 0 < c) {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ x ∂(Cyl.avgμ c), P x) : ∀ᵐ x ∂(Cyl.cellμ c), P x := by
  rw [cellμ_eq_smul c hc]
  exact Measure.smul_absolutelyContinuous.ae_le h

theorem integrable_cell_of_avg (c : ℝ) (hc : 0 < c) {f : ℝ × ℝ → ℝ}
    (h : Integrable f (Cyl.avgμ c)) : Integrable f (Cyl.cellμ c) := by
  rw [cellμ_eq_smul c hc]
  exact h.smul_measure ENNReal.ofReal_ne_top

theorem ageμ_slice' (c : ℝ) (hc : 0 < c) {P : Chart → Prop}
    (hae : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(Cyl.avgμ c), P (s, x) := by
  unfold ageμ at hae
  have : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have h1 := Measure.ae_ae_of_ae_prod hae
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) := by
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow _).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have : 0 < s ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
    simpa using this
  exact hac.ae_le h1


theorem quad_apply (Q : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) (N : Fin 3 → Fin 3 → ℝ) (j k : Fin 3) :
    (Q * (u • Matrix.of N) * Q.transpose) j k = ∑ a, ∑ b, (Q j a * u * Q k b) * N a b := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem inner_collapse (c ν : ℝ) (hc : 0 < c) (χo : ℝ → ℝ) (g : Chart → Ten3) (A : Chart → Mat3)
    (x' : ℝ × ℝ) (hρ : 0 < x'.1 ^ 2 + x'.2 ^ 2)
    (h1 : ∀ i j, Integrable (fun x : ℝ × ℝ => A (plS x', x) i j) (Cyl.cellμ c))
    (h2 : ∀ᵐ x ∂(Cyl.cellμ c), ∀ i j : Fin 3, (i = 1 ∨ j = 1) → A (plS x', x) i j = 0)
    (h3 : ∀ᵐ x ∂(Cyl.cellμ c), ∀ i j : Fin 3,
      g (plS x', x) (i, j) = χo (ν * plS x') * A (plS x', x) i j) (j k : Fin 3) :
    ∫ Y, IIIa.phaseMean c (plift c g) x' Y j k =
      (sigmaM c ν χo A x' j k + sigmaM c ν χo A x' k j) / 2 := by
  set ρ := Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) with hρdef
  have hρpos : 0 < ρ := Real.sqrt_pos.2 hρ
  have hu : plS x' = (ρ ^ 2)⁻¹ := by rw [hρdef, Real.sq_sqrt hρ.le]; rfl
  have hsq : Real.sqrt (plS x') = ρ⁻¹ := by
    rw [hu, ← inv_pow, Real.sqrt_sq (by positivity)]
  set Q := rotQ x' with hQdef
  set u := plS x' with hudef
  set P := phaseMean c ν χo A u with hP
  -- the entry field
  let Ef : ℝ × ℝ → Fin 3 → Fin 3 → ℝ := fun x i j =>
    if i = 1 ∨ j = 1 then 0 else χo (ν * u) * A (u, x) i j
  have hEf : ∀ i j, Integrable (fun x => Ef x i j) (Cyl.cellμ c) := by
    intro i j
    by_cases h : i = 1 ∨ j = 1
    · simp only [Ef, if_pos h]; exact integrable_zero _ _ _
    · simp only [Ef, if_neg h]; exact (h1 i j).const_mul _
  have hEint : ∀ i j, ∫ x, Ef x i j ∂(Cyl.cellμ c) = c * P i j := by
    intro i j
    have hav : ∀ f : ℝ × ℝ → ℝ, ∫ x, f x ∂(Cyl.avgμ c) = c⁻¹ * ∫ x, f x ∂(Cyl.cellμ c) := by
      intro f
      rw [Cyl.integral_avgμ hc.le]
      rfl
    by_cases h : i = 1 ∨ j = 1
    · simp [Ef, hP, phaseMean, if_pos h]
    · simp only [Ef, hP, phaseMean, if_neg h, hav, integral_const_mul]
      field_simp
  let Nf : Fin 3 → Fin 3 → ℝ × ℝ → ℝ := fun a b x => (Ef x a b + Ef x b a) / 2
  have hNf : ∀ a b, Integrable (Nf a b) (Cyl.cellμ c) := fun a b =>
    ((hEf a b).add (hEf b a)).div_const 2
  have hNint : ∀ a b, ∫ x, Nf a b x ∂(Cyl.cellμ c) = c * ((P a b + P b a) / 2) := by
    intro a b
    simp only [Nf]
    rw [integral_div, integral_add (hEf a b) (hEf b a), hEint, hEint]
    ring
  let Φ : ℝ × ℝ → ℝ := fun z =>
    (plFrame x' * (u • NearInst.nsSym (g (u, z))) * (plFrame x').transpose) j k
  let Φ2 : ℝ × ℝ → ℝ := fun x => ∑ a, ∑ b, (Q j a * u * Q k b) * Nf a b x
  have hQ : plFrame x' = Q := plFrame_eq_rotQ x'
  have hΦae : Φ =ᵐ[Cyl.cellμ c] Φ2 := by
    filter_upwards [h2, h3] with x hx2 hx3
    have hN : NearInst.nsSym (g (u, x)) = Matrix.of fun a b => Nf a b x := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [NearInst.nsSym, NearInst.symRZ, Nf, Ef, hx3, hx2] <;> ring
    simp only [Φ, Φ2, hN, hQ]
    exact quad_apply Q u _ j k
  have hΦ2int : Integrable Φ2 (Cyl.cellμ c) := by
    refine integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => ?_
    exact (hNf a b).const_mul _
  have hΦint : Integrable Φ (Cyl.cellμ c) := hΦ2int.congr hΦae.symm
  have hΦI : ∫ z in Cyl.cell c, Φ z = c * ∑ a, ∑ b, (Q j a * u * Q k b) * ((P a b + P b a) / 2) := by
    have e : ∫ z in Cyl.cell c, Φ z = ∫ z, Φ2 z ∂(Cyl.cellμ c) := integral_congr_ae hΦae
    rw [e]
    have : ∫ z, Φ2 z ∂(Cyl.cellμ c) =
        ∑ a, ∑ b, (Q j a * u * Q k b) * ∫ x, Nf a b x ∂(Cyl.cellμ c) := by
      simp only [Φ2]
      rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => (hNf a b).const_mul _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ fun b _ => (hNf a b).const_mul _]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hNint]; ring
  -- pointwise reduction and scaling
  have hstep1 : ∀ Y, IIIa.phaseMean c (plift c g) x' Y j k =
      c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), Φ (q, Y / ρ) := by
    intro Y
    have e : IIIa.phaseMean c (plift c g) x' Y j k =
        c⁻¹ * ∫ q in Ioc 0 c, Φ (redQ c q, Y * Real.sqrt u) := rfl
    rw [e, integral_redQ c hc (fun q => Φ (q, Y * Real.sqrt u)), hsq]
    simp only [div_eq_mul_inv]
  have hI : ∫ Y, IIIa.phaseMean c (plift c g) x' Y j k =
      ρ * (c⁻¹ * ∫ z in Cyl.cell c, Φ z) := by
    have e1 : ∫ Y, IIIa.phaseMean c (plift c g) x' Y j k =
        ∫ Y, (fun η => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), Φ (q, η)) (Y / ρ) :=
      integral_congr_ae (Eventually.of_forall hstep1)
    rw [e1, Measure.integral_comp_div (fun η => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), Φ (q, η)) ρ,
      abs_of_pos hρpos, smul_eq_mul, integral_const_mul,
      ← Cyl.integral_cell_eq_integral_integral hΦint]
  rw [hI, hΦI]
  have hρu : ρ * u = ρ⁻¹ := by
    rw [hu]; field_simp
  have hs1 : sigmaM c ν χo A x' j k =
      ρ⁻¹ * ∑ a, ∑ b, Q j a * Q k b * P a b := by
    have e : sigmaM c ν χo A x' j k = ∑ a, ∑ b, Q j a * (ρ⁻¹ * P a b) * Q k b := rfl
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hs2 : sigmaM c ν χo A x' k j =
      ρ⁻¹ * ∑ a, ∑ b, Q j a * Q k b * P b a := by
    have e : sigmaM c ν χo A x' k j = ∑ a, ∑ b, Q k a * (ρ⁻¹ * P a b) * Q j b := rfl
    rw [e, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hs1, hs2]
  have hsum : ∑ a, ∑ b, (Q j a * u * Q k b) * ((P a b + P b a) / 2) =
      (u / 2) * (∑ a, ∑ b, Q j a * Q k b * P a b + ∑ a, ∑ b, Q j a * Q k b * P b a) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsum, ← hρu]
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

theorem entry_le_frob' (M : Mat3) (i j : Fin 3) : ‖M i j‖ ≤ frob M := by
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  calc M i j ^ 2 ≤ ∑ b, M i b ^ 2 :=
        Finset.single_le_sum (f := fun b => M i b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, M a b ^ 2 :=
        Finset.single_le_sum (f := fun a => ∑ b, M a b ^ 2)
          (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i)

/-- The slice conditions at the age `s` that the inner computation needs. -/
def GoodSlice (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L)
    (s : ℝ) : Prop :=
  (∀ᵐ x ∂(Cyl.avgμ (cOf L.ν)), ∀ i j : Fin 3, (i = 1 ∨ j = 1) → thinRep T (s, x) i j = 0) ∧
  (∀ᵐ x ∂(Cyl.avgμ (cOf L.ν)),
    thinG Pl K L T (s, x) = cutFun K.χo L.ν (s, x) • ((WithLp.ofLp T).1 (s, x))) ∧
  (∀ i j : Fin 3, Integrable (fun x : ℝ × ℝ => thinRep T (s, x) i j) (Cyl.avgμ (cOf L.ν)))

theorem good_ae (hC0 : 0 < K.C0) (T : LStr Pl K L) (hAzi : ThinAziZero Pl K L T)
    (hOld : OldThinFinite (cOf L.ν) L.ν (thinRep T)) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi (6 / 5 / L.ν) → GoodSlice Pl K L T s := by
  have hν : 0 < L.ν := L.ν_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hθ : Ioi (6 / 5 / L.ν) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by positivity)
  have ha := ageμ_slice' (cOf L.ν) hc hAzi
  have hb := ageμ_slice' (cOf L.ν) hc (thinG_ae Pl K L hC0 T)
  have hc1 := hOld.2.prod_right_ae
  have hc2 := hOld.1.prodMk_left
  have hS : MeasurableSet (Ioi (6 / 5 / L.ν)) := measurableSet_Ioi
  rw [← ae_restrict_iff' hS]
  have ha' := ae_restrict_of_ae_restrict_of_subset hθ ha
  have hb' := ae_restrict_of_ae_restrict_of_subset hθ hb
  have hc1' : ∀ᵐ s ∂(volume.restrict (Ioi (6 / 5 / L.ν))), _ := hc1
  filter_upwards [ha', hb', hc1', hc2, ae_restrict_mem hS] with s hsa hsb hsc hsm hsmem
  refine ⟨hsa, hsb, fun i j => ?_⟩
  have hpos : 0 < s ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (lt_trans (by positivity) hsmem) _
  have hf : Integrable (fun x => frob (thinRep T (s, x))) (Cyl.avgμ (cOf L.ν)) := by
    have := hsc.const_mul (s ^ (-(3 / 2 : ℝ)))⁻¹
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  refine hf.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((continuous_apply j).comp (continuous_apply i)).comp_aestronglyMeasurable hsm
  · exact entry_le_frob' _ i j

end Aux

end TWBridge

open TWBridge PhasePrim in
/-- **Leaf `PartIII-b:C/rep/8/1/1/1/3/2/2`: the zero-width collapse of the phase mean.** -/
theorem sigmaCollapse : TWBridge.SigmaCollapse := by
  intro Pl K L hC0 T hAzi hOld hN1
  have hν : 0 < L.ν := L.ν_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hgood := TWBridge.good_ae Pl K L hC0 T hAzi hOld
  set θ : ℝ := 6 / 5 / L.ν with hθ
  have hnull : volume {s : ℝ | ¬ (s ∈ Ioi θ → TWBridge.GoodSlice Pl K L T s)} = 0 := by
    rw [← ae_iff] at *
    simpa [ae_iff] using hgood
  set t0 : Set ℝ := {s : ℝ | ¬ (s ∈ Ioi θ → TWBridge.GoodSlice Pl K L T s)} ∪ {θ} with ht0
  have ht0n : volume t0 = 0 := by
    rw [ht0]; exact measure_union_null hnull (measure_singleton θ)
  set t := toMeasurable volume t0 with ht
  have htm : MeasurableSet t := measurableSet_toMeasurable _ _
  have htn : volume t = 0 := by rw [ht, measure_toMeasurable]; exact ht0n
  have hpolar := polar_null htm htn
  have hne : ∀ᵐ x' : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), x' ≠ 0 := by
    rw [ae_iff]
    simpa using measure_singleton (0 : ℝ × ℝ)
  filter_upwards [hpolar, hne] with x' hx' hx0
  have hS : 0 < x'.1 ^ 2 + x'.2 ^ 2 := by
    rcases lt_or_eq_of_le (add_nonneg (sq_nonneg x'.1) (sq_nonneg x'.2)) with h | h
    · exact h
    · exfalso
      apply hx0
      have h1 : x'.1 = 0 := by nlinarith [sq_nonneg x'.1, sq_nonneg x'.2]
      have h2 : x'.2 = 0 := by nlinarith [sq_nonneg x'.1, sq_nonneg x'.2]
      exact Prod.ext h1 h2
  intro j k
  by_cases hout : Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)
  · rw [show (fun Y => meanSrc Pl K L T x' Y j k) = fun _ => 0 from
      funext fun Y => by rw [meanSrc_support Pl K L T x' Y hout]; rfl]
    simp only [integral_zero]
    have hχ : K.χo (L.ν * (x'.1 ^ 2 + x'.2 ^ 2)⁻¹) = 0 := by
      apply K.hχo.zero
      have h1 : 5 * L.ν / 6 < x'.1 ^ 2 + x'.2 ^ 2 := by
        have := Real.sqrt_lt_sqrt (by positivity) hout |> fun _ => hout
        have h2 := (Real.sqrt_lt_sqrt_iff (by positivity)).1 hout
        exact h2
      rw [← div_eq_mul_inv, div_le_iff₀ hS]
      linarith
    have hz : ∀ a b : Fin 3, sigmaM (cOf L.ν) L.ν K.χo (thinRep T) x' a b = 0 := by
      intro a b
      simp [sigmaM, phaseMean, hχ]
    rw [hz, hz]; simp
  · rw [not_lt] at hout
    have hcut : ∀ Y, meanSrc Pl K L T x' Y = IIIa.phaseMean (cOf L.ν) (plift (cOf L.ν) (thinG Pl K L T)) x' Y := by
      intro Y
      unfold meanSrc
      rw [phaseMean_cutLift, if_pos hout]
    have hu : plS x' ∈ Ioi θ := by
      have hρ2 : x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * L.ν / 6 := by
        have := Real.sqrt_le_sqrt_iff (by positivity) |>.1 hout
        exact this
      have hne' : plS x' ≠ θ := by
        intro h
        apply hx' ⟨hS, ?_⟩
        show (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ t
        have : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ t0 := Or.inr h
        exact subset_toMeasurable _ _ this
      have hge : θ ≤ plS x' := by
        have e : θ = (5 * L.ν / 6)⁻¹ := by rw [hθ]; field_simp
        rw [e]
        exact inv_anti₀ hS hρ2
      exact lt_of_le_of_ne hge (Ne.symm hne')
    have hG : TWBridge.GoodSlice Pl K L T (plS x') := by
      by_contra hbad
      apply hx' ⟨hS, ?_⟩
      show (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ t
      have : (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ∈ t0 := Or.inl (fun h => hbad (h hu))
      exact subset_toMeasurable _ _ this
    obtain ⟨ha, hb, hcc⟩ := hG
    have key := inner_collapse (cOf L.ν) L.ν hc K.χo (thinG Pl K L T) (thinRep T) x' hS
      (fun i j => integrable_cell_of_avg _ hc (hcc i j))
      (ae_cell_of_avg _ hc ha)
      (ae_cell_of_avg _ hc (hb.mono fun x hx i j => by
        rw [hx]
        simp [cutFun, thinRep, Ten3.toMatrix])) j k
    simpa only [hcut] using key


end UnforcedLeray.Short.PartIIIb.Concrete
