import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeConvectionAE
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellQuadraticGuard
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open Set

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.B0412

/-- The actual affine inlet field is the coordinate-weighted sum of its two complexified inlet
columns, pointwise on spacetime. -/
theorem eFun_eq_weighted_inletColumns {p : Params} (z : p.Z) :
    p.eFun (p.coord z) = fun x : SpaceTime =>
      ∑ i : Fin 2, (p.coord z i : ℂ) • p.Efun i x := by
  funext x
  ext k
  simp [Params.eFun, Params.Efun, realC_apply, Fin.sum_univ_succ]

#print axioms eFun_eq_weighted_inletColumns

/-- The transpose advection by the affine inlet is the coordinate-weighted sum of the inlet
column transpose advections, pointwise for every test. -/
theorem advT_eFun_eq_weighted_inletColumns {p : Params} (z : p.Z)
    (Φ : SpaceTime → CVec3) :
    advT (p.eFun (p.coord z)) Φ = fun x : SpaceTime =>
      ∑ i : Fin 2, (p.coord z i : ℂ) • advT (p.Efun i) Φ x := by
  funext x
  have he := congrFun (eFun_eq_weighted_inletColumns z) x
  change (∑ k : Fin 3, (p.eFun (p.coord z) x k) • dy k Φ x) = _
  rw [he]
  calc
    (∑ k : Fin 3,
        (∑ i : Fin 2, (p.coord z i : ℂ) • p.Efun i x k) • dy k Φ x) =
      ∑ k : Fin 3, ∑ i : Fin 2,
        (p.coord z i : ℂ) • (p.Efun i x k • dy k Φ x) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro i hi
          simp [smul_eq_mul, smul_smul, mul_assoc]
    _ = ∑ i : Fin 2, (p.coord z i : ℂ) •
        (∑ k : Fin 3, p.Efun i x k • dy k Φ x) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.smul_sum]
    _ = ∑ i : Fin 2, (p.coord z i : ℂ) • advT (p.Efun i) Φ x := rfl

#print axioms advT_eFun_eq_weighted_inletColumns

/-- A bounded real advecting field and bounded real partner give an integrable transpose
convection pairing on a compact-test phase cell. Both fields are the actual bounded backgrounds;
the derivative support of the test supplies the spatial localization. -/
theorem integrable_advT_pair_boundedBackgrounds {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {V W : ℝ → SpatialField} (hV : IsBoundedBackground V) (hW : IsBoundedBackground W) :
    Integrable (fun x : SpaceTime =>
      dotL (advT (fun x => realC (V x.1 x.2)) Φ x) (realC (W x.1 x.2)) )
      (volume.restrict (phaseCell P)) := by
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  have hR0 : R0 ≤ R := le_max_left _ _
  have hR1 : R1 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : R2 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hF := memLp_advT_background_cell hΦ hV q0E_ne_top
  have hG := memLp_boundedBackground_cut_cell (P := P) (R := R) hW
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ →
      advT (fun x => realC (V x.1 x.2)) Φ (τ, y) = 0 := by
    intro τ hτ y hy
    rw [advT]
    apply Finset.sum_eq_zero
    intro j hj
    fin_cases j <;> simp [hspace0 τ y (lt_of_le_of_lt hR0 hy),
      hspace1 τ y (lt_of_le_of_lt hR1 hy), hspace2 τ y (lt_of_le_of_lt hR2 hy)]
  exact integrable_dotL_of_memLp_compactFirst hF hG hzero

#print axioms integrable_advT_pair_boundedBackgrounds

/-- Guarded additivity of `pairF` in its first vector field argument. -/
theorem pairF_add_left_of_integrable {P : ℝ} [Fact (0 < P)]
    {F G H : SpaceTime → CVec3}
    (hF : Integrable (fun x => dotL (F x) (H x)) (volume.restrict (phaseCell P)))
    (hG : Integrable (fun x => dotL (G x) (H x)) (volume.restrict (phaseCell P)))
    (hFG : Integrable (fun x => dotL (F x + G x) (H x))
      (volume.restrict (phaseCell P))) :
    pairF P (fun x => F x + G x) H = pairF P F H + pairF P G H := by
  rw [pairF_eq_restrictedProductIntegral hFG,
    pairF_eq_restrictedProductIntegral hF, pairF_eq_restrictedProductIntegral hG]
  have hpoint (x : SpaceTime) : dotL (F x + G x) (H x) =
      dotL (F x) (H x) + dotL (G x) (H x) := by
    simp [dotL_apply]
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_add hF hG]
  simp [smul_add]

/-- Guarded additivity of `pairF` in its second vector field argument. -/
theorem pairF_add_right_of_integrable {P : ℝ} [Fact (0 < P)]
    {F G H : SpaceTime → CVec3}
    (hF : Integrable (fun x => dotL (H x) (F x)) (volume.restrict (phaseCell P)))
    (hG : Integrable (fun x => dotL (H x) (G x)) (volume.restrict (phaseCell P)))
    (hFG : Integrable (fun x => dotL (H x) (F x + G x))
      (volume.restrict (phaseCell P))) :
    pairF P H (fun x => F x + G x) = pairF P H F + pairF P H G := by
  rw [pairF_eq_restrictedProductIntegral hFG,
    pairF_eq_restrictedProductIntegral hF, pairF_eq_restrictedProductIntegral hG]
  have hpoint (x : SpaceTime) : dotL (H x) (F x + G x) =
      dotL (H x) (F x) + dotL (H x) (G x) := by
    simp [dotL_apply, Finset.sum_add_distrib, mul_add]
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_add hF hG]
  simp [smul_add]

/-- Guarded weighted finite additivity of `pairF` in its first vector field argument. -/
theorem pairF_weightedSum_left_of_integrable {P : ℝ} [Fact (0 < P)]
    {a : Fin 2 → ℂ} {F : Fin 2 → SpaceTime → CVec3} {G : SpaceTime → CVec3}
    (hTerm : ∀ i, Integrable (fun x => dotL (F i x) (G x))
      (volume.restrict (phaseCell P)))
    (hTotal : Integrable (fun x => dotL
      (∑ i : Fin 2, a i • F i x) (G x)) (volume.restrict (phaseCell P))) :
    pairF P (fun x => ∑ i : Fin 2, a i • F i x) G =
      ∑ i : Fin 2, a i * pairF P (F i) G := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  have hscaled (i : Fin 2) : Integrable
      (fun x => a i * dotL (F i x) (G x)) μ := by
    simpa [μ, mul_comm] using (hTerm i).const_mul (a i)
  have hpoint (x : SpaceTime) :
      dotL (∑ i : Fin 2, a i • F i x) (G x) =
        ∑ i : Fin 2, a i * dotL (F i x) (G x) := by
    calc
      _ = dotL (∑ i : Fin 2, a i • F i x) (G x) := rfl
      _ = (∑ i : Fin 2, dotL (a i • F i x)) (G x) := by rw [map_sum]
      _ = ∑ i : Fin 2, dotL (a i • F i x) (G x) := by
        rw [ContinuousLinearMap.sum_apply]
      _ = _ := by simp
  have hint :
      ∫ x : SpaceTime, dotL (∑ i : Fin 2, a i • F i x) (G x) ∂μ =
        ∑ i : Fin 2, a i * ∫ x : SpaceTime, dotL (F i x) (G x) ∂μ := by
    calc
      _ = ∫ x : SpaceTime, ∑ i : Fin 2, a i * dotL (F i x) (G x) ∂μ :=
        integral_congr_ae (ae_of_all _ hpoint)
      _ = ∑ i : Fin 2, ∫ x : SpaceTime, a i * dotL (F i x) (G x) ∂μ := by
        rw [integral_finsetSum Finset.univ (fun i hi => hscaled i)]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
  have hpair (i : Fin 2) : pairF P (F i) G =
      P⁻¹ • ∫ x : SpaceTime, dotL (F i x) (G x) ∂μ :=
    pairF_eq_restrictedProductIntegral (hTerm i)
  rw [pairF_eq_restrictedProductIntegral hTotal, hint]
  simp_rw [hpair]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Guarded weighted finite additivity of `pairF` in its second vector field argument. -/
theorem pairF_weightedSum_right_of_integrable {P : ℝ} [Fact (0 < P)]
    {a : Fin 2 → ℂ} {F : SpaceTime → CVec3} {G : Fin 2 → SpaceTime → CVec3}
    (hTerm : ∀ i, Integrable (fun x => dotL (F x) (G i x))
      (volume.restrict (phaseCell P)))
    (hTotal : Integrable (fun x => dotL
      (F x) (∑ i : Fin 2, a i • G i x)) (volume.restrict (phaseCell P))) :
    pairF P F (fun x => ∑ i : Fin 2, a i • G i x) =
      ∑ i : Fin 2, a i * pairF P F (G i) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  have hscaled (i : Fin 2) : Integrable
      (fun x => a i * dotL (F x) (G i x)) μ := by
    simpa [μ, mul_comm] using (hTerm i).const_mul (a i)
  have hpoint (x : SpaceTime) :
      dotL (F x) (∑ i : Fin 2, a i • G i x) =
        ∑ i : Fin 2, a i * dotL (F x) (G i x) := by
    calc
      _ = dotL (F x) (∑ i : Fin 2, a i • G i x) := rfl
      _ = ∑ i : Fin 2, (dotL (F x)) (a i • G i x) := by
        rw [map_sum]
      _ = _ := by simp
  have hint :
      ∫ x : SpaceTime, dotL (F x) (∑ i : Fin 2, a i • G i x) ∂μ =
        ∑ i : Fin 2, a i * ∫ x : SpaceTime, dotL (F x) (G i x) ∂μ := by
    calc
      _ = ∫ x : SpaceTime, ∑ i : Fin 2, a i * dotL (F x) (G i x) ∂μ :=
        integral_congr_ae (ae_of_all _ hpoint)
      _ = ∑ i : Fin 2, ∫ x : SpaceTime, a i * dotL (F x) (G i x) ∂μ := by
        rw [integral_finsetSum Finset.univ (fun i hi => hscaled i)]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
  have hpair (i : Fin 2) : pairF P F (G i) =
      P⁻¹ • ∫ x : SpaceTime, dotL (F x) (G i x) ∂μ :=
    pairF_eq_restrictedProductIntegral (hTerm i)
  rw [pairF_eq_restrictedProductIntegral hTotal, hint]
  simp_rw [hpair]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The pairing against the affine inlet in the second slot is the exact coordinate-weighted sum
of pairings against its actual inlet columns. -/
theorem pairF_affineInlet_right_eq_weighted {p : Params} (z : p.Z)
    {F : SpaceTime → CVec3}
    (hTerm : ∀ i : Fin 2, Integrable (fun x => dotL (F x) (p.Efun i x))
      (volume.restrict (phaseCell p.period)))
    (hTotal : Integrable (fun x => dotL (F x) (p.eFun (p.coord z) x))
      (volume.restrict (phaseCell p.period))) :
    pairF p.period F (p.eFun (p.coord z)) =
      ∑ i : Fin 2, (p.coord z i : ℂ) * pairF p.period F (p.Efun i) := by
  rw [eFun_eq_weighted_inletColumns z]
  exact pairF_weightedSum_right_of_integrable
    (a := fun i => (p.coord z i : ℂ)) hTerm
    (by simpa only [eFun_eq_weighted_inletColumns z] using hTotal)

/-- Transpose advection by the affine inlet in the first slot is the exact coordinate-weighted
sum of the corresponding inlet-column pairings. -/
theorem pairF_affineInlet_advT_left_eq_weighted {p : Params} (z : p.Z)
    (Φ : SpaceTime → CVec3) {G : SpaceTime → CVec3}
    (hTerm : ∀ i : Fin 2, Integrable
      (fun x => dotL (advT (p.Efun i) Φ x) (G x))
      (volume.restrict (phaseCell p.period)))
    (hTotal : Integrable
      (fun x => dotL (advT (p.eFun (p.coord z)) Φ x) (G x))
      (volume.restrict (phaseCell p.period))) :
    pairF p.period (advT (p.eFun (p.coord z)) Φ) G =
      ∑ i : Fin 2, (p.coord z i : ℂ) * pairF p.period (advT (p.Efun i) Φ) G := by
  rw [advT_eFun_eq_weighted_inletColumns z Φ]
  exact pairF_weightedSum_left_of_integrable
    (a := fun i => (p.coord z i : ℂ)) hTerm
    (by simpa only [advT_eFun_eq_weighted_inletColumns z Φ] using hTotal)

/-- The transpose convection pairing is additive in the advecting field when all three actual
cell integrals exist. -/
theorem pairF_advT_add_left_of_integrable {P : ℝ} [Fact (0 < P)]
    {A B H : SpaceTime → CVec3} {Φ : SpaceTime → CVec3}
    (hA : Integrable (fun x => dotL (advT A Φ x) (H x))
      (volume.restrict (phaseCell P)))
    (hB : Integrable (fun x => dotL (advT B Φ x) (H x))
      (volume.restrict (phaseCell P)))
    (hAB : Integrable (fun x => dotL (advT (fun y => A y + B y) Φ x) (H x))
      (volume.restrict (phaseCell P))) :
    pairF P (advT (fun y => A y + B y) Φ) H =
      pairF P (advT A Φ) H + pairF P (advT B Φ) H := by
  have hAdv : advT (fun y => A y + B y) Φ =
      fun x => advT A Φ x + advT B Φ x := by
    funext x
    simp [advT, Finset.sum_add_distrib, add_smul]
  have hsum : Integrable (fun x => dotL (advT A Φ x + advT B Φ x) (H x))
      (volume.restrict (phaseCell P)) := by
    apply Integrable.congr hAB
    filter_upwards [] with x
    rw [congrFun hAdv x]
  rw [hAdv]
  exact pairF_add_left_of_integrable hA hB hsum

/-- Guarded bilinear expansion of the total convection pairing under a sum of two actual
fields. The four term integrability hypotheses are retained individually. -/
theorem pairF_advT_sum_sum_expand_of_integrable {P : ℝ} [Fact (0 < P)]
    {A B H K Φ : SpaceTime → CVec3}
    (hAA : Integrable (fun x => dotL (advT A Φ x) (H x))
      (volume.restrict (phaseCell P)))
    (hAB : Integrable (fun x => dotL (advT A Φ x) (K x))
      (volume.restrict (phaseCell P)))
    (hBA : Integrable (fun x => dotL (advT B Φ x) (H x))
      (volume.restrict (phaseCell P)))
    (hBB : Integrable (fun x => dotL (advT B Φ x) (K x))
      (volume.restrict (phaseCell P)))
    (hTotal : Integrable (fun x => dotL
      (advT (fun y => A y + B y) Φ x) (H x + K x))
      (volume.restrict (phaseCell P))) :
    pairF P (advT (fun y => A y + B y) Φ) (fun x => H x + K x) =
      pairF P (advT A Φ) H + pairF P (advT A Φ) K +
      pairF P (advT B Φ) H + pairF P (advT B Φ) K := by
  have hA : Integrable (fun x => dotL (advT A Φ x) (H x + K x))
      (volume.restrict (phaseCell P)) := by
    apply Integrable.congr (hAA.add hAB)
    filter_upwards [] with x
    simp [dotL_apply, mul_add, Finset.sum_add_distrib]
  have hB : Integrable (fun x => dotL (advT B Φ x) (H x + K x))
      (volume.restrict (phaseCell P)) := by
    apply Integrable.congr (hBA.add hBB)
    filter_upwards [] with x
    simp [dotL_apply, mul_add, Finset.sum_add_distrib]
  calc
    _ = pairF P (advT A Φ) (fun x => H x + K x) +
        pairF P (advT B Φ) (fun x => H x + K x) :=
      pairF_advT_add_left_of_integrable hA hB hTotal
    _ = _ := by
      rw [pairF_add_right_of_integrable hAA hAB hA,
        pairF_add_right_of_integrable hBA hBB hB]
      ac_rfl

/-- The full raw-plus-state convection pairing splits into its four bilinear pieces. All four
pieces and the total are integrable from the actual raw/inlet and graph suppliers. -/
theorem selectedFullBackground_pairF_rawState_fourTerm {p : Params}
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular)
    {B : Budget} {z : p.Z} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
      (fun x => p.Ufun x + p.uOf z x) =
      pairF p.period (advT p.Ufun Φ) p.Ufun +
      pairF p.period (advT p.Ufun Φ) (p.uOf z) +
      pairF p.period (advT (p.uOf z) Φ) p.Ufun +
      pairF p.period (advT (p.uOf z) Φ) (p.uOf z) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let T : Fin 3 → SpaceTime → CVec3 := selectedFullConvectionTerm p z
  let D : Fin 3 → Fin 3 → SpaceTime → ℂ := fun i j x =>
    dotL (advT (T i) Φ x) (T j x)
  have hD (i j : Fin 3) : Integrable (D i j) μ := by
    simpa [D, μ, T] using
      selectedFullBackground_quadraticTerms_integrable (B := B) hRaw hInlet hΦ i j
  have hInner (i : Fin 3) : Integrable (fun x : SpaceTime => ∑ j : Fin 3, D i j x) μ := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hD i j
  have hSum : Integrable
      (fun x : SpaceTime => ∑ i : Fin 3, ∑ j : Fin 3, D i j x) μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hInner i
  have hsumT : (fun x : SpaceTime => ∑ i : Fin 3, T i x) =
      (fun x => p.Ufun x + p.uOf z x) := by
    exact selectedFullConvectionTerm_sum_eq_raw_add_state p (B := B) z
  have htotalPoint (x : SpaceTime) :
      dotL (advT (fun y => p.Ufun y + p.uOf z y) Φ x)
        (p.Ufun x + p.uOf z x) = ∑ i : Fin 3, ∑ j : Fin 3, D i j x := by
    have hsumValue : p.Ufun x + p.uOf z x = ∑ i : Fin 3, T i x := by
      exact (congrFun hsumT x).symm
    rw [← hsumT, hsumValue]
    let A : Fin 3 → CVec3 := fun i => advT (T i) Φ x
    let C : Fin 3 → CVec3 := fun j => T j x
    have hAdv : advT (fun y => ∑ i : Fin 3, T i y) Φ x = ∑ i : Fin 3, A i := by
      change (∑ k : Fin 3, (∑ i : Fin 3, T i x k) • dy k Φ x) =
        ∑ i : Fin 3, ∑ k : Fin 3, T i x k • dy k Φ x
      calc
        _ = ∑ k : Fin 3, ∑ i : Fin 3, T i x k • dy k Φ x := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_smul]
        _ = ∑ i : Fin 3, ∑ k : Fin 3, T i x k • dy k Φ x := by
          rw [Finset.sum_comm]
        _ = _ := rfl
    rw [hAdv]
    change dotL (∑ i : Fin 3, A i) (∑ j : Fin 3, C j) = _
    have hfirst : dotL (∑ i : Fin 3, A i) = ∑ i : Fin 3, dotL (A i) := by
      rw [map_sum]
    rw [hfirst, ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sum]
  have htotal : Integrable
      (fun x : SpaceTime => dotL (advT (fun y => p.Ufun y + p.uOf z y) Φ x)
        (p.Ufun x + p.uOf z x)) μ :=
    Integrable.congr hSum (ae_of_all _ fun x => (htotalPoint x).symm)
  have h00 : Integrable (fun x => dotL (advT p.Ufun Φ x) (p.Ufun x)) μ := by
    change Integrable (D 0 0) μ
    exact hD 0 0
  have h01 : Integrable (fun x => dotL (advT p.Ufun Φ x) (p.uOf z x)) μ := by
    have h := (hD 0 1).add (hD 0 2)
    apply Integrable.congr h
    filter_upwards [] with x
    change (∑ i : Fin 3, (advT p.Ufun Φ x) i * (p.eFun (p.coord z) x) i) +
        (∑ i : Fin 3, (advT p.Ufun Φ x) i * (rep (p.wOf z) x.1 x.2) i) =
      ∑ i : Fin 3, (advT p.Ufun Φ x) i *
        ((p.eFun (p.coord z) x) i + (rep (p.wOf z) x.1 x.2) i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h10 : Integrable (fun x => dotL (advT (p.uOf z) Φ x) (p.Ufun x)) μ := by
    have h := (hD 1 0).add (hD 2 0)
    apply Integrable.congr h
    filter_upwards [] with x
    have hAdv : advT (p.uOf z) Φ x = advT (T 1) Φ x + advT (T 2) Φ x := by
      change advT (fun y => T 1 y + T 2 y) Φ x = _
      simp [advT, Finset.sum_add_distrib, add_smul]
    rw [hAdv]
    change (∑ i : Fin 3, (advT (T 1) Φ x) i * (p.Ufun x) i) +
        (∑ i : Fin 3, (advT (T 2) Φ x) i * (p.Ufun x) i) =
      ∑ i : Fin 3, ((advT (T 1) Φ x) i + (advT (T 2) Φ x) i) * (p.Ufun x) i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h11 : Integrable (fun x => dotL (advT (p.uOf z) Φ x) (p.uOf z x)) μ := by
    simpa [μ] using
      selectedState_quadraticConvection_integrable hInlet (B := B) (z := z) hΦ
  exact pairF_advT_sum_sum_expand_of_integrable h00 h01 h10 h11 htotal

/-- The two cross pieces in the raw-plus-state convection are exactly the coordinate-weighted
raw/inlet cross pairings plus the raw/graph cross pairings. The inlet terms use actual bounded
columns, and the graph terms use the selected joint representative. -/
theorem selectedState_rawStateCross_pairF_expand {p : Params}
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular)
    {B : Budget} {z : p.Z} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    (pairF p.period (advT p.Ufun Φ) (p.uOf z) +
      pairF p.period (advT (p.uOf z) Φ) p.Ufun) =
      (pairF p.period (advT p.Ufun Φ) (fun x => rep (p.wOf z) x.1 x.2) +
        pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ) p.Ufun) +
      ∑ i : Fin 2, (p.coord z i : ℂ) *
        (pairF p.period (advT p.Ufun Φ) (p.Efun i) +
          pairF p.period (advT (p.Efun i) Φ) p.Ufun) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let E : SpaceTime → CVec3 := p.eFun (p.coord z)
  let W : SpaceTime → CVec3 := fun x => rep (p.wOf z) x.1 x.2
  let U : SpaceTime → CVec3 := p.Ufun
  letI : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hV : IsBoundedBackground
      (fun τ y => ∑ i : Fin 2, (p.coord z i) • p.inlet i τ y) :=
    isBoundedBackground_affineInlet hInlet (p.coord z)
  have hUe : Integrable (fun x => dotL (advT U Φ x) (E x)) μ := by
    change Integrable
      (fun x => dotL (advT (fun x : SpaceTime => realC (p.raw x.1 x.2)) Φ x)
        (realC (∑ i : Fin 2, (p.coord z i) • p.inlet i x.1 x.2)))
      (volume.restrict (phaseCell p.period))
    exact integrable_advT_pair_boundedBackgrounds (P := p.period) (Φ := Φ)
      (V := p.raw)
      (W := fun τ y => ∑ i : Fin 2, (p.coord z i) • p.inlet i τ y)
      hΦ hRaw.1 hV
  have hUw : Integrable (fun x => dotL (advT U Φ x) (W x)) μ := by
    simpa [U, W, Params.uOf, selectedFullConvectionTerm, μ] using
      selectedFullBackground_quadraticTerms_integrable (B := B) hRaw hInlet hΦ 0 2
  have hUtotal : Integrable (fun x => dotL (advT U Φ x) (E x + W x)) μ := by
    apply Integrable.congr (hUe.add hUw)
    filter_upwards [] with x
    change dotL (advT U Φ x) (E x) + dotL (advT U Φ x) (W x) =
      dotL (advT U Φ x) (E x + W x)
    rw [dotL_apply, dotL_apply, dotL_apply]
    change (∑ i : Fin 3, (advT U Φ x) i * (E x) i) +
        ∑ i : Fin 3, (advT U Φ x) i * (W x) i =
      ∑ i : Fin 3, (advT U Φ x) i * ((E x) i + (W x) i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hEraw : Integrable (fun x => dotL (advT E Φ x) (U x)) μ := by
    change Integrable
      (fun x => dotL
        (advT (fun x : SpaceTime => realC
          (∑ i : Fin 2, (p.coord z i) • p.inlet i x.1 x.2)) Φ x)
        (realC (p.raw x.1 x.2)))
      (volume.restrict (phaseCell p.period))
    exact integrable_advT_pair_boundedBackgrounds (P := p.period) (Φ := Φ)
      (V := fun τ y => ∑ i : Fin 2, (p.coord z i) • p.inlet i τ y)
      (W := p.raw) hΦ hV hRaw.1
  have hWraw : Integrable (fun x => dotL (advT W Φ x) (U x)) μ := by
    simpa [U, W, selectedFullConvectionTerm, μ] using
      selectedFullBackground_quadraticTerms_integrable (B := B) hRaw hInlet hΦ 2 0
  have hstateAdv : advT (fun x => E x + W x) Φ =
      fun x => advT E Φ x + advT W Φ x := by
    funext x
    simp [advT, Finset.sum_add_distrib, add_smul]
  have htotalStateRaw : Integrable
      (fun x => dotL (advT (fun y => E y + W y) Φ x) (U x)) μ := by
    apply Integrable.congr (hEraw.add hWraw)
    filter_upwards [] with x
    rw [congrFun hstateAdv x]
    change dotL (advT E Φ x) (U x) + dotL (advT W Φ x) (U x) =
      dotL (advT E Φ x + advT W Φ x) (U x)
    rw [dotL_apply, dotL_apply, dotL_apply]
    change (∑ i : Fin 3, (advT E Φ x) i * (U x) i) +
        ∑ i : Fin 3, (advT W Φ x) i * (U x) i =
      ∑ i : Fin 3, ((advT E Φ x) i + (advT W Φ x) i) * (U x) i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have htermsRight (i : Fin 2) :
      Integrable (fun x => dotL (advT U Φ x) (p.Efun i x)) μ := by
    change Integrable
      (fun x => dotL (advT (fun x : SpaceTime => realC (p.raw x.1 x.2)) Φ x)
        (realC (p.inlet i x.1 x.2))) (volume.restrict (phaseCell p.period))
    exact integrable_advT_pair_boundedBackgrounds (P := p.period) (Φ := Φ)
      (V := p.raw) (W := p.inlet i) hΦ hRaw.1 (hInlet i).1
  have htermsLeft (i : Fin 2) :
      Integrable (fun x => dotL (advT (p.Efun i) Φ x) (U x)) μ := by
    change Integrable
      (fun x => dotL (advT (fun x : SpaceTime => realC (p.inlet i x.1 x.2)) Φ x)
        (realC (p.raw x.1 x.2))) (volume.restrict (phaseCell p.period))
    exact integrable_advT_pair_boundedBackgrounds (P := p.period) (Φ := Φ)
      (V := p.inlet i) (W := p.raw) hΦ (hInlet i).1 hRaw.1
  have hright := pairF_affineInlet_right_eq_weighted (p := p) z htermsRight
    (by simpa [U, E] using hUe)
  have hleft := pairF_affineInlet_advT_left_eq_weighted (p := p) z Φ htermsLeft
    (by simpa [U, E] using hEraw)
  change (pairF p.period (advT U Φ) (fun x => E x + W x) +
      pairF p.period (advT (fun x => E x + W x) Φ) U) = _
  rw [pairF_add_right_of_integrable hUe hUw hUtotal]
  rw [pairF_advT_add_left_of_integrable hEraw hWraw
    htotalStateRaw]
  rw [hright, hleft]
  simp only [Fin.sum_univ_succ]
  ring

#print axioms pairF_add_left_of_integrable
#print axioms pairF_add_right_of_integrable
#print axioms pairF_weightedSum_left_of_integrable
#print axioms pairF_weightedSum_right_of_integrable
#print axioms pairF_affineInlet_right_eq_weighted
#print axioms pairF_affineInlet_advT_left_eq_weighted
#print axioms pairF_advT_add_left_of_integrable
#print axioms pairF_advT_sum_sum_expand_of_integrable
#print axioms selectedFullBackground_pairF_rawState_fourTerm
#print axioms selectedState_rawStateCross_pairF_expand

end UnforcedLeray.Cons.C03.Concrete
