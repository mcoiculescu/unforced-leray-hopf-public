import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.CompactFreeBodyRate.NormBridge
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphFlat
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceCylLpAe
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceWeakSolenoidal
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePlanarPerpZero
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L2.Slices
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2

/-!
# Identification of `T0flat` with `IIb.IsFlatResponse` in `IIb.InFlatClass c 2`

Shows that for `F ∈ InHr c 2` and `b0 ∈ InFlatClass c 2` solving `IsFlatResponse ν μ F b0`,
the periodic extension `B0220.periodize c (PartIIa.T0flat hc ν μ FH)` agrees `hMeas c 2`-almost
everywhere with `b0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.CompactFreeRateSub

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
  (stripSet measurePreserving_shiftQ ae_slices_of_measureH planeι_measurePreserving
   causalHeat_congr_of_slices hj2_integral_measureH_complex pepsC0FubiniSol pepsC0SliceDivFreeAE)

private theorem qPeriodic_int_flat {c : ℝ} {b : Profile → MeridC} (hper : B0220.QPeriodic c b)
    (m : ℤ) (p : Profile) :
    b (p.1, p.2.1 + (m : ℝ) * c, p.2.2) = b p := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : p.2.1 + ((k + 1 : ℤ) : ℝ) * c = (p.2.1 + ((k : ℤ) : ℝ) * c) + c := by push_cast; ring
    rw [e, hper (p.1, p.2.1 + ((k : ℤ) : ℝ) * c, p.2.2), ih]
  | pred k ih =>
    have e : (p.2.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c) + c = p.2.1 + ((-(k : ℤ) : ℤ) : ℝ) * c := by
      push_cast; ring
    have hstep := hper (p.1, p.2.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, p.2.2)
    dsimp only at hstep
    rw [e] at hstep
    exact hstep.symm.trans ih

private theorem periodize_eq_self_flat {c : ℝ} {f : Profile → MeridC}
    (hper : B0220.QPeriodic c f) :
    B0220.periodize c f = f := by
  funext p
  unfold B0220.periodize
  set m : ℤ := 1 - ⌈p.2.1 / c⌉
  have hred : B0220.reduceIoc c p.2.1 = p.2.1 + (m : ℝ) * c := by
    unfold B0220.reduceIoc; push_cast [m]; ring
  rw [hred]
  exact qPeriodic_int_flat hper m p

theorem ae_hMeas_periodize_congr {c : ℝ} (hc : 0 < c)
    {f g : Profile → MeridC} (hfg : f =ᵐ[measureH c] g) :
    B0220.periodize c f =ᵐ[hMeas c 2] B0220.periodize c g := by
  set G : Set Profile := {p | 0 < p.1 ∧ B0220.periodize c f p ≠ B0220.periodize c g p}
  have hcl : MeasurableSet (B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hnull : measureH c {p | f p ≠ g p} = 0 := ae_iff.1 hfg
  have hw : AEMeasurable weightH (volume.restrict (B0220.cell c)) :=
    measurable_weightH.aemeasurable
  have hcell : volume (G ∩ B0220.cell c) = 0 := by
    unfold measureH cellMeasure at hnull
    rw [withDensity_apply_eq_zero' hw, Measure.restrict_apply' hcl] at hnull
    refine measure_mono_null ?_ hnull
    rintro p ⟨hpG, hpc⟩
    refine ⟨⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpc.1 _)).ne', ?_⟩, hpc⟩
    intro heq
    apply hpG.2
    unfold B0220.periodize
    rw [B0220.reduceIoc_of_mem hc hpc.2.1]
    exact heq
  have hGcl : ∀ m : ℤ, volume ((fun p : Profile =>
      (p.1, p.2.1 + (m : ℝ) * c, p.2.2)) ⁻¹' (G ∩ B0220.cell c)) = 0 := fun m =>
    (measurePreserving_shiftQ ((m : ℝ) * c)).quasiMeasurePreserving.preimage_null hcell
  have hsub : G ⊆ ⋃ m : ℤ, (fun p : Profile =>
      (p.1, p.2.1 + (m : ℝ) * c, p.2.2)) ⁻¹' (G ∩ B0220.cell c) := by
    intro p hp
    set m : ℤ := 1 - ⌈p.2.1 / c⌉
    have hval : p.2.1 + (m : ℝ) * c = B0220.reduceIoc c p.2.1 := by
      unfold B0220.reduceIoc; push_cast [m]; ring
    have hmem : B0220.reduceIoc c p.2.1 ∈ Ioc 0 c := B0220.reduceIoc_mem hc _
    have hfix : ∀ K : Profile → MeridC,
        B0220.periodize c K (p.1, p.2.1 + (m : ℝ) * c, p.2.2) = B0220.periodize c K p := fun K => by
      unfold B0220.periodize
      rw [hval, B0220.reduceIoc_of_mem hc hmem]
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    show (p.1, p.2.1 + (m : ℝ) * c, p.2.2) ∈ G ∩ B0220.cell c
    refine ⟨⟨hp.1, ?_⟩, ⟨hp.1, ?_, trivial⟩⟩
    · show B0220.periodize c f (p.1, p.2.1 + (m : ℝ) * c, p.2.2) ≠
        B0220.periodize c g (p.1, p.2.1 + (m : ℝ) * c, p.2.2)
      rw [hfix f, hfix g]; exact hp.2
    · show p.2.1 + (m : ℝ) * c ∈ Ioc 0 c
      rw [hval]; exact hmem
  have hG0 : volume G = 0 := measure_mono_null hsub (measure_iUnion_null hGcl)
  refine ae_hMeas_of_ae_pos hc ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hG0] with p hp hpos
  by_contra hne
  exact hp ⟨hpos, hne⟩

/-! ### 1. `WeakSolenoidal` for `periodize c (PepsC 0 c FH)` -/

private theorem memLp_avgμ_of_isCylTest {c : ℝ} (hc : 0 < c) {ψ : ℝ × ℝ → ℝ}
    (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    MemLp (fun z : ℝ × ℝ => (ψ z : ℂ)) 2 (UnforcedLeray.Cyl.avgμ c) := by
  obtain ⟨L, hL⟩ := hψ.band
  let A : Set (ℝ × ℝ) := Icc (-c / 2) (c / 2) ×ˢ Icc (-max L 0) (max L 0)
  have hA : IsCompact A := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun z : ℝ × ℝ => (ψ z : ℂ)) :=
    Complex.continuous_ofReal.comp hψ.smooth.continuous
  have hfin : UnforcedLeray.Cyl.avgμ c A ≠ ⊤ := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [Measure.smul_apply, smul_eq_mul]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((Measure.restrict_apply_le _ _).trans_lt (hA.measure_lt_top (μ := volume)))).ne
  have hcell_ae : ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), z ∈ UnforcedLeray.Cyl.cell c := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne').2
      (ae_restrict_mem (measurableSet_Ico.prod MeasurableSet.univ))
  refine B0226.memLp_of_continuous_of_ae_vanish hcont hA hfin ?_ 2
  filter_upwards [hcell_ae] with z hz hzA
  have hgt : L < |z.2| := by
    by_contra hle
    exact hzA ⟨Ico_subset_Icc_self hz.1, abs_le.1 ((not_lt.1 hle).trans (le_max_left L 0))⟩
  simp [hL z hgt]

private theorem weakSolenoidal_periodize_pepsC0 {c : ℝ} (hc : 0 < c) (FH : HSpace c MeridC) :
    WeakSolenoidal (B0220.periodize c (PepsC 0 c FH : Profile → MeridC)) := by
  set W : HSpace c MeridC := PepsC 0 c FH
  set G₀ : CProf := B0220.periodize c (W : Profile → MeridC)
  have hG₀_sm : StronglyMeasurable G₀ :=
    (measurable_periodize_merid c (Lp.stronglyMeasurable W).measurable).stronglyMeasurable
  have hG₀_per : ∀ (s : ℝ) (z : ℝ × ℝ), G₀ (s, (z.1 + c, z.2)) = G₀ (s, z) :=
    fun s z => qPeriodic_periodize hc (W : Profile → MeridC) (s, z)
  have hG₀_hr : InHr c 2 G₀ := inHr_periodize hc W
  have hW_mem : W ∈ solenoidalHC 0 c := Submodule.starProjection_apply_mem _ FH
  have hdiv_ae := pepsC0SliceDivFreeAE c hc W hW_mem
  have hcyl_ae := sliceCylLpAe_proof c 2 hc one_lt_two G₀ hG₀_sm hG₀_per hG₀_hr.finite
  refine sliceWeakSolenoidal_proof c 2 G₀ hc one_lt_two hG₀_sm hG₀_per hG₀_hr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hdiv_ae, hcyl_ae] with s hs hdiv hcyl Φ hΦ
  have hΦ_cyl : UnforcedLeray.B0579.IsCylTest c Φ := ⟨hΦ.smooth, hΦ.periodic, hΦ.bounded⟩
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hG_mem : MemLp (fun z => G₀ (s, z)) 2 (UnforcedLeray.Cyl.avgμ c) := by
    have hm := hcyl.2
    rwa [h2] at hm
  have hG_comp : ∀ i : Fin 2, MemLp (fun z => G₀ (s, z) i) 2 (UnforcedLeray.Cyl.avgμ c) :=
    fun i => (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).comp_memLp' hG_mem
  have hpd0_eq : ∀ z : ℝ × ℝ, fderiv ℝ Φ z (1, 0) = UnforcedLeray.B0579.pd 0 Φ z := fun _ => rfl
  have hpd1_eq : ∀ z : ℝ × ℝ, fderiv ℝ Φ z (0, 1) = UnforcedLeray.B0579.pd 1 Φ z := fun _ => rfl
  have hint0 : Integrable (fun z => G₀ (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    simp_rw [hpd0_eq]
    exact (hG_comp 0).integrable_mul (memLp_avgμ_of_isCylTest hc (hΦ_cyl.pd 0))
  have hint1 : Integrable (fun z => G₀ (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ))
      (UnforcedLeray.Cyl.avgμ c) := by
    simp_rw [hpd1_eq]
    exact (hG_comp 1).integrable_mul (memLp_avgμ_of_isCylTest hc (hΦ_cyl.pd 1))
  refine ⟨hint0.add hint1, ?_⟩
  set hFun : ℝ × ℝ → ℂ := fun z =>
    G₀ (s, z) 0 * (fderiv ℝ Φ z (1, 0) : ℂ) + G₀ (s, z) 1 * (fderiv ℝ Φ z (0, 1) : ℂ)
  have hh_per : UnforcedLeray.Cyl.IsPeriodic c hFun := fun z => by
    have hp0 : UnforcedLeray.B0579.pd 0 Φ (z.1 + c, z.2) = UnforcedLeray.B0579.pd 0 Φ z :=
      (hΦ_cyl.pd 0).periodic z
    have hp1 : UnforcedLeray.B0579.pd 1 Φ (z.1 + c, z.2) = UnforcedLeray.B0579.pd 1 Φ z :=
      (hΦ_cyl.pd 1).periodic z
    show hFun (z.1 + c, z.2) = hFun z
    simp only [hFun, hpd0_eq, hpd1_eq, hG₀_per s z, hp0, hp1]
  rw [UnforcedLeray.Cyl.integral_avgμ hc.le, ← B0224.integral_strip_eq_cell hc hh_per]
  have hstrip_eq : ∫ z in B0224.strip c, hFun z =
      ∫ x in stripSet c,
        ((W : Profile → MeridC) (s, x) 0 * (UnforcedLeray.B0579.pd 0 Φ x : ℂ) +
          (W : Profile → MeridC) (s, x) 1 * (UnforcedLeray.B0579.pd 1 Φ x : ℂ)) := by
    change ∫ x in stripSet c, hFun x = _
    refine setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) fun x hx => ?_
    have hcell_mem : (s, x) ∈ B0220.cell c := ⟨hs, hx.1, trivial⟩
    have hG_W : G₀ (s, x) = (W : Profile → MeridC) (s, x) :=
      B0220.periodize_of_mem hc (W : Profile → MeridC) hcell_mem
    simp only [hFun, hpd0_eq, hpd1_eq, hG_W]
  rw [hstrip_eq, hdiv Φ hΦ_cyl, smul_zero]

/-! ### 2. `PerpPlanarSol` for `F - periodize c (PepsC 0 c FH)` -/

private theorem exists_planarSolTest_band {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    ∃ (s0 s1 L : ℝ), 0 < s0 ∧ 0 ≤ L ∧
      ∀ (i : Fin 2) (y : Coord), Ψ y i ≠ 0 → y.1 ∈ Icc s0 s1 ∧ |y.2.2| ≤ L := by
  let K : Set Coord := tsupport (fun x => Ψ x 0) ∪ tsupport (fun x => Ψ x 1)
  have hK : IsCompact K := (hΨ.smooth 0).compact.isCompact.union (hΨ.smooth 1).compact.isCompact
  have hK_pos : ∀ x ∈ K, 0 < x.1 := by
    rintro x (hx | hx)
    · exact ((hΨ.smooth 0).supp hx).1
    · exact ((hΨ.smooth 1).supp hx).1
  by_cases hKne : K.Nonempty
  · obtain ⟨xmin, hxminK, hmin⟩ := hK.exists_isMinOn hKne continuous_fst.continuousOn
    obtain ⟨xmax, _, hmax⟩ := hK.exists_isMaxOn hKne continuous_fst.continuousOn
    obtain ⟨xL, _, hLmax⟩ := hK.exists_isMaxOn hKne
      (continuous_abs.comp (continuous_snd.comp continuous_snd)).continuousOn
    refine ⟨xmin.1, xmax.1, |xL.2.2|, hK_pos xmin hxminK, abs_nonneg _, fun i y hy => ?_⟩
    have hyK : y ∈ K := by
      fin_cases i
      · exact Or.inl (subset_tsupport _ hy)
      · exact Or.inr (subset_tsupport _ hy)
    exact ⟨⟨hmin hyK, hmax hyK⟩, hLmax hyK⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    refine ⟨1, 1, 0, one_pos, le_refl 0, fun i y hy => ?_⟩
    exfalso
    have hyK : y ∈ K := by
      fin_cases i
      · exact Or.inl (subset_tsupport _ hy)
      · exact Or.inr (subset_tsupport _ hy)
    rw [hKne] at hyK
    exact hyK

private theorem perpPlanarSol_sub_periodize_pepsC0 {c : ℝ} (hc : 0 < c)
    {F F' : CProf} {M : Set Coord} {FH : HSpace c MeridC}
    (hF : InHr c 2 F) (hF'm : Measurable F')
    (hF'per : ∀ s q η, F' (s, (q + c, η)) = F' (s, (q, η)))
    (hM0 : volume M = 0)
    (hFF' : ∀ x : Coord, 0 < x.1 → x ∉ M → F x = F' x)
    (hF'_ae : F' =ᵐ[hMeas c 2] F)
    (hFH_coe : (FH : Profile → MeridC) =ᵐ[measureH c] F') :
    PerpPlanarSol (F - B0220.periodize c (PepsC 0 c FH : Profile → MeridC)) := by
  set W : HSpace c MeridC := PepsC 0 c FH
  set G₀ : CProf := B0220.periodize c (W : Profile → MeridC)
  have hG₀_sm : StronglyMeasurable G₀ :=
    (measurable_periodize_merid c (Lp.stronglyMeasurable W).measurable).stronglyMeasurable
  have hG₀_per : ∀ (s : ℝ) (z : ℝ × ℝ), G₀ (s, (z.1 + c, z.2)) = G₀ (s, z) :=
    fun s z => qPeriodic_periodize hc (W : Profile → MeridC) (s, z)
  have hG₀_hr : InHr c 2 G₀ := inHr_periodize hc W
  have hF's : StronglyMeasurable F' := hF'm.stronglyMeasurable
  have hF'per2 : ∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z) :=
    fun s z => hF'per s z.1 z.2
  have hN' : hNorm c 2 F' < ⊤ := by
    have heq : hNorm c 2 F' = hNorm c 2 F := eLpNorm_congr_ae hF'_ae
    rw [heq]; exact hF.finite
  have hFa : ∀ᵐ x ∂(volume : Measure Coord), 0 < x.1 → F x = F' x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hM0] with x hxM hx0
    exact hFF' x hx0 hxM
  intro Ψ hΨ
  have hvol : (volume : Measure Coord) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.volume_eq_prod _ _
  have hFint : ∀ k : Fin 2, Integrable (fun x : Coord => F' x k * ((Ψ x k : ℝ) : ℂ)) := fun k => by
    have hK : IntegrableOn F' (tsupport (fun x => Ψ x k)) :=
      LerayLiftSub.integrableOnCompact_proof c 2 F' hc one_lt_two hF's hF'per2 hN' _
        (hΨ.smooth k).compact.isCompact (hΨ.smooth k).supp
    exact (integrableTestPair_proof F' (fun x => Ψ x k) (hΨ.smooth k) hK).1 k
  have hGint : ∀ k : Fin 2, Integrable (fun x : Coord => G₀ x k * ((Ψ x k : ℝ) : ℂ)) := fun k => by
    have hK : IntegrableOn G₀ (tsupport (fun x => Ψ x k)) :=
      LerayLiftSub.integrableOnCompact_proof c 2 G₀ hc one_lt_two hG₀_sm hG₀_per hG₀_hr.finite _
        (hΨ.smooth k).compact.isCompact (hΨ.smooth k).supp
    exact (integrableTestPair_proof G₀ (fun x => Ψ x k) (hΨ.smooth k) hK).1 k
  have hD : ∀ k : Fin 2, Integrable (fun x : Coord => (F' x k - G₀ x k) * ((Ψ x k : ℝ) : ℂ)) :=
    fun k => ((hFint k).sub (hGint k)).congr (Eventually.of_forall fun x => by simp; ring)
  have hh : Integrable (fun x : Coord => ∑ i : Fin 2, (F' x i - G₀ x i) * ((Ψ x i : ℝ) : ℂ)) :=
    integrable_finsetSum Finset.univ fun i _ => hD i
  have hhP : Integrable (fun x : Coord => ∑ i : Fin 2, (F' x i - G₀ x i) * ((Ψ x i : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rw [← hvol]; exact hh
  have hae : (fun x : Coord => cdot (F - G₀) Ψ x) =ᵐ[volume]
      fun x : Coord => ∑ i : Fin 2, (F' x i - G₀ x i) * ((Ψ x i : ℝ) : ℂ) := by
    filter_upwards [hFa] with x hx
    by_cases hx0 : 0 < x.1
    · simp only [cdot, Pi.sub_apply, PiLp.sub_apply, hx hx0]
    · have hz : ∀ i : Fin 2, Ψ x i = 0 := fun i =>
        image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) fun h => hx0 ((hΨ.smooth i).supp h).1
      simp [cdot, hz]
  refine ⟨hh.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, hvol, integral_prod _ hhP]
  -- Build the smooth periodized test `M_Ψ ∈ solenoidalHC 0 c`
  obtain ⟨s0, s1, L, hs0, _, hband⟩ := exists_planarSolTest_band hΨ
  obtain ⟨R0, hR0⟩ := pcell_bound_gen (hΨ.smooth 0).compact (fun y : Coord => y.2.1) (by fun_prop)
  obtain ⟨R1, hR1⟩ := pcell_bound_gen (hΨ.smooth 1).compact (fun y : Coord => y.2.1) (by fun_prop)
  have hp0_cont : Continuous (pcellPer c (fun x => Ψ x 0)) :=
    (pcellPer_contDiff (hΨ.smooth 0).smooth hc hR0).continuous
  have hp1_cont : Continuous (pcellPer c (fun x => Ψ x 1)) :=
    (pcellPer_contDiff (hΨ.smooth 1).smooth hc hR1).continuous
  let M_fun : Profile → Fin 2 → ℂ := fun p i =>
    ((p.1 ^ (3 / 2 : ℝ) * pcellPer c (fun x => Ψ x i) p : ℝ) : ℂ)
  let M_Ψ : Profile → MeridC := fun p => WithLp.toLp 2 (M_fun p)
  have hs_cont : Continuous (fun p : Profile => p.1 ^ (3 / 2 : ℝ)) :=
    continuous_fst.rpow_const fun _ => Or.inr (by norm_num)
  have hM_cont : Continuous M_Ψ := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact Complex.continuous_ofReal.comp (hs_cont.mul hp0_cont)
    · exact Complex.continuous_ofReal.comp (hs_cont.mul hp1_cont)
  have hM_supp : ∀ (p : Profile) (i : Fin 2), pcellPer c (fun x => Ψ x i) p ≠ 0 →
      p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro p i hne
    have hex : ∃ n : ℤ, Ψ (p.1, (p.2.1 - n * c, p.2.2)) i ≠ 0 := by
      by_contra hall
      exact hne (by simp [pcellPer, fun n => not_ne_iff.1 (not_exists.1 hall n)])
    obtain ⟨n, hn⟩ := hex
    exact hband i (p.1, (p.2.1 - n * c, p.2.2)) hn
  have hA_comp : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hM_mem : MemLp M_Ψ 2 (measureH c) := by
    refine B0226.memLp_of_continuous_of_ae_vanish hM_cont hA_comp
      (B0226.measureH_band_ne_top c hs0 s1 L) ?_ 2
    filter_upwards [ae_cell_measureH c] with p hp hpA
    ext i
    show M_fun p i = 0
    have hp_zero : pcellPer c (fun x => Ψ x i) p = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := hM_supp p i hne
      exact hpA ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩
    simp [M_fun, hp_zero]
  -- Show `hM_mem.toLp M_Ψ ∈ solenoidalHC 0 c`
  have hM_sol : hM_mem.toLp M_Ψ ∈ solenoidalHC 0 c := by
    unfold solenoidalHC
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Φt, hg, rfl⟩ := hx
      have hFub := pepsC0FubiniSol c hc Φt hg M_fun hM_mem
      refine hFub.trans ?_
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      have hs_pos : 0 < s := hs
      set ψ : ℝ × ℝ → ℝ := fun y => Φt.1 (s, y)
      have hψ : UnforcedLeray.B0579.IsCylTest c ψ := by
        refine ⟨Φt.2.smooth.comp (contDiff_const.prodMk contDiff_id),
          fun x => Φt.2.periodic (s, x.1, x.2), ?_⟩
        obtain ⟨_, _, Lφ, _, hb⟩ := Φt.2.band
        refine ⟨Lφ, fun x hx => ?_⟩
        by_contra hne
        exact absurd (hb (s, x) hne).2 (not_le.mpr hx)
      have hc0 : ∀ x : ℝ × ℝ, cgrad 0 Φt.1 (s, x) 0 = ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) := by
        intro x
        have hd : HasFDerivAt Φt.1 (fderiv ℝ Φt.1 (s, x)) (s, x) :=
          ((Φt.2.smooth.differentiable (by simp)) (s, x)).hasFDerivAt
        have hcomp := hd.comp x (hasFDerivAt_prodMk_right s x)
        have hpd : UnforcedLeray.Axi.dQ Φt.1 (s, x) = UnforcedLeray.B0579.pd 0 ψ x := by
          rw [UnforcedLeray.Axi.dQ, UnforcedLeray.B0579.pd]
          change _ = fderiv ℝ (Φt.1 ∘ fun y : ℝ × ℝ => (s, y)) x _
          rw [hcomp.fderiv]; simp [UnforcedLeray.B0579.dir]
        simp [cgrad, B0226.Deps_zero, hpd]
      have hc1 : ∀ x : ℝ × ℝ, cgrad 0 Φt.1 (s, x) 1 = ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) := by
        intro x
        have hd : HasFDerivAt Φt.1 (fderiv ℝ Φt.1 (s, x)) (s, x) :=
          ((Φt.2.smooth.differentiable (by simp)) (s, x)).hasFDerivAt
        have hcomp := hd.comp x (hasFDerivAt_prodMk_right s x)
        have hpd : UnforcedLeray.Axi.dEta Φt.1 (s, x) = UnforcedLeray.B0579.pd 1 ψ x := by
          rw [UnforcedLeray.Axi.dEta, UnforcedLeray.B0579.pd]
          change _ = fderiv ℝ (Φt.1 ∘ fun y : ℝ × ℝ => (s, y)) x _
          rw [hcomp.fderiv]; simp [UnforcedLeray.B0579.dir]
        simp [cgrad, hpd]
      let Θ : ℝ × ℝ → Fin 2 → ℝ := fun z i => pcellPer c (fun y => Ψ y i) (s, z)
      have hΘ_sol : CylSolTest c Θ := LerayLiftSub.slicePerSolTest_proof c Ψ hc hΨ s
      have hΘ_df : UnforcedLeray.Short.IIIa.IsDivFreeTestField c Θ :=
        ⟨fun i => ⟨(hΘ_sol.comp i).smooth, (hΘ_sol.comp i).periodic, (hΘ_sol.comp i).bounded⟩,
          fun z => hΘ_sol.div_free z⟩
      let hReal : ℝ × ℝ → ℝ := fun x =>
        Θ x 0 * UnforcedLeray.B0579.pd 0 ψ x + Θ x 1 * UnforcedLeray.B0579.pd 1 ψ x
      have hhR_per : UnforcedLeray.Cyl.IsPeriodic c hReal := fun x => by
        have hp0 := (hψ.pd 0).periodic x
        have hp1 := (hψ.pd 1).periodic x
        have hΘ0 := (hΘ_sol.comp 0).periodic x
        have hΘ1 := (hΘ_sol.comp 1).periodic x
        show hReal (x.1 + c, x.2) = hReal x
        simp only [hReal, hp0, hp1, hΘ0, hΘ1]
      have hint_rew : (fun x : ℝ × ℝ => ∑ i : Fin 2, cgrad 0 Φt.1 (s, x) i * M_fun (s, x) i) =
          fun x => ((s ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (hReal x • (1 : ℂ)) := by
        funext x
        rw [Fin.sum_univ_two, hc0 x, hc1 x, Complex.real_smul, mul_one]
        simp only [M_fun, Θ, hReal]
        push_cast
        ring
      have hcell_eq : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
        unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell; rw [neg_div]
      change ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in B0224.strip c, ∑ i : Fin 2, cgrad 0 Φt.1 (s, x) i * M_fun (s, x) i = 0
      rw [hint_rew, integral_const_mul, integral_smul_const,
        B0224.integral_strip_eq_cell hc hhR_per, hcell_eq,
        UnforcedLeray.Short.IIIa.div_zero_aux_p0orth c Θ hΘ_df ψ hψ,
        zero_smul, mul_zero, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  -- Orthogonality `⟪M_Ψ, FH - W⟫_H = 0` unfolds to the planar integral of `(F' - G₀)·Ψ`
  have horth : inner ℂ (hM_mem.toLp M_Ψ) (FH - W) = 0 :=
    (Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal FH) _ hM_sol
  set pairH : Profile → ℂ := fun p =>
    ∑ i : Fin 2, starRingEnd ℂ (M_Ψ p i) * (F' p i - G₀ p i)
  have hFW_ae : ((FH - W : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
      fun p => F' p - G₀ p := by
    filter_upwards [Lp.coeFn_sub FH W, hFH_coe, periodize_ae_measureH hc W] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, ← h3]
  have hinner_ae : (fun p => inner ℂ (hM_mem.toLp M_Ψ p) ((FH - W : HSpace c MeridC) p))
      =ᵐ[measureH c] pairH := by
    filter_upwards [hM_mem.coeFn_toLp, hFW_ae] with p h1 h2
    rw [h1, h2]
    simp only [pairH, PiLp.inner_apply, PiLp.sub_apply, Fin.sum_univ_two, RCLike.inner_apply]
    ring
  have hpairH_int : Integrable pairH (measureH c) :=
    (L2.integrable_inner (hM_mem.toLp M_Ψ) (FH - W)).congr hinner_ae
  rw [L2.inner_def, integral_congr_ae hinner_ae, hj2_integral_measureH_complex hpairH_int] at horth
  have hDP : ∀ k : Fin 2, Integrable (fun x : Coord => (F' x k - G₀ x k) * ((Ψ x k : ℝ) : ℂ))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    intro k; rw [← hvol]; exact hD k
  have hA_slice : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k : Fin 2,
      Integrable (fun z : ℝ × ℝ => (F' (s, z) k - G₀ (s, z) k) * ((Ψ (s, z) k : ℝ) : ℂ)) :=
    ae_all_iff.2 fun k => (hDP k).prod_right_ae
  -- Identify the `s > 0` slice of `horth` with `∫_{ℝ²} (F' - G₀)·Ψ` via `integral_cell_periodize_mul`
  have hslice_eq : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ∫ x in B0224.strip c, pairH (s, x) =
        ∫ z : ℝ × ℝ, ∑ i : Fin 2, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hA_slice] with s hs hs_int
    have hs_pos : 0 < s := hs
    have hΨc := LerayLiftSub.slicePerSolTest_proof c Ψ hc hΨ s
    have hpair_s : ∀ x : ℝ × ℝ, pairH (s, x) = ((s ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        ∑ i : Fin 2, ((pcellPer c (fun y => Ψ y i) (s, x) : ℝ) : ℂ) *
          (F' (s, x) i - G₀ (s, x) i) := fun x => by
      simp only [pairH, M_Ψ, M_fun, Complex.conj_ofReal, Fin.sum_univ_two]
      push_cast
      ring
    simp_rw [hpair_s]
    rw [integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hs_pos]
    have hexp0 : -(3 / 2 : ℝ) + 3 / 2 = 0 := by norm_num
    rw [hexp0, Real.rpow_zero, Complex.ofReal_one, one_mul]
    set hPerSum : ℝ × ℝ → ℂ := fun z =>
      ∑ i : Fin 2, ((pcellPer c (fun y => Ψ y i) (s, z) : ℝ) : ℂ) * (F' (s, z) i - G₀ (s, z) i)
    have hhPerSum_per : UnforcedLeray.Cyl.IsPeriodic c hPerSum := fun z => by
      have hp0 := (hΨc.comp 0).periodic z
      have hp1 := (hΨc.comp 1).periodic z
      show hPerSum (z.1 + c, z.2) = hPerSum z
      simp only [hPerSum, Fin.sum_univ_two, hF'per2 s z, hG₀_per s z]
      rw [hp0, hp1]
    rw [B0224.integral_strip_eq_cell hc hhPerSum_per]
    have hfs : ∀ i : Fin 2, StronglyMeasurable (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) := fun i =>
      (Complex.continuous_ofReal.comp
        ((hΨ.smooth i).smooth.continuous.comp (continuous_const.prodMk continuous_id))).stronglyMeasurable
    have hgs : ∀ i : Fin 2, StronglyMeasurable (fun z : ℝ × ℝ => F' (s, z) i - G₀ (s, z) i) :=
      fun i =>
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (hF's.comp_measurable measurable_prodMk_left)).sub
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
          (hG₀_sm.comp_measurable measurable_prodMk_left))
    have hgper : ∀ i : Fin 2, UnforcedLeray.Cyl.IsPeriodic c (fun z => F' (s, z) i - G₀ (s, z) i) :=
      fun i z => by show F' (s, (z.1 + c, z.2)) i - G₀ (s, (z.1 + c, z.2)) i = _; rw [hF'per2 s z, hG₀_per s z]
    have hper_i : ∀ i : Fin 2, ∀ z : ℝ × ℝ,
        UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) z =
          ((pcellPer c (fun x => Ψ x i) (s, z) : ℝ) : ℂ) := fun i z => by
      unfold UnforcedLeray.Cyl.periodize pcellPer
      rw [Complex.ofReal_tsum]
    have hPf : ∀ i : Fin 2, StronglyMeasurable
        (UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ))) := fun i => by
      rw [funext (hper_i i)]
      exact (Complex.continuous_ofReal.comp (hΨc.comp i).smooth.continuous).stronglyMeasurable
    have hfgI : ∀ i : Fin 2,
        Integrable (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ) * (F' (s, z) i - G₀ (s, z) i)) :=
      fun i => (hs_int i).congr (ae_of_all _ fun _ => mul_comm _ _)
    have hcellI : ∀ i : Fin 2, IntegrableOn
        (fun z : ℝ × ℝ => ((pcellPer c (fun y => Ψ y i) (s, z) : ℝ) : ℂ) *
          (F' (s, z) i - G₀ (s, z) i)) (UnforcedLeray.Cyl.cell c) := fun i =>
      (LerayLiftSub.cellPeriodizeMulIntegrable_proof c _ _ hc (hfs i) (hgs i) (hPf i)
        (hgper i) (hfgI i)).congr (ae_of_all _ fun z => by dsimp only; rw [hper_i i z])
    have key : ∀ i : Fin 2,
        ∫ z in UnforcedLeray.Cyl.cell c,
          ((pcellPer c (fun y => Ψ y i) (s, z) : ℝ) : ℂ) * (F' (s, z) i - G₀ (s, z) i) =
          ∫ z : ℝ × ℝ, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) := fun i => by
      calc ∫ z in UnforcedLeray.Cyl.cell c,
              ((pcellPer c (fun y => Ψ y i) (s, z) : ℝ) : ℂ) * (F' (s, z) i - G₀ (s, z) i)
          = ∫ z in UnforcedLeray.Cyl.cell c,
              UnforcedLeray.Cyl.periodize c (fun z : ℝ × ℝ => ((Ψ (s, z) i : ℝ) : ℂ)) z *
                (F' (s, z) i - G₀ (s, z) i) :=
            integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [hper_i i z])
        _ = ∫ z : ℝ × ℝ, ((Ψ (s, z) i : ℝ) : ℂ) * (F' (s, z) i - G₀ (s, z) i) :=
            UnforcedLeray.Cyl.integral_cell_periodize_mul hc (hfs i) (hgs i) (hgper i) (hfgI i)
        _ = ∫ z : ℝ × ℝ, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) :=
            integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
    rw [show ∫ z in UnforcedLeray.Cyl.cell c, hPerSum z =
          ∑ i : Fin 2, ∫ z in UnforcedLeray.Cyl.cell c,
            ((pcellPer c (fun y => Ψ y i) (s, z) : ℝ) : ℂ) * (F' (s, z) i - G₀ (s, z) i)
        from integral_finsetSum _ fun i _ => hcellI i,
      show ∫ z : ℝ × ℝ, ∑ i : Fin 2, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) =
          ∑ i : Fin 2, ∫ z : ℝ × ℝ, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ)
        from integral_finsetSum _ fun i _ => hs_int i]
    exact Finset.sum_congr rfl fun i _ => key i
  have hIoi_zero : ∫ s in Ioi (0 : ℝ),
      ∫ z : ℝ × ℝ, ∑ i : Fin 2, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) = 0 := by
    rw [← integral_congr_ae hslice_eq]
    exact horth
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
    have hs_le : ¬ 0 < s := hs
    have hz : ∀ z : ℝ × ℝ, ∑ i : Fin 2, (F' (s, z) i - G₀ (s, z) i) * ((Ψ (s, z) i : ℝ) : ℂ) = 0 :=
      fun z => by
        have hΨ0 : ∀ i : Fin 2, Ψ (s, z) i = 0 := fun i =>
          image_eq_zero_of_notMem_tsupport (f := fun y => Ψ y i) fun h => hs_le ((hΨ.smooth i).supp h).1
        simp [hΨ0]
    simp [hz]]
  exact hIoi_zero

/-! ### 3. `flatDuhamel` on `G₀` solves `IsFlatResponse` in `InFlatClass c 2` and matches `T0flat` -/

private theorem flatDuhamel_inFlatClass_and_resp {ν c : ℝ} {μ : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hγ : 0 < μ.re + 1 / 4)
    {F G₀ : CProf} (hF : InHr c 2 F) (hGH : InHr c 2 G₀)
    (hGn : hNorm c 2 G₀ ≤ ENNReal.ofReal 1 * hNorm c 2 F)
    (hGs : WeakSolenoidal G₀) (hGp : PerpPlanarSol (F - G₀)) :
    IsFlatResponse ν μ F (flatDuhamel ν μ G₀) ∧ InFlatClass c 2 (flatDuhamel ν μ G₀) := by
  have hr : (1 : ℝ) < 2 := one_lt_two
  have hr3 : (2 : ℝ) < 3 := by norm_num
  have ha : 0 < μ.re + (3 / (2 : ℝ) - 1) / 2 := by
    have heq : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
    rwa [heq]
  have hbm := duhamelMeasurable 2 hr hr3 μ ha ν c hν hc G₀ hGH
  have hbn := duhamelBound 2 hr hr3 μ ha ν c hν hc G₀ hGH
  have hbper := duhamelPeriodic ν μ c G₀ hc hGH.periodic
  set b := flatDuhamel ν μ G₀
  have hbH : InHr c 2 b :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal 2 hr hr3 μ ha ν c hν hc G₀ hGH hGs hbH
  have hresp : IsFlatResponse ν μ F b := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation 2 hr hr3 μ ha ν c hν hc G₀ hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G₀ Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]; exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]; exact he
  have hfull := duhamelFullEq 2 hr hr3 μ ha ν c hν hc G₀ hGH hbH
  have hW_prop := windowBound_of winCutProps (windowHeatEq_of winCutProps)
    cylHeatMaxReg cylGradInterp windowWeightCompare
  obtain ⟨K, hK, hWK⟩ := hW_prop 2 hr hr3 μ
  set A : ℝ := 1 / (μ.re + (3 / (2 : ℝ) - 1) / 2)
  set B : ℝ := 1 + A
  have hA0 : 0 ≤ A := one_div_nonneg.2 ha.le
  have hK4 : 0 ≤ 4 * K := mul_nonneg (by norm_num) hK.le
  have hbF : hNorm c 2 b ≤ ENNReal.ofReal A * hNorm c 2 F := by
    calc hNorm c 2 b ≤ ENNReal.ofReal A * hNorm c 2 G₀ := hbn
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal 1 * hNorm c 2 F) := by gcongr
      _ = ENNReal.ofReal A * hNorm c 2 F := by rw [ENNReal.ofReal_one, one_mul]
  have hP : ENNReal.ofReal (4 * K) * (hNorm c 2 G₀ + hNorm c 2 b) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c 2 F := by
    have hGbF : hNorm c 2 G₀ + hNorm c 2 b ≤ ENNReal.ofReal B * hNorm c 2 F := by
      rw [ENNReal.ofReal_add zero_le_one hA0, add_mul]
      exact add_le_add hGn hbF
    calc ENNReal.ofReal (4 * K) * (hNorm c 2 G₀ + hNorm c 2 b)
        ≤ ENNReal.ofReal (4 * K) * (ENNReal.ofReal B * hNorm c 2 F) := by gcongr
      _ = ENNReal.ofReal (4 * K * B) * hNorm c 2 F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK4]
  have hPfin : ENNReal.ofReal (4 * K * B) * hNorm c 2 F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  obtain ⟨S, Q, E, hw⟩ := hWK ν c hν hc G₀ b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := weakGlue vS fw_vS_smooth c b S
    (fun a ha' => (hw a ha').1) (fun a ha' => (hw a ha').2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := weakGlue vQ0 fw_vQ0_smooth c b Q
    (fun a ha' => (hw a ha').2.1) (fun a ha' => (hw a ha').2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := weakGlue vEta fw_vEta_smooth c b E
    (fun a ha' => (hw a ha').2.2.1) (fun a ha' => (hw a ha').2.2.2.2.2.1)
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c 2 (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) G₀ +
        hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) b) := fun k => by
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.1
  have hSn : hNorm c 2 Sb ≤ ENNReal.ofReal (4 * K * B) * hNorm c 2 F := by
    have h := dyadicSummation 2 c hr.le hc Sb G₀ b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c 2)) hGH.meas hbH.meas hSk
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h.trans hP
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c 2 (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) G₀ +
        hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) b) := fun k => by
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.1
  have hQn : ENNReal.ofReal (Real.sqrt ν) * hNorm c 2 (sqrtS Qb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c 2 F :=
    (dyadicSummation 2 c hr.le hc (sqrtS Qb) G₀ b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c 2))) hGH.meas hbH.meas
      hQk).trans hP
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c 2 (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) G₀ +
        hNormOn c 2 (winSet2 ((2 : ℝ) ^ k)) b) := fun k => by
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2
  have hEn : ENNReal.ofReal (Real.sqrt ν) * hNorm c 2 (sqrtS Eb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c 2 F :=
    (dyadicSummation 2 c hr.le hc (sqrtS Eb) G₀ b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c 2))) hGH.meas hbH.meas
      hEk).trans hP
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQfin : hNorm c 2 (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hPfin).ne hsq0
  have hEfin : hNorm c 2 (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hPfin).ne hsq0
  refine ⟨hresp, ⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
    ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c 2), lt_of_le_of_lt hSn hPfin⟩,
    ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c 2)), hQfin⟩,
    ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c 2)), hEfin⟩⟩⟩

private theorem planeHeat_eq_flatHeat {θ : ℝ} (hθ : 0 < θ) (u : ℝ × ℝ → MeridC) (x : ℝ × ℝ) :
    B0224.planeHeat θ u x = flatHeat θ u x := by
  let ePlane : UnforcedLeray.Gaussian.Euc 2 ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.finTwoArrow)
  have hePlane_apply : ∀ y : UnforcedLeray.Gaussian.Euc 2, ePlane y = B0224.planeι y := fun _ => rfl
  have hmp : MeasurePreserving ePlane volume volume := planeι_measurePreserving
  have hkern : ∀ y : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ y = flatHeatKernel θ (B0224.planeι y) := fun y => by
    rw [B0224.planeι_apply]
    unfold UnforcedLeray.Gaussian.gaussKernel flatHeatKernel
    have hexp : -((2 : ℕ) : ℝ) / 2 = -1 := by norm_num
    have hnorm : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
        sq_abs, sq_abs]
    rw [hexp, Real.rpow_neg_one, hnorm]
  rw [B0224.planeHeat_of_pos hθ, flatHeat]
  have hcomp := hmp.integral_comp ePlane.measurableEmbedding
    (fun w : ℝ × ℝ => flatHeatKernel θ w • u (x - w))
  refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans hcomp
  rw [hkern y, ← hePlane_apply y]

private theorem qPeriodic_causalHeat {c : ℝ} (hc : 0 < c) (ν : ℝ) (μ : ℂ)
    (F : Profile → MeridC) : B0220.QPeriodic c (B0225.causalHeat c ν μ F) := fun p => by
  unfold B0225.causalHeat
  refine intervalIntegral.integral_congr fun σ _ => ?_
  dsimp only
  congr 1
  exact B0224.isPeriodic_planeHeat (B0224.isPeriodic_periodize_slice hc F σ) p.2

theorem t0flat_ae_eq_flat_response {ν c : ℝ} {μ : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hγ : 0 < μ.re + 1 / 4)
    {F b0 : CProf} (hF : InHr c 2 F)
    (hb0_resp : IsFlatResponse ν μ F b0) (hb0_class : InFlatClass c 2 b0)
    {F' : CProf} {M : Set Coord} {FH : HSpace c MeridC}
    (hF'm : Measurable F')
    (hF'per : ∀ s q η, F' (s, (q + c, η)) = F' (s, (q, η)))
    (hM0 : volume M = 0)
    (hFF' : ∀ x : Coord, 0 < x.1 → x ∉ M → F x = F' x)
    (hF'_ae : F' =ᵐ[hMeas c 2] F)
    (hFH_coe : (FH : Profile → MeridC) =ᵐ[measureH c] F')
    (hFH_norm : ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal ‖FH‖ = hNorm c 2 F) :
    B0220.periodize c (T0flat hc ν μ FH : Profile → MeridC) =ᵐ[hMeas c 2] b0 := by
  set W : HSpace c MeridC := PepsC 0 c FH
  set G₀ : CProf := B0220.periodize c (W : Profile → MeridC)
  have hG₀_m : Measurable G₀ := measurable_periodize_merid c (Lp.stronglyMeasurable W).measurable
  have hG₀_per : B0220.QPeriodic c G₀ := qPeriodic_periodize hc (W : Profile → MeridC)
  have hG₀_hr : InHr c 2 G₀ := inHr_periodize hc W
  have hG₀_norm : hNorm c 2 G₀ ≤ ENNReal.ofReal 1 * hNorm c 2 F := by
    rw [ENNReal.ofReal_one, one_mul, hNorm_two_eq hc hG₀_m hG₀_per,
      eLpNorm_congr_ae (periodize_ae_measureH hc W), ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top W),
      ← Lp.norm_def, ← hFH_norm]
    gcongr
    exact Submodule.norm_starProjection_apply_le _ FH
  have hGs : WeakSolenoidal G₀ := weakSolenoidal_periodize_pepsC0 hc FH
  have hGp : PerpPlanarSol (F - G₀) :=
    perpPlanarSol_sub_periodize_pepsC0 hc hF hF'm hF'per hM0 hFF' hF'_ae hFH_coe
  set b_c : CProf := flatDuhamel ν μ G₀
  obtain ⟨hb_c_resp, hb_c_class⟩ :=
    flatDuhamel_inFlatClass_and_resp hν hc hγ hF hG₀_hr hG₀_norm hGs hGp
  have ha : 0 < μ.re + (3 / (2 : ℝ) - 1) / 2 := by
    have heq : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
    rwa [heq]
  have hb0_sub : b0 - b_c =ᵐ[hMeas c 2] 0 :=
    flat_unique hc hν one_lt_two (by norm_num) ha (b0 - b_c)
      (flatClassSub c 2 b0 b_c hb0_class hb_c_class)
      (flatResponseSub ν μ F b0 b_c hb0_resp hb_c_resp)
  have hb_c_eq_b0 : b_c =ᵐ[hMeas c 2] b0 := by
    filter_upwards [hb0_sub] with x hx
    exact (sub_eq_zero.1 hx).symm
  -- Identify `periodize c (T0flat hc ν μ FH)` with `b_c = flatDuhamel ν μ G₀`
  let g : HgSpace c MeridC := (B0220.MsEquiv c MeridC).symm W
  have hMs_g : B0220.Ms c MeridC g = W := by
    rw [← B0220.MsEquiv_apply]
    exact LinearIsometryEquiv.apply_symm_apply _ W
  have hT0_eq : T0flat hc ν μ FH = B0225.R0 hc ν μ (B0220.Ms c MeridC g) := by
    change B0225.R0 hc ν μ W = _
    rw [hMs_g]
  have hT0_causal : (T0flat hc ν μ FH : Profile → MeridC) =ᵐ[measureH c]
      B0225.causalHeat c ν μ (g : Profile → MeridC) := by
    rw [hT0_eq]
    exact B0225.R0_Ms_ae_causalHeat hc ν hγ g
  have hper_T0 : B0220.periodize c (T0flat hc ν μ FH : Profile → MeridC) =ᵐ[hMeas c 2]
      B0225.causalHeat c ν μ (g : Profile → MeridC) := by
    have h1 := ae_hMeas_periodize_congr hc hT0_causal
    rwa [periodize_eq_self_flat (qPeriodic_causalHeat hc ν μ (g : Profile → MeridC))] at h1
  set g₀ : Profile → MeridC := fun p => p.1⁻¹ • G₀ p
  have hg_ae : (g : Profile → MeridC) =ᵐ[measureH c] g₀ := by
    have hMs_coe := B0220.coeFn_Ms c g
    rw [hMs_g] at hMs_coe
    filter_upwards [hMs_coe, periodize_ae_measureH hc W, ae_cell_measureH c] with p hp1 hp2 hp_cell
    have hs0 : p.1 ≠ 0 := hp_cell.1.ne'
    have hG_eq : p.1 • (g : Profile → MeridC) p = G₀ p := hp1.symm.trans hp2.symm
    calc (g : Profile → MeridC) p = p.1⁻¹ • (p.1 • (g : Profile → MeridC) p) :=
          (inv_smul_smul₀ hs0 _).symm
      _ = p.1⁻¹ • G₀ p := by rw [hG_eq]
  have hg₀_per : B0220.QPeriodic c g₀ := fun p => by
    show p.1⁻¹ • G₀ (p.1, p.2.1 + c, p.2.2) = p.1⁻¹ • G₀ p
    rw [hG₀_per p]
  have hcausal_eq_bc : B0225.causalHeat c ν μ (g : Profile → MeridC) =ᵐ[hMeas c 2] b_c := by
    refine ae_hMeas_of_ae_pos hc (Eventually.of_forall fun p hp => ?_)
    rw [causalHeat_congr_of_slices μ hν (ae_slices_of_measureH hc hg_ae) p hp]
    unfold B0225.causalHeat b_c flatDuhamel
    rw [intervalIntegral.integral_of_le hp.le,
      Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := p.1)).symm]
    refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
    have hθ : 0 < ν * (p.1 - σ) := mul_pos hν (sub_pos.2 hσ.2)
    have hper_g₀ : (fun z => B0220.periodize c g₀ (σ, z)) = fun z => σ⁻¹ • G₀ (σ, z) := by
      rw [periodize_eq_self_flat hg₀_per]
    rw [hper_g₀, B0224.planeHeat_smul]
    dsimp only
    rw [planeHeat_eq_flatHeat hθ, ← Complex.coe_smul σ⁻¹, smul_smul]
  exact hper_T0.trans (hcausal_eq_bc.trans hb_c_eq_b0)

end UnforcedLeray.Short.IIb.CompactFreeRateSub
