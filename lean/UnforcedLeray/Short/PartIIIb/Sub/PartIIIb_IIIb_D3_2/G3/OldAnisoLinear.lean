import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_3

/-!
# `PartIII-b:IIIb-D3/2/G3/1/2`: `ℝ`-linearity of the cell stress readout (`G3.OldReadoutLinear`)

Source of record: `the November 2 reference manuscript` (lines 4409-4412, 4537-4543,
4610-4612).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst

/-- Coordinate projection of a `Merid`-valued `L²` field is in `L²`. -/
private theorem memLp_embedMerid {μm : Measure (ℝ × ℝ)} {v : ℝ × ℝ → Merid}
    (hv : MemLp v 2 μm) (i : Fin 3) :
    MemLp (fun p => IIIa.embedMerid (v p) i) 2 μm := by
  have hcont : Continuous (fun x : Merid => IIIa.embedMerid x i) := by
    fin_cases i
    · exact (EuclideanSpace.proj 0 : Merid →L[ℝ] ℝ).continuous
    · exact continuous_const
    · exact (EuclideanSpace.proj 1 : Merid →L[ℝ] ℝ).continuous
  refine hv.norm.mono' (hcont.comp_aestronglyMeasurable hv.1) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  have hsq : (IIIa.embedMerid (v p) i) ^ 2 ≤ ‖v p‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    fin_cases i <;> simp [IIIa.embedMerid] <;> linarith [sq_nonneg (v p 0), sq_nonneg (v p 1)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (norm_nonneg _))

/-- The train meridional velocity slice at any age `s : ℝ` is in `L²` on the cell. -/
private theorem memLp_trainMer_slice {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) :
    MemLp (fun p => NearInst.trainMer tr (s, p)) 2 (volume.restrict (B0579.cell c)) := by
  by_cases hs : 0 ≤ s
  · have hmer : (fun p : ℝ × ℝ => NearInst.trainMer tr (s, p)) = tr.v s := by
      funext p; ext i; simp [NearInst.trainMer, IIIa.trainVel, hs]
    rw [hmer]
    have hset : UnforcedLeray.Cyl.cell c = B0579.cell c := by
      unfold UnforcedLeray.Cyl.cell B0579.cell
      rw [neg_div]
    have hcont : Continuous (fun x : ℝ × ℝ => tr.v s x) := by
      have hc := tr.isTrain.smooth_v.continuousOn
      refine continuousOn_univ.1 (hc.comp (continuousOn_const.prodMk continuousOn_id) ?_)
      exact fun x _ => ⟨Set.mem_Ici.2 hs, Set.mem_univ _⟩
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
    rw [← hset]
    exact tr.isTrain.finite_energy s hs
  · have hmer : (fun p : ℝ × ℝ => NearInst.trainMer tr (s, p)) = 0 := by
      funext p; ext i; simp [NearInst.trainMer, IIIa.trainVel, hs]
    rw [hmer]
    exact MemLp.zero

/-- Integrability of the normal-stress readout `2 M_{22} - M_{00}` on `B0579.cell c`. -/
private theorem integrable_symOuter_readout_cell {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (ξ : Xmc c m) :
    Integrable (fun p =>
        2 * IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ p) 2 2 -
          IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ p) 0 0)
      (volume.restrict (B0579.cell c)) := by
  set μcell := volume.restrict (B0579.cell c)
  have hv : MemLp (fun p => NearInst.trainMer tr (s, p)) 2 μcell := memLp_trainMer_slice tr s
  have hk : MemLp (kcMer ξ) 2 μcell := (Lp.memLp (kcLp ξ)).ae_eq (kcMer_ae ξ).symm
  have h_ij : ∀ i j : Fin 3,
      Integrable (fun p => IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer ξ p) i j) μcell :=
    fun i j =>
      ((memLp_embedMerid hv i).integrable_mul (memLp_embedMerid hk j)).add
        ((memLp_embedMerid hk i).integrable_mul (memLp_embedMerid hv j))
  exact ((h_ij 2 2).const_mul 2).sub (h_ij 0 0)

/-- Transfer of a.e. equality from `Cyl.avgμ c` to `volume.restrict (B0579.cell c)`. -/
private theorem ae_cell_of_ae_avg {c : ℝ} (hc : 0 < c) {E : Type*} {f g : ℝ × ℝ → E}
    (h : f =ᵐ[Cyl.avgμ c] g) : f =ᵐ[volume.restrict (B0579.cell c)] g := by
  have hcell : Cyl.cell c = B0579.cell c := by
    simp only [Cyl.cell, B0579.cell, neg_div]
  have hne : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  unfold Cyl.avgμ Cyl.cellμ at h
  rw [hcell] at h
  unfold Filter.EventuallyEq at h ⊢
  rwa [Measure.ae_ennreal_smul_measure_eq hne] at h

/-- `cellInt c F` equals `c⁻¹ * ∫ p in B0579.cell c, F p`. -/
private theorem cellInt_eq_cell (c : ℝ) (F : ℝ × ℝ → ℝ) :
    cellInt c F = c⁻¹ * ∫ p, F p ∂(volume.restrict (B0579.cell c)) := by
  unfold cellInt
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) := by
    rw [B0579.cell, neg_div, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  rw [hmeas]

/-- **Leaf 2 (`G3/1/2`)**: `ℝ`-linearity of the cell stress readout (source 4409-4412, 4537-4543,
4610-4612). -/
theorem oldReadoutLinear (D : SeqData) : G3.OldReadoutLinear D := by
  intro dm dp hst κ hκ m hfact hm S hS
  obtain ⟨N, hAct⟩ := eventually_atTop.1 hS
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨FI, hFI⟩ := hAct n hn
  rw [hFI]
  intro s ξ ξ' r
  set ν := retNu D.Pl D.σ₀ n
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  set c := cOf ν
  have hc : 0 < c := cOf_pos hν
  have : Fact (0 < c) := ⟨hc⟩
  set μcell := (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c)
  set F : Xmc c m → ℝ × ℝ → ℝ := fun y p =>
    2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, p)) (kcMer y p) 2 2 -
      IIIa.symOuter (NearInst.trainMer (D.train n) (s, p)) (kcMer y p) 0 0
  obtain ⟨hK_add_avg, hK_smul_avg⟩ := kcMerLinear m ν hν ξ ξ' r
  have hK_add : kcMer (ξ + ξ') =ᵐ[μcell] kcMer ξ + kcMer ξ' := ae_cell_of_ae_avg hc hK_add_avg
  have hK_smul : kcMer ((r : ℂ) • ξ) =ᵐ[μcell] r • kcMer ξ := ae_cell_of_ae_avg hc hK_smul_avg
  have hInt_ξ : Integrable (F ξ) μcell := integrable_symOuter_readout_cell (D.train n) s ξ
  have hInt_ξ' : Integrable (F ξ') μcell := integrable_symOuter_readout_cell (D.train n) s ξ'
  constructor
  · have hF_add : F (ξ + ξ') =ᵐ[μcell] fun p => F ξ p + F ξ' p := by
      filter_upwards [hK_add] with p hp
      dsimp only [F]
      rw [hp, Pi.add_apply, symOuter_add_right']
      simp only [Matrix.add_apply]
      ring
    change cellInt c (F (ξ + ξ')) = cellInt c (F ξ) + cellInt c (F ξ')
    rw [cellInt_eq_cell, cellInt_eq_cell, cellInt_eq_cell, integral_congr_ae hF_add,
      integral_add hInt_ξ hInt_ξ', mul_add]
  · have hF_smul : F ((r : ℂ) • ξ) =ᵐ[μcell] fun p => r * F ξ p := by
      filter_upwards [hK_smul] with p hp
      dsimp only [F]
      rw [hp, Pi.smul_apply, symOuter_smul_right']
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    change cellInt c (F ((r : ℂ) • ξ)) = r * cellInt c (F ξ)
    rw [cellInt_eq_cell, cellInt_eq_cell, integral_congr_ae hF_smul, integral_const_mul]
    ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
