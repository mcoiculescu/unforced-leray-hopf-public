import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal.DuhamelIntegrable

/-!
# Part II-b, task `PartII-b:T12/6/3` (`DsolSwap`): Fubini bookkeeping

Source of record: `the November 2 reference manuscript`, lines 1920-1930
(SP 1924, the Duhamel formula). The target `DsolSwap` is the statement of `Sub/T12_6.lean`.
The integrability input is `dsolDuhamelIntegrable` (`DuhamelIntegrable.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The Fubini integrand: the Duhamel body `1_{0<t<s} body(x,t)` paired with `(∂_q φ, ∂_η φ)(x)`. -/
def dswG (ν : ℝ) (μ : ℂ) (G : CProf) (φ : Coord → ℝ) (p : Coord × ℝ) : ℂ :=
  duhamelS.indicator (duhamelBody ν μ G) p 0 * (cpd 1 φ p.1 : ℂ) +
    duhamelS.indicator (duhamelBody ν μ G) p 1 * (cpd 2 φ p.1 : ℂ)

/-- A box `[σ,H] × [-R,R]²` with `σ > 0` containing the support of a coordinate test. -/
theorem dswBox {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ σ H R : ℝ, 0 < σ ∧ tsupport φ ⊆ Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) := by
  have hK : IsCompact (tsupport φ) := hφ.compact
  have hK₁ : IsCompact (insert ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) (tsupport φ)) := hK.insert _
  obtain ⟨x₀, hx₀, hmin⟩ :=
    hK₁.exists_isMinOn (Set.insert_nonempty _ _) continuous_fst.continuousOn
  have hpos : (0 : ℝ) < x₀.1 := by
    rcases Set.mem_insert_iff.mp hx₀ with h | h
    · rw [h]; norm_num
    · exact (hφ.supp h).1
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨x₀.1, R, R, hpos, fun y hy => ?_⟩
  have hn : ‖y‖ ≤ R := hR y hy
  have hy1 : ‖y.1‖ ≤ R := (norm_fst_le y).trans hn
  have hy2 : ‖y.2.1‖ ≤ R := ((norm_fst_le y.2).trans (norm_snd_le y)).trans hn
  have hy3 : ‖y.2.2‖ ≤ R := ((norm_snd_le y.2).trans (norm_snd_le y)).trans hn
  have hmin' : x₀.1 ≤ y.1 := isMinOn_iff.mp hmin y (Set.mem_insert_of_mem _ hy)
  rw [Real.norm_eq_abs] at hy1 hy2 hy3
  exact ⟨⟨hmin', (abs_le.mp hy1).2⟩, ⟨abs_le.mp hy2, abs_le.mp hy3⟩⟩

/-- The cutoff derivative `∂_j φ` vanishes off a set containing the support of `φ`. -/
theorem dswCpdZero {φ : Coord → ℝ} {B : Set Coord} (hB : tsupport φ ⊆ B) (j : Fin 3)
    {x : Coord} (hx : x ∉ B) : cpd j φ x = 0 := by
  have hfd : fderiv ℝ φ x = 0 := by
    by_contra hne
    exact hx (hB (support_fderiv_subset ℝ (Function.mem_support.mpr hne)))
  simp [cpd, hfd]

theorem dswCpdCont {φ : Coord → ℝ} (hφ : IsCoordTest φ) (j : Fin 3) :
    Continuous (cpd j φ) := by
  unfold cpd
  exact (hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

theorem dswCpdBdd {φ : Coord → ℝ} (hφ : IsCoordTest φ) (j : Fin 3) :
    ∃ C : ℝ, ∀ x : Coord, ‖cpd j φ x‖ ≤ C := by
  have hc : HasCompactSupport (cpd j φ) := by
    unfold cpd
    exact HasCompactSupport.fderiv_apply ℝ hφ.compact (cdir j)
  exact (dswCpdCont hφ j).bounded_above_of_compact_support hc

theorem dswG_zero_of_nmem (ν : ℝ) (μ : ℂ) (G : CProf) {φ : Coord → ℝ} {B : Set Coord}
    (hB : tsupport φ ⊆ B) {x : Coord} (hx : x ∉ B) (t : ℝ) :
    dswG ν μ G φ (x, t) = 0 := by
  unfold dswG
  simp [dswCpdZero hB 1 hx, dswCpdZero hB 2 hx]

theorem dswG_of_nonpos (ν : ℝ) (μ : ℂ) (G : CProf) (φ : Coord → ℝ) (x : Coord) {t : ℝ}
    (ht : t ≤ 0) : dswG ν μ G φ (x, t) = 0 := by
  have hmem : (x, t) ∉ duhamelS := fun h => by
    have h' : t ∈ Ioo (0 : ℝ) x.1 := h
    exact absurd h'.1 (not_lt.mpr ht)
  unfold dswG
  simp [Set.indicator_of_notMem hmem]

theorem dswG_of_pos (ν : ℝ) (μ : ℂ) (G : CProf) (φ : Coord → ℝ) {s t : ℝ} (z : ℝ × ℝ)
    (ht : 0 < t) (hts : t < s) :
    dswG ν μ G φ ((s, z), t) =
      (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
        (flatHeat (ν * (s - t)) (fun w => G (t, w)) z 0 * (cpd 1 φ (s, z) : ℂ) +
          flatHeat (ν * (s - t)) (fun w => G (t, w)) z 1 * (cpd 2 φ (s, z) : ℂ)) := by
  have hmem : ((s, z), t) ∈ duhamelS := show t ∈ Ioo (0 : ℝ) s from ⟨ht, hts⟩
  unfold dswG
  rw [Set.indicator_of_mem hmem]
  unfold duhamelBody
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem dswG_of_le (ν : ℝ) (μ : ℂ) (G : CProf) (φ : Coord → ℝ) {s t : ℝ} (z : ℝ × ℝ)
    (hts : s ≤ t) : dswG ν μ G φ ((s, z), t) = 0 := by
  have hmem : ((s, z), t) ∉ duhamelS := fun h => by
    have h' : t ∈ Ioo (0 : ℝ) s := h
    exact absurd h'.2 (not_lt.mpr hts)
  unfold dswG
  simp [Set.indicator_of_notMem hmem]

/-- One time slice of the Fubini swap: `∫_x dswG (x,t)` is the `s`-integral over `(t,∞)`. -/
theorem dswSlice (ν : ℝ) (μ : ℂ) (G : CProf) (φ : Coord → ℝ) {t : ℝ} (ht : 0 < t)
    (hI : Integrable (fun x : Coord => dswG ν μ G φ (x, t)) volume) :
    ∫ x : Coord, dswG ν μ G φ (x, t) =
      ∫ s in Ioi t, (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
        ∫ z : ℝ × ℝ, (flatHeat (ν * (s - t)) (fun z => G (t, z)) z 0 * (cpd 1 φ (s, z) : ℂ) +
          flatHeat (ν * (s - t)) (fun z => G (t, z)) z 1 * (cpd 2 φ (s, z) : ℂ)) := by
  have hsplit : ∫ x : Coord, dswG ν μ G φ (x, t) =
      ∫ s : ℝ, ∫ z : ℝ × ℝ, dswG ν μ G φ ((s, z), t) :=
    integral_prod (μ := volume) (ν := volume) (fun x : Coord => dswG ν μ G φ (x, t)) hI
  rw [hsplit, ← integral_indicator (measurableSet_Ioi : MeasurableSet (Ioi t))]
  congr 1
  funext s
  by_cases hts : t < s
  · have hs : s ∈ Ioi t := hts
    have key : ∀ z : ℝ × ℝ, dswG ν μ G φ ((s, z), t) =
        (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
          (flatHeat (ν * (s - t)) (fun w => G (t, w)) z 0 * (cpd 1 φ (s, z) : ℂ) +
            flatHeat (ν * (s - t)) (fun w => G (t, w)) z 1 * (cpd 2 φ (s, z) : ℂ)) :=
      fun z => dswG_of_pos ν μ G φ z ht hts
    rw [Set.indicator_of_mem hs]
    simp only [key]
    rw [integral_const_mul]
  · have hs : s ∉ Ioi t := fun h => hts h
    have key : ∀ z : ℝ × ℝ, dswG ν μ G φ ((s, z), t) = 0 :=
      fun z => dswG_of_le ν μ G φ z (not_lt.mp hts)
    rw [Set.indicator_of_notMem hs]
    simp only [key]
    simp

/-- **Leaf `PartII-b:T12/6/3`** (Fubini swap; SP 1924). -/
theorem dsolSwap : DsolSwap := by
  intro c r ν μ G hc hr1 hr3 hν ha hG φ hφ
  obtain ⟨σ, H, R, hσ, hsupp0⟩ := dswBox hφ
  obtain ⟨B, hBdef⟩ : ∃ B : Set Coord, B = Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R) :=
    ⟨_, rfl⟩
  have hsupp : tsupport φ ⊆ B := by rw [hBdef]; exact hsupp0
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hf : Integrable (duhamelS.indicator (duhamelBody ν μ G))
      ((volume.restrict B).prod volume) := by
    rw [hBdef]
    exact dsolDuhamelIntegrable c r ν μ G hc hr1 hr3 hν ha hG σ H R hσ
  -- integrability of the Fubini integrand on `B × ℝ`
  have hg : Integrable (fun q : Coord × ℝ => dswG ν μ G φ q)
      ((volume.restrict B).prod volume) := by
    obtain ⟨C0, hC0⟩ := dswCpdBdd hφ 1
    obtain ⟨C1, hC1⟩ := dswCpdBdd hφ 2
    have hi0 : Integrable (fun q : Coord × ℝ => duhamelS.indicator (duhamelBody ν μ G) q 0)
        ((volume.restrict B).prod volume) := by
      simpa using ContinuousLinearMap.integrable_comp
        (EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ) hf
    have hi1 : Integrable (fun q : Coord × ℝ => duhamelS.indicator (duhamelBody ν μ G) q 1)
        ((volume.restrict B).prod volume) := by
      simpa using ContinuousLinearMap.integrable_comp
        (EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ) hf
    have hm0 : AEStronglyMeasurable (fun q : Coord × ℝ => (cpd 1 φ q.1 : ℂ))
        ((volume.restrict B).prod volume) :=
      (Complex.continuous_ofReal.comp ((dswCpdCont hφ 1).comp continuous_fst)).aestronglyMeasurable
    have hm1 : AEStronglyMeasurable (fun q : Coord × ℝ => (cpd 2 φ q.1 : ℂ))
        ((volume.restrict B).prod volume) :=
      (Complex.continuous_ofReal.comp ((dswCpdCont hφ 2).comp continuous_fst)).aestronglyMeasurable
    have hb0 : ∀ᵐ q ∂((volume.restrict B).prod volume), ‖(cpd 1 φ q.1 : ℂ)‖ ≤ C0 :=
      Filter.Eventually.of_forall (fun q : Coord × ℝ => by rw [Complex.norm_real]; exact hC0 q.1)
    have hb1 : ∀ᵐ q ∂((volume.restrict B).prod volume), ‖(cpd 2 φ q.1 : ℂ)‖ ≤ C1 :=
      Filter.Eventually.of_forall (fun q : Coord × ℝ => by rw [Complex.norm_real]; exact hC1 q.1)
    unfold dswG
    exact (hi0.mul_bdd hm0 hb0).add (hi1.mul_bdd hm1 hb1)
  -- for a.e. `x ∈ B`, the `t`-slice is integrable and the flat Duhamel value is the `t`-integral
  have hae : ∀ᵐ x ∂(volume : Measure Coord), x ∈ B →
      Integrable (fun t : ℝ => duhamelS.indicator (duhamelBody ν μ G) (x, t)) volume :=
    (ae_restrict_iff' hBm).mp hf.prod_right_ae
  have hC2 : ∀ x : Coord,
      Integrable (fun t : ℝ => duhamelS.indicator (duhamelBody ν μ G) (x, t)) volume →
      flatDuhamel ν μ G x 0 * (cpd 1 φ x : ℂ) + flatDuhamel ν μ G x 1 * (cpd 2 φ x : ℂ) =
        ∫ t, dswG ν μ G φ (x, t) := by
    intro x hI
    have hcomp : ∀ i : Fin 2, flatDuhamel ν μ G x i =
        ∫ t, duhamelS.indicator (duhamelBody ν μ G) (x, t) i := by
      intro i
      rw [flatDuhamel_eq_integral]
      have := ContinuousLinearMap.integral_comp_comm
        (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ) hI
      simpa using this.symm
    have hI0 : Integrable (fun t : ℝ => duhamelS.indicator (duhamelBody ν μ G) (x, t) 0)
        volume := by
      simpa using ContinuousLinearMap.integrable_comp
        (EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ) hI
    have hI1 : Integrable (fun t : ℝ => duhamelS.indicator (duhamelBody ν μ G) (x, t) 1)
        volume := by
      simpa using ContinuousLinearMap.integrable_comp
        (EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ) hI
    unfold dswG
    dsimp only
    rw [hcomp 0, hcomp 1, integral_add (hI0.mul_const _) (hI1.mul_const _),
      integral_mul_const, integral_mul_const]
  have hLx0 : ∀ x : Coord, x ∉ B →
      flatDuhamel ν μ G x 0 * (cpd 1 φ x : ℂ) + flatDuhamel ν μ G x 1 * (cpd 2 φ x : ℂ) = 0 := by
    intro x hx
    rw [dswCpdZero hsupp 1 hx, dswCpdZero hsupp 2 hx]
    simp
  have hLHS : ∫ x : Coord, (flatDuhamel ν μ G x 0 * (cpd 1 φ x : ℂ) +
      flatDuhamel ν μ G x 1 * (cpd 2 φ x : ℂ)) = ∫ x in B, ∫ t, dswG ν μ G φ (x, t) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero hLx0).symm.trans ?_
    refine setIntegral_congr_ae hBm ?_
    filter_upwards [hae] with x hx hxB
    exact hC2 x (hx hxB)
  -- Fubini on `B × ℝ`
  have hFub : ∫ x in B, ∫ t, dswG ν μ G φ (x, t) = ∫ t, ∫ x in B, dswG ν μ G φ (x, t) :=
    integral_integral_swap (f := fun x t => dswG ν μ G φ (x, t)) hg
  have hperT : ∀ t : ℝ, ∫ x in B, dswG ν μ G φ (x, t) = ∫ x : Coord, dswG ν μ G φ (x, t) :=
    fun t => setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => dswG_zero_of_nmem ν μ G hsupp hx t)
  have hzeroT : ∀ t : ℝ, t ∉ Ioi (0 : ℝ) → ∫ x : Coord, dswG ν μ G φ (x, t) = 0 := by
    intro t ht
    have ht' : t ≤ 0 := not_lt.mp (show ¬ (0 : ℝ) < t from ht)
    have h0 : ∀ x : Coord, dswG ν μ G φ (x, t) = 0 := fun x => dswG_of_nonpos ν μ G φ x ht'
    simp [h0]
  have hT0 : ∫ t : ℝ, ∫ x : Coord, dswG ν μ G φ (x, t) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Coord, dswG ν μ G φ (x, t) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroT).symm
  have hslice : ∀ᵐ t ∂(volume : Measure ℝ),
      Integrable (fun x : Coord => dswG ν μ G φ (x, t)) volume := by
    filter_upwards [hg.prod_left_ae] with t ht
    exact IntegrableOn.integrable_of_forall_notMem_eq_zero ht
      (fun x hx => dswG_zero_of_nmem ν μ G hsupp hx t)
  have hfin : ∫ t in Ioi (0 : ℝ), ∫ x : Coord, dswG ν μ G φ (x, t) =
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi t, (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) *
        ∫ z : ℝ × ℝ, (flatHeat (ν * (s - t)) (fun z => G (t, z)) z 0 * (cpd 1 φ (s, z) : ℂ) +
          flatHeat (ν * (s - t)) (fun z => G (t, z)) z 1 * (cpd 2 φ (s, z) : ℂ)) := by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [hslice] with t hIt ht
    exact dswSlice ν μ G φ ht hIt
  calc ∫ x : Coord, (flatDuhamel ν μ G x 0 * (cpd 1 φ x : ℂ) +
        flatDuhamel ν μ G x 1 * (cpd 2 φ x : ℂ))
      = ∫ x in B, ∫ t, dswG ν μ G φ (x, t) := hLHS
    _ = ∫ t, ∫ x in B, dswG ν μ G φ (x, t) := hFub
    _ = ∫ t, ∫ x : Coord, dswG ν μ G φ (x, t) := by simp only [hperT]
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : Coord, dswG ν μ G φ (x, t) := hT0
    _ = _ := hfin

end UnforcedLeray.Short.IIb
